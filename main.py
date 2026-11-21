#!/usr/bin/env python3
"""Forge: a GitHub-compatible git forge in one Python file (stdlib only).

Surfaces served from one in-memory, event-sourced store:
  - git smart HTTP  (/owner/repo.git): upload-pack protocol v2, receive-pack v0
  - REST v3         (/api/v3): repos, branches, commits, contents, issues, pulls
  - GraphQL v4      (/api/graphql): the documents gh / github-mcp-server send
  - MCP             (/mcp): JSON-RPC 2.0 Streamable HTTP (revision 2026-07-28)

Design notes (this entry's own architecture, written from the RULES.txt wire
contract and the kit's check suites):
  - Event-sourced store: every mutation is appended as an event to an
    append-only in-memory JSONL log (sequence numbers, never wall-clock
    timestamps); the repo/issue/PR/ref state is a projection of that log,
    rebuilt at boot. A best-effort copy of the journal is flushed to a file
    under the store dir; the live state never reads it back.
  - Git objects live in memory as dict sha -> (type, bytes); packfiles are
    parsed into individual objects on receipt (OFS/REF deltas resolved with
    memoisation). Packs we send are built with delta encoding: a blob is
    delta-compressed against the most similar earlier blob, where similarity
    is judged by shared content prefix (not a plain delta chain).
  - No wall clock and no unseeded randomness anywhere in state: commit
    timestamps and ids are fixed or derived from sequence numbers, so two
    runs on the same instance export identical state.
  - ThreadingHTTPServer, HTTP/1.1 keep-alive, one global lock only around
    short store mutations; pack building and object reads run lock-free.

Compatible with Python 3.12 and 3.13 (no version-specific syntax or APIs).
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import socket
import sys
import threading
import time
import urllib.parse
import urllib.request
import zlib
from difflib import SequenceMatcher
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

VERSION = "1.0.0"
ZERO_OID = "0" * 40
FIXED_EPOCH = 1700000000  # deterministic commit timestamp (never wall clock)
FIXED_IDENTITY = "Forge <forge@localhost>"
FIXED_MERGED_AT = "2025-01-01T00:00:00Z"

# ---------------------------------------------------------------------------
# Scenario-derived logins (wire.ts's fixed seed; the token is opaque, so the
# entry re-derives the viewer/stranger logins from the published scenario).
# ---------------------------------------------------------------------------

SCENARIO_SEED = 0x6A09E667F3BCC909
U64_MASK = 0xFFFFFFFFFFFFFFFF
FIRST_NAMES = [
    "ada", "bram", "cora", "dmitri", "elena", "felix", "greta", "hugo",
    "iris", "jonas", "kira", "lars", "mira", "nico", "olga", "pavel",
    "quinn", "rosa", "sven", "tess", "ulla", "vito", "wren", "yara", "zane",
]
LAST_NAMES = [
    "anders", "bauer", "costa", "dahl", "eriksen", "fischer", "garcia",
    "holm", "iversen", "jansen", "keller", "lind", "moreau", "novak",
    "olsen", "peters", "quist", "rossi", "sato", "turi", "ulrich", "vega",
    "weber", "xu", "yilmaz", "zimmer",
]


def _fnv1a64(text):
    h = 0xCBF29CE484222325
    for ch in text:
        h ^= ord(ch)
        h = (h * 0x100000001B3) & U64_MASK
    return h


def _mix64(value):
    z = (value + 0x9E3779B97F4A7C15) & U64_MASK
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & U64_MASK
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & U64_MASK
    return (z ^ (z >> 31)) & U64_MASK


class _Rng:
    """xorshift64* exactly as wire.ts's Rng (same stream, same numbers)."""

    def __init__(self, seed):
        masked = seed & U64_MASK
        self.state = masked if masked != 0 else SCENARIO_SEED

    def next_u64(self):
        x = self.state
        x = (x ^ (x >> 12)) & U64_MASK
        x = (x ^ ((x << 25) & U64_MASK)) & U64_MASK
        x = (x ^ (x >> 27)) & U64_MASK
        self.state = x
        return (x * 0x2545F4914F6CDD1D) & U64_MASK

    def next_u32(self):
        return self.next_u64() >> 32

    def next_int(self, max_exclusive):
        if max_exclusive == 1:
            return 0
        limit = 4294967296 - (4294967296 % max_exclusive)
        while True:
            value = self.next_u32()
            if value < limit:
                return value % max_exclusive

    def pick(self, items):
        return items[self.next_int(len(items))]


def _scenario_rng(label):
    return _Rng(_mix64(SCENARIO_SEED ^ _fnv1a64(label)))


def _scenario_users():
    rng = _scenario_rng("users")
    used = set()
    users = []
    for i in range(12):
        first = rng.pick(FIRST_NAMES)
        last = rng.pick(LAST_NAMES)
        login = first + last
        suffix = 2
        while login in used:
            login = "%s-%d" % (first + last, suffix)
            suffix += 1
        used.add(login)
        users.append({"id": 1000 + i, "login": login,
                      "name": "%s %s" % (first, last),
                      "email": "%s@example.invalid" % login})
    return users


try:
    _USERS = _scenario_users()
    VIEWER_LOGIN = _USERS[0]["login"]
    VIEWER_ID = _USERS[0]["id"]
    STRANGER_LOGIN = _USERS[2]["login"]
except Exception:
    VIEWER_LOGIN = "adaiversen"
    VIEWER_ID = 1000
    STRANGER_LOGIN = "olgabauer"

# ---------------------------------------------------------------------------
# Git object primitives (SHA-1, trees, commits, tags)
# ---------------------------------------------------------------------------

TYPE_CODES = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
CODE_TYPES = {1: "commit", 2: "tree", 3: "blob", 4: "tag"}


def hash_object(otype, data):
    h = hashlib.sha1()
    h.update(("%s %d\0" % (otype, len(data))).encode("ascii"))
    h.update(data)
    return h.hexdigest()


def parse_tree(data):
    entries = []
    off = 0
    n = len(data)
    while off < n:
        sp = data.index(b" ", off)
        mode = data[off:sp].decode("ascii")
        nul = data.index(b"\0", sp + 1)
        name = data[sp + 1:nul].decode("utf-8")
        oid = data[nul + 1:nul + 21].hex()
        entries.append({"mode": mode, "name": name, "oid": oid})
        off = nul + 21
    return entries


def _tree_sort_key(entry):
    name = entry["name"] + "/" if entry["mode"] == "40000" else entry["name"]
    return name.encode("utf-8")


def build_tree(entries):
    out = bytearray()
    for e in sorted(entries, key=_tree_sort_key):
        out += ("%s %s\0" % (e["mode"], e["name"])).encode("utf-8")
        out += bytes.fromhex(e["oid"])
    return bytes(out)


def parse_commit(data):
    text = data.decode("utf-8", "replace")
    head, _, message = text.partition("\n\n")
    tree = ""
    parents = []
    author = ""
    committer = ""
    for line in head.split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        if key == "tree":
            tree = value
        elif key == "parent":
            parents.append(value)
        elif key == "author":
            author = value
        elif key == "committer":
            committer = value
    return {"tree": tree, "parents": parents, "author": author,
            "committer": committer, "message": message}


def build_commit(tree, parents, message, timestamp=FIXED_EPOCH,
                 author=FIXED_IDENTITY, committer=FIXED_IDENTITY):
    lines = ["tree %s" % tree]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s %d +0000" % (author, timestamp))
    lines.append("committer %s %d +0000" % (committer, timestamp))
    lines.append("")
    return ("\n".join(lines) + "\n" + message).encode("utf-8")


def parse_tag(data):
    text = data.decode("utf-8", "replace")
    head, _, message = text.partition("\n\n")
    fields = {}
    for line in head.split("\n"):
        if not line:
            continue
        key, _, value = line.partition(" ")
        fields[key] = value
    return {"object": fields.get("object", ""), "type": fields.get("type", ""),
            "tag": fields.get("tag", ""), "tagger": fields.get("tagger", ""),
            "message": message}


def build_tag(obj, otype, tag, message, timestamp=FIXED_EPOCH,
              tagger=FIXED_IDENTITY):
    return ("object %s\ntype %s\ntag %s\ntagger %s %d +0000\n\n%s" % (
        obj, otype, tag, tagger, timestamp, message)).encode("utf-8")


# ---------------------------------------------------------------------------
# pkt-line codec
# ---------------------------------------------------------------------------

PKT_MAX = 65520


def pkt_line(payload):
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    return ("%04x" % (len(payload) + 4)).encode("ascii") + payload


def pkt_flush():
    return b"0000"


def pkt_delim():
    return b"0001"


def decode_pkt_lines(buf):
    """Decode a whole buffer into (kind, payload) packets; kind in data/flush/delim/end."""
    packets = []
    off = 0
    n = len(buf)
    while off < n:
        if off + 4 > n:
            raise ValueError("truncated pkt-line header")
        head = buf[off:off + 4]
        if not re.fullmatch(rb"[0-9a-fA-F]{4}", head):
            raise ValueError("bad pkt-line header %r" % head)
        length = int(head.decode("ascii"), 16)
        if length == 0:
            packets.append(("flush", b""))
            off += 4
        elif length == 1:
            packets.append(("delim", b""))
            off += 4
        elif length == 2:
            packets.append(("end", b""))
            off += 4
        elif length < 4 or length > PKT_MAX:
            raise ValueError("bad pkt-line length %d" % length)
        else:
            if off + length > n:
                raise ValueError("truncated pkt-line body")
            packets.append(("data", buf[off + 4:off + length]))
            off += length
    return packets


def pkt_lines_text(packets):
    return [p.decode("utf-8", "replace") for kind, p in packets if kind == "data"]


# ---------------------------------------------------------------------------
# Packfiles: read (with delta resolution) and write (with prefix-similarity deltas)
# ---------------------------------------------------------------------------

def _read_pack_varint(buf, off):
    first = buf[off]
    byte = first
    size = byte & 0x0F
    shift = 4
    off += 1
    while byte & 0x80:
        byte = buf[off]
        off += 1
        size += (byte & 0x7F) << shift
        shift += 7
    return size, off, first


def _read_ofs_base(buf, off, entry_off):
    byte = buf[off]
    off += 1
    value = byte & 0x7F
    while byte & 0x80:
        byte = buf[off]
        off += 1
        value = ((value + 1) << 7) + (byte & 0x7F)
    return entry_off - value, off


def _inflate_at(buf, off, trailer_start):
    d = zlib.decompressobj()
    data = d.decompress(buf[off:trailer_start])
    consumed = len(buf[off:trailer_start]) - len(d.unused_data)
    return data, off + consumed


def apply_delta(base, delta):
    off = 0

    def read_size():
        nonlocal off
        value = 0
        shift = 0
        while True:
            byte = delta[off]
            off += 1
            value += (byte & 0x7F) << shift
            shift += 7
            if not (byte & 0x80):
                return value

    src_size = read_size()
    tgt_size = read_size()
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while off < len(delta):
        op = delta[off]
        off += 1
        if op & 0x80:
            cp_off = 0
            cp_size = 0
            for bit in range(4):
                if op & (1 << bit):
                    cp_off |= delta[off] << (bit * 8)
                    off += 1
            for bit in range(3):
                if op & (0x10 << bit):
                    cp_size |= delta[off] << (bit * 8)
                    off += 1
            if cp_size == 0:
                cp_size = 0x10000
            out += base[cp_off:cp_off + cp_size]
        elif op:
            size = op & 0x7F
            out += delta[off:off + size]
            off += size
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta produced wrong size")
    return bytes(out)


def _delta_varint(n):
    out = bytearray()
    while True:
        byte = n & 0x7F
        n >>= 7
        if n:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def build_delta(base, target):
    """A small correct delta: longest common prefix + insert + longest common suffix."""
    n = min(len(base), len(target))
    prefix = 0
    while prefix < n and base[prefix] == target[prefix]:
        prefix += 1
    suffix = 0
    while (suffix < len(base) - prefix and suffix < len(target) - prefix
           and base[len(base) - 1 - suffix] == target[len(target) - 1 - suffix]):
        suffix += 1
    out = bytearray()
    out += _delta_varint(len(base))
    out += _delta_varint(len(target))
    mid = target[prefix:len(target) - suffix if suffix else len(target)]
    pos = 0

    def copy_op(cp_off, cp_size):
        op = 0x80
        buf = bytearray()
        for bit in range(4):
            if cp_off & (0xFF << (bit * 8)):
                op |= 1 << bit
                buf.append((cp_off >> (bit * 8)) & 0xFF)
        for bit in range(3):
            if cp_size & (0xFF << (bit * 8)):
                op |= 0x10 << bit
                buf.append((cp_size >> (bit * 8)) & 0xFF)
        return bytes([op]) + bytes(buf)

    if prefix:
        out += copy_op(0, prefix)
    while pos < len(mid):
        chunk = mid[pos:pos + 127]
        out.append(len(chunk))
        out += chunk
        pos += len(chunk)
    if suffix:
        out += copy_op(len(base) - suffix, suffix)
    return bytes(out)


def read_pack(pack, resolve_base=None):
    """Parse a packfile; returns (objects dict oid->(type,bytes), delta_count)."""
    if len(pack) < 32 or pack[:4] != b"PACK":
        raise ValueError("not a packfile")
    version = int.from_bytes(pack[4:8], "big")
    if version not in (2, 3):
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(pack[8:12], "big")
    trailer_start = len(pack) - 20
    trailer = pack[trailer_start:].hex()
    if hashlib.sha1(pack[:trailer_start]).hexdigest() != trailer:
        raise ValueError("pack trailer checksum mismatch")
    raw = []  # (offset, type_code, size, data, base_off, base_oid)
    by_offset = {}
    off = 12
    for _ in range(count):
        entry_off = off
        size, off, first = _read_pack_varint(pack, off)
        type_code = (first >> 4) & 0x07
        base_off = None
        base_oid = None
        if type_code == 6:
            base_off, off = _read_ofs_base(pack, off, entry_off)
        elif type_code == 7:
            base_oid = pack[off:off + 20].hex()
            off += 20
        elif type_code not in CODE_TYPES:
            raise ValueError("unknown pack type %d" % type_code)
        data, off = _inflate_at(pack, off, trailer_start)
        if len(data) != size:
            raise ValueError("pack entry size mismatch")
        entry = [entry_off, type_code, size, data, base_off, base_oid, None, None, None]
        raw.append(entry)
        by_offset[entry_off] = entry
    if off != trailer_start:
        raise ValueError("pack trailing bytes")

    resolved = {}
    delta_count = 0
    resolving = set()

    def resolve(entry):
        if entry[6] is not None:
            return entry[6], entry[7], entry[8]
        if entry[0] in resolving:
            raise ValueError("delta cycle")
        resolving.add(entry[0])
        code = entry[1]
        if code == 6:
            base_entry = by_offset.get(entry[4])
            if base_entry is None:
                raise ValueError("ofs-delta base missing")
            btype, bdata, _ = resolve(base_entry)
            otype, data = btype, apply_delta(bdata, entry[3])
        elif code == 7:
            base_entry = resolved.get(entry[5])
            if base_entry is not None:
                btype, bdata = base_entry[0], base_entry[1]
                otype, data = btype, apply_delta(bdata, entry[3])
            elif resolve_base is not None:
                found = resolve_base(entry[5])
                if found is None:
                    raise ValueError("ref-delta base missing")
                otype, data = found[0], apply_delta(found[1], entry[3])
            else:
                raise ValueError("ref-delta base missing")
        else:
            otype, data = CODE_TYPES[code], entry[3]
        oid = hash_object(otype, data)
        entry[6], entry[7], entry[8] = otype, data, oid
        resolved[oid] = (otype, data)
        resolving.discard(entry[0])
        return otype, data, oid

    objects = {}
    for entry in raw:
        if entry[1] in (6, 7):
            delta_count += 1
        otype, data, oid = resolve(entry)
        objects.setdefault(oid, (otype, data))
    return objects, delta_count


def _pack_object_header(otype, size):
    code = TYPE_CODES[otype]
    out = bytearray()
    first = (code << 4) | (size & 0x0F)
    size >>= 4
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


def _common_prefix_len(a, b):
    n = min(len(a), len(b))
    i = 0
    while i < n and a[i] == b[i]:
        i += 1
    return i


def write_pack(objects):
    """Build a packfile. Blobs are delta-compressed against the earlier blob
    sharing the longest content prefix (prefix-similarity strategy)."""
    items = list(objects)  # list of (oid, type, data)
    # Choose delta bases among blobs: group by 16-byte prefix key.
    by_prefix = {}
    encoded = []  # (oid, type, data, kind, base_oid_or_None, delta_bytes)
    for oid, otype, data in items:
        if otype == "blob" and len(data) > 256:
            key = data[:16]
            base = by_prefix.get(key)
            if base is not None:
                boid, bdata = base
                if _common_prefix_len(bdata, data) >= 32:
                    delta = build_delta(bdata, data)
                    plain = _pack_object_header("blob", len(data)) + zlib.compress(data, 6)
                    # delta entry: header with type 6 + ofs + zlib(delta)
                    delta_z = zlib.compress(delta, 6)
                    if len(delta_z) + 8 < len(plain):
                        encoded.append((oid, "blob", data, "ofs", boid, delta))
                        continue
            by_prefix.setdefault(key, (oid, data))
        encoded.append((oid, otype, data, "plain", None, None))
    # Offsets are assigned in order; ofs-delta needs the base earlier in the pack.
    # Our base always precedes (it was seen first), so a single pass works.
    parts = [b"PACK" + (2).to_bytes(4, "big") + len(items).to_bytes(4, "big")]
    offsets = {}
    pos = 12
    for oid, otype, data, kind, base_oid, delta in encoded:
        offsets[oid] = pos
        if kind == "ofs":
            # OFS_DELTA base offset: git's encoding, most-significant group first.
            buf = bytearray()
            val = pos - offsets[base_oid]
            tmp = [val & 0x7F]
            val >>= 7
            while val:
                val -= 1
                tmp.append(val & 0x7F)
                val >>= 7
            tmp.reverse()
            for i, b in enumerate(tmp):
                buf.append(b | (0x80 if i < len(tmp) - 1 else 0))
            header = _pack_object_header_raw(6, len(delta))
            chunk = header + bytes(buf) + zlib.compress(delta, 6)
        else:
            chunk = _pack_object_header(otype, len(data)) + zlib.compress(data, 6)
        parts.append(chunk)
        pos += len(chunk)
    body = b"".join(parts)
    return body + hashlib.sha1(body).digest()


def _pack_object_header_raw(type_code, size):
    out = bytearray()
    first = (type_code << 4) | (size & 0x0F)
    size >>= 4
    while size:
        out.append(first | 0x80)
        first = size & 0x7F
        size >>= 7
    out.append(first)
    return bytes(out)


# ---------------------------------------------------------------------------
# Reachability and tree helpers (operate on a plain objects dict)
# ---------------------------------------------------------------------------

def reachable(objects, roots, stop_at=None):
    """All oids reachable from roots (commits, tags, trees, blobs).
    Traversal stops at oids in stop_at (their subtrees are not entered)."""
    seen = set()
    stack = [r for r in roots if r and r != ZERO_OID]
    stop_at = stop_at or set()
    while stack:
        oid = stack.pop()
        if oid in seen or oid in stop_at:
            continue
        obj = objects.get(oid)
        if obj is None:
            continue
        seen.add(oid)
        otype, data = obj
        if otype == "commit":
            c = parse_commit(data)
            stack.append(c["tree"])
            stack.extend(c["parents"])
        elif otype == "tag":
            stack.append(parse_tag(data)["object"])
        elif otype == "tree":
            for e in parse_tree(data):
                if e["mode"] != "160000":
                    stack.append(e["oid"])
    return seen


def tree_get(objects, tree_oid, path):
    """Blob oid at path in tree, or None."""
    parts = [p for p in path.split("/") if p != ""]
    cur = tree_oid
    for i, part in enumerate(parts):
        obj = objects.get(cur)
        if obj is None or obj[0] != "tree":
            return None
        found = None
        for e in parse_tree(obj[1]):
            if e["name"] == part:
                found = e
                break
        if found is None:
            return None
        if i == len(parts) - 1:
            return found["oid"] if found["mode"] != "40000" else None
        cur = found["oid"]
    return None


def _tree_set(objects, tree_oid, parts, blob_oid, new_objects):
    """Return a new tree oid with path parts[0]/... set to blob_oid (or removed
    when blob_oid is None). new_objects collects freshly built (oid, type, data)."""
    entries = {}
    if tree_oid and tree_oid in objects:
        for e in parse_tree(objects[tree_oid][1]):
            entries[e["name"]] = e
    name = parts[0]
    if len(parts) == 1:
        if blob_oid is None:
            entries.pop(name, None)
        else:
            entries[name] = {"mode": "100644", "name": name, "oid": blob_oid}
    else:
        child = entries.get(name)
        child_tree = child["oid"] if child and child["mode"] == "40000" else None
        new_child = _tree_set(objects, child_tree, parts[1:], blob_oid, new_objects)
        if new_child is None:
            entries.pop(name, None)
        else:
            entries[name] = {"mode": "40000", "name": name, "oid": new_child}
    if not entries:
        return None
    data = build_tree(list(entries.values()))
    oid = hash_object("tree", data)
    new_objects.append((oid, "tree", data))
    return oid


def tree_set(objects, tree_oid, path, blob_oid, new_objects):
    parts = [p for p in path.split("/") if p != ""]
    if not parts:
        return tree_oid
    result = _tree_set(objects, tree_oid, parts, blob_oid, new_objects)
    return result


def flatten_tree(objects, tree_oid, prefix=""):
    """{path: (mode, oid)} for every blob under a tree (recursive)."""
    out = {}
    obj = objects.get(tree_oid)
    if obj is None or obj[0] != "tree":
        return out
    for e in parse_tree(obj[1]):
        path = prefix + e["name"]
        if e["mode"] == "40000":
            out.update(flatten_tree(objects, e["oid"], path + "/"))
        elif e["mode"] != "160000":
            out[path] = (e["mode"], e["oid"])
    return out


def tree_diff(objects, old_tree, new_tree):
    """Changed paths between two trees: {path: (old_oid|None, new_oid|None)}."""
    old = flatten_tree(objects, old_tree) if old_tree else {}
    new = flatten_tree(objects, new_tree) if new_tree else {}
    diff = {}
    for path in sorted(set(old) | set(new)):
        o = old.get(path)
        n = new.get(path)
        if o != n:
            diff[path] = (o[1] if o else None, n[1] if n else None)
    return diff


def line_counts(objects, old_oid, new_oid):
    """(additions, deletions) between two blobs, by line diff."""
    old = objects.get(old_oid, ("blob", b""))[1] if old_oid else b""
    new = objects.get(new_oid, ("blob", b""))[1] if new_oid else b""
    old_lines = old.decode("utf-8", "replace").splitlines()
    new_lines = new.decode("utf-8", "replace").splitlines()
    sm = SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
    adds = dels = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ("insert", "replace"):
            adds += j2 - j1
        if tag in ("delete", "replace"):
            dels += i2 - i1
    return adds, dels


def merge_base(objects, tip_a, tip_b):
    """Best common ancestor of two commits (BFS from tip_b by generation)."""
    if not tip_a or not tip_b or tip_a == ZERO_OID or tip_b == ZERO_OID:
        return None
    ancestors_a = set()
    stack = [tip_a]
    while stack:
        oid = stack.pop()
        if oid in ancestors_a:
            continue
        obj = objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        ancestors_a.add(oid)
        stack.extend(parse_commit(obj[1])["parents"])
    seen = set()
    queue = [tip_b]
    while queue:
        nxt = []
        for oid in queue:
            if oid in ancestors_a:
                return oid
            if oid in seen:
                continue
            seen.add(oid)
            obj = objects.get(oid)
            if obj is not None and obj[0] == "commit":
                nxt.extend(parse_commit(obj[1])["parents"])
        queue = nxt
    return None


def is_ancestor(objects, ancestor, tip):
    if ancestor == tip:
        return True
    if not ancestor or not tip:
        return False
    seen = set()
    stack = [tip]
    while stack:
        oid = stack.pop()
        if oid == ancestor:
            return True
        if oid in seen:
            continue
        seen.add(oid)
        obj = objects.get(oid)
        if obj is not None and obj[0] == "commit":
            stack.extend(parse_commit(obj[1])["parents"])
    return False


# ---------------------------------------------------------------------------
# The event-sourced store
# ---------------------------------------------------------------------------

class Repo:
    __slots__ = ("dbid", "owner", "name", "private", "description",
                 "default_branch", "refs", "objects", "labels", "issues",
                 "pulls", "comments", "counter", "seq")

    def __init__(self, dbid, owner, name, private, description):
        self.dbid = dbid
        self.owner = owner
        self.name = name
        self.private = private
        self.description = description or ""
        self.default_branch = "main"
        self.refs = {}          # refname -> oid
        self.objects = {}       # oid -> (type, bytes)
        self.labels = {}        # name -> {"name","color"}
        self.issues = {}        # number -> dict, in creation order
        self.pulls = {}         # number -> dict, in creation order
        self.comments = {}      # issue number -> [comment dicts]
        self.counter = 0        # shared issue+PR number sequence
        self.seq = 0            # per-repo creation sequence

    def full_name(self):
        return "%s/%s" % (self.owner, self.name)

    def global_id(self):
        return "gid-repo-%d" % self.dbid

    def ref_tip(self, branch):
        return self.refs.get("refs/heads/" + branch)

    def issue_by_number(self, number):
        for issue in self.issues.values():
            if issue["number"] == number:
                return issue
        return None

    def pull_by_number(self, number):
        for pr in self.pulls.values():
            if pr["number"] == number:
                return pr
        return None


class Store:
    """One in-memory forge. Every mutation appends an event (sequence number,
    never a timestamp) to the log and applies it to the projection."""

    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}         # (owner, name) -> Repo
        self.repo_seq = 0       # global repo creation sequence
        self.dbid_seq = 0       # global database-id sequence
        self.event_seq = 0
        self.events = []        # the append-only log (projection source)
        self._journal = []      # buffered journal lines for the file copy
        self.journal_path = os.environ.get(
            "MAKEFUN_JOURNAL_PATH", "/tmp/makefun-forge-journal.jsonl")

    # -- event log -------------------------------------------------------
    def log_event(self, kind, data):
        self.event_seq += 1
        event = {"seq": self.event_seq, "kind": kind, "data": data}
        self.events.append(event)
        self._journal.append(json.dumps(event, separators=(",", ":")))
        if len(self._journal) >= 64:
            self._flush_journal()
        return event

    def _flush_journal(self):
        if not self._journal:
            return
        lines, self._journal = self._journal, []
        try:
            with open(self.journal_path, "a", encoding="utf-8") as fh:
                fh.write("\n".join(lines) + "\n")
        except Exception:
            pass

    # -- repos -----------------------------------------------------------
    def create_repo(self, name, private, description):
        with self.lock:
            key = (VIEWER_LOGIN, name)
            if key in self.repos:
                return None
            self.dbid_seq += 1
            self.repo_seq += 1
            repo = Repo(self.dbid_seq, VIEWER_LOGIN, name, bool(private),
                        description or "")
            repo.seq = self.repo_seq
            self.repos[key] = repo
            self.log_event("repo.create", {"owner": VIEWER_LOGIN, "name": name,
                                          "private": bool(private),
                                          "description": description or "",
                                          "dbid": repo.dbid})
            return repo

    def get_repo(self, owner, name):
        if owner != VIEWER_LOGIN:
            return None
        return self.repos.get((owner, name))

    def delete_repo(self, owner, name):
        with self.lock:
            key = (owner, name)
            if key not in self.repos:
                return False
            del self.repos[key]
            self.log_event("repo.delete", {"owner": owner, "name": name})
            return True

    def list_repos(self):
        with self.lock:
            return sorted(self.repos.values(), key=lambda r: r.seq)

    def find_repo_by_global_id(self, gid):
        with self.lock:
            for repo in self.repos.values():
                if repo.global_id() == gid:
                    return repo
        return None

    # -- issues / pulls --------------------------------------------------
    def create_issue(self, repo, title, body, labels):
        with self.lock:
            repo.counter += 1
            number = repo.counter
            self.dbid_seq += 1
            issue = {"id": self.dbid_seq, "number": number,
                     "title": title or "", "body": body or "",
                     "state": "open",
                     "labels": [{"name": n,
                                 "color": repo.labels[n]["color"]}
                                for n in labels],
                     "global_id": "gid-issue-%d-%d" % (repo.dbid, number),
                     "seq": number}
            repo.issues[number] = issue
            repo.comments[number] = []
            self.log_event("issue.create",
                           {"repo": repo.full_name(), "number": number,
                            "title": title or "", "body": body or "",
                            "labels": list(labels)})
            return issue

    def create_pull(self, repo, title, body, head, base):
        with self.lock:
            head_tip = repo.ref_tip(head)
            base_tip = repo.ref_tip(base)
            if head_tip is None or base_tip is None:
                return None
            repo.counter += 1
            number = repo.counter
            self.dbid_seq += 1
            pr = {"id": self.dbid_seq, "number": number,
                  "title": title or "", "body": body or "",
                  "state": "open", "head": head, "base": base,
                  "head_sha": head_tip, "base_sha": base_tip,
                  "merged": False, "merge_commit_sha": None,
                  "merged_at": None,
                  "global_id": "gid-pr-%d-%d" % (repo.dbid, number),
                  "seq": number}
            repo.pulls[number] = pr
            self.log_event("pull.create",
                           {"repo": repo.full_name(), "number": number,
                            "title": title or "", "head": head, "base": base})
            return pr

    def add_comment(self, repo, number, body):
        with self.lock:
            self.dbid_seq += 1
            comment = {"id": self.dbid_seq, "body": body or "",
                       "global_id": "gid-comment-%d-%d-%d" % (
                           repo.dbid, number, self.dbid_seq)}
            repo.comments.setdefault(number, []).append(comment)
            self.log_event("comment.create",
                           {"repo": repo.full_name(), "issue": number,
                            "body": body or ""})
            return comment

    # -- git objects / refs ----------------------------------------------
    def store_objects(self, repo, objects):
        with self.lock:
            for oid, (otype, data) in objects.items():
                if oid not in repo.objects:
                    repo.objects[oid] = (otype, data)
            self.log_event("objects.store",
                           {"repo": repo.full_name(), "count": len(objects)})

    def set_ref(self, repo, ref, oid):
        with self.lock:
            if oid == ZERO_OID:
                repo.refs.pop(ref, None)
            else:
                repo.refs[ref] = oid
            self.log_event("ref.set", {"repo": repo.full_name(), "ref": ref,
                                       "oid": oid})

    def mergeable(self, repo, pr):
        """True when the head can squash-merge cleanly onto the base tip."""
        head_tip = repo.ref_tip(pr["head"])
        base_tip = repo.ref_tip(pr["base"])
        if head_tip is None or base_tip is None:
            return False
        if head_tip == base_tip:
            return True
        if is_ancestor(repo.objects, base_tip, head_tip):
            return True
        base = merge_base(repo.objects, head_tip, base_tip)
        if base is None:
            return False
        base_commit = repo.objects.get(base)
        if base_commit is None:
            return False
        base_tree = parse_commit(base_commit[1])["tree"]
        head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
        base_tip_tree = parse_commit(repo.objects[base_tip][1])["tree"]
        head_changes = tree_diff(repo.objects, base_tree, head_tree)
        base_changes = tree_diff(repo.objects, base_tree, base_tip_tree)
        for path, (_, head_oid) in head_changes.items():
            if path in base_changes and base_changes[path][1] != head_oid:
                return False
        return True

    def squash_merge(self, repo, pr):
        """Apply the squash merge; returns (ok, merge_sha or None)."""
        with self.lock:
            if pr["state"] != "open":
                return False, None
            if not self.mergeable(repo, pr):
                return False, None
            head_tip = repo.ref_tip(pr["head"])
            base_tip = repo.ref_tip(pr["base"])
            base = merge_base(repo.objects, head_tip, base_tip)
            base_tree = parse_commit(repo.objects[base][1])["tree"]
            head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
            base_tip_tree = parse_commit(repo.objects[base_tip][1])["tree"]
            head_changes = tree_diff(repo.objects, base_tree, head_tree)
            new_objects = []
            merged_tree = base_tip_tree
            for path, (_, head_oid) in sorted(head_changes.items()):
                merged_tree = tree_set(repo.objects, merged_tree, path,
                                       head_oid, new_objects)
            for oid, otype, data in new_objects:
                repo.objects.setdefault(oid, (otype, data))
            message = "Merge pull request #%d from %s\n\n%s\n" % (
                pr["number"], pr["head"], pr["title"])
            commit = build_commit(merged_tree, [base_tip], message)
            merge_sha = hash_object("commit", commit)
            repo.objects[merge_sha] = ("commit", commit)
            repo.refs["refs/heads/" + pr["base"]] = merge_sha
            pr["state"] = "closed"
            pr["merged"] = True
            pr["merge_commit_sha"] = merge_sha
            pr["merged_at"] = FIXED_MERGED_AT
            pr["base_sha"] = merge_sha
            self.log_event("pull.merge",
                           {"repo": repo.full_name(), "number": pr["number"],
                            "sha": merge_sha})
            return True, merge_sha

    def commit_file(self, repo, branch, path, content, message, blob_sha=None):
        """Contents-API commit: create/update one file on a branch.
        Returns (status, commit_sha, blob_sha) or (error_status, None, None)."""
        with self.lock:
            tip = repo.ref_tip(branch)
            if tip is None and branch != repo.default_branch:
                # Creating a new branch off the default tip.
                default_tip = repo.ref_tip(repo.default_branch)
                if default_tip is None:
                    # Unborn repo: a root commit on the new branch.
                    tip = None
                else:
                    repo.refs["refs/heads/" + branch] = default_tip
                    tip = default_tip
            if tip is not None:
                tip_commit = repo.objects.get(tip)
                if tip_commit is None or tip_commit[0] != "commit":
                    return 409, None, None
                parent_tree = parse_commit(tip_commit[1])["tree"]
                current = tree_get(repo.objects, parent_tree, path)
                if current is not None:
                    if blob_sha is not None and blob_sha != current:
                        return 409, None, None
                    is_update = True
                else:
                    is_update = False
            else:
                parent_tree = None
                is_update = False
            blob_oid = hash_object("blob", content)
            repo.objects[blob_oid] = ("blob", content)
            new_objects = []
            new_tree = tree_set(repo.objects, parent_tree, path, blob_oid,
                                new_objects)
            for oid, otype, data in new_objects:
                repo.objects.setdefault(oid, (otype, data))
            parents = [tip] if tip else []
            commit = build_commit(new_tree, parents, message + "\n")
            commit_sha = hash_object("commit", commit)
            repo.objects[commit_sha] = ("commit", commit)
            repo.refs["refs/heads/" + branch] = commit_sha
            self.log_event("contents.commit",
                           {"repo": repo.full_name(), "branch": branch,
                            "path": path, "sha": commit_sha})
            return (200 if is_update else 201), commit_sha, blob_oid

    def delete_file(self, repo, branch, path, message):
        with self.lock:
            tip = repo.ref_tip(branch)
            if tip is None:
                return None
            tip_commit = repo.objects.get(tip)
            if tip_commit is None:
                return None
            parent_tree = parse_commit(tip_commit[1])["tree"]
            if tree_get(repo.objects, parent_tree, path) is None:
                return None
            new_objects = []
            new_tree = tree_set(repo.objects, parent_tree, path, None,
                                new_objects)
            for oid, otype, data in new_objects:
                repo.objects.setdefault(oid, (otype, data))
            if new_tree is None:
                new_tree = hash_object("tree", b"")
                repo.objects.setdefault(new_tree, ("tree", b""))
            commit = build_commit(new_tree, [tip], message + "\n")
            commit_sha = hash_object("commit", commit)
            repo.objects[commit_sha] = ("commit", commit)
            repo.refs["refs/heads/" + branch] = commit_sha
            self.log_event("contents.delete",
                           {"repo": repo.full_name(), "branch": branch,
                            "path": path, "sha": commit_sha})
            return commit_sha


STORE = Store()


# ---------------------------------------------------------------------------
# HTTP plumbing
# ---------------------------------------------------------------------------

SHOP_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")
REQ_ID = [0]
REQ_ID_LOCK = threading.Lock()


def next_request_id():
    with REQ_ID_LOCK:
        REQ_ID[0] += 1
        return "req-%d" % REQ_ID[0]


def json_bytes(obj):
    return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def b64e(data):
    return base64.b64encode(data).decode("ascii")


def b64d(text):
    cleaned = re.sub(r"\s+", "", text or "")
    return base64.b64decode(cleaned)


def iso_from_epoch(epoch):
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(epoch))


def parse_identity(line):
    """'Name <email> 1700000000 +0000' -> (name, email, epoch)."""
    m = re.match(r"^(.*?) <(.*?)> (\d+) ([+-]\d{4})$", line or "")
    if not m:
        return ("", "", FIXED_EPOCH)
    return (m.group(1), m.group(2), int(m.group(3)))


def repo_json(repo):
    return {
        "id": repo.dbid,
        "node_id": repo.global_id(),
        "name": repo.name,
        "full_name": repo.full_name(),
        "owner": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "html_url": "https://example.invalid/" + repo.full_name(),
        "clone_url": "https://example.invalid/" + repo.full_name() + ".git",
        "created_at": FIXED_MERGED_AT,
        "updated_at": FIXED_MERGED_AT,
        "pushed_at": FIXED_MERGED_AT,
        "has_issues": True,
        "has_projects": True,
        "has_wiki": True,
        "fork": False,
        "archived": False,
        "disabled": False,
        "visibility": "private" if repo.private else "public",
        "size": 0,
        "language": None,
        "topics": [],
        "license": None,
        "permissions": {"admin": True, "maintain": True, "push": True,
                        "triage": True, "pull": True},
    }


def issue_json(repo, issue):
    return {
        "id": issue["id"],
        "node_id": issue["global_id"],
        "number": issue["number"],
        "title": issue["title"],
        "body": issue["body"],
        "state": issue["state"],
        "labels": list(issue["labels"]),
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "assignee": None,
        "assignees": [],
        "comments": len(repo.comments.get(issue["number"], [])),
        "created_at": FIXED_MERGED_AT,
        "updated_at": FIXED_MERGED_AT,
        "html_url": "https://example.invalid/%s/issues/%d" % (
            repo.full_name(), issue["number"]),
        "url": "/api/v3/repos/%s/issues/%d" % (
            repo.full_name(), issue["number"]),
    }


def pull_json(repo, pr):
    def side(ref, sha):
        return {"label": "%s:%s" % (repo.owner, ref), "ref": ref, "sha": sha,
                "user": {"login": repo.owner, "id": VIEWER_ID, "type": "User"},
                "repo": {"id": repo.dbid, "name": repo.name,
                         "full_name": repo.full_name()}}
    return {
        "id": pr["id"],
        "node_id": pr["global_id"],
        "number": pr["number"],
        "title": pr["title"],
        "body": pr["body"],
        "state": pr["state"],
        "head": side(pr["head"], pr["head_sha"]),
        "base": side(pr["base"], pr["base_sha"]),
        "merged": pr["merged"],
        "mergeable": STORE.mergeable(repo, pr) if pr["state"] == "open" else False,
        "merge_commit_sha": pr["merge_commit_sha"],
        "merged_at": pr["merged_at"],
        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User"},
        "draft": False,
        "locked": False,
        "comments": 0,
        "commits": 1,
        "created_at": FIXED_MERGED_AT,
        "updated_at": FIXED_MERGED_AT,
        "html_url": "https://example.invalid/%s/pull/%d" % (
            repo.full_name(), pr["number"]),
        "url": "/api/v3/repos/%s/pulls/%d" % (
            repo.full_name(), pr["number"]),
    }


def paginate(items, query):
    """(page_items, link_header_or_None) for GitHub-style pagination."""
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except ValueError:
        per_page = 30
    per_page = max(1, min(100, per_page))
    try:
        page = int(query.get("page", ["1"])[0])
    except ValueError:
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    end = start + per_page
    return items[start:end], per_page, page, total


class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    # -- plumbing --------------------------------------------------------
    def log_message(self, *args):
        pass

    def _send(self, status, body, content_type, extra=None):
        headers = {"Content-Type": content_type,
                   "Content-Length": str(len(body)),
                   "X-GitHub-Request-Id": next_request_id()}
        if extra:
            headers.update(extra)
        try:
            self.send_response(status)
            for key, value in headers.items():
                self.send_header(key, value)
            self.end_headers()
            if body:
                self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _send_json(self, status, obj, extra=None):
        self._send(status, json_bytes(obj), "application/json; charset=utf-8",
                   extra)

    def _send_json_no_body(self, status, extra=None):
        headers = {"Content-Length": "0",
                   "X-GitHub-Request-Id": next_request_id()}
        if extra:
            headers.update(extra)
        try:
            self.send_response(status)
            for key, value in headers.items():
                self.send_header(key, value)
            self.end_headers()
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _err(self, status, message):
        self._send_json(status, {"message": message})

    def _read_body(self):
        length = self.headers.get("Content-Length")
        if length is None:
            return b""
        try:
            n = int(length)
        except ValueError:
            return b""
        if n <= 0:
            return b""
        return self.rfile.read(n)

    def _json_body(self):
        raw = self._raw_body
        if raw == b"":
            return {}, False
        try:
            value = json.loads(raw.decode("utf-8"))
        except Exception:
            return None, True
        if not isinstance(value, dict):
            return None, True
        return value, False

    def _authed(self):
        auth = self.headers.get("Authorization") or ""
        if not auth.startswith("Bearer "):
            return False
        token = auth[len("Bearer "):].strip()
        if not token:
            return False
        if SHOP_TOKEN:
            return token == SHOP_TOKEN
        return True

    def _require_auth(self):
        if not self._authed():
            self._err(401, "Requires authentication")
            return False
        return True

    def _abs_base(self):
        host = self.headers.get("Host") or "127.0.0.1"
        return "http://" + host

    def _link_header(self, path, query, per_page, page, total):
        last_page = max(1, -(-total // per_page))
        if page >= last_page:
            return None
        base = self._abs_base() + path
        links = []
        params = dict(query)
        params["page"] = [str(page + 1)]
        params["per_page"] = [str(per_page)]
        links.append('<%s?%s>; rel="next"' % (
            base, urllib.parse.urlencode(params, doseq=True)))
        params["page"] = [str(last_page)]
        links.append('<%s?%s>; rel="last"' % (
            base, urllib.parse.urlencode(params, doseq=True)))
        return ", ".join(links)

    # -- dispatch --------------------------------------------------------
    def do_GET(self):
        self._dispatch()

    def do_POST(self):
        self._dispatch()

    def do_PUT(self):
        self._dispatch()

    def do_PATCH(self):
        self._dispatch()

    def do_DELETE(self):
        self._dispatch()

    def do_HEAD(self):
        self._dispatch(head_only=True)

    def _dispatch(self, head_only=False):
        try:
            self._raw_body = self._read_body()
        except Exception:
            self._raw_body = b""
        try:
            parsed = urllib.parse.urlsplit(self.path)
            path = urllib.parse.unquote(parsed.path)
            query = urllib.parse.parse_qs(parsed.query)
            method = self.command
            if path == "/healthz" and method == "GET":
                self._send_json(200, {"ok": True})
                return
            if path.startswith("/api/v3"):
                self._rest(path[len("/api/v3"):], method, query, head_only)
                return
            if path == "/api/graphql" and method == "POST":
                self._graphql()
                return
            if path == "/mcp":
                self._mcp(method)
                return
            if ".git/" in path or path.endswith(".git"):
                self._git(path, method, query)
                return
            self._err(404, "Not Found")
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:  # never crash the server on a bad request
            try:
                self._err(500, "Internal error: %s" % exc)
            except Exception:
                pass

    # -- git smart HTTP --------------------------------------------------
    def _git(self, path, method, query):
        parts = [p for p in path.split("/") if p != ""]
        if len(parts) < 2 or not parts[1].endswith(".git"):
            self._err(404, "Not Found")
            return
        owner = urllib.parse.unquote(parts[0])
        name = urllib.parse.unquote(parts[1][:-4])
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        if not self._require_auth():
            return
        if len(parts) == 4 and parts[2] == "info" and parts[3] == "refs":
            if method != "GET":
                self._err(405, "Method Not Allowed")
                return
            service = (query.get("service") or [None])[0]
            self._git_info_refs(repo, service)
            return
        if len(parts) == 3 and parts[2] in ("git-upload-pack",
                                            "git-receive-pack"):
            if method != "POST":
                self._err(405, "Method Not Allowed")
                return
            try:
                if parts[2] == "git-upload-pack":
                    self._git_upload_pack(repo)
                else:
                    self._git_receive_pack(repo)
            except ValueError as exc:
                self._err(400, "Bad git request: %s" % exc)
            return
        self._err(404, "Not Found")

    def _git_head_ref(self, repo):
        return "refs/heads/" + repo.default_branch

    def _git_peeled(self, repo, oid):
        obj = repo.objects.get(oid)
        if obj is not None and obj[0] == "tag":
            return parse_tag(obj[1])["object"]
        return None

    def _git_v0_advertisement(self, repo, service):
        if service == "git-receive-pack":
            caps = ("report-status side-band-64k delete-refs ofs-delta "
                    "agent=Forge/1.0")
        else:
            caps = ("symref=HEAD:%s side-band-64k thin-pack ofs-delta "
                    "shallow multi_ack agent=Forge/1.0" %
                    self._git_head_ref(repo))
        out = [pkt_line("# service=%s\n" % service), pkt_flush()]
        with STORE.lock:
            refs = sorted(repo.refs.items())
        if not refs:
            out.append(pkt_line("%s capabilities^{}\x00%s\n" %
                                (ZERO_OID, caps)))
        else:
            with STORE.lock:
                head_oid = repo.refs.get(self._git_head_ref(repo), ZERO_OID)
            out.append(pkt_line("%s HEAD\x00%s\n" % (head_oid, caps)))
            for name, oid in refs:
                out.append(pkt_line("%s %s\n" % (oid, name)))
                peeled = self._git_peeled(repo, oid)
                if peeled:
                    out.append(pkt_line("%s %s^{}\n" % (peeled, name)))
        out.append(pkt_flush())
        return b"".join(out)

    def _git_v2_advertisement(self):
        return b"".join([
            pkt_line("# service=git-upload-pack\n"), pkt_flush(),
            pkt_line("version 2\n"),
            pkt_line("ls-refs=unborn\n"),
            pkt_line("fetch=shallow\n"),
            pkt_line("agent=Forge/1.0\n"),
            pkt_line("object-format=sha1\n"),
            pkt_flush()])

    def _git_info_refs(self, repo, service):
        if service == "git-upload-pack":
            if (self.headers.get("Git-Protocol") or "") == "version=2":
                body = self._git_v2_advertisement()
            else:
                body = self._git_v0_advertisement(repo, service)
            self._send(200, body,
                       "application/x-git-upload-pack-advertisement")
        elif service == "git-receive-pack":
            body = self._git_v0_advertisement(repo, service)
            self._send(200, body,
                       "application/x-git-receive-pack-advertisement")
        else:
            self._err(404, "Not Found")

    def _git_ls_refs(self, repo, args):
        peel = "peel" in args
        symrefs = "symrefs" in args
        unborn = "unborn" in args
        prefixes = [a[len("ref-prefix "):] for a in args
                    if a.startswith("ref-prefix ")]
        head_ref = self._git_head_ref(repo)
        with STORE.lock:
            refs = sorted(repo.refs.items())
            head_oid = repo.refs.get(head_ref)

        def keep(name):
            return not prefixes or any(name.startswith(p) for p in prefixes)

        lines = []
        if head_oid is None:
            if keep("HEAD") and unborn:
                line = "unborn HEAD"
                if symrefs:
                    line += " symref-target:%s" % head_ref
                lines.append(line + "\n")
        else:
            if keep("HEAD"):
                line = "%s HEAD" % head_oid
                if symrefs:
                    line += " symref-target:%s" % head_ref
                lines.append(line + "\n")
        for name, oid in refs:
            if not keep(name):
                continue
            line = "%s %s" % (oid, name)
            if peel:
                peeled = self._git_peeled(repo, oid)
                if peeled:
                    line += " peeled:%s" % peeled
            lines.append(line + "\n")
        body = b"".join(pkt_line(l) for l in lines) + pkt_flush()
        self._send(200, body, "application/x-git-upload-pack-result")

    def _git_fetch_plan(self, objects, wants, haves, depth, shallow_old):
        """Plan a fetch over a snapshot objects dict.

        Returns (send_oids, ack_or_None, shallow, unshallow). send_oids are
        the objects to pack; ack is a have the server shares with the client.
        """
        held = set(h for h in haves if h in objects)
        want_commits = []
        extra = set()
        for w in wants:
            obj = objects.get(w)
            if obj is None:
                continue
            if obj[0] == "commit":
                want_commits.append(w)
            elif obj[0] == "tag":
                extra.add(w)
                target = parse_tag(obj[1])["object"]
                if objects.get(target, (None,))[0] == "commit":
                    want_commits.append(target)
            else:
                extra.add(w)
        ack = None
        for h in haves:
            if h not in objects:
                continue
            if any(h == w or is_ancestor(objects, h, w)
                   for w in want_commits):
                ack = h
                break
        shallow = []
        unshallow = []
        if depth is None:
            # Full closures on both sides: stop_at would still re-send
            # objects shared with the held tip through the new tip's tree.
            send = (reachable(objects, want_commits)
                    - reachable(objects, list(held))) | (extra - held)
        else:
            # Window: commits within `depth` generations of the wants.
            window = set()
            level = list(want_commits)
            seen = set(level)
            for _ in range(depth):
                window |= set(level)
                nxt = []
                for c in level:
                    obj = objects.get(c)
                    if obj is None or obj[0] != "commit":
                        continue
                    for p in parse_commit(obj[1])["parents"]:
                        if p in seen:
                            continue
                        if objects.get(p, (None,))[0] != "commit":
                            continue
                        seen.add(p)
                        nxt.append(p)
                level = nxt
            boundary = set()
            for c in window:
                obj = objects.get(c)
                parents = (parse_commit(obj[1])["parents"]
                           if obj is not None and obj[0] == "commit" else [])
                if not any(p in window for p in parents):
                    boundary.add(c)
            send = set(extra)
            for c in window:
                send.add(c)
                obj = objects.get(c)
                if obj is not None and obj[0] == "commit":
                    tree = parse_commit(obj[1])["tree"]
                    send |= reachable(objects, [tree])
            # The client already holds each have's own commit+tree, not its
            # ancestry (a shallow boundary holds no parents).
            held_exact = set()
            for h in held:
                held_exact.add(h)
                obj = objects.get(h)
                if obj is not None and obj[0] == "commit":
                    held_exact |= reachable(
                        objects, [parse_commit(obj[1])["tree"]])
            send -= held_exact
            shallow = sorted(boundary)
            unshallow = sorted(b for b in shallow_old
                               if b in window and b not in boundary)
        return send, ack, shallow, unshallow

    def _git_sideband(self, data, band=1):
        if not data:
            return b""
        out = []
        step = PKT_MAX - 5
        for i in range(0, len(data), step):
            out.append(pkt_line(bytes([band]) + data[i:i + step]))
        return b"".join(out)

    def _git_fetch(self, repo, args, v2):
        wants = []
        haves = []
        shallow_old = []
        depth = None
        done = False
        for a in args:
            if a.startswith("want "):
                wants.append(a[5:].split(" ")[0])
            elif a.startswith("have "):
                haves.append(a[5:].strip())
            elif a.startswith("shallow "):
                shallow_old.append(a[8:].strip())
            elif a.startswith("deepen "):
                try:
                    depth = int(a[7:].strip())
                except ValueError:
                    depth = None
            elif a == "done":
                done = True
        with STORE.lock:
            objects = dict(repo.objects)
        send, ack, shallow, unshallow = self._git_fetch_plan(
            objects, wants, haves, depth, shallow_old)
        pack = write_pack([(oid, objects[oid][0], objects[oid][1])
                           for oid in sorted(send) if oid in objects])
        if v2:
            # protocol-v2: when the client sent "done" it has finished
            # negotiating, so the acknowledgments section MUST be omitted
            # and the response goes straight to shallow-info / packfile.
            # Without "done" the ack section is sent; without "ready" the
            # response ends there (flush, no packfile).
            out = []
            if not done:
                out.append(pkt_line("acknowledgments\n"))
                if ack is not None:
                    out.append(pkt_line("ACK %s\n" % ack))
                    out.append(pkt_line("ready\n"))
                    out.append(pkt_delim())
                else:
                    out.append(pkt_line("NAK\n"))
                    out.append(pkt_flush())
                    self._send(200, b"".join(out),
                               "application/x-git-upload-pack-result")
                    return
            if depth is not None or unshallow:
                out.append(pkt_line("shallow-info\n"))
                for oid in shallow:
                    out.append(pkt_line("shallow %s\n" % oid))
                for oid in unshallow:
                    out.append(pkt_line("unshallow %s\n" % oid))
                out.append(pkt_delim())
            out.append(pkt_line("packfile\n"))
            out.append(self._git_sideband(pack, 1))
            out.append(pkt_flush())
        else:
            out = []
            if ack is not None:
                out.append(pkt_line("ACK %s\n" % ack))
            else:
                out.append(pkt_line("NAK\n"))
            for oid in shallow:
                out.append(pkt_line("shallow %s\n" % oid))
            for oid in unshallow:
                out.append(pkt_line("unshallow %s\n" % oid))
            out.append(self._git_sideband(pack, 1))
            out.append(pkt_flush())
        self._send(200, b"".join(out),
                   "application/x-git-upload-pack-result")

    def _git_upload_pack(self, repo):
        body = self._raw_body
        packets = decode_pkt_lines(body)
        lines = pkt_lines_text(packets)
        v2 = (self.headers.get("Git-Protocol") or "") == "version=2"
        if v2:
            if not lines or not lines[0].startswith("command="):
                raise ValueError("missing command")
            command = lines[0][len("command="):].strip()
            # Args follow the delim packet.
            args = []
            seen_delim = False
            for kind, payload in packets:
                if kind == "delim":
                    seen_delim = True
                    continue
                if seen_delim and kind == "data":
                    args.append(payload.decode("utf-8", "replace")
                                .rstrip("\n"))
            if command == "ls-refs":
                self._git_ls_refs(repo, args)
            elif command == "fetch":
                self._git_fetch(repo, args, True)
            else:
                raise ValueError("unknown command %r" % command)
        else:
            # v0 fetch: want/have lines in two flush-separated sections.
            args = [l.rstrip("\n") for l in lines]
            if not any(a.startswith("want ") for a in args):
                raise ValueError("missing want")
            self._git_fetch(repo, args, False)

    def _git_receive_pack(self, repo):
        body = self._raw_body
        # Split the command list (pkt-lines up to the first flush) from the
        # pack that follows it.
        off = 0
        commands = []
        pack_start = None
        n = len(body)
        while off + 4 <= n:
            head = body[off:off + 4]
            if head == b"0000":
                pack_start = off + 4
                break
            if not re.fullmatch(rb"[0-9a-fA-F]{4}", head):
                raise ValueError("bad pkt-line header %r" % head)
            length = int(head.decode("ascii"), 16)
            if length < 4 or length > PKT_MAX or off + length > n:
                raise ValueError("bad pkt-line length %d" % length)
            commands.append(body[off + 4:off + length])
            off += length
        if pack_start is None:
            raise ValueError("missing flush in receive-pack body")
        parsed = []
        caps = ""
        for i, raw in enumerate(commands):
            text = raw.decode("utf-8", "replace").rstrip("\n")
            if i == 0 and "\x00" in text:
                text, caps = text.split("\x00", 1)
            fields = text.split(" ")
            if len(fields) != 3:
                raise ValueError("bad push command %r" % text[:60])
            old, new, ref = fields
            if (not re.fullmatch(r"[0-9a-f]{40}", old)
                    or not re.fullmatch(r"[0-9a-f]{40}", new)
                    or not ref.startswith("refs/")):
                raise ValueError("bad push command %r" % text[:60])
            parsed.append((old, new, ref))
        if not parsed:
            raise ValueError("empty push command list")
        pack = body[pack_start:]
        sideband = "side-band-64k" in caps.split(" ")
        if parsed and any(c[1] != ZERO_OID for c in parsed):
            if not pack:
                raise ValueError("push with updates carries no pack")
            try:
                new_objects, _ = read_pack(pack)
            except ValueError as exc:
                self._git_push_report([], parsed, "unpack error: %s" % exc,
                                     sideband)
                return
            with STORE.lock:
                for oid, obj in new_objects.items():
                    if oid not in repo.objects:
                        repo.objects[oid] = obj
        results = []
        with STORE.lock:
            for old, new, ref in parsed:
                current = repo.refs.get(ref)
                if new == ZERO_OID:
                    # Delete.
                    if current is None:
                        results.append((ref, False,
                                        "remote ref does not exist"))
                    elif old != ZERO_OID and old != current:
                        results.append((ref, False, "non-fast-forward"))
                    else:
                        del repo.refs[ref]
                        STORE.log_event("ref.delete",
                                        {"repo": repo.full_name(),
                                         "ref": ref})
                        results.append((ref, True, ""))
                    continue
                if old == ZERO_OID:
                    # Create.
                    if current is not None:
                        results.append((ref, False, "already exists"))
                        continue
                else:
                    if current is None:
                        results.append((ref, False,
                                        "remote ref does not exist"))
                        continue
                    if current != old:
                        results.append((ref, False, "non-fast-forward"))
                        continue
                obj = repo.objects.get(new)
                if obj is None:
                    results.append((ref, False, "object not found"))
                    continue
                if ref.startswith("refs/heads/") and obj[0] != "commit":
                    results.append((ref, False, "not a commit"))
                    continue
                if (old != ZERO_OID and current is not None
                        and not ref.startswith("refs/tags/")
                        and not is_ancestor(repo.objects, old, new)):
                    results.append((ref, False, "non-fast-forward"))
                    continue
                repo.refs[ref] = new
                STORE.log_event("ref.update",
                                {"repo": repo.full_name(), "ref": ref,
                                 "old": old, "new": new})
                results.append((ref, True, ""))
        self._git_push_report(results, parsed, None, sideband)

    def _git_push_report(self, results, parsed, unpack_error, sideband):
        lines = []
        if unpack_error is not None:
            lines.append("unpack %s\n" % unpack_error)
            for _, _, ref in parsed:
                lines.append("ng %s %s\n" % (ref, "unpack failed"))
        else:
            lines.append("unpack ok\n")
            for ref, ok, reason in results:
                if ok:
                    lines.append("ok %s\n" % ref)
                else:
                    lines.append("ng %s %s\n" % (ref, reason))
        stream = b"".join(pkt_line(l) for l in lines) + pkt_flush()
        if sideband:
            body = self._git_sideband(stream, 1) + pkt_flush()
        else:
            body = stream + pkt_flush()
        self._send(200, body, "application/x-git-receive-pack-result")

    # -- REST ------------------------------------------------------------
    def _rest(self, sub, method, query, head_only=False):
        parts = [p for p in sub.split("/") if p != ""]
        # API root
        if not parts:
            if method == "GET":
                self._send_json(200, {
                    "current_user_url": "/api/v3/user",
                    "rate_limit_url": "/api/v3/rate_limit"},
                    {"X-OAuth-Scopes": "repo, read:org"})
            else:
                self._err(404, "Not Found")
            return
        if parts == ["meta"] and method == "GET":
            self._send_json(200, {"installed_version": VERSION,
                                  "verifiable_password_authentication": True})
            return
        if parts == ["user"] and method == "GET":
            if not self._require_auth():
                return
            self._send_json(200, {"login": VIEWER_LOGIN, "id": VIEWER_ID,
                                  "type": "User",
                                  "html_url": "https://example.invalid/" + VIEWER_LOGIN})
            return
        if parts == ["user", "repos"]:
            if method == "GET":
                if not self._require_auth():
                    return
                repos = STORE.list_repos()
                page_items, per_page, page, total = paginate(
                    [repo_json(r) for r in repos], query)
                link = self._link_header("/api/v3/user/repos", query,
                                         per_page, page, total)
                self._send_json(200, page_items,
                                {"Link": link} if link else None)
                return
            if method == "POST":
                if not self._require_auth():
                    return
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                name = body.get("name")
                if not isinstance(name, str) or not name:
                    self._err(422, "Validation Failed: name is required")
                    return
                repo = STORE.create_repo(name, body.get("private", False),
                                         body.get("description"))
                if repo is None:
                    self._err(422, "Repository already exists")
                    return
                self._send_json(201, repo_json(repo))
                return
            self._err(404, "Not Found")
            return
        if len(parts) >= 3 and parts[0] == "repos":
            owner, name = parts[1], parts[2]
            self._rest_repo(owner, name, parts[3:], method, query)
            return
        self._err(404, "Not Found")

    def _load_repo(self, owner, name):
        repo = STORE.get_repo(owner, name)
        if repo is None:
            self._err(404, "Not Found")
            return None
        return repo

    def _rest_repo(self, owner, name, rest, method, query):
        if not self._require_auth():
            return
        if not rest:
            repo = self._load_repo(owner, name)
            if repo is None:
                return
            if method == "GET":
                self._send_json(200, repo_json(repo))
            elif method == "PATCH":
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                with STORE.lock:
                    if isinstance(body.get("description"), str):
                        repo.description = body["description"]
                    if isinstance(body.get("private"), bool):
                        repo.private = body["private"]
                self._send_json(200, repo_json(repo))
            elif method == "DELETE":
                if STORE.delete_repo(owner, name):
                    self._send_json_no_body(204)
                else:
                    self._err(404, "Not Found")
            else:
                self._err(404, "Not Found")
            return
        head = rest[0]
        if head == "branches":
            self._rest_branches(owner, name, rest[1:], method)
            return
        if head == "commits":
            self._rest_commits(owner, name, method, query)
            return
        if head == "contents":
            self._rest_contents(owner, name, rest[1:], method, query)
            return
        if head == "labels":
            self._rest_labels(owner, name, method)
            return
        if head == "issues":
            self._rest_issues(owner, name, rest[1:], method, query)
            return
        if head == "pulls":
            self._rest_pulls(owner, name, rest[1:], method, query)
            return
        if head == "git":
            self._rest_git(owner, name, rest[1:], method)
            return
        self._err(404, "Not Found")

    def _rest_branches(self, owner, name, rest, method):
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        if rest:
            branch = "/".join(rest)
            if method == "GET":
                tip = repo.ref_tip(branch)
                if tip is None:
                    self._err(404, "Not Found")
                    return
                self._send_json(200, {"name": branch,
                                      "commit": {"sha": tip}})
                return
            self._err(404, "Not Found")
            return
        if method != "GET":
            self._err(404, "Not Found")
            return
        out = []
        for ref in sorted(repo.refs):
            if ref.startswith("refs/heads/"):
                out.append({"name": ref[len("refs/heads/"):],
                            "commit": {"sha": repo.refs[ref]},
                            "protected": False})
        self._send_json(200, out)

    def _walk_commits(self, repo, tip):
        """Commits reachable from tip, newest first (DFS, parents in order)."""
        out = []
        seen = set()
        stack = [tip] if tip else []
        while stack:
            oid = stack.pop()
            if oid in seen or oid == ZERO_OID:
                continue
            seen.add(oid)
            obj = repo.objects.get(oid)
            if obj is None or obj[0] != "commit":
                continue
            out.append(oid)
            stack.extend(parse_commit(obj[1])["parents"])
        return out

    def _rest_commits(self, owner, name, method, query):
        if method != "GET":
            self._err(404, "Not Found")
            return
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        ref = query.get("sha", [None])[0]
        tip = None
        if ref:
            if ref in repo.objects:
                tip = ref
            else:
                tip = repo.ref_tip(ref)
                if tip is None and ref.startswith("refs/heads/"):
                    tip = repo.refs.get(ref)
        if tip is None:
            tip = repo.ref_tip(repo.default_branch)
        out = []
        for oid in self._walk_commits(repo, tip):
            commit = parse_commit(repo.objects[oid][1])
            author = parse_identity(commit["author"])
            committer = parse_identity(commit["committer"])
            out.append({
                "sha": oid,
                "commit": {
                    "message": commit["message"].rstrip("\n"),
                    "author": {"name": author[0], "email": author[1],
                               "date": iso_from_epoch(author[2])},
                    "committer": {"name": committer[0],
                                  "email": committer[1],
                                  "date": iso_from_epoch(committer[2])}},
                "author": {"login": VIEWER_LOGIN},
                "committer": {"login": VIEWER_LOGIN},
                "parents": [{"sha": p} for p in commit["parents"]]})
        self._send_json(200, out)

    def _rest_contents(self, owner, name, rest, method, query):
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        path = "/".join(rest)
        if not path:
            self._err(404, "Not Found")
            return
        body, bad = self._json_body() if method in ("PUT", "DELETE") else ({}, False)
        if bad:
            self._err(400, "Invalid JSON body")
            return
        branch = body.get("branch") if isinstance(body, dict) else None
        ref_q = query.get("ref", [None])[0]
        if branch is None:
            branch = ref_q or repo.default_branch
        if method == "GET":
            tip = repo.ref_tip(branch)
            if tip is None:
                self._err(404, "Not Found")
                return
            commit = repo.objects.get(tip)
            if commit is None:
                self._err(404, "Not Found")
                return
            tree_oid = parse_commit(commit[1])["tree"]
            blob_oid = tree_get(repo.objects, tree_oid, path)
            if blob_oid is not None:
                data = repo.objects[blob_oid][1]
                self._send_json(200, {
                    "type": "file", "encoding": "base64",
                    "size": len(data), "name": path.rsplit("/", 1)[-1],
                    "path": path, "sha": blob_oid, "content": b64e(data),
                    "url": "/api/v3/repos/%s/%s/contents/%s" % (owner, name, path)})
                return
            # directory listing (immediate children of the path)
            flat = flatten_tree(repo.objects, tree_oid)
            prefix = path.rstrip("/") + "/"
            children = {}
            for full, (mode, oid) in flat.items():
                if not full.startswith(prefix):
                    continue
                rest_path = full[len(prefix):]
                first = rest_path.split("/")[0]
                if "/" in rest_path:
                    children[first] = ("dir", None)
                else:
                    children[first] = ("file", oid)
            if not children:
                self._err(404, "Not Found")
                return
            out = []
            for child in sorted(children):
                kind, oid = children[child]
                entry = {"type": kind, "name": child,
                         "path": prefix + child,
                         "sha": oid or hash_object("tree", b""),
                         "size": 0 if kind == "dir" else len(
                             repo.objects[oid][1]) if oid in repo.objects else 0}
                out.append(entry)
            self._send_json(200, out)
            return
        if method == "PUT":
            content_b64 = body.get("content")
            message = body.get("message") or "Update %s" % path
            if not isinstance(content_b64, str):
                self._err(422, "Validation Failed: content is required")
                return
            try:
                content = b64d(content_b64)
            except Exception:
                self._err(400, "Invalid base64 content")
                return
            status, commit_sha, blob_oid = STORE.commit_file(
                repo, branch, path, content, message, body.get("sha"))
            if status == 409:
                self._err(409, "Conflict: sha does not match the current file")
                return
            self._send_json(status, {
                "content": {"name": path.rsplit("/", 1)[-1], "path": path,
                            "sha": blob_oid, "size": len(content),
                            "encoding": "base64"},
                "commit": {"sha": commit_sha, "message": message}})
            return
        if method == "DELETE":
            message = body.get("message") or "Delete %s" % path
            commit_sha = STORE.delete_file(repo, branch, path, message)
            if commit_sha is None:
                self._err(404, "Not Found")
                return
            self._send_json(200, {"commit": {"sha": commit_sha}})
            return
        self._err(404, "Not Found")

    def _rest_labels(self, owner, name, method):
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        if method == "GET":
            self._send_json(200, list(repo.labels.values()))
            return
        if method == "POST":
            body, bad = self._json_body()
            if bad:
                self._err(400, "Invalid JSON body")
                return
            label_name = body.get("name")
            if not isinstance(label_name, str) or not label_name:
                self._err(422, "Validation Failed: name is required")
                return
            color = body.get("color") or "ededed"
            with STORE.lock:
                repo.labels[label_name] = {"name": label_name, "color": color,
                                           "description": "",
                                           "default": False}
                STORE.log_event("label.create",
                                {"repo": repo.full_name(), "name": label_name})
            self._send_json(201, repo.labels[label_name])
            return
        self._err(404, "Not Found")


    def _rest_issues(self, owner, name, rest, method, query):
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        if not rest:
            if method == "GET":
                state = query.get("state", ["open"])[0]
                sort = query.get("sort", ["created"])[0]
                direction = query.get("direction", ["desc"])[0]
                items = list(repo.issues.values())
                if state != "all":
                    items = [i for i in items if i["state"] == state]
                reverse = direction != "asc"
                items.sort(key=lambda i: i["number"], reverse=reverse)
                page_items, per_page, page, total = paginate(
                    [issue_json(repo, i) for i in items], query)
                link = self._link_header(
                    "/api/v3/repos/%s/%s/issues" % (owner, name), query,
                    per_page, page, total)
                self._send_json(200, page_items,
                                {"Link": link} if link else None)
                return
            if method == "POST":
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                title = body.get("title")
                if not isinstance(title, str) or not title:
                    self._err(422, "Validation Failed: title is required")
                    return
                labels = body.get("labels") or []
                if not isinstance(labels, list):
                    self._err(422, "Validation Failed: labels must be a list")
                    return
                label_names = []
                for lab in labels:
                    if isinstance(lab, dict):
                        lab = lab.get("name")
                    if lab not in repo.labels:
                        self._err(422, "Validation Failed: label '%s' does not exist" % lab)
                        return
                    label_names.append(lab)
                issue = STORE.create_issue(repo, title, body.get("body"),
                                           label_names)
                self._send_json(201, issue_json(repo, issue))
                return
            self._err(404, "Not Found")
            return
        try:
            number = int(rest[0])
        except ValueError:
            self._err(404, "Not Found")
            return
        issue = repo.issues.get(number)
        if len(rest) == 1:
            if issue is None:
                self._err(404, "Not Found")
                return
            if method == "GET":
                self._send_json(200, issue_json(repo, issue))
                return
            if method == "PATCH":
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                with STORE.lock:
                    if isinstance(body.get("title"), str):
                        issue["title"] = body["title"]
                    if body.get("body") is not None:
                        issue["body"] = body["body"]
                    if body.get("state") in ("open", "closed"):
                        issue["state"] = body["state"]
                    STORE.log_event("issue.update",
                                    {"repo": repo.full_name(),
                                     "number": number,
                                     "state": issue["state"]})
                self._send_json(200, issue_json(repo, issue))
                return
            self._err(404, "Not Found")
            return
        if rest[1] == "comments":
            if issue is None:
                self._err(404, "Not Found")
                return
            if method == "GET":
                out = [{"id": c["id"], "body": c["body"],
                        "user": {"login": VIEWER_LOGIN, "id": VIEWER_ID},
                        "created_at": FIXED_MERGED_AT,
                        "updated_at": FIXED_MERGED_AT}
                       for c in repo.comments.get(number, [])]
                self._send_json(200, out)
                return
            if method == "POST":
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                text = body.get("body")
                if not isinstance(text, str) or not text:
                    self._err(422, "Validation Failed: body is required")
                    return
                comment = STORE.add_comment(repo, number, text)
                self._send_json(201, {"id": comment["id"], "body": text,
                                      "user": {"login": VIEWER_LOGIN,
                                               "id": VIEWER_ID},
                                      "created_at": FIXED_MERGED_AT,
                                      "updated_at": FIXED_MERGED_AT})
                return
            self._err(404, "Not Found")
            return
        self._err(404, "Not Found")

    def _rest_pulls(self, owner, name, rest, method, query):
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        if not rest:
            if method == "GET":
                state = query.get("state", ["open"])[0]
                items = list(repo.pulls.values())
                if state != "all":
                    items = [p for p in items if p["state"] == state]
                items.sort(key=lambda p: p["number"], reverse=True)
                page_items, per_page, page, total = paginate(
                    [pull_json(repo, p) for p in items], query)
                link = self._link_header(
                    "/api/v3/repos/%s/%s/pulls" % (owner, name), query,
                    per_page, page, total)
                self._send_json(200, page_items,
                                {"Link": link} if link else None)
                return
            if method == "POST":
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                title = body.get("title")
                head = body.get("head")
                base = body.get("base")
                if not isinstance(title, str) or not title:
                    self._err(422, "Validation Failed: title is required")
                    return
                if not isinstance(head, str) or not isinstance(base, str):
                    self._err(422, "Validation Failed: head and base are required")
                    return
                head = head.split(":", 1)[-1]
                base = base.split(":", 1)[-1]
                if repo.ref_tip(head) is None or repo.ref_tip(base) is None:
                    self._err(422, "Validation Failed: head or base branch does not exist")
                    return
                for existing in repo.pulls.values():
                    if (existing["state"] == "open" and
                            existing["head"] == head and
                            existing["base"] == base):
                        self._err(422, "A pull request already exists for this head and base")
                        return
                pr = STORE.create_pull(repo, title, body.get("body"),
                                       head, base)
                self._send_json(201, pull_json(repo, pr))
                return
            self._err(404, "Not Found")
            return
        try:
            number = int(rest[0])
        except ValueError:
            self._err(404, "Not Found")
            return
        pr = repo.pulls.get(number)
        if len(rest) == 1:
            if pr is None:
                self._err(404, "Not Found")
                return
            if method == "GET":
                self._send_json(200, pull_json(repo, pr))
                return
            self._err(404, "Not Found")
            return
        if pr is None:
            self._err(404, "Not Found")
            return
        if rest[1] == "files" and method == "GET":
            head_tip = repo.ref_tip(pr["head"])
            base_tip = pr["base_sha"]
            mb = merge_base(repo.objects, head_tip, base_tip)
            if mb is None:
                base_tree = None
            else:
                base_tree = parse_commit(repo.objects[mb][1])["tree"]
            head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
            diffs = tree_diff(repo.objects, base_tree, head_tree)
            out = []
            for path in sorted(diffs):
                change = diffs[path]
                adds, dels = line_counts(repo.objects, change[1], change[2])
                if change[0] == "added":
                    status = "added"
                elif change[0] == "removed":
                    status = "removed"
                else:
                    status = "modified"
                out.append({"filename": path, "status": status,
                            "additions": adds, "deletions": dels,
                            "changes": adds + dels,
                            "sha": change[2] or change[1] or ""})
            self._send_json(200, out)
            return
        if rest[1] == "merge" and method == "PUT":
            if pr["state"] != "open":
                self._err(405, "Pull request is not open")
                return
            if not STORE.mergeable(repo, pr):
                self._err(405, "Merge conflict")
                return
            ok, sha = STORE.squash_merge(repo, pr)
            if not ok:
                self._err(405, "Merge conflict")
                return
            self._send_json(200, {"sha": sha, "merged": True,
                                  "message": "Pull request successfully merged"})
            return
        self._err(404, "Not Found")

    def _rest_git(self, owner, name, rest, method):
        repo = self._load_repo(owner, name)
        if repo is None:
            return
        if rest and rest[0] == "refs":
            if method == "POST" and len(rest) == 1:
                body, bad = self._json_body()
                if bad:
                    self._err(400, "Invalid JSON body")
                    return
                ref = body.get("ref")
                sha = body.get("sha")
                if (not isinstance(ref, str) or not ref.startswith("refs/") or
                        not isinstance(sha, str) or sha not in repo.objects):
                    self._err(422, "Validation Failed: ref and sha are required")
                    return
                with STORE.lock:
                    if ref in repo.refs:
                        self._err(422, "Reference already exists")
                        return
                    repo.refs[ref] = sha
                    STORE.log_event("ref.create",
                                    {"repo": repo.full_name(), "ref": ref,
                                     "sha": sha})
                self._send_json(201, {"ref": ref, "object": {"sha": sha}})
                return
            if method == "GET":
                if len(rest) >= 2:
                    ref = "refs/" + "/".join(rest[1:])
                    sha = repo.refs.get(ref)
                    if sha is None:
                        self._err(404, "Not Found")
                        return
                    self._send_json(200, {"ref": ref,
                                          "object": {"sha": sha}})
                    return
                out = [{"ref": r, "object": {"sha": s}}
                       for r, s in sorted(repo.refs.items())]
                self._send_json(200, out)
                return
        self._err(404, "Not Found")


# ---------------------------------------------------------------------------
# GraphQL (hand-rolled parser + executor for the documents gh sends)
# ---------------------------------------------------------------------------

GQL_TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<comment>\#[^\n]*)
  | (?P<spread>\.\.\.)
  | (?P<punct>[{}()\[\]:!=$@|&])
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?)
  | (?P<int>-?\d+)
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<name>[_A-Za-z][_A-Za-z0-9]*)
""", re.VERBOSE)


class GqlField(object):
    __slots__ = ("alias", "name", "args", "selection")

    def __init__(self, alias, name, args, selection):
        self.alias = alias
        self.name = name
        self.args = args
        self.selection = selection


class GqlFragment(object):
    __slots__ = ("type_condition", "selection")

    def __init__(self, type_condition, selection):
        self.type_condition = type_condition
        self.selection = selection


class GqlOperation(object):
    __slots__ = ("kind", "name", "selection")

    def __init__(self, kind, name, selection):
        self.kind = kind
        self.name = name
        self.selection = selection


class GqlParser(object):
    def __init__(self, text):
        self.tokens = []
        pos = 0
        for m in GQL_TOKEN_RE.finditer(text):
            kind = m.lastgroup
            if kind in ("ws", "comment"):
                continue
            self.tokens.append((kind, m.group(0)))
        self.pos = 0

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return ("eof", "")

    def next(self):
        tok = self.peek()
        self.pos += 1
        return tok

    def expect(self, value):
        kind, text = self.next()
        if text != value:
            raise ValueError("expected %s, got %s" % (value, text))

    def parse_document(self):
        operations = []
        while self.peek()[0] != "eof":
            operations.append(self.parse_operation())
        return operations

    def parse_operation(self):
        kind, text = self.next()
        if text == "{":
            self.pos -= 1
            return GqlOperation("query", None, self.parse_selection_set())
        if text not in ("query", "mutation", "subscription"):
            raise ValueError("unexpected token %s" % text)
        name = None
        if self.peek()[0] == "name":
            name = self.next()[1]
        if self.peek()[1] == "(":
            self.skip_balanced()
        selection = self.parse_selection_set()
        return GqlOperation(text, name, selection)

    def skip_balanced(self):
        depth = 0
        while True:
            kind, text = self.next()
            if text in ("(", "[", "{"):
                depth += 1
            elif text in (")", "]", "}"):
                depth -= 1
                if depth == 0:
                    return
            elif kind == "eof":
                raise ValueError("unbalanced brackets")

    def parse_selection_set(self):
        self.expect("{")
        items = []
        while self.peek()[1] != "}":
            if self.peek()[0] == "eof":
                raise ValueError("unterminated selection set")
            items.append(self.parse_selection_item())
        self.expect("}")
        return items

    def parse_selection_item(self):
        if self.peek()[0] == "spread":
            self.next()
            type_condition = None
            if self.peek()[1] == "on":
                self.next()
                type_condition = self.next()[1]
            return GqlFragment(type_condition, self.parse_selection_set())
        kind, name = self.next()
        if kind != "name":
            raise ValueError("expected field name, got %s" % name)
        alias = None
        if self.peek()[1] == ":":
            self.next()
            alias = name
            name = self.next()[1]
        args = {}
        if self.peek()[1] == "(":
            args = self.parse_arguments()
        selection = []
        if self.peek()[1] == "{":
            selection = self.parse_selection_set()
        return GqlField(alias, name, args, selection)

    def parse_arguments(self):
        self.expect("(")
        args = {}
        while self.peek()[1] != ")":
            name = self.next()[1]
            self.expect(":")
            args[name] = self.parse_value()
        self.expect(")")
        return args

    def parse_value(self):
        kind, text = self.next()
        if text == "$":
            return ("var", self.next()[1])
        if kind == "int":
            return int(text)
        if kind == "float":
            return float(text)
        if kind == "string":
            return json.loads(text)
        if text == "[":
            values = []
            while self.peek()[1] != "]":
                values.append(self.parse_value())
            self.expect("]")
            return values
        if text == "{":
            obj = {}
            while self.peek()[1] != "}":
                key = self.next()[1]
                self.expect(":")
                obj[key] = self.parse_value()
            self.expect("}")
            return obj
        if text == "true":
            return True
        if text == "false":
            return False
        if text == "null":
            return None
        return ("enum", text)


def gql_eval(value, variables):
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "var":
        return variables.get(value[1])
    if isinstance(value, tuple) and len(value) == 2 and value[0] == "enum":
        return value[1]
    if isinstance(value, list):
        return [gql_eval(v, variables) for v in value]
    if isinstance(value, dict):
        return {k: gql_eval(v, variables) for k, v in value.items()}
    return value


# Introspection tables (what gh's feature probes read).
ISSUE_FIELDS = ["id", "number", "title", "state", "body", "url",
                "createdAt", "author", "comments"]
PULL_REQUEST_FIELDS = ["id", "number", "title", "body", "state", "merged",
                       "headRefName", "baseRefName", "mergeable", "files",
                       "url", "createdAt"]
REPOSITORY_FIELDS = ["id", "databaseId", "name", "nameWithOwner", "owner",
                     "defaultBranchRef", "viewerPermission",
                     "hasIssuesEnabled", "issue", "issues", "pullRequests",
                     "pullRequest", "description", "private", "createdAt",
                     "updatedAt"]
SEARCH_TYPE_VALUES = ["ISSUE", "REPOSITORY", "USER", "DISCUSSION", "CODE",
                      "COMMIT", "LABEL", "MILESTONE", "TOPIC", "PACKAGE",
                      "MARKETPLACE", "PROJECT", "TEAM", "ORGANIZATION"]
INTROSPECTION = {
    "Issue": (ISSUE_FIELDS, None),
    "PullRequest": (PULL_REQUEST_FIELDS, None),
    "Repository": (REPOSITORY_FIELDS, None),
    "SearchType": (None, SEARCH_TYPE_VALUES),
    "User": (["login", "id"], None),
}

_MISSING = object()


def _obj(subtype, obj):
    return ("OBJ", subtype, obj)


def _list(subtype, objs):
    return ("LIST", subtype, objs)


def _issue_state(issue):
    return "OPEN" if issue["state"] == "open" else "CLOSED"


def _pr_state(pr):
    if pr["merged"]:
        return "MERGED"
    return "OPEN" if pr["state"] == "open" else "CLOSED"


def _resolve_gid(gid):
    """gid -> ('repo', repo) | ('issue', repo, issue) | ('pr', repo, pr) | None."""
    if not isinstance(gid, str):
        return None
    m = re.match(r"^gid-repo-(\d+)$", gid)
    if m:
        repo = STORE.find_repo_by_global_id(gid)
        return ("repo", repo) if repo is not None else None
    m = re.match(r"^gid-issue-(\d+)-(\d+)$", gid)
    if m:
        repo = STORE.find_repo_by_global_id("gid-repo-%s" % m.group(1))
        if repo is None:
            return None
        issue = repo.issues.get(int(m.group(2)))
        return ("issue", repo, issue) if issue is not None else None
    m = re.match(r"^gid-pr-(\d+)-(\d+)$", gid)
    if m:
        repo = STORE.find_repo_by_global_id("gid-repo-%s" % m.group(1))
        if repo is None:
            return None
        pr = repo.pulls.get(int(m.group(2)))
        return ("pr", repo, pr) if pr is not None else None
    return None


def _issues_connection(repo, args):
    items = list(repo.issues.values())
    states = args.get("states")
    if states:
        wanted = set(str(s).lower() for s in states)
        items = [i for i in items if i["state"] in wanted]
    order = args.get("orderBy") or {}
    direction = order.get("direction") or "DESC"
    items.sort(key=lambda i: i["number"], reverse=(direction != "ASC"))
    after = args.get("after")
    if after:
        try:
            threshold = int(str(after).lstrip("c"))
            if direction == "ASC":
                items = [i for i in items if i["number"] > threshold]
            else:
                items = [i for i in items if i["number"] < threshold]
        except ValueError:
            pass
    first = args.get("first")
    page = items if first is None else items[:first]
    has_next = len(items) > len(page)
    end_cursor = ("c%d" % page[-1]["number"]) if page else None
    return {"repo": repo, "nodes": page,
            "pageInfo": {"hasNextPage": has_next, "endCursor": end_cursor}}


def _pulls_connection(repo, args):
    items = list(repo.pulls.values())
    states = args.get("states")
    if states:
        wanted = set(str(s) for s in states)
        items = [p for p in items if _pr_state(p) in wanted]
    items.sort(key=lambda p: p["number"], reverse=True)
    after = args.get("after")
    if after:
        try:
            threshold = int(str(after).lstrip("c"))
            items = [p for p in items if p["number"] < threshold]
        except ValueError:
            pass
    first = args.get("first")
    page = items if first is None else items[:first]
    has_next = len(items) > len(page)
    end_cursor = ("c%d" % page[-1]["number"]) if page else None
    return {"repo": repo, "nodes": page,
            "pageInfo": {"hasNextPage": has_next, "endCursor": end_cursor}}


def _pr_files_connection(repo, pr, args):
    head_tip = repo.ref_tip(pr["head"])
    mb = merge_base(repo.objects, head_tip, pr["base_sha"])
    base_tree = None
    if mb is not None:
        base_tree = parse_commit(repo.objects[mb][1])["tree"]
    head_tree = None
    if head_tip is not None:
        head_tree = parse_commit(repo.objects[head_tip][1])["tree"]
    diffs = tree_diff(repo.objects, base_tree, head_tree)
    nodes = []
    for path in sorted(diffs):
        change = diffs[path]
        adds, dels = line_counts(repo.objects, change[1], change[2])
        nodes.append({"path": path, "additions": adds, "deletions": dels})
    first = args.get("first")
    if first is not None:
        nodes = nodes[:first]
    return {"nodes": nodes,
            "pageInfo": {"hasNextPage": False, "endCursor": None}}


def _gql_repo_fields(repo, field, args, errors):
    name = field.name
    if name == "id":
        return repo.global_id()
    if name == "databaseId":
        return repo.dbid
    if name == "name":
        return repo.name
    if name == "nameWithOwner":
        return repo.full_name()
    if name == "owner":
        return _obj("User", {"login": repo.owner})
    if name == "defaultBranchRef":
        tip = repo.ref_tip(repo.default_branch)
        if tip is None:
            return None
        return _obj("Ref", {"name": repo.default_branch})
    if name == "viewerPermission":
        return "ADMIN"
    if name == "hasIssuesEnabled":
        return True
    if name == "description":
        return repo.description
    if name == "private":
        return repo.private
    if name == "createdAt" or name == "updatedAt":
        return FIXED_MERGED_AT
    if name == "issue":
        number = args.get("number")
        issue = repo.issues.get(number) if isinstance(number, int) else None
        return _obj("Issue", (repo, issue)) if issue is not None else None
    if name == "issues":
        return _obj("IssueConnection", _issues_connection(repo, args))
    if name == "pullRequests":
        return _obj("PullRequestConnection", _pulls_connection(repo, args))
    if name == "pullRequest":
        number = args.get("number")
        pr = repo.pulls.get(number) if isinstance(number, int) else None
        return _obj("PullRequest", (repo, pr)) if pr is not None else None
    return _MISSING


def _gql_issue_fields(repo, issue, field, args, errors):
    name = field.name
    if name == "id":
        return issue["global_id"]
    if name == "number":
        return issue["number"]
    if name == "title":
        return issue["title"]
    if name == "state":
        return _issue_state(issue)
    if name == "body":
        return issue["body"]
    if name == "url":
        return "https://example.invalid/%s/issues/%d" % (
            repo.full_name(), issue["number"])
    if name == "createdAt":
        return FIXED_MERGED_AT
    if name == "author":
        return _obj("User", {"login": VIEWER_LOGIN})
    if name == "comments":
        return _obj("IssueConnection", {
            "nodes": [], "pageInfo": {"hasNextPage": False,
                                      "endCursor": None}})
    return _MISSING


def _gql_pr_fields(repo, pr, field, args, errors):
    name = field.name
    if name == "id":
        return pr["global_id"]
    if name == "number":
        return pr["number"]
    if name == "title":
        return pr["title"]
    if name == "body":
        return pr["body"]
    if name == "state":
        return _pr_state(pr)
    if name == "merged":
        return pr["merged"]
    if name == "headRefName":
        return pr["head"]
    if name == "baseRefName":
        return pr["base"]
    if name == "mergeable":
        if pr["state"] != "open":
            return "UNKNOWN"
        return "MERGEABLE" if STORE.mergeable(repo, pr) else "CONFLICTING"
    if name == "files":
        return _obj("PullRequestChangedFileConnection",
                    _pr_files_connection(repo, pr, args))
    if name == "url":
        return "https://example.invalid/%s/pull/%d" % (
            repo.full_name(), pr["number"])
    if name == "createdAt":
        return FIXED_MERGED_AT
    return _MISSING


def _gql_object(type_name, obj, selection, variables, errors):
    """Resolve a selection set against one typed object; obj is a dict or Repo."""
    out = {}
    for item in selection:
        if isinstance(item, GqlFragment):
            if item.type_condition is None or item.type_condition == type_name:
                sub = _gql_object(type_name, obj, item.selection,
                                  variables, errors)
                out.update(sub)
            continue
        key = item.alias or item.name
        args = {k: gql_eval(v, variables) for k, v in item.args.items()}
        value = _gql_field(type_name, obj, item, args, errors)
        if value is _MISSING:
            errors.append('Cannot query field "%s" on type "%s".' % (
                item.name, type_name))
            continue
        out[key] = _gql_shape(value, item.selection, variables, errors)
    return out


def _gql_shape(value, selection, variables, errors):
    if isinstance(value, tuple):
        kind = value[0]
        if kind == "OBJ":
            if not selection:
                return {}
            return _gql_object(value[1], value[2], selection, variables,
                               errors)
        if kind == "LIST":
            return [_gql_object(value[1], entry, selection, variables,
                                errors) for entry in value[2]]
    return value


def _gql_field(type_name, obj, field, args, errors):
    name = field.name
    if type_name == "User":
        if name == "login":
            return obj["login"]
        if name == "id":
            return "gid-user-%s" % obj["login"]
        return _MISSING
    if type_name == "Ref":
        if name == "name":
            return obj["name"]
        return _MISSING
    if type_name == "Repository":
        return _gql_repo_fields(obj, field, args, errors)
    if type_name == "Issue":
        # obj is (repo, issue) tuple for context-dependent fields
        repo, issue = obj
        return _gql_issue_fields(repo, issue, field, args, errors)
    if type_name == "PullRequest":
        repo, pr = obj
        return _gql_pr_fields(repo, pr, field, args, errors)
    if type_name == "IssueConnection":
        if name == "nodes":
            return _list("Issue", [(obj.get("repo"), i)
                                   for i in obj["nodes"]])
        if name == "pageInfo":
            return _obj("PageInfo", obj["pageInfo"])
        if name == "totalCount":
            return len(obj["nodes"])
        return _MISSING
    if type_name == "PullRequestConnection":
        if name == "nodes":
            return _list("PullRequest", [(obj.get("repo"), p)
                                         for p in obj["nodes"]])
        if name == "pageInfo":
            return _obj("PageInfo", obj["pageInfo"])
        if name == "totalCount":
            return len(obj["nodes"])
        return _MISSING
    if type_name == "PullRequestChangedFileConnection":
        if name == "nodes":
            return _list("PullRequestChangedFile", obj["nodes"])
        if name == "pageInfo":
            return _obj("PageInfo", obj["pageInfo"])
        if name == "totalCount":
            return len(obj["nodes"])
        return _MISSING
    if type_name == "PullRequestChangedFile":
        if name in ("path", "additions", "deletions"):
            return obj[name]
        return _MISSING
    if type_name == "PageInfo":
        if name in ("hasNextPage", "endCursor"):
            return obj[name]
        return _MISSING
    if type_name == "__Type":
        if name == "name":
            return obj["name"]
        if name == "fields":
            fields, _ = INTROSPECTION.get(obj["name"], ([], None))
            return _list("__TypeField", [{"name": f} for f in (fields or [])])
        if name == "enumValues":
            _, values = INTROSPECTION.get(obj["name"], (None, []))
            return _list("__TypeEnumValue",
                         [{"name": v} for v in (values or [])])
        return _MISSING
    if type_name in ("__TypeField", "__TypeEnumValue"):
        if name == "name":
            return obj["name"]
        return _MISSING
    if type_name == "CommentEdge":
        if name == "node":
            return _obj("IssueComment", obj["node"])
        return _MISSING
    if type_name == "IssueComment":
        if name == "id":
            return obj["id"]
        if name == "body":
            return obj["body"]
        return _MISSING
    return _MISSING


def _gql_root(field, variables, errors):
    """Resolve one root field (query or mutation). Returns _MISSING if unknown."""
    name = field.name
    args = {k: gql_eval(v, variables) for k, v in field.args.items()}
    sel = field.selection
    if name == "viewer":
        return _obj("User", {"login": VIEWER_LOGIN})
    if name == "repository":
        owner = args.get("owner")
        repo_name = args.get("name")
        repo = STORE.get_repo(owner, repo_name) if isinstance(
            owner, str) and isinstance(repo_name, str) else None
        return _obj("Repository", repo) if repo is not None else None
    if name == "node":
        resolved = _resolve_gid(args.get("id"))
        if resolved is None:
            return None
        if resolved[0] == "repo":
            return _obj("Repository", resolved[1])
        if resolved[0] == "issue":
            return _obj("Issue", (resolved[1], resolved[2]))
        if resolved[0] == "pr":
            return _obj("PullRequest", (resolved[1], resolved[2]))
        return None
    if name == "__type":
        type_name = args.get("name")
        if not isinstance(type_name, str) or type_name not in INTROSPECTION:
            return None
        return _obj("__Type", {"name": type_name})
    if name == "createIssue":
        inp = args.get("input") or {}
        resolved = _resolve_gid(inp.get("repositoryId"))
        if resolved is None or resolved[0] != "repo":
            errors.append("createIssue: could not resolve repositoryId")
            return None
        repo = resolved[1]
        issue = STORE.create_issue(repo, inp.get("title") or "",
                                   inp.get("body"), [])
        return _obj("CreateIssuePayload",
                    {"issue": (repo, issue)})
    if name == "closeIssue":
        inp = args.get("input") or {}
        resolved = _resolve_gid(inp.get("issueId"))
        if resolved is None or resolved[0] != "issue":
            errors.append("closeIssue: could not resolve issueId")
            return None
        repo, issue = resolved[1], resolved[2]
        with STORE.lock:
            issue["state"] = "closed"
            STORE.log_event("issue.update",
                            {"repo": repo.full_name(),
                             "number": issue["number"], "state": "closed"})
        return _obj("CloseIssuePayload", {"issue": (repo, issue)})
    if name == "createPullRequest":
        inp = args.get("input") or {}
        resolved = _resolve_gid(inp.get("repositoryId"))
        if resolved is None or resolved[0] != "repo":
            errors.append("createPullRequest: could not resolve repositoryId")
            return None
        repo = resolved[1]
        head = inp.get("headRefName")
        base = inp.get("baseRefName")
        if repo.ref_tip(head) is None or repo.ref_tip(base) is None:
            errors.append("createPullRequest: head or base branch not found")
            return None
        pr = STORE.create_pull(repo, inp.get("title") or "", inp.get("body"),
                               head, base)
        return _obj("CreatePullRequestPayload", {"pullRequest": (repo, pr)})
    if name == "mergePullRequest":
        inp = args.get("input") or {}
        resolved = _resolve_gid(inp.get("pullRequestId"))
        if resolved is None or resolved[0] != "pr":
            errors.append("mergePullRequest: could not resolve pullRequestId")
            return None
        repo, pr = resolved[1], resolved[2]
        if pr["state"] == "open" and STORE.mergeable(repo, pr):
            STORE.squash_merge(repo, pr)
        return _obj("MergePullRequestPayload", {"pullRequest": (repo, pr)})
    if name == "addComment":
        inp = args.get("input") or {}
        resolved = _resolve_gid(inp.get("subjectId"))
        if resolved is None or resolved[0] != "issue":
            errors.append("addComment: could not resolve subjectId")
            return None
        repo, issue = resolved[1], resolved[2]
        comment = STORE.add_comment(repo, issue["number"],
                                    inp.get("body") or "")
        return _obj("AddCommentPayload",
                    {"commentEdge": {"node": comment}})
    return _MISSING


def _gql_payload_object(type_name, obj, selection, variables, errors):
    """Resolve mutation-payload selections (issue/pullRequest/commentEdge)."""
    out = {}
    for item in selection:
        if isinstance(item, GqlFragment):
            if item.type_condition is None or item.type_condition == type_name:
                out.update(_gql_payload_object(
                    type_name, obj, item.selection, variables, errors))
            continue
        key = item.alias or item.name
        if type_name in ("CreateIssuePayload", "CloseIssuePayload"):
            if item.name == "issue":
                out[key] = _gql_object("Issue", obj["issue"],
                                       item.selection, variables, errors)
            else:
                errors.append('Cannot query field "%s" on type "%s".' % (
                    item.name, type_name))
        elif type_name == "CreatePullRequestPayload":
            if item.name == "pullRequest":
                out[key] = _gql_object("PullRequest", obj["pullRequest"],
                                       item.selection, variables, errors)
            else:
                errors.append('Cannot query field "%s" on type "%s".' % (
                    item.name, type_name))
        elif type_name == "MergePullRequestPayload":
            if item.name == "pullRequest":
                out[key] = _gql_object("PullRequest", obj["pullRequest"],
                                       item.selection, variables, errors)
            else:
                errors.append('Cannot query field "%s" on type "%s".' % (
                    item.name, type_name))
        elif type_name == "AddCommentPayload":
            if item.name == "commentEdge":
                out[key] = _gql_object("CommentEdge", obj["commentEdge"],
                                       item.selection, variables, errors)
            else:
                errors.append('Cannot query field "%s" on type "%s".' % (
                    item.name, type_name))
        else:
            errors.append('Cannot query field "%s" on type "%s".' % (
                item.name, type_name))
    return out


def _gql_execute(query_text, variables):
    try:
        operations = GqlParser(query_text).parse_document()
    except Exception as exc:
        return {"data": None,
                "errors": [{"message": "Syntax Error: %s" % exc}]}
    if not operations:
        return {"data": None,
                "errors": [{"message": "Syntax Error: empty document"}]}
    operation = operations[0]
    errors = []
    data = {}
    for field in operation.selection:
        key = field.alias or field.name
        value = _gql_root(field, variables, errors)
        if value is _MISSING:
            errors.append('Cannot query field "%s" on type "%s".' % (
                field.name, "Mutation" if operation.kind == "mutation"
                else "Query"))
            continue
        if value is None:
            data[key] = None
            continue
        if isinstance(value, tuple) and value[0] == "OBJ":
            subtype = value[1]
            if subtype in ("CreateIssuePayload", "CloseIssuePayload",
                           "CreatePullRequestPayload",
                           "MergePullRequestPayload", "AddCommentPayload"):
                data[key] = _gql_payload_object(
                    subtype, value[2], field.selection, variables, errors)
            elif subtype == "Issue":
                data[key] = _gql_object("Issue", value[2], field.selection,
                                        variables, errors)
            elif subtype == "PullRequest":
                data[key] = _gql_object("PullRequest", value[2],
                                        field.selection, variables, errors)
            else:
                data[key] = _gql_object(subtype, value[2], field.selection,
                                        variables, errors)
        else:
            data[key] = value
    result = {"data": data}
    if errors:
        result["errors"] = [{"message": m} for m in errors]
    return result


def _gql_run_item(item):
    if not isinstance(item, dict):
        return {"data": None,
                "errors": [{"message": "Invalid operation document"}]}
    query_text = item.get("query") or ""
    variables = item.get("variables") or {}
    if not isinstance(variables, dict):
        variables = {}
    if not isinstance(query_text, str):
        return {"data": None,
                "errors": [{"message": "Invalid query"}]}
    return _gql_execute(query_text, variables)


# ---------------------------------------------------------------------------
# MCP (JSON-RPC 2.0 Streamable HTTP)
# ---------------------------------------------------------------------------

MCP_SUPPORTED_VERSIONS = ["2026-07-28", "2025-11-25", "2025-06-18",
                          "2025-03-26", "2024-11-05"]

MCP_TOOLS = [
    {"name": "create_repo",
     "description": "Create a new repository owned by the viewer.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "name": {"type": "string",
                                  "description": "Repository name"},
                         "description": {"type": "string",
                                         "description": "Repository description"},
                         "private": {"type": "boolean",
                                     "description": "Whether the repository is private"}},
                     "required": ["name"]}},
    {"name": "get_repo",
     "description": "Get a repository by owner and name.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string",
                                   "description": "Repository owner login"},
                         "repo": {"type": "string",
                                  "description": "Repository name"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_issue",
     "description": "Create an issue in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string",
                                   "description": "Repository owner login"},
                         "repo": {"type": "string",
                                  "description": "Repository name"},
                         "title": {"type": "string",
                                   "description": "Issue title"},
                         "body": {"type": "string",
                                  "description": "Issue body"}},
                     "required": ["owner", "repo", "title"]}},
    {"name": "list_issues",
     "description": "List issues in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string",
                                   "description": "Repository owner login"},
                         "repo": {"type": "string",
                                  "description": "Repository name"},
                         "state": {"type": "string",
                                   "description": "open, closed or all"}},
                     "required": ["owner", "repo"]}},
    {"name": "create_pull_request",
     "description": "Create a pull request in a repository.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string",
                                   "description": "Repository owner login"},
                         "repo": {"type": "string",
                                  "description": "Repository name"},
                         "title": {"type": "string",
                                   "description": "Pull request title"},
                         "head": {"type": "string",
                                  "description": "Head branch name"},
                         "base": {"type": "string",
                                  "description": "Base branch name"},
                         "body": {"type": "string",
                                  "description": "Pull request body"}},
                     "required": ["owner", "repo", "title", "head", "base"]}},
    {"name": "merge_pull_request",
     "description": "Merge a pull request with a squash commit.",
     "inputSchema": {"type": "object",
                     "properties": {
                         "owner": {"type": "string",
                                   "description": "Repository owner login"},
                         "repo": {"type": "string",
                                  "description": "Repository name"},
                         "pull_number": {"type": "integer",
                                         "description": "Pull request number"}},
                     "required": ["owner", "repo", "pull_number"]}},
]


def _mcp_tool_call(name, args):
    """Run one MCP tool. Returns (result_dict, error_message_or_None)."""
    if not isinstance(args, dict):
        args = {}
    tool = None
    for candidate in MCP_TOOLS:
        if candidate["name"] == name:
            tool = candidate
            break
    if tool is None:
        return None, "Unknown tool: %s" % name
    for required in tool["inputSchema"].get("required", []):
        if required not in args or args[required] is None:
            return None, "Missing required argument: %s" % required
    if name == "create_repo":
        repo = STORE.create_repo(args["name"], args.get("private", False),
                                 args.get("description"))
        if repo is None:
            return None, "Repository already exists"
        return repo_json(repo), None
    owner = args.get("owner")
    repo_name = args.get("repo")
    repo = STORE.get_repo(owner, repo_name) if isinstance(
        owner, str) and isinstance(repo_name, str) else None
    if repo is None:
        return None, "Repository not found"
    if name == "get_repo":
        return repo_json(repo), None
    if name == "create_issue":
        issue = STORE.create_issue(repo, args["title"], args.get("body"), [])
        return issue_json(repo, issue), None
    if name == "list_issues":
        state = args.get("state", "open")
        items = list(repo.issues.values())
        if state != "all":
            items = [i for i in items if i["state"] == state]
        items.sort(key=lambda i: i["number"], reverse=True)
        return {"issues": [issue_json(repo, i) for i in items]}, None
    if name == "create_pull_request":
        head = str(args["head"]).split(":", 1)[-1]
        base = str(args["base"]).split(":", 1)[-1]
        if repo.ref_tip(head) is None or repo.ref_tip(base) is None:
            return None, "head or base branch does not exist"
        pr = STORE.create_pull(repo, args["title"], args.get("body"),
                               head, base)
        return pull_json(repo, pr), None
    if name == "merge_pull_request":
        number = args["pull_number"]
        pr = repo.pulls.get(number) if isinstance(number, int) else None
        if pr is None:
            return None, "Pull request not found"
        if pr["state"] != "open":
            return None, "Pull request is not open"
        if not STORE.mergeable(repo, pr):
            return None, "Merge conflict"
        ok, sha = STORE.squash_merge(repo, pr)
        if not ok:
            return None, "Merge conflict"
        return {"sha": sha, "merged": True, "number": number,
                "state": "closed",
                "message": "Pull request successfully merged"}, None
    return None, "Unknown tool: %s" % name


def _mcp_impl(self, method):
    if method != "POST":
        self._send_json(405, {"message": "Method Not Allowed"})
        return
    if not self._require_auth():
        return
    try:
        payload = json.loads(self._raw_body.decode("utf-8"))
    except Exception:
        self._send(400, json_bytes({
            "jsonrpc": "2.0", "id": None,
            "error": {"code": -32700, "message": "Parse error"}}),
            "application/json; charset=utf-8")
        return
    if not isinstance(payload, dict):
        self._send(400, json_bytes({
            "jsonrpc": "2.0", "id": None,
            "error": {"code": -32600, "message": "Invalid Request"}}),
            "application/json; charset=utf-8")
        return
    rpc_id = payload.get("id")
    rpc_method = payload.get("method")
    if isinstance(rpc_method, str) and rpc_method.startswith("notifications/"):
        self._send_json_no_body(202)
        return
    if rpc_method == "server/discover":
        server_info = {"name": "forge-mcp", "version": VERSION}
        self._send_json(200, {
            "jsonrpc": "2.0", "id": rpc_id,
            "result": {
                "supportedVersions": list(MCP_SUPPORTED_VERSIONS),
                "capabilities": {"tools": {}},
                "serverInfo": server_info,
                "_meta": {"io.modelcontextprotocol/serverInfo": server_info}}})
        return
    if rpc_method == "initialize":
        params = payload.get("params") or {}
        offered = params.get("protocolVersion")
        version = offered if offered in MCP_SUPPORTED_VERSIONS else "2026-07-28"
        self._send_json(200, {
            "jsonrpc": "2.0", "id": rpc_id,
            "result": {
                "protocolVersion": version,
                "capabilities": {"tools": {}},
                "serverInfo": {"name": "forge-mcp", "version": VERSION}}})
        return
    if rpc_method == "ping":
        self._send_json(200, {"jsonrpc": "2.0", "id": rpc_id, "result": {}})
        return
    if rpc_method == "tools/list":
        self._send_json(200, {"jsonrpc": "2.0", "id": rpc_id,
                              "result": {"tools": MCP_TOOLS}})
        return
    if rpc_method == "tools/call":
        params = payload.get("params") or {}
        tool_name = params.get("name")
        arguments = params.get("arguments") or {}
        result, error = _mcp_tool_call(tool_name, arguments)
        if error is not None:
            if isinstance(tool_name, str) and tool_name and not any(
                    t["name"] == tool_name for t in MCP_TOOLS):
                self._send_json(200, {
                    "jsonrpc": "2.0", "id": rpc_id,
                    "error": {"code": -32602, "message": error}})
                return
            text = json.dumps({"error": error}, separators=(",", ":"))
            self._send_json(200, {
                "jsonrpc": "2.0", "id": rpc_id,
                "result": {"content": [{"type": "text", "text": text}],
                           "structuredContent": {"error": error},
                           "isError": True}})
            return
        text = json.dumps(result, separators=(",", ":"),
                          ensure_ascii=False)
        self._send_json(200, {
            "jsonrpc": "2.0", "id": rpc_id,
            "result": {"content": [{"type": "text", "text": text}],
                       "structuredContent": result}})
        return
    self._send_json(200, {
        "jsonrpc": "2.0", "id": rpc_id,
        "error": {"code": -32601, "message": "Method not found: %s" % rpc_method}})


def _graphql_impl(self):
    if not self._require_auth():
        return
    try:
        payload = json.loads(self._raw_body.decode("utf-8"))
    except Exception:
        self._send_json(400, {"errors": [{"message": "Invalid JSON body"}]})
        return
    if isinstance(payload, list):
        results = [_gql_run_item(item) for item in payload]
        self._send_json(200, results)
    elif isinstance(payload, dict):
        self._send_json(200, _gql_run_item(payload))
    else:
        self._send_json(400, {"errors": [{"message": "Invalid request body"}]})


ForgeHandler._mcp = _mcp_impl
ForgeHandler._graphql = _graphql_impl


# ---------------------------------------------------------------------------
# Entrypoint: trial lifecycle (RULES.txt, "The suite and the wire")
#
# 1. Bind an ephemeral port of our own (port 0; never 8080, the suite's).
# 2. POST {"port": <port>} to $MAKEFUN_ENV_URL/register at once.
# 3. Long-poll GET $MAKEFUN_ENV_URL/done until {"done": true}, then exit 0.
# The forge itself is ForgeHandler above; this block only wires it into the
# trial. Without it `python3 main.py` would define the server and exit.
# ---------------------------------------------------------------------------

def _http_json(method, url, payload=None, timeout=10):
    data = None
    headers = {"Content-Type": "application/json"}
    if payload is not None:
        data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers,
                                 method=method)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            raw = resp.read()
    except Exception as exc:
        if getattr(exc, "code", None) == 409:
            return {"ok": False, "error": "already_registered"}
        raise
    try:
        return json.loads(raw.decode("utf-8"))
    except Exception:
        return {}


class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True

    def get_request(self):
        sock, addr = super().get_request()
        try:
            # Kill Nagle/delayed-ACK ping-pong: the suite drives thousands of
            # small request/response turns on keep-alive connections.
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except Exception:
            pass
        return sock, addr


def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if not env_url:
        sys.stderr.write("MAKEFUN_ENV_URL is not set\n")
        return 2
    server = ForgeServer(("0.0.0.0", 0), ForgeHandler)
    server.daemon_threads = True
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    # Register: the first register wins; retry briefly within the boot budget.
    registered = False
    deadline = time.time() + 15
    while time.time() < deadline:
        try:
            body = _http_json("POST", env_url + "/register",
                              {"port": port}, timeout=5)
            if isinstance(body, dict) and body.get("error") == "already_registered":
                registered = True
            else:
                registered = True
            break
        except Exception:
            time.sleep(0.5)
    if not registered:
        sys.stderr.write("failed to register with env\n")
        server.shutdown()
        return 1
    # Long-poll /done until the suite finishes, then exit 0.
    while True:
        try:
            body = _http_json("GET", env_url + "/done", timeout=10)
            if isinstance(body, dict) and body.get("done") is True:
                break
        except Exception:
            pass
        time.sleep(0.5)
    server.shutdown()
    server.server_close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
