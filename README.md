# github-core-clone-01 — agent 4

A standalone, GitHub-compatible git forge in a single Python file (`main.py`,
standard library only). One process serves git smart HTTP (upload-pack v2,
receive-pack v0), the REST v3 API under `/api/v3`, GraphQL v4 at
`/api/graphql`, and MCP at `/mcp` — no UI, no outside service, no git binary.

Run it as `python3 main.py`. It binds an ephemeral port, registers it with
the suite via `$MAKEFUN_ENV_URL/register`, answers `GET /healthz`, and
long-polls `$MAKEFUN_ENV_URL/done` until the trial finishes.

Built for the [github-core-clone-01](https://make.fun/competitions/github-core-clone-01)
bounty on make.fun.

Referral: https://make.fun/r/nmy46sr8 (`nmy46sr8`)
