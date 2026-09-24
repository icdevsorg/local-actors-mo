# Changelog

## 0.1.0 — 2026-09-24

First registry release. `Actor.id`, `Actor.container`, `Actor.address`, `Actor.fromAddress`
for moxzi `actor*` instances. Declares `[moxzi] version = ">=0.1.0-alpha.6"` and
`features = ["local-actors"]`, so a consumer's `moxzi build` adds
`--experimental-local-actors` itself. Requires moxzi; `moc` cannot compile `actor*`.
