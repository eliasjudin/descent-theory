# AGENTS.md

## Cursor Cloud specific instructions

This is a **Lean 4** mathematical proof library (descent theory). There is no web server, database, or runtime service — "running" the application means building and type-checking the proofs.

### Toolchain

The project uses **elan** (Lean's version manager, installed at `~/.elan/bin`). The exact Lean/Lake version is pinned in `lean-toolchain` (currently `leanprover/lean4:v4.27.0-rc1`). Elan resolves it automatically.

### Development loop

See `CONTRIBUTING.md` for the full CI-equivalent local loop. In short:

```bash
lake exe cache get   # fetch pre-built mathlib oleans (minutes vs hours)
lake build           # build the Descent library
lake build Descent.All  # build full project aggregator
lake lint            # run Lean linters
lake exe lint-style Descent  # run style linter
lake test            # run test driver
```

### Caveats

- **Always run `lake exe cache get` after a fresh clone or after mathlib dependency changes.** Without the cache, building mathlib from source can take several hours.
- `lake lint` is the slowest check (~3 min) because it runs multiple Lean linters across all declarations.
- `lake exe lint-style Descent` has no visible output on success — exit code 0 means pass.
- `lake test` similarly produces no test-framework output; the test driver compiles and exits 0 on success.
- The `scripts/` directory contains CI gate scripts (`ci_high_risk_gate.sh`, `ci_warning_gate.sh`) used in GitHub Actions; they are not needed for local development.
