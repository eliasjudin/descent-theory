# Contributing to `descent-theory`

## Prerequisites

- Lean toolchain from `lean-toolchain`
- Lake (`lake --version`)
- Mathlib cache (recommended): `lake exe cache get`

## Local development loop

Run the same checks as CI before opening a PR:

```bash
lake build
lake build Descent.All
lake lint
lake exe lint-style Descent
lake test
```

## High-risk Lean edits

Treat these as high-risk and run the full loop above:

- `[simp]` attribute changes
- new/modified typeclass instances
- syntax/macros/elaborators
- priority changes
- `set_option` changes

CI also runs targeted builds when high-risk patterns are detected by `scripts/ci_high_risk_gate.sh`.

## `sorry` policy

- Do not introduce `sorry` in normal contributions.
- If a temporary `sorry` is unavoidable, add an explicit entry to `SORRY_TRACKER.md`.
- CI enforces an exact match between `SORRY_TRACKER.md` and warnings in build logs.

## Style and structure

- Keep imports as narrow as practical.
- Include module docstrings and declaration docstrings for nontrivial API.
- Prefer stable entry points (`Descent.lean`, `Descent/FiberedCategory.lean`, `Descent/Pseudofunctor.lean`)
  over deep module imports in downstream code.

## Pull request checklist

- [ ] Scope is minimal and coherent.
- [ ] Full local loop passes.
- [ ] New/changed declarations have docs when needed.
- [ ] `CHANGELOG.md` updated for user-visible changes.
- [ ] Any temporary `sorry` accounted for in `SORRY_TRACKER.md` (preferably none).
