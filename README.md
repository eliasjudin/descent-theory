# Descent theory in Lean 4

[![CI](https://github.com/eliasjudin/descent-theory/actions/workflows/ci.yml/badge.svg)](https://github.com/eliasjudin/descent-theory/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

A Lean 4/Mathlib library formalizing **Čech-style descent theory along a single morphism**
`p : E ⟶ B` in a base category with pullbacks.

The development uses the Čech overlaps `E ×_B E` and `E ×_B E ×_B E`, together with a
unit condition (along the diagonal) and a cocycle condition (on triple overlaps).

Two equivalent viewpoints are developed in parallel:

- **Fibered categories** (`pA : 𝒜 ⥤ C` with `pA.IsFibered`)
- **Pseudofunctors** (`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`)

In addition, the project relates the single-morphism formulation to Mathlib’s
`CategoryTheory.Pseudofunctor.DescentData` for the **singleton cover**.

## Status

This repository is now structured for public collaboration:

- CI enforces `lake build`, `lake build Descent.All`, `lake lint`, `lake exe lint-style Descent`,
  and `lake test`.
- Warning hygiene is gated, with an explicit `SORRY_TRACKER.md` allowlist policy.
- Descent APIs are exposed through stable entry points (`Descent.API`, `Descent.lean`,
  `Descent/FiberedCategory.lean`, `Descent/Pseudofunctor.lean`).
- Full project compilation coverage is exposed via `Descent.All`.

For most downstream users, import `Descent.API`.
Use `Descent.lean` when you want only the core single-morphism API without compatibility aggregators.

## Local quality loop

Use the same commands locally that CI enforces:

```bash
lake build
lake build Descent.All
lake lint
lake exe lint-style Descent
lake test
```

`lake lint` and `lake test` are wired through dedicated Lake drivers that import
`Descent.Lint` and `Descent.Test`.

## Conventions

- Prefer specific imports over broad imports.
- For broad downstream use, prefer `Descent.API`.
- For pseudofunctor Čech descent, prefer focused imports under
  `Descent/Pseudofunctor/Descent/CechDescentData/*`; use
  `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean` only for broad compatibility imports.
- Keep module headers and module-level docstrings in every Lean file.
- Keep warning output clean; only tracked temporary `sorry`s are allowed by CI.
- Treat edits touching `[simp]` attributes, instances, syntax/macros, priorities,
  or global options (`set_option`) as high-risk and run the full quality loop.

## Contribution workflow

- Start with `CONTRIBUTING.md` for local setup and PR checklist.
- For upstream strategy and mathlib-facing naming/module notes, see `MATHLIB_INTEGRATION.md`.
- Keep `CHANGELOG.md` updated under the `Unreleased` section for user-visible changes.

## Project layout

- `Descent/API.lean`: canonical consumer-facing API aggregator.
- `Descent/All.lean`: full-project import aggregator used by CI for maintained-module coverage.
- `Descent/Cech.lean`: Čech kernel pair and triple-overlap conventions.
- `Descent/FiberedCategory/`: reindexing on fibers and single-morphism descent data.
- `Descent/FiberedCategory/Descent/PseudofunctorEquiv.lean`: bridge between fibered-category
  descent data and pseudofunctor Čech descent data for the pseudofunctor of fibers.
- `Descent/FiberedCategory/Descent/SingleMorphismComparison.lean`: fibered comparison functor and
  singleton-criteria bridge theorems.
- `Descent/Pseudofunctor/`: reindexing for pseudofunctors and single-morphism descent data.
- `Descent/Pseudofunctor/Descent/CechDescentData/Conversions.lean`: single↔singleton data
  conversions and morphism transport.
- `Descent/Pseudofunctor/Descent/CechDescentData/Functors.lean`: conversion functors.
- `Descent/Pseudofunctor/Descent/CechDescentData/Equiv.lean`: singleton equivalence.
- `Descent/Pseudofunctor/Descent/CechDescentData/Comparison.lean`: single-morphism comparison
  functor and descent/effective-descent criteria.
- `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean`: compatibility aggregator.
- `Descent/Examples/BridgeSanity.lean` and `Descent/Examples/SingletonEquiv.lean`: regression
  checks.

## Related references

- Stacks Project (algebraic geometry): https://stacks.math.columbia.edu/
- Lean “Stacks project” effort (informal): https://github.com/Paul-Lez/Stacks-project

## License

Apache 2.0. See `LICENSE`.
