# Mathlib Integration Notes

This document tracks how this repository is prepared for incremental upstreaming into `mathlib4`.

## Current integration posture

- Public-facing APIs live under `Descent.*` namespaces for release stability in this repository.
- Upstream-candidate core category-theory modules are isolated under `Descent/CategoryTheory/*`.
- CI enforces warning hygiene, lint, style, regression builds, and full-module coverage
  through `lake build Descent.All`.

## Upstream-candidate modules

- `Descent/CategoryTheory/FiberedCategory/Reindexing.lean`
- `Descent/CategoryTheory/FiberedCategory/PseudofunctorOfFibers.lean`
- `Descent/CategoryTheory/InternalCategory/Basic.lean`
- `Descent/CategoryTheory/Sites/Descent/SingleMorphism.lean`

## Downstream bridge modules (repository-specific)

These are valuable for the library but likely not first-wave upstream targets:

- `Descent/FiberedCategory/Descent/PseudofunctorEquiv.lean`
- `Descent/FiberedCategory/Descent/SingleMorphismComparison.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData.lean`
- `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean`

## Upstream checklist per module

1. Minimize imports.
2. Normalize naming to mathlib conventions.
3. Remove repository-only wrappers where possible.
4. Ensure `lake build`/`lake lint`/`lake exe lint-style` pass on the extracted module set.
5. Provide focused examples/tests showing intended API use.

## Recommended local verification

```bash
lake build
lake build Descent.All
lake lint
lake exe lint-style Descent
lake test
```
