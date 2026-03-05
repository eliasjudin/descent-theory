# Mathlib Integration Notes

This document tracks how this repository is prepared for incremental upstreaming into `mathlib4`.

## Current integration posture

- Public-facing APIs live under `Descent.*` namespaces for release stability in this repository.
- `Descent.lean` is the user-facing umbrella, with topic-level imports under `Descent.*`.
  Avoid repository-wide `API` or `All` aggregators in favor of root/topic modules.
- Upstream-candidate core category-theory modules are isolated under `Descent/CategoryTheory/*`.
- CI enforces warning hygiene, lint, style, regression builds, and full-module coverage
  through `lake build`, `lake build Descent`, and `lake test`.
- Regression examples are being kept import-lean (`Descent/Examples/BridgeSanity.lean`,
  `Descent/Examples/SingletonEquiv.lean`) by targeting focused
  `Descent/Pseudofunctor/Descent/CechDescentData/*` modules where possible, while the regression
  driver itself lives in `DescentTestDriver.lean` and imports those example modules directly
  rather than adding another repository-wide umbrella under or alongside `Descent.*`.

## Upstream-candidate modules

- `Descent/CategoryTheory/FiberedCategory/Reindexing/Basic.lean`
- `Descent/CategoryTheory/FiberedCategory/Reindexing/Iso.lean`
- `Descent/CategoryTheory/FiberedCategory/Reindexing.lean` (stable repository umbrella)
- `Descent/CategoryTheory/FiberedCategory/PseudofunctorOfFibers.lean`
- `Descent/CategoryTheory/InternalCategory/Basic.lean`
- `Descent/CategoryTheory/Sites/Descent/SingleMorphism.lean`

## Downstream bridge modules (repository-specific)

These are valuable for the library but likely not first-wave upstream targets:

- `Descent/FiberedCategory/Descent/PseudofunctorEquiv.lean`
- `Descent/FiberedCategory/Descent/SingleMorphismComparison.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData.lean`
- `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean`

`CechDescentDataEquiv` is retained as a compatibility aggregator.

Current split for pseudofunctor single-morphism descent:

- `Descent/Pseudofunctor/Descent/CechDescentData/Conversions/SingleToSingleton.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData/Conversions/SingletonToSingle.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData/Conversions/Hom.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData/Conversions.lean` (stable repository umbrella)
- `Descent/Pseudofunctor/Descent/CechDescentData/Functors.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData/Equiv.lean`
- `Descent/Pseudofunctor/Descent/CechDescentData/Comparison.lean`

Prefer deep imports from the focused files above in internal modules, while keeping downstream
code on the root/topic umbrellas.

## Upstream checklist per module

1. Minimize imports.
2. Normalize naming to mathlib conventions.
3. Remove repository-only wrappers where possible.
4. Ensure `lake build`/`lake lint`/`lake exe lint-style` pass on the extracted module set.
5. Provide focused examples/tests showing intended API use.

## Recommended local verification

```bash
lake build
lake build Descent
lake lint
lake exe lint-style Descent
lake test
```
