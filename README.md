# Descent Theory in Lean 4

[![CI](https://github.com/eliasjudin/descent-theory/actions/workflows/ci.yml/badge.svg)](https://github.com/eliasjudin/descent-theory/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

This project formalizes Čech-style descent along a single morphism `p : E ⟶ B` in a category
with pullbacks.

## Mathematical content

The library develops two equivalent formulations of single-morphism descent:

- fibered categories (`pA : 𝒜 ⥤ C` with `pA.IsFibered`)
- pseudofunctors (`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`)

Using Čech overlaps (`E ×_B E` and `E ×_B E ×_B E`), it defines descent data and the comparison
functor `Φₚ` from objects over `B` to descent data over `p`.

It then defines:

- `IsDescentMorphism`: `Φₚ` is fully faithful
- `IsEffectiveDescentMorphism`: `Φₚ` is an equivalence

Main bridges proved in the repository:

- equivalence between the fibered-category and pseudofunctor descent-data viewpoints
- equivalence between the Čech single-morphism pseudofunctor formulation and Mathlib's
  singleton-family descent data (`CategoryTheory.Pseudofunctor.DescentData`)
- equivalences with Mathlib's `IsPrestackFor` and `IsStackFor` for `Presieve.singleton p`

## Use

For downstream use, import:

```lean
import Descent.API
```

Core and full aggregators:

- `Descent`: core single-morphism API
- `Descent.API`: canonical public API (core + bridge/equivalence modules)
- `Descent.All`: full-project aggregator used in CI

## Build

```bash
lake build
lake lint
lake test
```

Toolchain: `leanprover/lean4:v4.27.0-rc1`.

## License

Apache 2.0 (`LICENSE`).
