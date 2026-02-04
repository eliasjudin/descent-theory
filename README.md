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

This library is under active development: APIs and file organization may change.

If you are looking for the main entry point, start with `Descent.lean` and then
follow imports into `Descent/`.

## Project layout

- `Descent/Cech.lean`: Čech kernel pair and triple-overlap conventions.
- `Descent/FiberedCategory/`: reindexing on fibers and single-morphism descent data.
- `Descent/FiberedCategory/Descent/PseudofunctorEquiv.lean`: bridge between fibered-category
  descent data and pseudofunctor Čech descent data for the pseudofunctor of fibers.
- `Descent/Pseudofunctor/`: reindexing for pseudofunctors and single-morphism descent data.
- `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean`: comparison with Mathlib’s
  singleton-cover descent data.

## Related references

- Stacks Project (algebraic geometry): https://stacks.math.columbia.edu/
- Lean “Stacks project” effort (informal): https://github.com/Paul-Lez/Stacks-project

## License

Apache 2.0. See `LICENSE`.
