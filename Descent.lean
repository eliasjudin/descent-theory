/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin

# Descent Theory Library

This library provides a formalization of descent theory for both fibered categories
and pseudofunctors in Lean 4 / Mathlib4.

## Structure

The library is organized into two main branches:

### Fibered Categories (`Descent.FiberedCategory`)
Descent theory for Grothendieck fibrations using mathlib's `IsFibered` class.

- `Descent.FiberedCategory.Reindexing`: Reindexing functors with coherence isomorphisms
- `Descent.FiberedCategory.Descent.SingleMorphism`: Descent data for single morphisms

### Pseudofunctors (`Descent.Pseudofunctor`)
Descent theory for pseudofunctors `F : Cᵒᵖ ⥤ᵖ Cat`.

- `Descent.Pseudofunctor.Reindexing`: Reindexing for pseudofunctors
- `Descent.Pseudofunctor.Descent.SingleMorphism`: Descent data for single morphisms
- `Descent.Pseudofunctor.Descent.SingleMorphismEquiv`: Equivalence with mathlib's DescentData
- `Descent.Pseudofunctor.Descent.Prestack`: Full faithfulness theorem for prestacks
- `Descent.Pseudofunctor.Descent.Stack`: Stack condition definition

### Shared Foundations (`Descent`)
- `Descent.Cech`: Čech kernel pair definitions and lemmas

## Mathematical Background

This library formalizes classical descent theory from algebraic geometry:

- **Čech descent** using kernel pairs rather than internal categories
- **Cocycle conditions** formulated as groupoid composition laws
- **Prestack condition**: The comparison functor is fully faithful
- **Stack condition**: The comparison functor is an equivalence

## References

- [Janelidze, Tholen, "Facets of Descent II"]
- [Vistoli, "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory"]
- [Stacks Project](https://stacks.math.columbia.edu)
- [SGA1, Exposé VI]
-/

-- Basic / shared definitions
import Descent.Cech

-- Fibered category approach
import Descent.FiberedCategory.Reindexing
import Descent.FiberedCategory.Descent.SingleMorphism

-- Pseudofunctor approach
import Descent.Pseudofunctor.Reindexing
import Descent.Pseudofunctor.Descent.SingleMorphism
import Descent.Pseudofunctor.Descent.SingleMorphismEquiv
import Descent.Pseudofunctor.Descent.Prestack
import Descent.Pseudofunctor.Descent.Stack
