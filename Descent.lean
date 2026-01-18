/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.Cech.Eq

import Descent.FiberedCategory.Reindexing
import Descent.FiberedCategory.Descent.SingleMorphism

import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Descent.CategoryTheory.Sites.Descent.SingleMorphism
import Descent.Pseudofunctor.Reindexing
import Descent.Pseudofunctor.Descent.CechDescentData

/-!
# Descent theory

This is the main entry point for the `Descent` library.

The library develops Čech-style descent along a single morphism `p : E ⟶ B`, both for
fibered categories (`pA : 𝒜 ⥤ C` with `pA.IsFibered`) and for pseudofunctors
(`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`).

To relate the Čech-style pseudofunctor descent data to Mathlib's
`CategoryTheory.Pseudofunctor.DescentData` for a singleton family, import
`Descent.Pseudofunctor.Descent.CechDescentDataEquiv`.
-/
