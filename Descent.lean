/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.FiberedCategory
import Descent.Pseudofunctor

/-!
# Descent theory

This is the main entry point for the `Descent` library.

The library develops Čech-style descent along a single morphism `p : E ⟶ B`, both for
fibered categories (`pA : 𝒜 ⥤ C` with `pA.IsFibered`) and for pseudofunctors
(`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`).

For the Čech groupoid `Eq(p)`, import `Descent.Cech.Eq`.

To relate the Čech-style pseudofunctor descent data to Mathlib's
`CategoryTheory.Pseudofunctor.DescentData` for a singleton family, import
`Descent.Pseudofunctor.Descent.CechDescentDataEquiv`.
-/
