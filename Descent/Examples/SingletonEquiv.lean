/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentDataEquiv

/-!
# Examples: singleton-cover equivalence

This file exercises the equivalence between Čech-style descent data along `p : E ⟶ B` and
Mathlib's singleton-family descent data.
-/

open CategoryTheory

namespace Descent.Examples

universe u v u' v'

section

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable (F : CategoryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {E B : C} (p : E ⟶ B)

open Descent.Pseudofunctor.Descent

noncomputable example :
    Descent.Pseudofunctor.Descent.CechDescentData (F := F) p ≌
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := fun _ : PUnit.{1} => p) :=
  Descent.Pseudofunctor.Descent.singleSingletonDescentDataEquiv (F := F) p

/-!
## Direction sanity checks

These are lightweight checks that pin down the direction conventions used in the singleton-family
comparison: our Čech gluing morphism is `π₂^* ⟶ π₁^*`, while Mathlib’s `DescentData.hom` uses the
opposite direction; the equivalence compensates for this via `inv`/`symm`.
-/

example (D : CechDescentData (F := F) p) :
    (singleToSingletonDescentData (F := F) p D).obj PUnit.unit = D.obj :=
  rfl

example (D : CechDescentData (F := F) p) :
    D.ξ =
      ((singleToSingletonFunctor (F := F) p ⋙ singletonToSingleFunctor (F := F) p).obj D).ξ := by
  -- The unit isomorphism has underlying morphism `𝟙`, so `comm` reduces to equality of `ξ`.
  simpa [singleSingletonUnit] using (singleSingletonUnit (F := F) p D).hom.comm

end

end Descent.Examples
