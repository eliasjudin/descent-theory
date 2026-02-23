/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData.Equiv

/-!
# Examples: singleton-cover equivalence

Regression checks for the singleton-cover equivalence.
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
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := fun _ : PUnit.{1} ↦ p) :=
  Descent.Pseudofunctor.Descent.single_singleton_descent_data_equiv (F := F) p

/-!
## Direction sanity checks

Checks for the direction conventions used by the conversion/equivalence.
-/

example (D : CechDescentData (F := F) p) :
    (single_to_singleton_descent_data (F := F) p D).obj PUnit.unit = D.obj :=
  rfl

example (D : CechDescentData (F := F) p) :
    D.ξ =
      ((single_to_singleton_functor (F := F) p ⋙ singleton_to_single_functor (F := F) p).obj D).ξ := by
  simpa [single_singleton_unit] using (single_singleton_unit (F := F) p D).hom.comm

end

end Descent.Examples
