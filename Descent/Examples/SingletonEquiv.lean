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

noncomputable example :
    Descent.Pseudofunctor.Descent.CechDescentData (F := F) p ≌
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := fun _ : PUnit.{1} => p) :=
  Descent.Pseudofunctor.Descent.singleSingletonDescentDataEquiv (F := F) p

end

end Descent.Examples

