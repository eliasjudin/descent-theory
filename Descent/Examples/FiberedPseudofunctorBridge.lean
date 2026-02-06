/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.PseudofunctorEquiv

/-!
# Examples: fibered categories vs. pseudofunctors

This file exercises the bridge between fibered-category descent data and pseudofunctor Čech
descent data for the pseudofunctor of fibers.
-/

open CategoryTheory

namespace Descent.Examples

universe u v w

section

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {𝒜 : Type w} [Category.{v} 𝒜]
variable (pA : 𝒜 ⥤ C) [pA.IsFibered]
variable {E B : C} (p : E ⟶ B)

noncomputable example :
    Descent.FiberedCategory.Descent.SingleMorphismDescentData (pA := pA) p ≌
      Descent.Pseudofunctor.Descent.CechDescentData
        (F := Descent.FiberedCategory.Descent.fibers_pseudofunctor (pA := pA)) p :=
  Descent.FiberedCategory.Descent.single_cech_descent_data_equiv (pA := pA) p

end

end Descent.Examples
