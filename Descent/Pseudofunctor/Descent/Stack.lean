/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Stacks: effectiveness of descent data

We define a notion of stack for pseudofunctors
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, as the combination of the prestack
condition (descent for morphisms) and essential surjectivity of the
comparison functor `toDescentData` for covering families.
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

universe v' v u' u

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- A pseudofunctor is a stack if descent data are effective for every covering family. -/
class IsStack (J : GrothendieckTopology C) : Prop extends Pseudofunctor.IsPrestack (F := F) J where
  essSurj {ι : Type*} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
      (hf : Sieve.ofArrows X f ∈ J S) :
      Functor.EssSurj (Pseudofunctor.toDescentData (F := F) (f := f))

end Descent.Pseudofunctor.Descent
