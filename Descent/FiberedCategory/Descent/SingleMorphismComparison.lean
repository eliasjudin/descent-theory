/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor.Descent.CechDescentDataEquiv

/-!
# The comparison functor for fibered-category descent data

Let `pA : 𝒜 ⥤ C` be a fibered functor and `p : E ⟶ B` a morphism in the base category.

This file defines the comparison functor
`Φₚ : Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p`
by composing the pseudofunctor-level comparison functor with the established equivalence between
pseudofunctor Čech descent data and fibered-category descent data.

We also introduce the standard predicates `IsDescentMorphism` and `IsEffectiveDescentMorphism`,
defined in terms of this functor.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.FiberedCategory.Descent

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜]

noncomputable section

open Descent.FiberedCategory

variable (pA : 𝒜 ⥤ C) [pA.IsFibered]

section HasPullbacks

variable [Limits.HasPullbacks C]

variable {E B : C} (p : E ⟶ B)

/-- The comparison functor `Φₚ : Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p`. -/
noncomputable def single_morphism_comparison_functor :
    Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p := by
  exact
    show Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p from
      (Descent.Pseudofunctor.Descent.single_morphism_comparison_functor
        (F := fibers_pseudofunctor (pA := pA)) p) ⋙
      (cech_to_single_functor (pA := pA) (p := p))

/-- The canonical descent datum on `p^* a`, obtained from `Φₚ`. -/
noncomputable def single_morphism_comparison_descent_data (a : Fiber pA B) :
    SingleMorphismDescentData (pA := pA) p :=
  (single_morphism_comparison_functor (pA := pA) p).obj a

/-- `p` is a descent morphism for `pA` if `Φₚ` is fully faithful. -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (single_morphism_comparison_functor (pA := pA) p).FullyFaithful

/-- `p` is an effective descent morphism for `pA` if `Φₚ` is an equivalence. -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (single_morphism_comparison_functor (pA := pA) p).IsEquivalence

end HasPullbacks

end

end Descent.FiberedCategory.Descent
