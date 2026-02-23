/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor.Descent.CechDescentData.Comparison

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

theorem is_descent_morphism_iff_pseudofunctor_is_descent_morphism :
    IsDescentMorphism (pA := pA) p ↔
      Descent.Pseudofunctor.Descent.IsDescentMorphism (F := fibers_pseudofunctor (pA := pA)) p := by
  let e := single_cech_descent_data_equiv (pA := pA) p
  let G := Descent.Pseudofunctor.Descent.single_morphism_comparison_functor
    (F := fibers_pseudofunctor (pA := pA)) p
  let H := cech_to_single_functor (pA := pA) (p := p)
  haveI : H.Faithful := by
    simpa [H, e, single_cech_descent_data_equiv] using (show e.inverse.Faithful from inferInstance)
  refine ⟨fun ⟨hGH⟩ ↦ ?_, fun ⟨hG⟩ ↦ ?_⟩
  ·
    refine ⟨CategoryTheory.Functor.FullyFaithful.ofCompFaithful (F := G) (G := H) ?_⟩
    simpa [single_morphism_comparison_functor,
      Descent.Pseudofunctor.Descent.single_morphism_comparison_functor, G, H] using hGH
  ·
    refine ⟨?_⟩
    simpa [single_morphism_comparison_functor,
      Descent.Pseudofunctor.Descent.single_morphism_comparison_functor, G, H] using
      hG.comp (by
        simpa [H, e, single_cech_descent_data_equiv] using e.fullyFaithfulInverse)

theorem is_effective_descent_morphism_iff_pseudofunctor_is_effective_descent_morphism :
    IsEffectiveDescentMorphism (pA := pA) p ↔
      Descent.Pseudofunctor.Descent.IsEffectiveDescentMorphism (F := fibers_pseudofunctor (pA := pA)) p := by
  let e := single_cech_descent_data_equiv (pA := pA) p
  let G := Descent.Pseudofunctor.Descent.single_morphism_comparison_functor
    (F := fibers_pseudofunctor (pA := pA)) p
  let H := cech_to_single_functor (pA := pA) (p := p)
  haveI : H.IsEquivalence := by
    simpa [H, e, single_cech_descent_data_equiv] using (show e.inverse.IsEquivalence from inferInstance)
  refine ⟨fun hGH ↦ ?_, fun hG ↦ ?_⟩
  ·
    have : (G ⋙ H).IsEquivalence := by
      simpa [single_morphism_comparison_functor,
        Descent.Pseudofunctor.Descent.single_morphism_comparison_functor, G, H] using hGH
    haveI : (G ⋙ H).IsEquivalence := this
    exact CategoryTheory.Functor.isEquivalence_of_comp_right G H
  ·
    haveI : G.IsEquivalence := hG
    have : (G ⋙ H).IsEquivalence := by infer_instance
    simpa [single_morphism_comparison_functor,
      Descent.Pseudofunctor.Descent.single_morphism_comparison_functor, G, H] using this

theorem is_prestack_for_singleton_iff_descent_morphism :
    CategoryTheory.Pseudofunctor.IsPrestackFor (F := fibers_pseudofunctor (pA := pA))
      (S := B) (CategoryTheory.Presieve.singleton p) ↔
        IsDescentMorphism (pA := pA) p := by
  let h₁ := is_descent_morphism_iff_pseudofunctor_is_descent_morphism (pA := pA) (p := p)
  let h₂ := Descent.Pseudofunctor.Descent.is_prestack_for_singleton_iff_descent_morphism
    (F := fibers_pseudofunctor (pA := pA)) (p := p)
  exact h₂.trans h₁.symm

theorem is_stack_for_singleton_iff_effective_descent_morphism :
    CategoryTheory.Pseudofunctor.IsStackFor (F := fibers_pseudofunctor (pA := pA))
      (S := B) (CategoryTheory.Presieve.singleton p) ↔
        IsEffectiveDescentMorphism (pA := pA) p := by
  let h₁ := is_effective_descent_morphism_iff_pseudofunctor_is_effective_descent_morphism
    (pA := pA) (p := p)
  let h₂ := Descent.Pseudofunctor.Descent.is_stack_for_singleton_iff_effective_descent_morphism
    (F := fibers_pseudofunctor (pA := pA)) (p := p)
  exact h₂.trans h₁.symm

end HasPullbacks

end

end Descent.FiberedCategory.Descent
