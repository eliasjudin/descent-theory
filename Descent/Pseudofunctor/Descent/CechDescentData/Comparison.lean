/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData.Equiv

/-!
# Descent criteria for a single morphism

Comparison functor and singleton-cover descent criteria.
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

open Opposite
open Descent.Cech
open Descent.Pseudofunctor
open CategoryTheory.Pseudofunctor

universe v' v u' u

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

variable {E B : C} (p : E ⟶ B)
/-- Comparison functor landing in `CechDescentData`. -/
noncomputable def single_morphism_comparison_functor :
    F.obj (.mk (op B)) ⥤ CechDescentData (F := F) p :=
  (CategoryTheory.Pseudofunctor.single_morphism_comparison_functor (F := F) p) ⋙
    singleton_to_single_functor (F := F) p

/-- `p` is a descent morphism for `F` when the comparison functor is fully faithful. -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (single_morphism_comparison_functor (F := F) p).FullyFaithful

/-- `p` is an effective descent morphism for `F` when the comparison functor is an equivalence. -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (single_morphism_comparison_functor (F := F) p).IsEquivalence

/-!
## Relation with Mathlib's `IsPrestackFor`/`IsStackFor` for `Presieve.singleton p`
-/

theorem is_descent_morphism_iff_to_descent_data_fully_faithful :
    IsDescentMorphism (F := F) p ↔
      Nonempty (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).FullyFaithful := by
  let e := single_singleton_descent_data_equiv (F := F) p
  let G := CategoryTheory.Pseudofunctor.single_morphism_comparison_functor (F := F) p
  let H := singleton_to_single_functor (F := F) p
  haveI : H.Faithful := by
    simpa [H, e, single_singleton_descent_data_equiv] using (show e.inverse.Faithful from inferInstance)
  refine ⟨fun ⟨hGH⟩ ↦ ?_, fun ⟨hG⟩ ↦ ?_⟩
  ·
    refine ⟨CategoryTheory.Functor.FullyFaithful.ofCompFaithful (F := G) (G := H) ?_⟩
    simpa [single_morphism_comparison_functor,
      CategoryTheory.Pseudofunctor.single_morphism_comparison_functor, G, H] using hGH
  ·
    refine ⟨?_⟩
    simpa [single_morphism_comparison_functor,
      CategoryTheory.Pseudofunctor.single_morphism_comparison_functor, G, H] using
      hG.comp (by
        simpa [H, e, single_singleton_descent_data_equiv] using e.fullyFaithfulInverse)

theorem is_effective_descent_morphism_iff_to_descent_data_equivalence :
    IsEffectiveDescentMorphism (F := F) p ↔
      (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).IsEquivalence := by
  let e := single_singleton_descent_data_equiv (F := F) p
  let G := CategoryTheory.Pseudofunctor.single_morphism_comparison_functor (F := F) p
  let H := singleton_to_single_functor (F := F) p
  haveI : H.IsEquivalence := by
    simpa [H, e, single_singleton_descent_data_equiv] using (show e.inverse.IsEquivalence from inferInstance)
  refine ⟨fun hGH ↦ ?_, fun hG ↦ ?_⟩
  ·
    have : (G ⋙ H).IsEquivalence := by
      simpa [single_morphism_comparison_functor,
        CategoryTheory.Pseudofunctor.single_morphism_comparison_functor, G, H] using hGH
    haveI : (G ⋙ H).IsEquivalence := this
    exact CategoryTheory.Functor.isEquivalence_of_comp_right G H
  ·
    haveI : G.IsEquivalence := hG
    have : (G ⋙ H).IsEquivalence := by infer_instance
    simpa [single_morphism_comparison_functor,
      CategoryTheory.Pseudofunctor.single_morphism_comparison_functor, G, H] using this

theorem is_prestack_for_singleton_iff_descent_morphism :
    CategoryTheory.Pseudofunctor.IsPrestackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
      IsDescentMorphism (F := F) p := by
  have hPresieve :
      CategoryTheory.Presieve.ofArrows (fun _ : PUnit.{1} ↦ E) (fun _ : PUnit.{1} ↦ p) =
        CategoryTheory.Presieve.singleton p := by
    simpa using (CategoryTheory.Presieve.ofArrows_pUnit (f := p))
  have h :
      CategoryTheory.Pseudofunctor.IsPrestackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
        Nonempty (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).FullyFaithful := by
    simpa [hPresieve] using
      (CategoryTheory.Pseudofunctor.isPrestackFor_ofArrows_iff (F := F) (S := B)
        (f := fun _ : PUnit.{1} ↦ p))
  let hd := is_descent_morphism_iff_to_descent_data_fully_faithful (F := F) p
  refine ⟨fun hstack ↦ ?_, fun hdesc ↦ ?_⟩
  · exact hd.2 (h.1 hstack)
  · exact h.2 (hd.1 hdesc)

theorem is_stack_for_singleton_iff_effective_descent_morphism :
    CategoryTheory.Pseudofunctor.IsStackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
      IsEffectiveDescentMorphism (F := F) p := by
  have hPresieve :
      CategoryTheory.Presieve.ofArrows (fun _ : PUnit.{1} ↦ E) (fun _ : PUnit.{1} ↦ p) =
        CategoryTheory.Presieve.singleton p := by
    simpa using (CategoryTheory.Presieve.ofArrows_pUnit (f := p))
  have h :
      CategoryTheory.Pseudofunctor.IsStackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
        (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).IsEquivalence := by
    simpa [hPresieve] using
      (CategoryTheory.Pseudofunctor.isStackFor_ofArrows_iff (F := F) (S := B)
        (f := fun _ : PUnit.{1} ↦ p))
  let he := is_effective_descent_morphism_iff_to_descent_data_equivalence (F := F) p
  refine ⟨fun hstack ↦ ?_, fun hdesc ↦ ?_⟩
  · exact he.2 (h.1 hstack)
  · exact h.2 (he.1 hdesc)

end

end Descent.Pseudofunctor.Descent
