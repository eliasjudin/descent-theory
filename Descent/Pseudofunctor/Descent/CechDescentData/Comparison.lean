/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData.Equiv

/-!
# Descent criteria for a single morphism

This file packages the comparison functor and descent/effective-descent criteria,
including the singleton-cover prestack/stack equivalences.
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
/-- The comparison functor `Φₚ : F(B) ⥤ Des_F(p)` from the paper (Facets of Descent II, §3.2),
landing in the Čech-style descent data defined in `CechDescentData.lean`.

It is defined as `CategoryTheory.Pseudofunctor.single_morphism_comparison_functor` for the
singleton family, followed by the (inverse) functor
from Mathlib's descent data to our Čech-style descent data. -/
noncomputable def single_morphism_comparison_functor :
    F.obj (.mk (op B)) ⥤ CechDescentData (F := F) p :=
  (CategoryTheory.Pseudofunctor.single_morphism_comparison_functor (F := F) p) ⋙
    singleton_to_single_functor (F := F) p

/-- `p` is a descent morphism for `F` if the comparison functor `Φₚ` is fully faithful
(Facets of Descent II, §3.2). -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (single_morphism_comparison_functor (F := F) p).FullyFaithful

/-- `p` is an effective descent morphism for `F` if the comparison functor `Φₚ` is an equivalence
of categories (Facets of Descent II, §3.2). -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (single_morphism_comparison_functor (F := F) p).IsEquivalence

/-!
## Relation with Mathlib's `IsPrestackFor`/`IsStackFor` for `Presieve.singleton p`

Mathlib’s descent theory is formulated for arbitrary presieves `R` via the functor
`F.toDescentData (fun (f : R.category) ↦ f.obj.hom)`. In the singleton case, the presieve
`Presieve.singleton p` is (definitionally) the same as `Presieve.ofArrows _ (fun _ : PUnit.{1} ↦ p)`,
see `CategoryTheory.Presieve.ofArrows_pUnit`.

The functor `single_morphism_comparison_functor` differs from
`CategoryTheory.Pseudofunctor.single_morphism_comparison_functor` only by postcomposition with the
(inverse) equivalence `singleton_to_single_functor`, so it has the same “fully faithful” and “is
equivalence” properties.
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
