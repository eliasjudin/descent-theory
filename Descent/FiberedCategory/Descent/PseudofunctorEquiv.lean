/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.SingleMorphism
import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.CategoryTheory.FiberedCategory.PseudofunctorOfFibers

/-!
# Relating fibered-category and pseudofunctor descent data

Let `pA : 𝒜 ⥤ C` be a fibered functor. The associated pseudofunctor of fibers
`CategoryTheory.FiberedCategory.pseudofunctor_of_fibers (pA := pA)` sends `S : C` to the fiber
category `Fiber pA S` and a morphism `f : R ⟶ S` to the reindexing functor `f^*`.

This repository contains two Čech-style descent data notions along a single morphism `p : E ⟶ B`:

* `Descent.FiberedCategory.Descent.SingleMorphismDescentData (pA := pA) p` for fibered categories,
  where the gluing map is stored as an isomorphism.
* `Descent.Pseudofunctor.Descent.CechDescentData (F := F) p` for pseudofunctors
  `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, where the gluing map is stored as a morphism.

In the case `F = pseudofunctor_of_fibers pA`, these two categories should be equivalent. This file
provides the comparison functors and the resulting equivalence.

The conversions `single_to_cech_descent_data` and `cech_to_single_descent_data`, together with the
equivalence packaging (`unitIso`, `counitIso`, and the triangle identity), are implemented here.
Any remaining placeholders in this bridge are inherited only from upstream cleavage-coherence
placeholders for `pseudofunctor_of_fibers`.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.FiberedCategory.Descent

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜]

noncomputable section

open Opposite

variable (pA : 𝒜 ⥤ C) [pA.IsFibered]

/-- The pseudofunctor of fibers associated to a fibered functor `pA : 𝒜 ⥤ C`. -/
abbrev fibers_pseudofunctor :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, w} :=
  CategoryTheory.FiberedCategory.pseudofunctor_of_fibers (pA := pA)

@[simp]
lemma fibers_pseudofunctor_reindex {R S : C} (f : R ⟶ S) :
    Descent.Pseudofunctor.reindex (F := fibers_pseudofunctor (pA := pA)) f =
      Descent.FiberedCategory.reindex (pA := pA) f := by
  rfl

section HasPullbacks

variable [Limits.HasPullbacks C]

variable {E B : C} (p : E ⟶ B)

open Descent.Cech
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private lemma xi12_fibers {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi12 (F := fibers_pseudofunctor (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi12 (pA := pA) p ξ := by
  simp [Descent.Pseudofunctor.Descent.xi12, Descent.FiberedCategory.Descent.xi12, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

private lemma xi23_fibers {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi23 (F := fibers_pseudofunctor (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi23 (pA := pA) p ξ := by
  simp [Descent.Pseudofunctor.Descent.xi23, Descent.FiberedCategory.Descent.xi23, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

private lemma xi13_fibers {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi13 (F := fibers_pseudofunctor (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi13 (pA := pA) p ξ := by
  simp [Descent.Pseudofunctor.Descent.xi13, Descent.FiberedCategory.Descent.xi13, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

/-- Turn fibered-category descent data into pseudofunctor Čech descent data. -/
noncomputable def single_to_cech_descent_data
    (D : SingleMorphismDescentData (pA := pA) p) :
    Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p where
  obj := D.obj
  ξ := D.ξ.hom
  unit := by
    simpa [Descent.Pseudofunctor.Descent.diag_iso_p1, Descent.Pseudofunctor.Descent.diag_iso_p2,
      Descent.FiberedCategory.Descent.diag_iso_p1, Descent.FiberedCategory.Descent.diag_iso_p2,
      Descent.Pseudofunctor.reindex, CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
      CategoryTheory.pseudofunctorOfIsLocallyDiscrete] using D.unit
  cocycle := by
    simpa [xi12_fibers (pA := pA) (p := p), xi23_fibers (pA := pA) (p := p),
      xi13_fibers (pA := pA) (p := p)] using D.cocycle

/-- Turn pseudofunctor Čech descent data into fibered-category descent data. -/
noncomputable def cech_to_single_descent_data
    (D : Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p) :
    SingleMorphismDescentData (pA := pA) p := by
  haveI : IsIso D.ξ := by
    infer_instance
  refine
    { obj := D.obj
      ξ := asIso D.ξ
      unit := by
        simpa [Descent.Pseudofunctor.Descent.diag_iso_p1, Descent.Pseudofunctor.Descent.diag_iso_p2,
          Descent.FiberedCategory.Descent.diag_iso_p1, Descent.FiberedCategory.Descent.diag_iso_p2,
          Descent.Pseudofunctor.reindex, CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
          CategoryTheory.pseudofunctorOfIsLocallyDiscrete] using D.unit
      cocycle := by
        let ξIso : (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj D.obj ≅
            (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj D.obj :=
          asIso D.ξ
        simpa [xi12_fibers (pA := pA) (p := p), xi23_fibers (pA := pA) (p := p),
          xi13_fibers (pA := pA) (p := p)] using
          (show
            Descent.Pseudofunctor.Descent.xi23 (F := fibers_pseudofunctor (pA := pA)) p ξIso.hom ≫
                Descent.Pseudofunctor.Descent.xi12 (F := fibers_pseudofunctor (pA := pA)) p ξIso.hom =
              Descent.Pseudofunctor.Descent.xi13 (F := fibers_pseudofunctor (pA := pA)) p ξIso.hom
            from by
              simpa [ξIso] using D.cocycle) }

/-- The functor from fibered-category descent data to pseudofunctor Čech descent data. -/
noncomputable def single_to_cech_functor :
    SingleMorphismDescentData (pA := pA) p ⥤
      Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p where
  obj D := single_to_cech_descent_data (pA := pA) p D
  map {D D'} f :=
    { hom := f.hom
      comm := by
        simpa [single_to_cech_descent_data, fibers_pseudofunctor_reindex] using f.comm }
  map_id D := by
    apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
    change (SingleMorphismDescentData.Hom.id (pA := pA) D).hom =
      (Descent.Pseudofunctor.Descent.CechDescentData.Hom.id
            (single_to_cech_descent_data (pA := pA) p D)).hom
    simp [single_to_cech_descent_data]
  map_comp {X Y Z} f g := by
    apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
    let f' :
        Descent.Pseudofunctor.Descent.CechDescentData.Hom
          (single_to_cech_descent_data (pA := pA) p X) (single_to_cech_descent_data (pA := pA) p Y) :=
      { hom := f.hom
        comm := by
          simpa [single_to_cech_descent_data, fibers_pseudofunctor_reindex] using f.comm }
    let g' :
        Descent.Pseudofunctor.Descent.CechDescentData.Hom
          (single_to_cech_descent_data (pA := pA) p Y) (single_to_cech_descent_data (pA := pA) p Z) :=
      { hom := g.hom
        comm := by
          simpa [single_to_cech_descent_data, fibers_pseudofunctor_reindex] using g.comm }
    change (SingleMorphismDescentData.Hom.comp (pA := pA) f g).hom = (f'.comp g').hom
    simp [f', g']

/-- The functor from pseudofunctor Čech descent data to fibered-category descent data. -/
noncomputable def cech_to_single_functor :
    Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p ⥤
      SingleMorphismDescentData (pA := pA) p where
  obj D := cech_to_single_descent_data (pA := pA) p D
  map {D D'} f :=
    { hom := f.hom
      comm := by
        simpa [fibers_pseudofunctor_reindex] using f.comm }
  map_id D := by
    apply SingleMorphismDescentData.Hom.ext (pA := pA)
    change (Descent.Pseudofunctor.Descent.CechDescentData.Hom.id D).hom =
      (SingleMorphismDescentData.Hom.id (pA := pA) (cech_to_single_descent_data (pA := pA) p D)).hom
    simp [cech_to_single_descent_data]
  map_comp {X Y Z} f g := by
    apply SingleMorphismDescentData.Hom.ext (pA := pA)
    let f' :
        SingleMorphismDescentData.Hom (pA := pA)
          (cech_to_single_descent_data (pA := pA) p X) (cech_to_single_descent_data (pA := pA) p Y) :=
      { hom := f.hom
        comm := by
          simpa [fibers_pseudofunctor_reindex, cech_to_single_descent_data] using f.comm }
    let g' :
        SingleMorphismDescentData.Hom (pA := pA)
          (cech_to_single_descent_data (pA := pA) p Y) (cech_to_single_descent_data (pA := pA) p Z) :=
      { hom := g.hom
        comm := by
          simpa [fibers_pseudofunctor_reindex, cech_to_single_descent_data] using g.comm }
    change (Descent.Pseudofunctor.Descent.CechDescentData.Hom.comp f g).hom = (f'.comp g').hom
    simp [f', g']

/-- Component of the unit isomorphism for `single_cech_descent_data_equiv`. -/
private def single_cech_unit_component
    (D : SingleMorphismDescentData (pA := pA) p) :
    D ≅ ((single_to_cech_functor (pA := pA) p ⋙ cech_to_single_functor (pA := pA) p).obj D) := by
  refine ⟨?hom, ?inv, ?hom_inv_id, ?inv_hom_id⟩
  · refine ⟨𝟙 D.obj, ?_⟩
    simp [single_to_cech_functor, cech_to_single_functor,
      single_to_cech_descent_data, cech_to_single_descent_data]
  · refine ⟨𝟙 D.obj, ?_⟩
    simp [single_to_cech_functor, cech_to_single_functor,
      single_to_cech_descent_data, cech_to_single_descent_data]
  · apply SingleMorphismDescentData.Hom.ext (pA := pA)
    change 𝟙 D.obj ≫ 𝟙 D.obj = 𝟙 D.obj
    simp
  · apply SingleMorphismDescentData.Hom.ext (pA := pA)
    change 𝟙 D.obj ≫ 𝟙 D.obj = 𝟙 D.obj
    simp

/-- Unit natural isomorphism for `single_cech_descent_data_equiv`. -/
private def single_cech_unitIso :
    𝟭 (SingleMorphismDescentData (pA := pA) p) ≅
      single_to_cech_functor (pA := pA) p ⋙ cech_to_single_functor (pA := pA) p := by
  refine NatIso.ofComponents (fun D ↦ single_cech_unit_component (pA := pA) (p := p) D)
    (fun {D D'} f ↦ by
      apply SingleMorphismDescentData.Hom.ext (pA := pA)
      change f.hom ≫ 𝟙 D'.obj = 𝟙 D.obj ≫ f.hom
      simp)

/-- Component of the counit isomorphism for `single_cech_descent_data_equiv`. -/
private def single_cech_counit_component
    (D : Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p) :
    ((cech_to_single_functor (pA := pA) p ⋙ single_to_cech_functor (pA := pA) p).obj D) ≅ D := by
  refine ⟨?hom, ?inv, ?hom_inv_id, ?inv_hom_id⟩
  · refine ⟨𝟙 D.obj, ?_⟩
    simp [single_to_cech_functor, cech_to_single_functor,
      single_to_cech_descent_data, cech_to_single_descent_data]
  · refine ⟨𝟙 D.obj, ?_⟩
    simp [single_to_cech_functor, cech_to_single_functor,
      single_to_cech_descent_data, cech_to_single_descent_data]
  · apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
    change 𝟙 D.obj ≫ 𝟙 D.obj = 𝟙 D.obj
    simp
  · apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
    change 𝟙 D.obj ≫ 𝟙 D.obj = 𝟙 D.obj
    simp

/-- Counit natural isomorphism for `single_cech_descent_data_equiv`. -/
private def single_cech_counitIso :
    cech_to_single_functor (pA := pA) p ⋙ single_to_cech_functor (pA := pA) p ≅
      𝟭 (Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p) := by
  refine NatIso.ofComponents (fun D ↦ single_cech_counit_component (pA := pA) (p := p) D)
    (fun {D D'} f ↦ by
      apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
      change f.hom ≫ 𝟙 D'.obj = 𝟙 D.obj ≫ f.hom
      simp)

/-- The expected equivalence between fibered-category and pseudofunctor Čech descent data. -/
noncomputable def single_cech_descent_data_equiv :
    SingleMorphismDescentData (pA := pA) p ≌
      Descent.Pseudofunctor.Descent.CechDescentData (F := fibers_pseudofunctor (pA := pA)) p := by
  refine
    { functor := single_to_cech_functor (pA := pA) p
      inverse := cech_to_single_functor (pA := pA) p
      unitIso := single_cech_unitIso (pA := pA) (p := p)
      counitIso := single_cech_counitIso (pA := pA) (p := p)
      functor_unitIso_comp := by
        intro X
        apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
        change 𝟙 X.obj ≫ 𝟙 X.obj = 𝟙 X.obj
        simp }

end HasPullbacks

end

end Descent.FiberedCategory.Descent
