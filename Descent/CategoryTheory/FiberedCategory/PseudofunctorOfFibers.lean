/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.CategoryTheory.FiberedCategory.Reindexing
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The pseudofunctor of fibers of a fibered category

Let `pA : 𝒜 ⥤ C` be a fibered functor. For each `S : C`, we have the fiber category
`Fiber pA S`, and for each morphism `f : R ⟶ S`, reindexing gives a functor
`f^* : Fiber pA S ⥤ Fiber pA R`.

This file packages the reindexing data into a pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.

Note: coherence constraints are discharged by
`CategoryTheory.pseudofunctorOfIsLocallyDiscrete` via its default `by cat_disch` obligations.
-/

open CategoryTheory
open CategoryTheory.Functor
open Opposite

namespace CategoryTheory

namespace FiberedCategory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜]

noncomputable section

/-- Fiber category object part for the pseudofunctor of fibers. -/
private abbrev fibers_obj (pA : 𝒜 ⥤ C) [pA.IsFibered] (X : LocallyDiscrete Cᵒᵖ) : Cat.{v, w} :=
  Cat.of (Fiber pA (unop X.as))

/-- Reindexing functor as the morphism part for the pseudofunctor of fibers. -/
private abbrev fibers_map (pA : 𝒜 ⥤ C) [pA.IsFibered] {X Y : LocallyDiscrete Cᵒᵖ}
    (f : X ⟶ Y) : fibers_obj (pA := pA) X ⟶ fibers_obj (pA := pA) Y :=
  (reindex (pA := pA) f.as.unop).toCatHom

/-- Identity coherence for the morphism part of the pseudofunctor of fibers. -/
private abbrev fibers_mapId (pA : 𝒜 ⥤ C) [pA.IsFibered] (X : LocallyDiscrete Cᵒᵖ) :
    fibers_map (pA := pA) (𝟙 X) ≅ 𝟙 (fibers_obj (pA := pA) X) :=
  CategoryTheory.Cat.Hom.isoMk (by
    simpa using (reindex_id_iso_nat_iso (pA := pA) (S := unop X.as)))

/-- Composition coherence for the morphism part of the pseudofunctor of fibers. -/
private abbrev fibers_mapComp (pA : 𝒜 ⥤ C) [pA.IsFibered]
    {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fibers_map (pA := pA) (f ≫ g) ≅ fibers_map (pA := pA) f ≫ fibers_map (pA := pA) g :=
  CategoryTheory.Cat.Hom.isoMk (by
    simpa using (reindex_comp_iso (pA := pA) (g := g.as.unop) (f := f.as.unop)))

/-- Associator coherence for the pseudofunctor of fibers. -/
private lemma fibers_map₂_associator (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    ∀ {X Y Z W : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W),
      (fibers_mapComp (pA := pA) (f ≫ g) h).hom ≫
          Bicategory.whiskerRight (fibers_mapComp (pA := pA) f g).hom (fibers_map (pA := pA) h) ≫
            (Bicategory.associator (fibers_map (pA := pA) f) (fibers_map (pA := pA) g)
              (fibers_map (pA := pA) h)).hom ≫
              Bicategory.whiskerLeft (fibers_map (pA := pA) f)
                (fibers_mapComp (pA := pA) g h).inv ≫
                (fibers_mapComp (pA := pA) f (g ≫ h)).inv =
        eqToHom (by simp [fibers_map]) := by
  intro X Y Z W f g h
  ext a
  apply Fiber.hom_ext
  let φ : (reindexObj (pA := pA) ((h.as.unop ≫ g.as.unop) ≫ f.as.unop) a).1 ⟶ a.1 :=
    IsPreFibered.pullbackMap (p := pA) a.2 ((h.as.unop ≫ g.as.unop) ≫ f.as.unop)
  haveI : IsCartesian pA ((h.as.unop ≫ g.as.unop) ≫ f.as.unop) φ := by
    dsimp [φ]
    infer_instance
  apply IsCartesian.ext (p := pA) (f := ((h.as.unop ≫ g.as.unop) ≫ f.as.unop)) (φ := φ)
  trans IsPreFibered.pullbackMap (p := pA) a.2 (h.as.unop ≫ (g.as.unop ≫ f.as.unop))
  · change
      Fiber.fiberInclusion.map
          (((fibers_mapComp (pA := pA) (f ≫ g) h).hom ≫
                  Bicategory.whiskerRight (fibers_mapComp (pA := pA) f g).hom
                    (fibers_map (pA := pA) h) ≫
                (Bicategory.associator (fibers_map (pA := pA) f) (fibers_map (pA := pA) g)
                  (fibers_map (pA := pA) h)).hom ≫
              Bicategory.whiskerLeft (fibers_map (pA := pA) f)
                (fibers_mapComp (pA := pA) g h).inv ≫
            (fibers_mapComp (pA := pA) f (g ≫ h)).inv).toNatTrans.app a) ≫
        φ =
        IsPreFibered.pullbackMap (p := pA) a.2 (h.as.unop ≫ g.as.unop ≫ f.as.unop)
    simp [φ, fibers_map, fibers_mapComp, Fiber.fiberInclusion, Category.assoc]
    change
      (reindex_comp_iso_obj (pA := pA) h.as.unop (g.as.unop ≫ f.as.unop) a).hom.1 ≫
        (((reindex (pA := pA) h.as.unop).map
              (reindex_comp_iso_obj (pA := pA) g.as.unop f.as.unop a).hom).1 ≫
            (reindex_comp_iso_obj (pA := pA) h.as.unop g.as.unop
                ((reindex (pA := pA) f.as.unop).obj a)).inv.1 ≫
            (reindex_comp_iso_obj (pA := pA) (h.as.unop ≫ g.as.unop) f.as.unop a).inv.1) ≫
          IsPreFibered.pullbackMap (p := pA) a.2 ((h.as.unop ≫ g.as.unop) ≫ f.as.unop) =
        IsPreFibered.pullbackMap (p := pA) a.2 (h.as.unop ≫ (g.as.unop ≫ f.as.unop))
    simp [Category.assoc]
    rw [CategoryTheory.FiberedCategory.reindex_comp_iso_obj_inv_comp_pullback_assoc
      (pA := pA) (g := h.as.unop) (f := g.as.unop)
      (a := (reindex (pA := pA) f.as.unop).obj a)]
    rw [reindex_map_comp_pullback_assoc (pA := pA) (f := h.as.unop)
      (φ := (reindex_comp_iso_obj (pA := pA) g.as.unop f.as.unop a).hom)]
    have h_gf :=
      reindex_comp_iso_obj_hom_comp_pullback (pA := pA) (g := g.as.unop) (f := f.as.unop) a
    have h_hgf :=
      reindex_comp_iso_obj_hom_comp_pullback (pA := pA) (g := h.as.unop)
        (f := g.as.unop ≫ f.as.unop) a
    rw [h_gf]
    exact h_hgf
  have h_assoc : h.as.unop ≫ (g.as.unop ≫ f.as.unop) = (h.as.unop ≫ g.as.unop) ≫ f.as.unop := by
    simp [Category.assoc]
  simpa [h_assoc, Category.assoc] using
    (reindex_obj_iso_of_eq_hom_comp_pullback (pA := pA)
      (f := h.as.unop ≫ (g.as.unop ≫ f.as.unop))
      (g := (h.as.unop ≫ g.as.unop) ≫ f.as.unop)
      (h := h_assoc) a).symm

/-- Left unitor coherence for the pseudofunctor of fibers. -/
private lemma fibers_map₂_left_unitor (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    ∀ {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y),
      (fibers_mapComp (pA := pA) (𝟙 X) f).hom ≫
          Bicategory.whiskerRight (fibers_mapId (pA := pA) X).hom (fibers_map (pA := pA) f) ≫
            (Bicategory.leftUnitor (fibers_map (pA := pA) f)).hom =
        eqToHom (by simp [fibers_map]) := by
  intro X Y f
  ext a
  apply Fiber.hom_ext
  let φ : (reindexObj (pA := pA) f.as.unop a).1 ⟶ a.1 :=
    IsPreFibered.pullbackMap (p := pA) a.2 f.as.unop
  haveI : IsCartesian pA f.as.unop φ := by
    dsimp [φ]
    infer_instance
  apply IsCartesian.ext (p := pA) (f := f.as.unop) (φ := φ)
  simp [φ, fibers_map, fibers_mapComp, fibers_mapId, Fiber.fiberInclusion, reindex_id_iso_hom_eq,
    reindex_comp_iso_obj_hom_comp_pullback, Category.assoc]
  have h_id : f.as.unop ≫ 𝟙 (unop X.as) = f.as.unop := by
    simp
  simpa [reindex, reindex_id_iso, fiber_iso, h_id, Category.assoc] using
    (reindex_obj_iso_of_eq_hom_comp_pullback (pA := pA)
      (f := f.as.unop ≫ 𝟙 (unop X.as))
      (g := f.as.unop)
      (h := h_id) a).symm

/-- Right unitor coherence for the pseudofunctor of fibers. -/
private lemma fibers_map₂_right_unitor (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    ∀ {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y),
      (fibers_mapComp (pA := pA) f (𝟙 Y)).hom ≫
          Bicategory.whiskerLeft (fibers_map (pA := pA) f) (fibers_mapId (pA := pA) Y).hom ≫
            (Bicategory.rightUnitor (fibers_map (pA := pA) f)).hom =
        eqToHom (by simp [fibers_map]) := by
  intro X Y f
  ext a
  apply Fiber.hom_ext
  let φ : (reindexObj (pA := pA) f.as.unop a).1 ⟶ a.1 :=
    IsPreFibered.pullbackMap (p := pA) a.2 f.as.unop
  haveI : IsCartesian pA f.as.unop φ := by
    dsimp [φ]
    infer_instance
  apply IsCartesian.ext (p := pA) (f := f.as.unop) (φ := φ)
  simp [φ, fibers_map, fibers_mapComp, fibers_mapId, Fiber.fiberInclusion, reindex_id_iso_hom_eq,
    reindex_comp_iso_obj_hom_comp_pullback, Category.assoc]
  have h_id : 𝟙 (unop Y.as) ≫ f.as.unop = f.as.unop := by
    simp
  simpa [h_id, Category.assoc] using
    (reindex_obj_iso_of_eq_hom_comp_pullback (pA := pA)
      (f := 𝟙 (unop Y.as) ≫ f.as.unop)
      (g := f.as.unop)
      (h := h_id) a).symm

/-- The pseudofunctor of fibers associated to a fibered functor `pA : 𝒜 ⥤ C`. -/
noncomputable def pseudofunctor_of_fibers (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, w} :=
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
    (B := LocallyDiscrete Cᵒᵖ) (C := Cat.{v, w})
    (obj := fibers_obj (pA := pA))
    (map := fun f => fibers_map (pA := pA) f)
    (mapId := fibers_mapId (pA := pA))
    (mapComp := fun f g => fibers_mapComp (pA := pA) f g)
    (map₂_associator := fibers_map₂_associator (pA := pA))
    (map₂_left_unitor := fibers_map₂_left_unitor (pA := pA))
    (map₂_right_unitor := fibers_map₂_right_unitor (pA := pA))

@[simp]
lemma pseudofunctor_of_fibers_obj (pA : 𝒜 ⥤ C) [pA.IsFibered] (S : C) :
    (pseudofunctor_of_fibers (pA := pA)).obj (.mk (op S)) = Cat.of (Fiber pA S) :=
  rfl

@[simp]
lemma pseudofunctor_of_fibers_map {pA : 𝒜 ⥤ C} [pA.IsFibered]
    {R S : C} (f : R ⟶ S) :
    (pseudofunctor_of_fibers (pA := pA)).map f.op.toLoc =
      (reindex (pA := pA) f).toCatHom := by
  rfl

end

end FiberedCategory

end CategoryTheory
