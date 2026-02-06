/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.CategoryTheory.FiberedCategory.Reindexing
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

/-!
# The pseudofunctor of fibers of a fibered category

Let `pA : 𝒜 ⥤ C` be a fibered functor. For each `S : C`, we have the fiber category
`Fiber pA S`, and for each morphism `f : R ⟶ S`, reindexing gives a functor
`f^* : Fiber pA S ⥤ Fiber pA R`.

This file packages the reindexing data into a pseudofunctor
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.

Note: constructing a pseudofunctor from a fibered category requires coherence conditions for the
chosen cleavage. We record these coherences as fields, but leave some proofs as `sorry` (with
explicit TODO notes), since downstream development in this repository may proceed with sorries.
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
  -- Checklist: contravariance and overlap-map orientation are fixed by `fibers_map`.
  sorry

/-- Left unitor coherence for the pseudofunctor of fibers. -/
private lemma fibers_map₂_left_unitor (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    ∀ {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y),
      (fibers_mapComp (pA := pA) (𝟙 X) f).hom ≫
          Bicategory.whiskerRight (fibers_mapId (pA := pA) X).hom (fibers_map (pA := pA) f) ≫
            (Bicategory.leftUnitor (fibers_map (pA := pA) f)).hom =
        eqToHom (by simp [fibers_map]) := by
  intro X Y f
  -- Checklist: unitor direction is consistent with the chosen `f^*` orientation.
  sorry

/-- Right unitor coherence for the pseudofunctor of fibers. -/
private lemma fibers_map₂_right_unitor (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    ∀ {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y),
      (fibers_mapComp (pA := pA) f (𝟙 Y)).hom ≫
          Bicategory.whiskerLeft (fibers_map (pA := pA) f) (fibers_mapId (pA := pA) Y).hom ≫
            (Bicategory.rightUnitor (fibers_map (pA := pA) f)).hom =
        eqToHom (by simp [fibers_map]) := by
  intro X Y f
  -- Checklist: unitor direction is consistent with the chosen `f^*` orientation.
  sorry

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
