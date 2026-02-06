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

/-- The pseudofunctor of fibers associated to a fibered functor `pA : 𝒜 ⥤ C`. -/
noncomputable def pseudofunctor_of_fibers (pA : 𝒜 ⥤ C) [pA.IsFibered] :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, w} :=
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
    (B := LocallyDiscrete Cᵒᵖ) (C := Cat.{v, w})
    (obj := fun X => Cat.of (Fiber pA (unop X.as)))
    (map := fun {X Y} f => (reindex (pA := pA) f.as.unop).toCatHom)
    (mapId := fun X => CategoryTheory.Cat.Hom.isoMk (by
      simpa using (reindex_id_iso_nat_iso (pA := pA) (S := unop X.as))))
    (mapComp := fun {X Y Z} f g => CategoryTheory.Cat.Hom.isoMk (by
      simpa using (reindex_comp_iso (pA := pA) (g := g.as.unop) (f := f.as.unop))))
    (map₂_associator := by
      -- TODO: coherence (pentagon) for the chosen pullbacks/reindexing isomorphisms.
      -- This is a standard cleavage-coherence statement.
      sorry)
    (map₂_left_unitor := by
      -- TODO: coherence (left unitor) for the chosen pullbacks/reindexing isomorphisms.
      sorry)
    (map₂_right_unitor := by
      -- TODO: coherence (right unitor) for the chosen pullbacks/reindexing isomorphisms.
      sorry)

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
