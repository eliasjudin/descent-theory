/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Reindexing

/-!
# Examples: reindexing for pseudofunctors

Small `example`s that exercise the basic reindexing coherence isomorphisms for a pseudofunctor
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
-/

open CategoryTheory

namespace Descent.Examples

open Opposite
open Descent.Pseudofunctor

universe v' v u' u

section

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

example {T R S : C} (g : T ⟶ R) (f : R ⟶ S) {a b : F.obj (.mk (op S))} (φ : a ⟶ b) :
    (reindex_comp_iso_obj (F := F) g f a).hom ≫ (reindex F g).map ((reindex F f).map φ) =
      (reindex F (g ≫ f)).map φ ≫ (reindex_comp_iso_obj (F := F) g f b).hom := by
  dsimp [reindex_comp_iso_obj, reindex]
  let α := (CategoryTheory.Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc)).hom
  have h := α.naturality φ
  exact h.symm

example {S : C} {a b : F.obj (.mk (op S))} (φ : a ⟶ b) :
    (reindex F (𝟙 S)).map φ ≫ (reindex_id_iso_obj (F := F) b).hom =
      (reindex_id_iso_obj (F := F) a).hom ≫ φ := by
  dsimp [reindex_id_iso_obj, reindex]
  let α := (CategoryTheory.Cat.Hom.toNatIso (F.mapId (.mk (op S)))).hom
  exact α.naturality φ

end

end Descent.Examples
