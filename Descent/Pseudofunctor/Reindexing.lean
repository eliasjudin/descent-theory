/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Reindexing for pseudofunctors

Defines `reindex` and the basic coherence isomorphisms for a pseudofunctor
`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
-/

open CategoryTheory

namespace Descent.Pseudofunctor

open Opposite

universe v' v u' u

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

/-!
## Reindexing for pseudofunctors
-/

/-- Reindexing along a morphism for a pseudofunctor. -/
abbrev reindex {R S : C} (f : R ⟶ S) :
    F.obj (.mk (op S)) ⥤ F.obj (.mk (op R)) :=
  (F.map f.op.toLoc).toFunctor

/-- If `f = g`, then `f^* a ≅ g^* a`. -/
def reindexObjIsoOfEq {R S : C} {f g : R ⟶ S} (h : f = g)
    (a : F.obj (.mk (op S))) :
    (reindex F f).obj a ≅ (reindex F g).obj a := by
  refine eqToIso ?_
  simpa using congrArg (fun k => (reindex F k).obj a) h

@[simp]
lemma reindexObjIsoOfEq_hom {R S : C} {f g : R ⟶ S} (h : f = g) (a : F.obj (.mk (op S))) :
    (reindexObjIsoOfEq (F := F) (f := f) (g := g) h a).hom =
      eqToHom (by simpa using congrArg (fun k => (reindex F k).obj a) h) := by
  cases h
  simp [reindexObjIsoOfEq]

@[simp]
lemma reindexObjIsoOfEq_inv {R S : C} {f g : R ⟶ S} (h : f = g) (a : F.obj (.mk (op S))) :
    (reindexObjIsoOfEq (F := F) (f := f) (g := g) h a).inv =
      eqToHom (by
        simpa using (congrArg (fun k => (reindex F k).obj a) h).symm) := by
  cases h
  simp [reindexObjIsoOfEq]

/-- The canonical isomorphism `(g ≫ f)^* a ≅ g^* (f^* a)`. -/
def reindexCompIsoObj {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : F.obj (.mk (op S))) :
    (reindex F (g ≫ f)).obj a ≅
      (reindex F g).obj ((reindex F f).obj a) :=
  (CategoryTheory.Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc)).app a

/-- The canonical isomorphism `((𝟙 S)^* a) ≅ a`. -/
def reindexIdIsoObj {S : C} (a : F.obj (.mk (op S))) :
    (reindex F (𝟙 S)).obj a ≅ a :=
  (CategoryTheory.Cat.Hom.toNatIso (F.mapId (.mk (op S)))).app a

end

end Descent.Pseudofunctor
