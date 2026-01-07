/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.Pseudofunctor.Reindexing

/-!
# Descent data along a single morphism (pseudofunctor version)

For a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` and a morphism `p : E ⟶ B`,
we define the category of descent data along `p` using the Čech kernel pair
`E ×_B E` and triple overlaps `E ×_B E ×_B E`. This avoids any internal-category
formalization, relying only on pullbacks.

## Mathematical Background

### Cocycle Convention

The gluing isomorphism `ξ : π₂^* obj ≅ π₁^* obj` can be thought of as assigning to each
pair `(e₁, e₂)` in the kernel pair an isomorphism from the fiber over `e₂` to the fiber
over `e₁`. The direction is `π₂^* → π₁^*`, i.e., "second coordinate to first coordinate".

The cocycle condition `ξ₂₃ ≫ ξ₁₂ = ξ₁₃` states that for any triple `(e₁, e₂, e₃)`:
```
  ξ(e₂, e₃) ≫ ξ(e₁, e₂) = ξ(e₁, e₃)
```
This is the standard groupoid associativity law: transitioning `e₃ → e₂ → e₁` equals
transitioning `e₃ → e₁` directly.

### Unit Convention

The unit condition `diag^*(ξ) = id` expresses that the transition from a point to itself
is the identity. Formally, restricting `ξ` along the diagonal `diag : E → E ×_B E` (which
sends `e` to `(e, e)`) must yield the identity isomorphism.

## Main definitions

* `SingleMorphismDescentDatum`: Descent data for a pseudofunctor relative to a morphism
* `SingleMorphismDescentData`: The category of descent data
* `single_morphism_comparison_xi`: The canonical descent isomorphism on `p^* a`
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

open Opposite
open Descent.Cech
open Descent.Pseudofunctor

universe v' v u' u

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

/-!
## Auxiliary isomorphisms for the diagonal
-/

/-- The canonical isomorphism `diag^*(π₁^* a) ≅ a`. -/
def diag_iso_p1 {E B : C} (p : E ⟶ B) (a : F.obj (.mk (op E))) :
    (reindex F (Limits.pullback.diagonal p)).obj ((reindex F (p1 p)).obj a) ≅ a := by
  refine
    (reindex_comp_iso_obj (F := F) (g := Limits.pullback.diagonal p) (f := p1 p) a).symm ≪≫
      (reindex_objIsoOfEq (F := F) (f := Limits.pullback.diagonal p ≫ p1 p) (g := 𝟙 E)
        (by simp) a) ≪≫
        reindex_id_isoObj (F := F) a

/-- The canonical isomorphism `diag^*(π₂^* a) ≅ a`. -/
def diag_iso_p2 {E B : C} (p : E ⟶ B) (a : F.obj (.mk (op E))) :
    (reindex F (Limits.pullback.diagonal p)).obj ((reindex F (p2 p)).obj a) ≅ a := by
  refine
    (reindex_comp_iso_obj (F := F) (g := Limits.pullback.diagonal p) (f := p2 p) a).symm ≪≫
      (reindex_objIsoOfEq (F := F) (f := Limits.pullback.diagonal p ≫ p2 p) (g := 𝟙 E)
        (by simp) a) ≪≫
        reindex_id_isoObj (F := F) a

/-!
## Descent data for a single morphism
-/

/-- The morphism on the `(1,2)`-overlap induced from `ξ`. -/
def xi_12 {E B : C} (p : E ⟶ B) {C₀ : F.obj (.mk (op E))}
    (ξ : (reindex F (p2 p)).obj C₀ ≅ (reindex F (p1 p)).obj C₀) :
    (reindex F (p12 p ≫ p2 p)).obj C₀ ⟶ (reindex F (p12 p ≫ p1 p)).obj C₀ := by
  refine
    (reindex_comp_iso_obj (F := F) (g := p12 p) (f := p2 p) C₀).hom ≫
      (reindex F (p12 p)).map ξ.hom ≫
      (reindex_comp_iso_obj (F := F) (g := p12 p) (f := p1 p) C₀).inv

/-- The morphism on the `(2,3)`-overlap induced from `ξ`, transported so that its codomain
is the `(1,2)`-pullback. -/
def xi_23 {E B : C} (p : E ⟶ B) {C₀ : F.obj (.mk (op E))}
    (ξ : (reindex F (p2 p)).obj C₀ ≅ (reindex F (p1 p)).obj C₀) :
    (reindex F (p23 p ≫ p2 p)).obj C₀ ⟶ (reindex F (p12 p ≫ p2 p)).obj C₀ := by
  refine
    (reindex_comp_iso_obj (F := F) (g := p23 p) (f := p2 p) C₀).hom ≫
      (reindex F (p23 p)).map ξ.hom ≫
      (reindex_comp_iso_obj (F := F) (g := p23 p) (f := p1 p) C₀).inv ≫
        (reindex_objIsoOfEq (F := F) (a := C₀) (by simp)).hom

/-- The morphism on the `(1,3)`-overlap induced from `ξ`, transported so that its domain and
codomain match those of `xi_23` and `xi_12`. -/
def xi_13 {E B : C} (p : E ⟶ B) {C₀ : F.obj (.mk (op E))}
    (ξ : (reindex F (p2 p)).obj C₀ ≅ (reindex F (p1 p)).obj C₀) :
    (reindex F (p23 p ≫ p2 p)).obj C₀ ⟶ (reindex F (p12 p ≫ p1 p)).obj C₀ := by
  refine
    (reindex_objIsoOfEq (F := F) (a := C₀) (by simp)).hom ≫
      (reindex_comp_iso_obj (F := F) (g := p13 p) (f := p2 p) C₀).hom ≫
        (reindex F (p13 p)).map ξ.hom ≫
          (reindex_comp_iso_obj (F := F) (g := p13 p) (f := p1 p) C₀).inv ≫
            (reindex_objIsoOfEq (F := F) (a := C₀) (by simp)).hom

/-- Descent data for `F` relative to `p : E ⟶ B` using the Čech kernel pair. -/
structure SingleMorphismDescentDatum {E B : C} (p : E ⟶ B) where
  /-- The object over `E`. -/
  obj : F.obj (.mk (op E))
  /-- The gluing isomorphism `π₂^* obj ≅ π₁^* obj` over `E ×_B E`. -/
  ξ : (reindex F (p2 p)).obj obj ≅ (reindex F (p1 p)).obj obj
  /-- Unit condition: restricting along the diagonal yields the identity. -/
  unit :
    (diag_iso_p2 (F := F) p obj).inv ≫
        (reindex F (Limits.pullback.diagonal p)).map ξ.hom ≫
          (diag_iso_p1 (F := F) p obj).hom =
      𝟙 obj
  /-- Cocycle condition on triple overlaps. -/
  cocycle : xi_23 (F := F) p ξ ≫ xi_12 (F := F) p ξ = xi_13 (F := F) p ξ

namespace SingleMorphismDescentDatum

variable {F}
variable {E B : C} {p : E ⟶ B}

/-- Morphisms of descent data are morphisms compatible with the glueing isomorphisms. -/
structure Hom (D D' : SingleMorphismDescentDatum (F := F) p) where
  /-- The underlying morphism over `E`. -/
  hom : D.obj ⟶ D'.obj
  /-- Compatibility with the gluing isomorphisms. -/
  comm :
    D.ξ.hom ≫ (reindex F (p1 p)).map hom =
      (reindex F (p2 p)).map hom ≫ D'.ξ.hom

@[ext]
lemma Hom.ext {D D' : SingleMorphismDescentDatum (F := F) p} (f g : Hom D D')
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of descent data. -/
@[simps]
def Hom.id (D : SingleMorphismDescentDatum (F := F) p) : Hom D D where
  hom := 𝟙 D.obj
  comm := by simp

/-- Composition of morphisms of descent data. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : SingleMorphismDescentDatum (F := F) p} (f : Hom D₁ D₂)
    (g : Hom D₂ D₃) : Hom D₁ D₃ where
  hom := f.hom ≫ g.hom
  comm := by
    simp [Functor.map_comp]
    calc
      D₁.ξ.hom ≫ (reindex F (p1 p)).map f.hom ≫ (reindex F (p1 p)).map g.hom =
          (reindex F (p2 p)).map f.hom ≫ D₂.ξ.hom ≫
            (reindex F (p1 p)).map g.hom := by
        simpa [Category.assoc] using congrArg (· ≫ (reindex F (p1 p)).map g.hom) f.comm
      _ =
          (reindex F (p2 p)).map f.hom ≫ (reindex F (p2 p)).map g.hom ≫
            D₃.ξ.hom := by
        simpa [Category.assoc] using congrArg ((reindex F (p2 p)).map f.hom ≫ ·) g.comm

instance instCategory : Category (SingleMorphismDescentDatum (F := F) p) where
  Hom D D' := Hom D D'
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

end SingleMorphismDescentDatum

/-- The category of descent data for `F` relative to `p`. -/
abbrev SingleMorphismDescentData {E B : C} (p : E ⟶ B) : Type _ :=
  SingleMorphismDescentDatum (F := F) p

/-- The canonical descent isomorphism on `p^* a`. -/
def single_morphism_comparison_xi {E B : C} (p : E ⟶ B) (a : F.obj (.mk (op B))) :
    (reindex F (p2 p)).obj ((reindex F p).obj a) ≅
      (reindex F (p1 p)).obj ((reindex F p).obj a) := by
  refine
    (reindex_comp_iso_obj (F := F) (g := p2 p) (f := p) a).symm ≪≫ ?_ ≪≫
      (reindex_comp_iso_obj (F := F) (g := p1 p) (f := p) a)
  exact
    reindex_objIsoOfEq (F := F) (f := p2 p ≫ p) (g := p1 p ≫ p) (a := a) (by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm)

end

end Descent.Pseudofunctor.Descent
