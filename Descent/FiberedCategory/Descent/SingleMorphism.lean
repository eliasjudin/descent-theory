/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.FiberedCategory.Reindexing

/-!
# Descent data for a single morphism (fibered category)

Defines Čech-style descent data for a fibered category `pA : 𝒜 ⥤ C` along
`p : E ⟶ B`, with unit and cocycle conditions on overlaps. Main definitions
are `SingleMorphismDescentDatum`, `SingleMorphismDescentData`, and
`singleMorphismComparisonXi`.
-/

open CategoryTheory Functor Category

namespace Descent.FiberedCategory.Descent

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜] (pA : 𝒜 ⥤ C) [pA.IsFibered]

noncomputable section

open CategoryTheory.Functor
open Descent.FiberedCategory
open Descent.Cech


section

variable [Limits.HasPullbacks C]

/-- The canonical isomorphism `diag^*(π₁^* a) ≅ a`. -/
noncomputable def diagIsoP1 {E B : C} (p : E ⟶ B) (a : Fiber pA E) :
    (reindex (pA := pA) (Limits.pullback.diagonal p)).obj
        ((reindex (pA := pA) (p1 p)).obj a) ≅ a := by
  -- rewrite in terms of `reindexObj`
  change
      reindexObj (pA := pA) (Limits.pullback.diagonal p)
          (reindexObj (pA := pA) (p1 p) a) ≅ a
  refine
      (reindexCompIsoObj (pA := pA) (g := Limits.pullback.diagonal p) (f := p1 p) a).symm ≪≫ ?_
  refine
    (reindexObjIsoOfEq (pA := pA) (f := Limits.pullback.diagonal p ≫ p1 p) (g := 𝟙 E)
        (by simp) a)
      ≪≫
      ?_
  exact reindexIdIso (pA := pA) a

/-- The canonical isomorphism `diag^*(π₂^* a) ≅ a`. -/
noncomputable def diagIsoP2 {E B : C} (p : E ⟶ B) (a : Fiber pA E) :
    (reindex (pA := pA) (Limits.pullback.diagonal p)).obj
        ((reindex (pA := pA) (p2 p)).obj a) ≅ a := by
  change
      reindexObj (pA := pA) (Limits.pullback.diagonal p)
          (reindexObj (pA := pA) (p2 p) a) ≅ a
  refine
      (reindexCompIsoObj (pA := pA) (g := Limits.pullback.diagonal p) (f := p2 p) a).symm ≪≫ ?_
  refine
    (reindexObjIsoOfEq (pA := pA) (f := Limits.pullback.diagonal p ≫ p2 p) (g := 𝟙 E)
        (by simp) a)
      ≪≫
      ?_
  exact reindexIdIso (pA := pA) a

/-!
## Descent data for a single morphism

We use the Čech overlaps of `p : E ⟶ B` and the cocycle convention
`ξ₂₃ ≫ ξ₁₂ = ξ₁₃`.
-/

section

variable {pA}

/-!
### Induced morphisms on triple overlaps

We define `ξ₁₂`, `ξ₂₃`, `ξ₁₃` on `E ×_B E ×_B E` using pullback/reindexing isomorphisms
so the cocycle `ξ₂₃ ≫ ξ₁₂ = ξ₁₃` is well-typed.
-/

/-- The morphism on the `(1,2)`-overlap induced from `ξ`. -/
noncomputable def xi12 {E B : C} (p : E ⟶ B) {C₀ : Fiber pA E}
    (ξ : (reindex (pA := pA) (p2 p)).obj C₀ ≅ (reindex (pA := pA) (p1 p)).obj C₀) :
    reindexObj (pA := pA) (p12 p ≫ p2 p) C₀ ⟶ reindexObj (pA := pA) (p12 p ≫ p1 p) C₀ := by
  refine
    (reindexCompIsoObj (pA := pA) (g := p12 p) (f := p2 p) C₀).hom ≫
      (reindex (pA := pA) (p12 p)).map ξ.hom ≫
      (reindexCompIsoObj (pA := pA) (g := p12 p) (f := p1 p) C₀).inv

/-- The morphism on the `(2,3)`-overlap induced from `ξ`, transported so that its codomain
is the `(1,2)`-pullback. -/
noncomputable def xi23 {E B : C} (p : E ⟶ B) {C₀ : Fiber pA E}
    (ξ : (reindex (pA := pA) (p2 p)).obj C₀ ≅ (reindex (pA := pA) (p1 p)).obj C₀) :
    reindexObj (pA := pA) (p23 p ≫ p2 p) C₀ ⟶ reindexObj (pA := pA) (p12 p ≫ p2 p) C₀ := by
  refine
    (reindexCompIsoObj (pA := pA) (g := p23 p) (f := p2 p) C₀).hom ≫
      (reindex (pA := pA) (p23 p)).map ξ.hom ≫
      (reindexCompIsoObj (pA := pA) (g := p23 p) (f := p1 p) C₀).inv ≫
        (reindexObjIsoOfEq (pA := pA) (a := C₀)
          (by simp)).hom

/-- The morphism on the `(1,3)`-overlap induced from `ξ`, transported so that its domain and
codomain match those of `xi23` and `xi12`. -/
noncomputable def xi13 {E B : C} (p : E ⟶ B) {C₀ : Fiber pA E}
    (ξ : (reindex (pA := pA) (p2 p)).obj C₀ ≅ (reindex (pA := pA) (p1 p)).obj C₀) :
    reindexObj (pA := pA) (p23 p ≫ p2 p) C₀ ⟶ reindexObj (pA := pA) (p12 p ≫ p1 p) C₀ := by
  refine
    (reindexObjIsoOfEq (pA := pA) (a := C₀)
        (by simp)).hom ≫
      (reindexCompIsoObj (pA := pA) (g := p13 p) (f := p2 p) C₀).hom ≫
        (reindex (pA := pA) (p13 p)).map ξ.hom ≫
          (reindexCompIsoObj (pA := pA) (g := p13 p) (f := p1 p) C₀).inv ≫
            (reindexObjIsoOfEq (pA := pA) (a := C₀)
              (by simp)).hom

/-!
### Descent data
-/

/-- Descent data for `pA` relative to `p : E ⟶ B`.

This is the usual Čech formulation: an object over `E` equipped with a gluing isomorphism on
`E ×_B E` satisfying unit and cocycle conditions. -/
structure SingleMorphismDescentDatum {E B : C} (p : E ⟶ B) where
  /-- The object over `E`. -/
  obj : Fiber pA E
  /-- The gluing isomorphism `π₂^* obj ≅ π₁^* obj` over `E ×_B E`. -/
  ξ : (reindex (pA := pA) (p2 p)).obj obj ≅ (reindex (pA := pA) (p1 p)).obj obj
  /-- Unit condition: restricting along the diagonal yields the identity. -/
  unit :
    (diagIsoP2 (pA := pA) p obj).inv ≫
        (reindex (pA := pA) (Limits.pullback.diagonal p)).map ξ.hom ≫
          (diagIsoP1 (pA := pA) p obj).hom =
      𝟙 obj
  /-- Cocycle condition on triple overlaps. -/
  cocycle : xi23 (pA := pA) p ξ ≫ xi12 (pA := pA) p ξ = xi13 (pA := pA) p ξ

namespace SingleMorphismDescentDatum

variable {E B : C} {p : E ⟶ B}

/-- Morphisms of descent data are morphisms in the fiber over `E` compatible with the glueing
isomorphisms. -/
structure Hom (D D' : SingleMorphismDescentDatum (pA := pA) p) where
  /-- The underlying morphism in the fiber over `E`. -/
  hom : D.obj ⟶ D'.obj
  /-- Compatibility with the gluing isomorphisms. -/
  comm :
    D.ξ.hom ≫ (reindex (pA := pA) (p1 p)).map hom =
      (reindex (pA := pA) (p2 p)).map hom ≫ D'.ξ.hom

@[ext]
lemma Hom.ext {D D' : SingleMorphismDescentDatum (pA := pA) p} {f g : Hom (pA := pA) D D'}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of descent data. -/
@[simps]
def Hom.id (D : SingleMorphismDescentDatum (pA := pA) p) : Hom (pA := pA) D D where
  hom := 𝟙 D.obj
  comm := by simp

/-- Composition of morphisms of descent data. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : SingleMorphismDescentDatum (pA := pA) p} (f : Hom (pA := pA) D₁ D₂)
    (g : Hom (pA := pA) D₂ D₃) : Hom (pA := pA) D₁ D₃ where
  hom := f.hom ≫ g.hom
  comm := by
    -- Expand and use the commutativity conditions for `f` and `g`.
    -- (We keep this proof `simp`-friendly to ease later rewriting.)
    simp [Functor.map_comp]
    calc
      D₁.ξ.hom ≫ (reindex (pA := pA) (p1 p)).map f.hom ≫ (reindex (pA := pA) (p1 p)).map g.hom =
          (reindex (pA := pA) (p2 p)).map f.hom ≫ D₂.ξ.hom ≫
            (reindex (pA := pA) (p1 p)).map g.hom := by
        simpa [Category.assoc] using congrArg (· ≫ (reindex (pA := pA) (p1 p)).map g.hom) f.comm
      _ =
          (reindex (pA := pA) (p2 p)).map f.hom ≫ (reindex (pA := pA) (p2 p)).map g.hom ≫
            D₃.ξ.hom := by
        simpa [Category.assoc] using congrArg ((reindex (pA := pA) (p2 p)).map f.hom ≫ ·) g.comm

instance instCategory : Category (SingleMorphismDescentDatum (pA := pA) p) where
  Hom D D' := Hom (pA := pA) D D'
  id := Hom.id (pA := pA)
  comp f g := Hom.comp (pA := pA) f g
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

end SingleMorphismDescentDatum

/-- The category of descent data for `pA` relative to `p`. -/
abbrev SingleMorphismDescentData {E B : C} (p : E ⟶ B) : Type _ :=
  SingleMorphismDescentDatum (pA := pA) p

/-- The canonical descent isomorphism on `p^* a`.

It is induced from the equality `π₁ ≫ p = π₂ ≫ p` identifying the two composites
`E ×_B E ⟶ B`. -/
noncomputable def singleMorphismComparisonXi {E B : C} (p : E ⟶ B) (a : Fiber pA B) :
    (reindex (pA := pA) (p2 p)).obj ((reindex (pA := pA) p).obj a) ≅
      (reindex (pA := pA) (p1 p)).obj ((reindex (pA := pA) p).obj a) := by
  -- Rewrite to `reindexObj` to use our coherence isomorphisms.
  change
    reindexObj (pA := pA) (p2 p) (reindexObj (pA := pA) p a) ≅
      reindexObj (pA := pA) (p1 p) (reindexObj (pA := pA) p a)
  refine (reindexCompIsoObj (pA := pA) (g := p2 p) (f := p) a).symm ≪≫ ?_ ≪≫
      (reindexCompIsoObj (pA := pA) (g := p1 p) (f := p) a)
  exact
    reindexObjIsoOfEq (pA := pA) (a := a) (by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm)

end

end

end

end Descent.FiberedCategory.Descent
