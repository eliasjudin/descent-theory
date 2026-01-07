/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.FiberedCategory.Reindexing

/-!
# Descent Data for a Single Morphism

This file defines descent data for a fibered category relative to a morphism
`p : E ⟶ B`, following the approach of Janelidze-Tholen "Facets of Descent II".

## Main definitions

Given a fibered category `pA : 𝒜 ⥤ C` and a morphism `p : E ⟶ B` in `C`:

* `SingleMorphismDescentDatum pA p`: An object in the fiber over `E` together with
  an isomorphism over the kernel pair `E ×_B E` satisfying unit and cocycle
  conditions.

* `SingleMorphismDescentData pA p`: The category of descent data for `pA` relative to `p`.

* `single_morphism_comparison_xi pA p a`: The canonical descent isomorphism on
  `p^* a`, induced from the equality `π₁ ≫ p = π₂ ≫ p` of the two maps
  `E ×_B E ⟶ B`.

## Mathematical Background

For a morphism `p : E ⟶ B`, the kernel pair gives rise to the Čech groupoid:
- Objects: `E`
- Morphisms: `E ×_B E` (the 2-fold overlap)
- Triple overlaps: `E ×_B E ×_B E` (for the cocycle condition)

A descent datum consists of:
- An object `x` in the fiber `Fib pA E`
- An isomorphism `ξ : π₂*(x) ≅ π₁*(x)` in the fiber over `E ×_B E`
- Unit condition: `diag*(ξ) = id` (restriction along diagonal)
- Cocycle condition: `π₁₃*(ξ) = π₂₃*(ξ) ∘ π₁₂*(ξ)` (on triple overlaps)

The canonical isomorphism `single_morphism_comparison_xi` is the usual gluing
isomorphism on `p^* a` coming from the equality `π₁ ≫ p = π₂ ≫ p`.

## References

* [Janelidze, Tholen, "Facets of Descent II"]
* [Vistoli, "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory"]

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
noncomputable def diag_iso_p1 {E B : C} (p : E ⟶ B) (a : Fiber pA E) :
    (reindex (pA := pA) (Limits.pullback.diagonal p)).obj
        ((reindex (pA := pA) (p1 p)).obj a) ≅ a := by
  -- rewrite in terms of `reindex_obj`
  change
      reindex_obj (pA := pA) (Limits.pullback.diagonal p)
          (reindex_obj (pA := pA) (p1 p) a) ≅ a
  refine
      (reindex_comp_iso_obj (pA := pA) (g := Limits.pullback.diagonal p) (f := p1 p) a).symm ≪≫ ?_
  refine
    (reindex_objIsoOfEq (pA := pA) (f := Limits.pullback.diagonal p ≫ p1 p) (g := 𝟙 E)
        (by simp) a)
      ≪≫
      ?_
  exact reindex_id_iso (pA := pA) a

/-- The canonical isomorphism `diag^*(π₂^* a) ≅ a`. -/
noncomputable def diag_iso_p2 {E B : C} (p : E ⟶ B) (a : Fiber pA E) :
    (reindex (pA := pA) (Limits.pullback.diagonal p)).obj
        ((reindex (pA := pA) (p2 p)).obj a) ≅ a := by
  change
      reindex_obj (pA := pA) (Limits.pullback.diagonal p)
          (reindex_obj (pA := pA) (p2 p) a) ≅ a
  refine
      (reindex_comp_iso_obj (pA := pA) (g := Limits.pullback.diagonal p) (f := p2 p) a).symm ≪≫ ?_
  refine
    (reindex_objIsoOfEq (pA := pA) (f := Limits.pullback.diagonal p ≫ p2 p) (g := 𝟙 E)
        (by simp) a)
      ≪≫
      ?_
  exact reindex_id_iso (pA := pA) a

/-!
## Descent data for a single morphism

Let `p : E ⟶ B` be a morphism in the base category.

Following Janelidze–Tholen (Facets of Descent II), a descent datum for a fibered category
`pA : 𝒜 ⥤ C` relative to `p` can be described as:

* an object `C ∈ Fiber pA E`,
* an isomorphism `ξ : π₂^* C ≅ π₁^* C` over the kernel pair `E ×_B E`,
* satisfying the usual unit and cocycle conditions.

### Cocycle Convention

**Important:** The cocycle condition is formulated as `ξ₂₃ ≫ ξ₁₂ = ξ₁₃`, which corresponds
to the groupoid composition law. Thinking of `ξ` as a "transition function" on overlaps:

- `ξ : π₂^* C → π₁^* C` assigns to each pair `(e₁, e₂)` an isomorphism from the
  fiber over `e₂` to the fiber over `e₁`
- `ξ₁₂` is this isomorphism on the `(e₁, e₂)` component of a triple `(e₁, e₂, e₃)`
- `ξ₂₃` is this isomorphism on the `(e₂, e₃)` component
- `ξ₁₃` is this isomorphism on the `(e₁, e₃)` component

The cocycle `ξ₂₃ ≫ ξ₁₂ = ξ₁₃` then says: "transitioning from `e₃` to `e₂` to `e₁`
equals transitioning directly from `e₃` to `e₁`".

This is consistent with the direction of `ξ` (from `π₂^*` to `π₁^*`).
-/

section

variable {pA}

/-!
### The induced morphisms on triple overlaps

Given `ξ : π₂^* C ≅ π₁^* C` on `E ×_B E`, we obtain morphisms on the triple overlap
`E ×_B E ×_B E` (with projections `π₁₂, π₂₃, π₁₃`) by pulling back and re-associating via the
canonical isomorphisms `reindex_comp_iso_obj` and the equalities from `Cech.lean`.

The morphisms `ξ₁₂`, `ξ₂₃`, `ξ₁₃` are defined with domains and codomains chosen to make
the cocycle condition `ξ₂₃ ≫ ξ₁₂ = ξ₁₃` an equality of morphisms with the same source and target.
-/

/-- The morphism on the `(1,2)`-overlap induced from `ξ`. -/
noncomputable def xi_12 {E B : C} (p : E ⟶ B) {C₀ : Fiber pA E}
    (ξ : (reindex (pA := pA) (p2 p)).obj C₀ ≅ (reindex (pA := pA) (p1 p)).obj C₀) :
    reindex_obj (pA := pA) (p12 p ≫ p2 p) C₀ ⟶ reindex_obj (pA := pA) (p12 p ≫ p1 p) C₀ := by
  refine
    (reindex_comp_iso_obj (pA := pA) (g := p12 p) (f := p2 p) C₀).hom ≫
      (reindex (pA := pA) (p12 p)).map ξ.hom ≫
      (reindex_comp_iso_obj (pA := pA) (g := p12 p) (f := p1 p) C₀).inv

/-- The morphism on the `(2,3)`-overlap induced from `ξ`, transported so that its codomain
is the `(1,2)`-pullback. -/
noncomputable def xi_23 {E B : C} (p : E ⟶ B) {C₀ : Fiber pA E}
    (ξ : (reindex (pA := pA) (p2 p)).obj C₀ ≅ (reindex (pA := pA) (p1 p)).obj C₀) :
    reindex_obj (pA := pA) (p23 p ≫ p2 p) C₀ ⟶ reindex_obj (pA := pA) (p12 p ≫ p2 p) C₀ := by
  refine
    (reindex_comp_iso_obj (pA := pA) (g := p23 p) (f := p2 p) C₀).hom ≫
      (reindex (pA := pA) (p23 p)).map ξ.hom ≫
      (reindex_comp_iso_obj (pA := pA) (g := p23 p) (f := p1 p) C₀).inv ≫
        (reindex_objIsoOfEq (pA := pA) (a := C₀)
          (by simp)).hom

/-- The morphism on the `(1,3)`-overlap induced from `ξ`, transported so that its domain and
codomain match those of `xi_23` and `xi_12`. -/
noncomputable def xi_13 {E B : C} (p : E ⟶ B) {C₀ : Fiber pA E}
    (ξ : (reindex (pA := pA) (p2 p)).obj C₀ ≅ (reindex (pA := pA) (p1 p)).obj C₀) :
    reindex_obj (pA := pA) (p23 p ≫ p2 p) C₀ ⟶ reindex_obj (pA := pA) (p12 p ≫ p1 p) C₀ := by
  refine
    (reindex_objIsoOfEq (pA := pA) (a := C₀)
        (by simp)).hom ≫
      (reindex_comp_iso_obj (pA := pA) (g := p13 p) (f := p2 p) C₀).hom ≫
        (reindex (pA := pA) (p13 p)).map ξ.hom ≫
          (reindex_comp_iso_obj (pA := pA) (g := p13 p) (f := p1 p) C₀).inv ≫
            (reindex_objIsoOfEq (pA := pA) (a := C₀)
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
    (diag_iso_p2 (pA := pA) p obj).inv ≫
        (reindex (pA := pA) (Limits.pullback.diagonal p)).map ξ.hom ≫
          (diag_iso_p1 (pA := pA) p obj).hom =
      𝟙 obj
  /-- Cocycle condition on triple overlaps. -/
  cocycle : xi_23 (pA := pA) p ξ ≫ xi_12 (pA := pA) p ξ = xi_13 (pA := pA) p ξ

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
lemma Hom.ext {D D' : SingleMorphismDescentDatum (pA := pA) p} (f g : Hom (pA := pA) D D')
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
noncomputable def single_morphism_comparison_xi {E B : C} (p : E ⟶ B) (a : Fiber pA B) :
    (reindex (pA := pA) (p2 p)).obj ((reindex (pA := pA) p).obj a) ≅
      (reindex (pA := pA) (p1 p)).obj ((reindex (pA := pA) p).obj a) := by
  -- Rewrite to `reindex_obj` to use our coherence isomorphisms.
  change
    reindex_obj (pA := pA) (p2 p) (reindex_obj (pA := pA) p a) ≅
      reindex_obj (pA := pA) (p1 p) (reindex_obj (pA := pA) p a)
  refine (reindex_comp_iso_obj (pA := pA) (g := p2 p) (f := p) a).symm ≪≫ ?_ ≪≫
      (reindex_comp_iso_obj (pA := pA) (g := p1 p) (f := p) a)
  exact
    reindex_objIsoOfEq (pA := pA) (a := a) (by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm)

end

end

end

end Descent.FiberedCategory.Descent
