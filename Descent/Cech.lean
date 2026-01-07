/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Čech Kernel Pair Conventions

This file defines the Čech objects and projections associated to a morphism `p : E ⟶ B`
in a category with pullbacks. These are the basic building blocks for descent data.

## Mathematical Background

For a morphism `p : E ⟶ B`, the **Čech nerve** is a simplicial object encoding the
"overlap structure" of `p`. The first few levels are:
- `E` (0-simplices): the "points"
- `E ×_B E` (1-simplices): pairs of points with same image under `p`
- `E ×_B E ×_B E` (2-simplices): triples of points with same image

### Choice of Triple Overlap

**Important convention:** We define `cechThree p := pullback (p2 p) (p1 p)`, which models
*composable pairs* in the Čech groupoid. This is canonically isomorphic to, but not
definitionally equal to, the more symmetric `E ×_B E ×_B E` obtained as an iterated
pullback with different bracketing.

Concretely, an element of `cechThree p` can be thought of as a pair `((e₁, e₂), (e₂', e₃))`
where `e₂ = e₂'`. The projections are:
- `p12`: projects to `(e₁, e₂)`
- `p23`: projects to `(e₂, e₃)`
- `p13`: projects to `(e₁, e₃)` (the composite)

The cocycle condition `π₁₃*(ξ) = π₂₃*(ξ) ∘ π₁₂*(ξ)` on descent data corresponds to
`ξ(e₁, e₃) = ξ(e₂, e₃) ∘ ξ(e₁, e₂)`, which is the standard groupoid composition law.

## Main definitions

Given a morphism `p : E ⟶ B`:

* `cechTwo p`: The 2-fold overlap `E ×_B E` (the kernel pair of `p`)
* `p1 p`, `p2 p`: The two projections `E ×_B E ⟶ E`
* `diag p`: The diagonal `E ⟶ E ×_B E`
* `cechThree p`: The 3-fold overlap `E ×_B E ×_B E` (as composable pairs)
* `p12 p`, `p23 p`, `p13 p`: The projections from the 3-fold to 2-fold overlap

## Key Lemmas

* `diag_p1`, `diag_p2`: The diagonal followed by either projection is the identity
* `p1_comp_p_eq_p2_comp_p`: Both projections compose with `p` to give the same map
* `p12_p2_eq_p23_p1`: The middle coordinate is shared: `p12 ≫ p2 = p23 ≫ p1`
* `p13_p1`, `p13_p2`: The outer coordinates: `p13 ≫ p1 = p12 ≫ p1`, `p13 ≫ p2 = p23 ≫ p2`

## References

* [Janelidze, Tholen, "Facets of Descent II"]
* [Vistoli, "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory"]
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
-/

open CategoryTheory

namespace Descent.Cech

universe u v

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

noncomputable section

/-!
## 2-fold overlap (kernel pair)
-/

/-- The Čech 2-fold overlap object `E ×_B E` associated to `p : E ⟶ B`. -/
abbrev cechTwo {E B : C} (p : E ⟶ B) : C :=
  Limits.pullback.diagonalObj p

/-- The first projection `E ×_B E ⟶ E`. -/
abbrev p1 {E B : C} (p : E ⟶ B) : cechTwo p ⟶ E :=
  Limits.pullback.fst (f := p) (g := p)

/-- The second projection `E ×_B E ⟶ E`. -/
abbrev p2 {E B : C} (p : E ⟶ B) : cechTwo p ⟶ E :=
  Limits.pullback.snd (f := p) (g := p)

/-- The diagonal `E ⟶ E ×_B E`. -/
abbrev diag {E B : C} (p : E ⟶ B) : E ⟶ cechTwo p :=
  Limits.pullback.diagonal p

@[simp] lemma diag_p1 {E B : C} (p : E ⟶ B) : diag p ≫ p1 p = 𝟙 E := by
  simp [diag, p1]

@[simp] lemma diag_p2 {E B : C} (p : E ⟶ B) : diag p ≫ p2 p = 𝟙 E := by
  simp [diag, p2]

/-- The key pullback condition: `p1 p ≫ p = p2 p ≫ p`. -/
lemma p1_comp_p_eq_p2_comp_p {E B : C} (p : E ⟶ B) : p1 p ≫ p = p2 p ≫ p := by
  simp only [p1, p2, Limits.pullback.condition]

/-!
## 3-fold overlap

The 3-fold overlap is defined as `pullback (p2 p) (p1 p)`, modeling *composable pairs*
of elements in the kernel pair. This choice ensures that the cocycle condition for
descent data has the natural form `ξ₂₃ ≫ ξ₁₂ = ξ₁₃` (composition in the Čech groupoid).
-/

/-- The Čech 3-fold overlap object `E ×_B E ×_B E` associated to `p : E ⟶ B`.

This is defined as `pullback (p2 p) (p1 p)`, which models composable pairs in the
kernel pair groupoid. An element can be thought of as `((e₁, e₂), (e₂, e₃))` where
the second component of the first pair equals the first component of the second pair. -/
abbrev cechThree {E B : C} (p : E ⟶ B) : C :=
  Limits.pullback (p2 p) (p1 p)

/-- The projection `E ×_B E ×_B E ⟶ E ×_B E` picking the `(1,2)`-coordinates.

For an element `((e₁, e₂), (e₂, e₃))`, this returns `(e₁, e₂)`. -/
abbrev p12 {E B : C} (p : E ⟶ B) : cechThree p ⟶ cechTwo p :=
  Limits.pullback.fst (f := p2 p) (g := p1 p)

/-- The projection `E ×_B E ×_B E ⟶ E ×_B E` picking the `(2,3)`-coordinates.

For an element `((e₁, e₂), (e₂, e₃))`, this returns `(e₂, e₃)`. -/
abbrev p23 {E B : C} (p : E ⟶ B) : cechThree p ⟶ cechTwo p :=
  Limits.pullback.snd (f := p2 p) (g := p1 p)

/-- The key condition for the triple overlap: `p12 ≫ p2 = p23 ≫ p1`. -/
@[simp] lemma p12_p2_eq_p23_p1 {E B : C} (p : E ⟶ B) :
    p12 p ≫ p2 p = p23 p ≫ p1 p := by
  simp only [p12, p23, Limits.pullback.condition]

/-- The projection `E ×_B E ×_B E ⟶ E ×_B E` picking the `(1,3)`-coordinates.

For an element `((e₁, e₂), (e₂, e₃))`, this returns `(e₁, e₃)`. This is the
"composition" map in the Čech groupoid structure. -/
abbrev p13 {E B : C} (p : E ⟶ B) : cechThree p ⟶ cechTwo p :=
  Limits.pullback.lift (p12 p ≫ p1 p) (p23 p ≫ p2 p) (by
    simp only [Category.assoc]
    calc p12 p ≫ (p1 p ≫ p) = p12 p ≫ (p2 p ≫ p) := by rw [p1_comp_p_eq_p2_comp_p]
      _ = (p12 p ≫ p2 p) ≫ p := by rw [Category.assoc]
      _ = (p23 p ≫ p1 p) ≫ p := by rw [p12_p2_eq_p23_p1]
      _ = p23 p ≫ (p1 p ≫ p) := by rw [← Category.assoc]
      _ = p23 p ≫ (p2 p ≫ p) := by rw [p1_comp_p_eq_p2_comp_p])

@[simp] lemma p13_p1 {E B : C} (p : E ⟶ B) :
    p13 p ≫ p1 p = p12 p ≫ p1 p := by
  simp [p13]

@[simp] lemma p13_p2 {E B : C} (p : E ⟶ B) :
    p13 p ≫ p2 p = p23 p ≫ p2 p := by
  simp [p13]

end

end Descent.Cech
