/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Čech kernel pair conventions

Defines the Čech overlaps for a morphism `p : E ⟶ B` in a category with pullbacks.
We set `cechTripleOverlap p := pullback (p2 p) (p1 p)` so the cocycle reads
`ξ₂₃ ≫ ξ₁₂ = ξ₁₃`. Main definitions are `cechKernelPair`, `cechTripleOverlap` and the projections
`p1`, `p2`, `p12`, `p23`, `p13`, with basic lemmas about diagonals and projections.
-/

open CategoryTheory

namespace CategoryTheory.Cech

universe u v

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

noncomputable section

/-!
## 2-fold overlap (kernel pair)
-/

/-- The Čech 2-fold overlap object `E ×_B E` associated to `p : E ⟶ B`. -/
abbrev cechKernelPair {E B : C} (p : E ⟶ B) : C :=
  Limits.pullback.diagonalObj p

/-- The first projection `E ×_B E ⟶ E`. -/
abbrev p1 {E B : C} (p : E ⟶ B) : cechKernelPair p ⟶ E :=
  Limits.pullback.fst (f := p) (g := p)

/-- The second projection `E ×_B E ⟶ E`. -/
abbrev p2 {E B : C} (p : E ⟶ B) : cechKernelPair p ⟶ E :=
  Limits.pullback.snd (f := p) (g := p)

/-- The diagonal `E ⟶ E ×_B E`. -/
abbrev diag {E B : C} (p : E ⟶ B) : E ⟶ cechKernelPair p :=
  Limits.pullback.diagonal p

@[reassoc]
lemma diag_p1 {E B : C} (p : E ⟶ B) : diag p ≫ p1 p = 𝟙 E := by
  simp [diag, p1]

@[reassoc]
lemma diag_p2 {E B : C} (p : E ⟶ B) : diag p ≫ p2 p = 𝟙 E := by
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
abbrev cechTripleOverlap {E B : C} (p : E ⟶ B) : C :=
  Limits.pullback (p2 p) (p1 p)

/-- The projection `E ×_B E ×_B E ⟶ E ×_B E` picking the `(1,2)`-coordinates.

For an element `((e₁, e₂), (e₂, e₃))`, this returns `(e₁, e₂)`. -/
abbrev p12 {E B : C} (p : E ⟶ B) : cechTripleOverlap p ⟶ cechKernelPair p :=
  Limits.pullback.fst (f := p2 p) (g := p1 p)

/-- The projection `E ×_B E ×_B E ⟶ E ×_B E` picking the `(2,3)`-coordinates.

For an element `((e₁, e₂), (e₂, e₃))`, this returns `(e₂, e₃)`. -/
abbrev p23 {E B : C} (p : E ⟶ B) : cechTripleOverlap p ⟶ cechKernelPair p :=
  Limits.pullback.snd (f := p2 p) (g := p1 p)

/-- The key condition for the triple overlap: `p12 ≫ p2 = p23 ≫ p1`. -/
@[simp, reassoc] lemma p12_p2_eq_p23_p1 {E B : C} (p : E ⟶ B) :
    p12 p ≫ p2 p = p23 p ≫ p1 p := by
  simp only [p12, p23, Limits.pullback.condition]

/-!
### Coordinate projections on the triple overlap

These are the maps `E ×_B E ×_B E ⟶ E` picking out the 1st/2nd/3rd component. They are defined in
terms of `p12`, `p23`, `p1`, `p2`. We avoid adding simp lemmas for their definitional unfoldings, as
these can easily create simp loops; use `p12_p2_eq_p23_p1` to rewrite between the two expressions
for the middle projection (`p12 ≫ p2` vs `p23 ≫ p1`) when needed.
-/

/-- The `(1)`-coordinate projection `E ×_B E ×_B E ⟶ E`. -/
abbrev p1Triple {E B : C} (p : E ⟶ B) : cechTripleOverlap p ⟶ E :=
  p12 p ≫ p1 p

/-- The `(2)`-coordinate projection `E ×_B E ×_B E ⟶ E`. -/
abbrev p2Triple {E B : C} (p : E ⟶ B) : cechTripleOverlap p ⟶ E :=
  p12 p ≫ p2 p

/-- The `(3)`-coordinate projection `E ×_B E ×_B E ⟶ E`. -/
abbrev p3Triple {E B : C} (p : E ⟶ B) : cechTripleOverlap p ⟶ E :=
  p23 p ≫ p2 p

/-- The projection `E ×_B E ×_B E ⟶ E ×_B E` picking the `(1,3)`-coordinates.

For an element `((e₁, e₂), (e₂, e₃))`, this returns `(e₁, e₃)`. This is the
"composition" map in the Čech groupoid structure. -/
abbrev p13 {E B : C} (p : E ⟶ B) : cechTripleOverlap p ⟶ cechKernelPair p :=
  Limits.pullback.lift (p12 p ≫ p1 p) (p23 p ≫ p2 p) (by
    simp only [Category.assoc]
    calc
      p12 p ≫ p1 p ≫ p = p12 p ≫ p2 p ≫ p := by simp [p1_comp_p_eq_p2_comp_p]
      _ = p23 p ≫ p1 p ≫ p := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ p) (p12_p2_eq_p23_p1 p)
      _ = p23 p ≫ p2 p ≫ p := by simp [p1_comp_p_eq_p2_comp_p])

@[reassoc]
lemma p13_p1 {E B : C} (p : E ⟶ B) :
    p13 p ≫ p1 p = p12 p ≫ p1 p := by
  simp [p13]

@[reassoc]
lemma p13_p2 {E B : C} (p : E ⟶ B) :
    p13 p ≫ p2 p = p23 p ≫ p2 p := by
  simp [p13]

end

end CategoryTheory.Cech
