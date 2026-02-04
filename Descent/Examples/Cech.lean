/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech.Eq

/-!
# Examples: Čech overlaps

Small `example`s that exercise the Čech overlap API (`simp`, `reassoc`) to catch regressions.
-/

open CategoryTheory

namespace Descent.Examples

open Descent.Cech

universe u v

section Cech

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {E B : C} (p : E ⟶ B)

example : diag p ≫ p1 p = 𝟙 E := by simp
example : diag p ≫ p2 p = 𝟙 E := by simp

example {X : C} (f : E ⟶ X) : diag p ≫ p1 p ≫ f = f := by simp
example {X : C} (f : E ⟶ X) : diag p ≫ p2 p ≫ f = f := by simp

example : p12 p ≫ p2 p = p23 p ≫ p1 p := by simp

end Cech

section Eq

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {E B : C} (p : E ⟶ B)

example : eqId p ≫ eqDom p = 𝟙 E := by simp
example : eqId p ≫ eqCod p = 𝟙 E := by simp

example {X : C} (f : E ⟶ X) : eqId p ≫ eqDom p ≫ f = f := by simp

/-!
Regression tests for the convention that the Čech triple overlap is the object of composable
pairs for `Eq(p)`, i.e. `cechTripleOverlap p = pullback (eqDom p) (eqCod p)`.
-/

example : cechTripleOverlap p = Limits.pullback (eqDom p) (eqCod p) := rfl

example : Limits.pullback.fst (eqDom p) (eqCod p) = p12 p := rfl

example : Limits.pullback.snd (eqDom p) (eqCod p) = p23 p := rfl

example : eqComp p ≫ p1 p = p12 p ≫ p1 p := by
  simp [eqComp, CategoryTheory.Cech.p13]

example : eqComp p ≫ p2 p = p23 p ≫ p2 p := by
  simp [eqComp, CategoryTheory.Cech.p13]

end Eq

end Descent.Examples
