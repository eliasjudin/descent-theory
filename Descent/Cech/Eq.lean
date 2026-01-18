/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech

/-!
# The Čech groupoid `Eq(p)`

In *Facets of Descent, II* (§3.1), a morphism `p : E ⟶ B` in a category with pullbacks induces an
internal category `Eq(p)` whose object of objects is `E` and whose object of morphisms is the kernel
pair `E ×_B E`.

This file records the corresponding (Čech) data:
- `eqHom p := E ×_B E`
- `eqDom p := π₂`, `eqCod p := π₁`
- `eqId p := Δ : E ⟶ E ×_B E`
- `eqComp p := π₁₃ : E ×_B E ×_B E ⟶ E ×_B E`

We do not develop a general internal-category API here; this file only provides the basic maps and
identities needed elsewhere in the library.
-/

open CategoryTheory

namespace Descent.Cech

universe u v

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]

noncomputable section

section

variable {E B : C} (p : E ⟶ B)

/-!
## Structure maps
-/

/-- The object of morphisms of `Eq(p)`, i.e. `E ×_B E`. -/
abbrev eqHom : C := cechKernelPair p

/-- The domain map of `Eq(p)` (paper notation: `d := π₂`). -/
abbrev eqDom : eqHom p ⟶ E := p2 p

/-- The codomain map of `Eq(p)` (paper notation: `c := π₁`). -/
abbrev eqCod : eqHom p ⟶ E := p1 p

/-- The identity map of `Eq(p)` (paper notation: `e`). -/
abbrev eqId : E ⟶ eqHom p := diag p

/-- The object of composable pairs in `Eq(p)`, i.e. `E ×_B E ×_B E`. -/
abbrev eqCompObj : C := cechTripleOverlap p

/-- The composition map of `Eq(p)` (paper notation: `m := π₁,₃`). -/
abbrev eqComp : eqCompObj p ⟶ eqHom p := p13 p

/-!
## Basic identities
-/

@[simp, reassoc]
lemma eqId_comp_eqDom : eqId p ≫ eqDom p = 𝟙 E := by
  simp [eqId, eqDom]

@[simp, reassoc]
lemma eqId_comp_eqCod : eqId p ≫ eqCod p = 𝟙 E := by
  simp [eqId, eqCod]

@[simp, reassoc]
lemma eqComp_comp_eqCod : eqComp p ≫ eqCod p = p12 p ≫ eqCod p := by
  simp [eqComp, eqCod]

@[simp, reassoc]
lemma eqComp_comp_eqDom : eqComp p ≫ eqDom p = p23 p ≫ eqDom p := by
  simp [eqComp, eqDom]

/-- The equivalence relation induced by `p` is its kernel pair (paper §3.1). -/
lemma isKernelPair_eqCod_eqDom : CategoryTheory.IsKernelPair p (eqCod p) (eqDom p) := by
  simpa [eqCod, eqDom, p1, p2, cechKernelPair] using
    (CategoryTheory.Limits.pullback.diagonal_isKernelPair (f := p))

end

end

end Descent.Cech
