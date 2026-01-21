/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.CategoryTheory.InternalCategory.Basic

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

In addition, in §3.1 the paper considers the internal functor `p̄ : Eq(p) ⟶ B`. We do not have a
general internal-category API in Mathlib, but we record the underlying morphism of objects and
morphisms:
- `pbarObj p := p`
- `pbarHom p := π₁ ≫ p` (which equals `π₂ ≫ p`)

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
## The internal functor `p̄ : Eq(p) ⟶ B`

The paper defines an internal functor `p̄ : Eq(p) ⟶ B` with
`p̄₀ = p` and `p̄₁ = π₁ ≫ p = π₂ ≫ p`.

Since Mathlib does not currently provide a bundled internal-category theory, we only record the
object part and the map on morphisms of this functor.
-/

/-- The object map of the internal functor `p̄ : Eq(p) ⟶ B` (paper §3.1). -/
abbrev pbarObj : E ⟶ B := p

/-- The map on morphisms of the internal functor `p̄ : Eq(p) ⟶ B` (paper §3.1).

This is `π₁ ≫ p` (which equals `π₂ ≫ p`). -/
abbrev pbarHom : eqHom p ⟶ B := eqCod p ≫ p

@[reassoc]
lemma pbarHom_eq_eqDom_comp : pbarHom p = eqDom p ≫ p := by
  -- Both composites are the canonical map `E ×_B E ⟶ B`.
  simpa [pbarHom, eqCod, eqDom] using (p1_comp_p_eq_p2_comp_p p)

@[reassoc]
lemma eqCod_comp_pbarObj : eqCod p ≫ pbarObj p = pbarHom p := by
  rfl

@[reassoc]
lemma eqDom_comp_pbarObj : eqDom p ≫ pbarObj p = pbarHom p := by
  -- Rewrite `pbarHom` via the other projection.
  simpa [pbarObj] using (pbarHom_eq_eqDom_comp (p := p)).symm

/-!
## The diagonal `δ : E ⟶ Eq(p)`

In §3.1, the paper also records the diagonal internal functor `δ : E ⟶ Eq(p)` from the discrete
internal category on `E`, with `δ₀ = 1_E` and `δ₁ = e`.

Since we do not yet have a bundled internal-category functor API, we record its object and morphism
maps and the resulting factorization of `p` through `p̄`.
-/

/-- The object map of the diagonal `δ : E ⟶ Eq(p)` (paper §3.1). -/
abbrev deltaObj : E ⟶ E := 𝟙 E

/-- The map on morphisms of the diagonal `δ : E ⟶ Eq(p)` (paper §3.1).

This is the diagonal `e : E ⟶ E ×_B E`. -/
abbrev deltaHom : E ⟶ eqHom p := eqId p

omit [Limits.HasPullbacks C] in
@[reassoc]
lemma deltaObj_comp_pbarObj : deltaObj ≫ pbarObj p = p := by
  simp [deltaObj, pbarObj]

@[reassoc]
lemma deltaHom_comp_pbarHom : deltaHom p ≫ pbarHom p = p := by
  simp [deltaHom, pbarHom, eqId, eqCod]

/-!
## Basic identities
-/

@[reassoc]
lemma eqId_comp_eqDom : eqId p ≫ eqDom p = 𝟙 E := by
  simp [eqId, eqDom]

@[reassoc]
lemma eqId_comp_eqCod : eqId p ≫ eqCod p = 𝟙 E := by
  simp [eqId, eqCod]

@[reassoc]
lemma eqComp_comp_eqCod : eqComp p ≫ eqCod p = p12 p ≫ eqCod p := by
  simp [eqComp, eqCod]

@[reassoc]
lemma eqComp_comp_eqDom : eqComp p ≫ eqDom p = p23 p ≫ eqDom p := by
  simp [eqComp, eqDom]

/-- The equivalence relation induced by `p` is its kernel pair (paper §3.1). -/
lemma isKernelPair_eqCod_eqDom : CategoryTheory.IsKernelPair p (eqCod p) (eqDom p) := by
  simpa [eqCod, eqDom, p1, p2, cechKernelPair] using
    (CategoryTheory.Limits.pullback.diagonal_isKernelPair (f := p))

/-- The internal category `Eq(p)` (Facets of Descent, II, §3.1). -/
noncomputable def eqInternalCategory : CategoryTheory.InternalCategory (C := C) where
  obj := E
  hom := eqHom p
  dom := eqDom p
  cod := eqCod p
  id := eqId p
  comp := eqComp p
  id_comp_dom := eqId_comp_eqDom (p := p)
  id_comp_cod := eqId_comp_eqCod (p := p)
  comp_comp_dom := by
    rw [eqComp_comp_eqDom (p := p)]
  comp_comp_cod := by
    rw [eqComp_comp_eqCod (p := p)]
  comp_id := by
    apply Limits.pullback.hom_ext <;> simp [Category.assoc, eqComp, eqCod, eqDom, eqId]
  id_comp := by
    apply Limits.pullback.hom_ext <;> simp [Category.assoc, eqComp, eqCod, eqDom, eqId]
  assoc := by
    apply Limits.pullback.hom_ext <;> simp [Category.assoc, eqComp, eqCod, eqDom]

end

end

end Descent.Cech
