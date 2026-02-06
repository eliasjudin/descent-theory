/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.SingleMorphism

/-!
# The comparison functor for fibered-category descent data

Let `pA : 𝒜 ⥤ C` be a fibered functor and `p : E ⟶ B` a morphism in the base category.

This file defines the comparison functor
`Φₚ : Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p`
which sends an object `a` over `B` to its pullback `p^* a` over `E`, equipped with the canonical
descent isomorphism on `E ×_B E`.

We also introduce the standard predicates `IsDescentMorphism` and `IsEffectiveDescentMorphism`,
defined in terms of this functor.

Some proofs are left as `sorry` (unit/cocycle axioms and naturality), since they amount to
standard coherence lemmas for pullback/reindexing isomorphisms.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.FiberedCategory.Descent

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜]

noncomputable section

open Descent.FiberedCategory
open Descent.Cech

variable (pA : 𝒜 ⥤ C) [pA.IsFibered]

section HasPullbacks

variable [Limits.HasPullbacks C]

variable {E B : C} (p : E ⟶ B)

/-- Unit coherence for the canonical comparison descent datum on `p^* a`. -/
private lemma single_morphism_comparison_unit (a : Fiber pA B) :
    (diag_iso_p2 (pA := pA) p ((reindex (pA := pA) p).obj a)).inv ≫
        (reindex (pA := pA) (Limits.pullback.diagonal p)).map
          (single_morphism_comparison_xi (pA := pA) p a).hom ≫
          (diag_iso_p1 (pA := pA) p ((reindex (pA := pA) p).obj a)).hom =
      𝟙 ((reindex (pA := pA) p).obj a) := by
  -- Checklist: `ξ` is oriented as `π₂^* (p^* a) ⟶ π₁^* (p^* a)` and unit is along `diag`.
  sorry

/-- Cocycle coherence for the canonical comparison descent datum on `p^* a`. -/
private lemma single_morphism_comparison_cocycle (a : Fiber pA B) :
    xi23 (pA := pA) p (single_morphism_comparison_xi (pA := pA) p a) ≫
        xi12 (pA := pA) p (single_morphism_comparison_xi (pA := pA) p a) =
      xi13 (pA := pA) p (single_morphism_comparison_xi (pA := pA) p a) := by
  -- Checklist: cocycle convention is exactly `ξ₂₃ ≫ ξ₁₂ = ξ₁₃`.
  sorry

/-- Naturality of the canonical comparison isomorphism `ξ` under reindexing along `p`. -/
private lemma single_morphism_comparison_naturality {a b : Fiber pA B} (f : a ⟶ b) :
    (single_morphism_comparison_xi (pA := pA) p a).hom ≫
        (reindex (pA := pA) (p1 p)).map ((reindex (pA := pA) p).map f) =
      (reindex (pA := pA) (p2 p)).map ((reindex (pA := pA) p).map f) ≫
        (single_morphism_comparison_xi (pA := pA) p b).hom := by
  -- Checklist: source/target agree with the fixed pullback leg conventions `p12`, `p23`, `p13`.
  sorry

/-- The canonical descent data on the pullback `p^* a`. -/
noncomputable def single_morphism_comparison_descent_data (a : Fiber pA B) :
    SingleMorphismDescentData (pA := pA) p where
  obj := (reindex (pA := pA) p).obj a
  ξ := single_morphism_comparison_xi (pA := pA) p a
  unit := by
    simpa using single_morphism_comparison_unit (pA := pA) (p := p) a
  cocycle := by
    simpa using single_morphism_comparison_cocycle (pA := pA) (p := p) a

/-- The comparison functor `Φₚ : Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p`. -/
noncomputable def single_morphism_comparison_functor :
    Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p where
  obj a := single_morphism_comparison_descent_data (pA := pA) p a
  map {a b} f :=
    { hom := (reindex (pA := pA) p).map f
      comm := by
        simpa [single_morphism_comparison_descent_data] using
          single_morphism_comparison_naturality (pA := pA) (p := p) f }
  map_id a := by
    apply SingleMorphismDescentData.Hom.ext (pA := pA)
    -- Unfold the identity in the target category to access the simp lemma `Hom.id_hom`.
    change (reindex (pA := pA) p).map (𝟙 a) =
      (SingleMorphismDescentData.Hom.id (pA := pA)
          (single_morphism_comparison_descent_data (pA := pA) p a)).hom
    simp
    rfl
  map_comp {a b c} f g := by
    apply SingleMorphismDescentData.Hom.ext (pA := pA)
    let DX := single_morphism_comparison_descent_data (pA := pA) p a
    let DY := single_morphism_comparison_descent_data (pA := pA) p b
    let DZ := single_morphism_comparison_descent_data (pA := pA) p c
    let f' : SingleMorphismDescentData.Hom (pA := pA) DX DY :=
      { hom := (reindex (pA := pA) p).map f
        comm := by
          simpa [DX, DY, single_morphism_comparison_descent_data] using
            single_morphism_comparison_naturality (pA := pA) (p := p) f }
    let g' : SingleMorphismDescentData.Hom (pA := pA) DY DZ :=
      { hom := (reindex (pA := pA) p).map g
        comm := by
          simpa [DY, DZ, single_morphism_comparison_descent_data] using
            single_morphism_comparison_naturality (pA := pA) (p := p) g }
    change (reindex (pA := pA) p).map (f ≫ g) =
      (SingleMorphismDescentData.Hom.comp (pA := pA)
          (D₁ := DX) (D₂ := DY) (D₃ := DZ) f' g').hom
    simp [f', g']

/-- `p` is a descent morphism for `pA` if `Φₚ` is fully faithful. -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (single_morphism_comparison_functor (pA := pA) p).FullyFaithful

/-- `p` is an effective descent morphism for `pA` if `Φₚ` is an equivalence. -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (single_morphism_comparison_functor (pA := pA) p).IsEquivalence

end HasPullbacks

end

end Descent.FiberedCategory.Descent
