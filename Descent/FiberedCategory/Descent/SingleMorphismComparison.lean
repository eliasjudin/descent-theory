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

variable (pA : 𝒜 ⥤ C) [pA.IsFibered]

section HasPullbacks

variable [Limits.HasPullbacks C]

variable {E B : C} (p : E ⟶ B)

/-- The canonical descent data on the pullback `p^* a`. -/
noncomputable def single_morphism_comparison_descent_data (a : Fiber pA B) :
    SingleMorphismDescentData (pA := pA) p where
  obj := (reindex (pA := pA) p).obj a
  ξ := single_morphism_comparison_xi (pA := pA) p a
  unit := by
    -- TODO: prove the unit axiom using the defining equation `p1 ≫ p = p2 ≫ p` and the
    -- coherence isomorphisms for `reindex`.
    sorry
  cocycle := by
    -- TODO: prove the cocycle axiom on triple overlaps using the associativity coherence for
    -- `reindexCompIsoObj` and the naturality of `reindexObjIsoOfEq`.
    sorry

/-- The comparison functor `Φₚ : Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p`. -/
noncomputable def single_morphism_comparison_functor :
    Fiber pA B ⥤ SingleMorphismDescentData (pA := pA) p where
  obj a := single_morphism_comparison_descent_data (pA := pA) p a
  map {a b} f :=
    { hom := (reindex (pA := pA) p).map f
      comm := by
        -- TODO: naturality of `single_morphism_comparison_xi`.
        -- This follows from naturality of `reindexCompIsoObj` and `reindexObjIsoOfEq`.
        sorry }
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
    -- We only care about the underlying morphism in the fiber over `E`.
    -- Make the source/target descent data explicit so that the `Hom.comp_hom` simp lemma applies.
    let DX := single_morphism_comparison_descent_data (pA := pA) p a
    let DY := single_morphism_comparison_descent_data (pA := pA) p b
    let DZ := single_morphism_comparison_descent_data (pA := pA) p c
    -- Unfold categorical composition as `Hom.comp`.
    change (reindex (pA := pA) p).map (f ≫ g) =
      (SingleMorphismDescentData.Hom.comp (pA := pA)
          (D₁ := DX) (D₂ := DY) (D₃ := DZ)
          { hom := (reindex (pA := pA) p).map f, comm := by
              -- TODO: naturality of `single_morphism_comparison_xi`.
              sorry }
          { hom := (reindex (pA := pA) p).map g, comm := by
              -- TODO: naturality of `single_morphism_comparison_xi`.
              sorry }).hom
    simp

/-- `p` is a descent morphism for `pA` if `Φₚ` is fully faithful. -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (single_morphism_comparison_functor (pA := pA) p).FullyFaithful

/-- `p` is an effective descent morphism for `pA` if `Φₚ` is an equivalence. -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (single_morphism_comparison_functor (pA := pA) p).IsEquivalence

end HasPullbacks

end

end Descent.FiberedCategory.Descent
