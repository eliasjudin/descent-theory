/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.SingleMorphism
import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.CategoryTheory.FiberedCategory.PseudofunctorOfFibers

/-!
# Relating fibered-category and pseudofunctor descent data

Let `pA : 𝒜 ⥤ C` be a fibered functor. The associated pseudofunctor of fibers
`CategoryTheory.FiberedCategory.pseudofunctorOfFibers (pA := pA)` sends `S : C` to the fiber
category `Fiber pA S` and a morphism `f : R ⟶ S` to the reindexing functor `f^*`.

This repository contains two Čech-style descent data notions along a single morphism `p : E ⟶ B`:

* `Descent.FiberedCategory.Descent.SingleMorphismDescentData (pA := pA) p` for fibered categories,
  where the gluing map is stored as an isomorphism.
* `Descent.Pseudofunctor.Descent.CechDescentData (F := F) p` for pseudofunctors
  `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, where the gluing map is stored as a morphism.

In the case `F = pseudofunctorOfFibers pA`, these two categories should be equivalent. This file
provides the comparison functors and records the expected equivalence. Some proofs are left as
`sorry`, since relating the two sets of coherence isomorphisms requires additional (standard)
cleavage-coherence lemmas.

The object-level conversions `singleToCechDescentData` and `cechToSingleDescentData` are fully
proved (including the unit and cocycle conditions). The remaining `sorry`s are only for packaging
the `≌` data (`unitIso`, `counitIso`, and the triangle identity).
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.FiberedCategory.Descent

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜]

noncomputable section

open Opposite

variable (pA : 𝒜 ⥤ C) [pA.IsFibered]

/-- The pseudofunctor of fibers associated to a fibered functor `pA : 𝒜 ⥤ C`. -/
abbrev fibersPseudofunctor :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, w} :=
  CategoryTheory.FiberedCategory.pseudofunctorOfFibers (pA := pA)

@[simp]
lemma fibersPseudofunctor_reindex {R S : C} (f : R ⟶ S) :
    Descent.Pseudofunctor.reindex (F := fibersPseudofunctor (pA := pA)) f =
      Descent.FiberedCategory.reindex (pA := pA) f := by
  rfl

section HasPullbacks

variable [Limits.HasPullbacks C]

variable {E B : C} (p : E ⟶ B)

open Descent.Cech
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private lemma xi12_fibers {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi12 (F := fibersPseudofunctor (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi12 (pA := pA) p ξ := by
  classical
  simp [Descent.Pseudofunctor.Descent.xi12, Descent.FiberedCategory.Descent.xi12, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

private lemma xi23_fibers {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi23 (F := fibersPseudofunctor (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi23 (pA := pA) p ξ := by
  classical
  simp [Descent.Pseudofunctor.Descent.xi23, Descent.FiberedCategory.Descent.xi23, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

private lemma xi13_fibers {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi13 (F := fibersPseudofunctor (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi13 (pA := pA) p ξ := by
  classical
  simp [Descent.Pseudofunctor.Descent.xi13, Descent.FiberedCategory.Descent.xi13, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

/-- Turn fibered-category descent data into pseudofunctor Čech descent data. -/
noncomputable def singleToCechDescentData
    (D : SingleMorphismDescentData (pA := pA) p) :
    Descent.Pseudofunctor.Descent.CechDescentData (F := fibersPseudofunctor (pA := pA)) p where
  obj := D.obj
  ξ := D.ξ.hom
  unit := by
    -- The diagonal isomorphisms for the pseudofunctor of fibers reduce to the fibered-category ones.
    simpa [Descent.Pseudofunctor.Descent.diagIsoP1, Descent.Pseudofunctor.Descent.diagIsoP2,
      Descent.FiberedCategory.Descent.diagIsoP1, Descent.FiberedCategory.Descent.diagIsoP2,
      Descent.Pseudofunctor.reindex, CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
      CategoryTheory.pseudofunctorOfIsLocallyDiscrete] using D.unit
  cocycle := by
    simpa [xi12_fibers (pA := pA) (p := p), xi23_fibers (pA := pA) (p := p),
      xi13_fibers (pA := pA) (p := p)] using D.cocycle

/-- Turn pseudofunctor Čech descent data into fibered-category descent data. -/
noncomputable def cechToSingleDescentData
    (D : Descent.Pseudofunctor.Descent.CechDescentData (F := fibersPseudofunctor (pA := pA)) p) :
    SingleMorphismDescentData (pA := pA) p := by
  classical
  -- The Čech axioms imply `IsIso D.ξ` (see `Descent.Pseudofunctor.Descent.CechDescentData`).
  haveI : IsIso D.ξ := by
    infer_instance
  refine
    { obj := D.obj
      ξ := asIso D.ξ
      unit := by
        -- The diagonal isomorphisms for the pseudofunctor of fibers reduce to the fibered-category ones.
        simpa [Descent.Pseudofunctor.Descent.diagIsoP1, Descent.Pseudofunctor.Descent.diagIsoP2,
          Descent.FiberedCategory.Descent.diagIsoP1, Descent.FiberedCategory.Descent.diagIsoP2,
          Descent.Pseudofunctor.reindex, CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
          CategoryTheory.pseudofunctorOfIsLocallyDiscrete] using D.unit
      cocycle := by
        -- Rewrite `D.cocycle` to use the isomorphism `ξIso := asIso D.ξ` explicitly.
        let ξIso : (Descent.FiberedCategory.reindex (pA := pA) (p2 p)).obj D.obj ≅
            (Descent.FiberedCategory.reindex (pA := pA) (p1 p)).obj D.obj :=
          asIso D.ξ
        have hc :
            Descent.Pseudofunctor.Descent.xi23 (F := fibersPseudofunctor (pA := pA)) p ξIso.hom ≫
                Descent.Pseudofunctor.Descent.xi12 (F := fibersPseudofunctor (pA := pA)) p ξIso.hom =
              Descent.Pseudofunctor.Descent.xi13 (F := fibersPseudofunctor (pA := pA)) p ξIso.hom := by
          simpa [ξIso] using D.cocycle
        -- Translate each term to the fibered-category expression.
        simpa [xi12_fibers (pA := pA) (p := p), xi23_fibers (pA := pA) (p := p),
          xi13_fibers (pA := pA) (p := p)] using hc }

/-- The functor from fibered-category descent data to pseudofunctor Čech descent data. -/
noncomputable def singleToCechFunctor :
    SingleMorphismDescentData (pA := pA) p ⥤
      Descent.Pseudofunctor.Descent.CechDescentData (F := fibersPseudofunctor (pA := pA)) p where
  obj D := singleToCechDescentData (pA := pA) p D
  map {D D'} f :=
    { hom := f.hom
      comm := by
        -- The commutativity condition is definitionally the same after unfolding `ξ`.
        simpa [singleToCechDescentData, fibersPseudofunctor_reindex] using f.comm }
  map_id D := by
    apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
    -- Unfold the identity in the source and target categories.
    change (SingleMorphismDescentData.Hom.id (pA := pA) D).hom =
      (Descent.Pseudofunctor.Descent.CechDescentData.Hom.id (singleToCechDescentData (pA := pA) p D)).hom
    simp [singleToCechDescentData]
  map_comp {X Y Z} f g := by
    apply Descent.Pseudofunctor.Descent.CechDescentData.Hom.ext
    -- Make the mapped morphisms explicit so that `Hom.comp_hom` applies without typeclass noise.
    let f' :
        Descent.Pseudofunctor.Descent.CechDescentData.Hom
          (singleToCechDescentData (pA := pA) p X) (singleToCechDescentData (pA := pA) p Y) :=
      { hom := f.hom
        comm := by
          simpa [singleToCechDescentData, fibersPseudofunctor_reindex] using f.comm }
    let g' :
        Descent.Pseudofunctor.Descent.CechDescentData.Hom
          (singleToCechDescentData (pA := pA) p Y) (singleToCechDescentData (pA := pA) p Z) :=
      { hom := g.hom
        comm := by
          simpa [singleToCechDescentData, fibersPseudofunctor_reindex] using g.comm }
    change (SingleMorphismDescentData.Hom.comp (pA := pA) f g).hom = (f'.comp g').hom
    simp [f', g']

/-- The functor from pseudofunctor Čech descent data to fibered-category descent data. -/
noncomputable def cechToSingleFunctor :
    Descent.Pseudofunctor.Descent.CechDescentData (F := fibersPseudofunctor (pA := pA)) p ⥤
      SingleMorphismDescentData (pA := pA) p where
  obj D := cechToSingleDescentData (pA := pA) p D
  map {D D'} f :=
    { hom := f.hom
      comm := by
        -- `asIso` does not change the underlying morphism, and reindexing for `fibersPseudofunctor`
        -- agrees with fibered-category reindexing.
        simpa [fibersPseudofunctor_reindex] using f.comm }
  map_id D := by
    apply SingleMorphismDescentData.Hom.ext (pA := pA)
    -- Unfold the identity in the source and target categories.
    change (Descent.Pseudofunctor.Descent.CechDescentData.Hom.id D).hom =
      (SingleMorphismDescentData.Hom.id (pA := pA) (cechToSingleDescentData (pA := pA) p D)).hom
    simp [cechToSingleDescentData]
  map_comp {X Y Z} f g := by
    apply SingleMorphismDescentData.Hom.ext (pA := pA)
    -- Make the mapped morphisms explicit so that `Hom.comp_hom` applies without typeclass noise.
    let f' :
        SingleMorphismDescentData.Hom (pA := pA)
          (cechToSingleDescentData (pA := pA) p X) (cechToSingleDescentData (pA := pA) p Y) :=
      { hom := f.hom
        comm := by
          simpa [fibersPseudofunctor_reindex, cechToSingleDescentData] using f.comm }
    let g' :
        SingleMorphismDescentData.Hom (pA := pA)
          (cechToSingleDescentData (pA := pA) p Y) (cechToSingleDescentData (pA := pA) p Z) :=
      { hom := g.hom
        comm := by
          simpa [fibersPseudofunctor_reindex, cechToSingleDescentData] using g.comm }
    change (Descent.Pseudofunctor.Descent.CechDescentData.Hom.comp f g).hom = (f'.comp g').hom
    simp [f', g']

/-- The expected equivalence between fibered-category and pseudofunctor Čech descent data. -/
noncomputable def singleCechDescentDataEquiv :
    SingleMorphismDescentData (pA := pA) p ≌
      Descent.Pseudofunctor.Descent.CechDescentData (F := fibersPseudofunctor (pA := pA)) p := by
  classical
  refine
    { functor := singleToCechFunctor (pA := pA) p
      inverse := cechToSingleFunctor (pA := pA) p
      unitIso := by
        -- TODO: construct the unit isomorphism explicitly.
        -- One expects the identity on the underlying fiber object, after identifying the
        -- coherence isomorphisms used in the two descent-data structures.
        sorry
      counitIso := by
        -- TODO: construct the counit isomorphism explicitly.
        sorry
      functor_unitIso_comp := by
        -- TODO: triangle identity.
        sorry }

end HasPullbacks

end

end Descent.FiberedCategory.Descent
