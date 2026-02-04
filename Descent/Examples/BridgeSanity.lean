/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor.Descent.CechDescentDataEquiv

/-!
# Examples: bridge sanity checks

This file contains low-level sanity checks for the bridge between fibered-category single-morphism
descent data and pseudofunctor Čech descent data for the pseudofunctor of fibers.

These tests aim to detect convention mismatches (e.g. swapped projections or reversed cocycle
convention) via definitional equalities and `simp`, without relying on the (currently partial)
equivalence packaging in `singleCechDescentDataEquiv`.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.Examples

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable {𝒜 : Type w} [Category.{v} 𝒜]
variable (pA : 𝒜 ⥤ C) [pA.IsFibered]
variable {E B : C} (p : E ⟶ B)

open Descent.FiberedCategory.Descent
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

abbrev F : CategoryTheory.Pseudofunctor (CategoryTheory.LocallyDiscrete Cᵒᵖ) Cat.{v, w} :=
  fibersPseudofunctor (pA := pA)

/-!
## Basic component checks
-/

example (D : SingleMorphismDescentData (pA := pA) p) :
    (singleToCechDescentData (pA := pA) p D).obj = D.obj :=
  rfl

example (D : SingleMorphismDescentData (pA := pA) p) :
    (singleToCechDescentData (pA := pA) p D).ξ = D.ξ.hom :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (cechToSingleDescentData (pA := pA) p D).obj = D.obj :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (cechToSingleDescentData (pA := pA) p D).ξ.hom = D.ξ :=
  rfl

/-!
## Round-trip checks (on `.obj` and `.ξ`)

These avoid any use of the (currently partial) `≌` data.
-/

example (D : SingleMorphismDescentData (pA := pA) p) :
    (cechToSingleDescentData (pA := pA) p (singleToCechDescentData (pA := pA) p D)).obj = D.obj :=
  rfl

example (D : SingleMorphismDescentData (pA := pA) p) :
    (cechToSingleDescentData (pA := pA) p (singleToCechDescentData (pA := pA) p D)).ξ.hom =
      D.ξ.hom :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (singleToCechDescentData (pA := pA) p (cechToSingleDescentData (pA := pA) p D)).obj = D.obj :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (singleToCechDescentData (pA := pA) p (cechToSingleDescentData (pA := pA) p D)).ξ = D.ξ :=
  rfl

/-!
## Round-trip checks (on morphisms)
-/

example {D D' : SingleMorphismDescentData (pA := pA) p} (f : D ⟶ D') :
    ((cechToSingleFunctor (pA := pA) p).map ((singleToCechFunctor (pA := pA) p).map f)).hom =
      f.hom :=
  rfl

example {D D' : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p} (f : D ⟶ D') :
    ((singleToCechFunctor (pA := pA) p).map ((cechToSingleFunctor (pA := pA) p).map f)).hom =
      f.hom :=
  rfl

/-!
## Comparison isomorphisms: fibered vs. pseudofunctor

For the pseudofunctor of fibers, the canonical comparison isomorphism `ξ` on `p^* a` should
definitionally agree with the fibered-category construction.
-/

example (a : Fiber pA B) :
    (Descent.Pseudofunctor.Descent.singleMorphismComparisonXi (F := F (pA := pA)) p a).hom =
      (singleMorphismComparisonXi (pA := pA) p a).hom :=
by
  classical
  -- Unfold the pseudofunctor comparison isomorphism and simplify the `Cat` wrappers.
  simp [Descent.Pseudofunctor.Descent.singleMorphismComparisonXi, singleMorphismComparisonXi,
    Descent.Pseudofunctor.reindexCompIsoObj, Descent.Pseudofunctor.reindexObjIsoOfEq,
    Descent.Pseudofunctor.reindex,
    CategoryTheory.FiberedCategory.pseudofunctorOfFibers, CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

/-!
## Compatibility of the induced morphisms on triple overlaps

For the pseudofunctor of fibers, the induced morphisms `xi12/xi23/xi13` should reduce to the
fibered-category ones (this catches swapped-projection or cocycle-convention mistakes).
-/

example {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi12 (F := F (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi12 (pA := pA) p ξ := by
  classical
  simp [Descent.Pseudofunctor.Descent.xi12, Descent.FiberedCategory.Descent.xi12, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

example {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi23 (F := F (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi23 (pA := pA) p ξ := by
  classical
  simp [Descent.Pseudofunctor.Descent.xi23, Descent.FiberedCategory.Descent.xi23, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

example {C₀ : Fiber pA E}
    (ξ :
      (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi13 (F := F (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi13 (pA := pA) p ξ := by
  classical
  simp [Descent.Pseudofunctor.Descent.xi13, Descent.FiberedCategory.Descent.xi13, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctorOfFibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

/-!
## Compatibility with Mathlib's singleton-family descent data (object component)
-/

example (D : SingleMorphismDescentData (pA := pA) p) :
    (Descent.Pseudofunctor.Descent.singleToSingletonDescentData (F := F (pA := pA)) p
          (singleToCechDescentData (pA := pA) p D)).obj PUnit.unit =
      D.obj :=
  rfl

end

end Descent.Examples
