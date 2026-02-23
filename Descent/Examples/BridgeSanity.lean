/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.FiberedCategory.Descent.SingleMorphismComparison
import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.Pseudofunctor.Descent.CechDescentData.Equiv

/-!
# Examples: bridge sanity checks

Low-level checks for the bridge between fibered and pseudofunctor descent data.
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
  fibers_pseudofunctor (pA := pA)

/-!
## Basic component checks
-/

example (D : SingleMorphismDescentData (pA := pA) p) :
    (single_to_cech_descent_data (pA := pA) p D).obj = D.obj :=
  rfl

example (D : SingleMorphismDescentData (pA := pA) p) :
    (single_to_cech_descent_data (pA := pA) p D).ξ = D.ξ.hom :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (cech_to_single_descent_data (pA := pA) p D).obj = D.obj :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (cech_to_single_descent_data (pA := pA) p D).ξ.hom = D.ξ :=
  rfl

/-!
## Round-trip checks (on `.obj` and `.ξ`)
-/

example (D : SingleMorphismDescentData (pA := pA) p) :
    (cech_to_single_descent_data (pA := pA) p
          (single_to_cech_descent_data (pA := pA) p D)).obj =
      D.obj :=
  rfl

example (D : SingleMorphismDescentData (pA := pA) p) :
    (cech_to_single_descent_data (pA := pA) p
          (single_to_cech_descent_data (pA := pA) p D)).ξ.hom =
        D.ξ.hom :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (single_to_cech_descent_data (pA := pA) p
          (cech_to_single_descent_data (pA := pA) p D)).obj =
      D.obj :=
  rfl

example (D : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p) :
    (single_to_cech_descent_data (pA := pA) p
          (cech_to_single_descent_data (pA := pA) p D)).ξ =
      D.ξ :=
  rfl

/-!
## Round-trip checks (on morphisms)
-/

example {D D' : SingleMorphismDescentData (pA := pA) p} (f : D ⟶ D') :
    ((cech_to_single_functor (pA := pA) p).map ((single_to_cech_functor (pA := pA) p).map f)).hom =
      f.hom :=
  rfl

example {D D' : Descent.Pseudofunctor.Descent.CechDescentData (F := F (pA := pA)) p} (f : D ⟶ D') :
    ((single_to_cech_functor (pA := pA) p).map ((cech_to_single_functor (pA := pA) p).map f)).hom =
      f.hom :=
  rfl

/-!
## Comparison isomorphisms: fibered vs. pseudofunctor
-/

example (a : Fiber pA B) :
    (Descent.Pseudofunctor.Descent.single_morphism_comparison_xi (F := F (pA := pA)) p a).hom =
      (single_morphism_comparison_xi (pA := pA) p a).hom :=
by
  simp [Descent.Pseudofunctor.Descent.single_morphism_comparison_xi, single_morphism_comparison_xi,
    Descent.Pseudofunctor.reindex_comp_iso_obj, Descent.Pseudofunctor.reindex_obj_iso_of_eq,
    Descent.Pseudofunctor.reindex,
    CategoryTheory.FiberedCategory.pseudofunctor_of_fibers, CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

/-!
## Compatibility of induced morphisms on triple overlaps
-/

example {C₀ : Fiber pA E}
    (ξ :
    (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi12 (F := F (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi12 (pA := pA) p ξ := by
  simp [Descent.Pseudofunctor.Descent.xi12, Descent.FiberedCategory.Descent.xi12, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

example {C₀ : Fiber pA E}
    (ξ :
    (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi23 (F := F (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi23 (pA := pA) p ξ := by
  simp [Descent.Pseudofunctor.Descent.xi23, Descent.FiberedCategory.Descent.xi23, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

example {C₀ : Fiber pA E}
    (ξ :
    (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p2 p)).obj C₀ ≅
        (Descent.FiberedCategory.reindex (pA := pA) (Descent.Cech.p1 p)).obj C₀) :
    Descent.Pseudofunctor.Descent.xi13 (F := F (pA := pA)) p ξ.hom =
      Descent.FiberedCategory.Descent.xi13 (pA := pA) p ξ := by
  simp [Descent.Pseudofunctor.Descent.xi13, Descent.FiberedCategory.Descent.xi13, pullHom,
    CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.FiberedCategory.pseudofunctor_of_fibers,
    CategoryTheory.pseudofunctorOfIsLocallyDiscrete]

/-!
## Compatibility with singleton-family descent data (object component)
-/

example (D : SingleMorphismDescentData (pA := pA) p) :
    (Descent.Pseudofunctor.Descent.single_to_singleton_descent_data (F := F (pA := pA)) p
          (single_to_cech_descent_data (pA := pA) p D)).obj PUnit.unit =
      D.obj :=
  rfl

/-!
## Fibered ↔ pseudofunctor criteria checks
-/

example :
    IsDescentMorphism (pA := pA) p ↔
      Descent.Pseudofunctor.Descent.IsDescentMorphism (F := F (pA := pA)) p := by
  simpa using
    (is_descent_morphism_iff_pseudofunctor_is_descent_morphism (pA := pA) (p := p))

example :
    IsEffectiveDescentMorphism (pA := pA) p ↔
      Descent.Pseudofunctor.Descent.IsEffectiveDescentMorphism (F := F (pA := pA)) p := by
  simpa using
    (is_effective_descent_morphism_iff_pseudofunctor_is_effective_descent_morphism
      (pA := pA) (p := p))

example :
    CategoryTheory.Pseudofunctor.IsPrestackFor (F := F (pA := pA))
      (S := B) (CategoryTheory.Presieve.singleton p) ↔
        IsDescentMorphism (pA := pA) p := by
  simpa using (is_prestack_for_singleton_iff_descent_morphism (pA := pA) (p := p))

example :
    CategoryTheory.Pseudofunctor.IsStackFor (F := F (pA := pA))
      (S := B) (CategoryTheory.Presieve.singleton p) ↔
        IsEffectiveDescentMorphism (pA := pA) p := by
  simpa using
    (is_stack_for_singleton_iff_effective_descent_morphism (pA := pA) (p := p))

end

end Descent.Examples
