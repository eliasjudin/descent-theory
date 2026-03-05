/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# Basic reindexing on fibers of a fibered category

Defines the reindexing functors `f^* : Fiber p S ⥤ Fiber p R` for a fibered
functor `p : 𝒜 ⥤ C`, together with their defining pullback-map simp lemma.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace CategoryTheory

namespace FiberedCategory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜] (pA : 𝒜 ⥤ C) [pA.IsFibered]

noncomputable section

/-- Reindexing (pullback) functor on the standard fibers of a fibered category. -/
def reindex {R S : C} (f : R ⟶ S) : Fiber pA S ⥤ Fiber pA R where
  obj a :=
    ⟨IsPreFibered.pullbackObj (p := pA) a.2 f,
      IsPreFibered.pullbackObj_proj (p := pA) a.2 f⟩
  map {a b} φ := by
    haveI : pA.IsHomLift (𝟙 S) φ.1 := φ.2
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1) := by
      simpa using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1))
    refine
      ⟨IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) b.2 f)
          (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1),
        inferInstance⟩
  map_id a := by
    apply Fiber.hom_ext
    change
        IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) a.2 f)
            (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ 𝟙 a.1) =
          𝟙 (IsPreFibered.pullbackObj (p := pA) a.2 f)
    simp
  map_comp {a b c} φ ψ := by
    apply Fiber.hom_ext
    haveI : pA.IsHomLift (𝟙 S) φ.1 := φ.2
    haveI : pA.IsHomLift (𝟙 S) ψ.1 := ψ.2
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1) := by
      simpa using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1))
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1) := by
      simpa using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1))
    haveI : pA.IsHomLift (𝟙 S) (φ.1 ≫ ψ.1) := by
      simpa using (inferInstance : pA.IsHomLift (𝟙 S ≫ 𝟙 S) (φ.1 ≫ ψ.1))
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)) := by
      simpa [Category.assoc] using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)))
    change
        IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) c.2 f)
            (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)) =
          IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) b.2 f)
              (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1) ≫
            IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) c.2 f)
              (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1)
    let θ :=
      IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) b.2 f)
          (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1) ≫
        IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) c.2 f)
          (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1)
    haveI : pA.IsHomLift (𝟙 R) θ := by
      dsimp [θ]
      infer_instance
    symm
    apply
      IsCartesian.map_uniq (p := pA) (f := f)
        (φ := IsPreFibered.pullbackMap (p := pA) c.2 f)
        (φ' := IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)) θ
    dsimp [θ]
    simp [Category.assoc]

/-- The object part of `reindex`. -/
abbrev reindexObj {R S : C} (f : R ⟶ S) (a : Fiber pA S) : Fiber pA R :=
  (reindex (pA := pA) f).obj a

@[simp, reassoc]
lemma reindex_map_comp_pullback {R S : C} (f : R ⟶ S) {a b : Fiber pA S} (φ : a ⟶ b) :
    ((reindex (pA := pA) f).map φ).1 ≫ IsPreFibered.pullbackMap (p := pA) b.2 f =
      IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1 := by
  dsimp [reindex]
  simp

end

end FiberedCategory

end CategoryTheory
