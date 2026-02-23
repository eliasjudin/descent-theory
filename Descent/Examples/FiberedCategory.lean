/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.FiberedCategory.Reindexing

/-!
# Examples: reindexing in fibered categories

Small `example`s that exercise the basic reindexing coherence isomorphisms on fibers.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.Examples

open Descent.FiberedCategory

universe u v w

section

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜]
variable (pA : 𝒜 ⥤ C) [pA.IsFibered]

example {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : Fiber pA S) :
    (reindex_comp_iso_obj (pA := pA) g f a).hom.1 ≫
        IsPreFibered.pullbackMap (p := pA)
            (IsPreFibered.pullbackObj_proj (p := pA) a.2 f) g ≫
          IsPreFibered.pullbackMap (p := pA) a.2 f =
      IsPreFibered.pullbackMap (p := pA) a.2 (g ≫ f) := by
  simp

example {S : C} (a : Fiber pA S) :
    (reindex_id_iso (pA := pA) a).hom.1 =
      IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S) :=
  reindex_id_iso_hom_eq (pA := pA) a

end

end Descent.Examples
