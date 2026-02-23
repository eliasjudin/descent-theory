/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData.Conversions

/-!
# Functors between single and singleton descent data
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

open Opposite
open Descent.Cech
open Descent.Pseudofunctor
open CategoryTheory.Pseudofunctor

universe v' v u' u

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

variable {E B : C} (p : E ⟶ B)

/-- Single-to-singleton descent-data functor. -/
def single_to_singleton_functor :
    CechDescentData (F := F) p ⥤
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p)) where
  obj := single_to_singleton_descent_data F p
  map := single_to_singleton_hom F p
  map_id := fun D => by
    ext i
    cases i
    simp [single_to_singleton_hom, single_to_singleton_descent_data, CechDescentData.instCategory]
  map_comp := fun f g => by
    ext i
    cases i
    simp [single_to_singleton_hom, single_to_singleton_descent_data,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom, CechDescentData.instCategory]

/-- Singleton-to-single descent-data functor. -/
def singleton_to_single_functor :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p)) ⥤
      CechDescentData (F := F) p where
  obj := singleton_to_single_descent_data F p
  map := singleton_to_single_hom F p
  map_id := fun D => by
    apply CechDescentData.Hom.ext
    simp [singleton_to_single_hom, singleton_to_single_descent_data, CechDescentData.instCategory]
  map_comp := fun f g => by
    apply CechDescentData.Hom.ext
    simp [singleton_to_single_hom, singleton_to_single_descent_data,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom, CechDescentData.instCategory]

end

end Descent.Pseudofunctor.Descent
