/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData.Conversions.SingleToSingleton
import Descent.Pseudofunctor.Descent.CechDescentData.Conversions.SingletonToSingle

/-!
# Morphism-level conversions for singleton-cover descent data

This file contains the morphism transport between single-morphism Čech descent
data and singleton-family descent data.
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

private lemma single_to_singleton_hom_aux_comm {D₁ D₂ : CechDescentData (F := F) p}
    (f : D₁ ⟶ D₂) {Y : C} (g₁ g₂ : Y ⟶ E) (h : g₁ ≫ p = g₂ ≫ p) :
    (F.map g₁.op.toLoc).toFunctor.map f.hom ≫ single_to_singleton_hom_aux F p D₂ g₁ g₂ h =
      single_to_singleton_hom_aux F p D₁ g₁ g₂ h ≫
        (F.map g₂.op.toLoc).toFunctor.map f.hom := by
  have hcomm_inv :
      (F.map (p1 p).op.toLoc).toFunctor.map f.hom ≫ inv D₂.ξ =
        inv D₁.ξ ≫ (F.map (p2 p).op.toLoc).toFunctor.map f.hom := by
    have := congrArg (fun t => inv D₁.ξ ≫ t ≫ inv D₂.ξ) f.comm
    simpa [Descent.Pseudofunctor.reindex, Category.assoc] using this
  simp [single_to_singleton_hom_aux, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Category.assoc]
  have hmap :
      (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
            ((F.map (p1 p).op.toLoc).toFunctor.map f.hom) ≫
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map (inv D₂.ξ) =
        (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map (inv D₁.ξ) ≫
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
            ((F.map (p2 p).op.toLoc).toFunctor.map f.hom) := by
    have :=
      congrArg
        (fun t =>
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map t)
        hcomm_inv
    simpa [Functor.map_comp] using this
  have hmap' :
      (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
            ((F.map (p1 p).op.toLoc).toFunctor.map f.hom) ≫
          inv ((F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map D₂.ξ) =
        inv ((F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map D₁.ξ) ≫
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
            ((F.map (p2 p).op.toLoc).toFunctor.map f.hom) := by
    simpa using hmap
  rw [cancel_epi
    ((F.mapComp' (p1 p).op.toLoc (Limits.pullback.lift g₁ g₂ h).op.toLoc g₁.op.toLoc (by
        have hu1 : Limits.pullback.lift g₁ g₂ h ≫ p1 p = g₁ :=
          Limits.pullback.lift_fst _ _ _
        have hu1' : (p1 p).op ≫ (Limits.pullback.lift g₁ g₂ h).op = g₁.op := by
          have hu1op : (Limits.pullback.lift g₁ g₂ h ≫ p1 p).op = g₁.op :=
            congrArg (fun k => k.op) hu1
          rw [op_comp] at hu1op
          exact hu1op
        have hu1Loc : ((p1 p).op ≫ (Limits.pullback.lift g₁ g₂ h).op).toLoc = g₁.op.toLoc :=
          congrArg (fun k => k.toLoc) hu1'
        simpa [Quiver.Hom.comp_toLoc] using hu1Loc)).hom.toNatTrans.app
      D₁.obj)]
  rw [← Category.assoc, hmap']
  simp [Category.assoc]

/-- Convert a morphism of single-morphism descent data to singleton-family descent data. -/
def single_to_singleton_hom {D₁ D₂ : CechDescentData (F := F) p}
    (f : D₁ ⟶ D₂) :
    single_to_singleton_descent_data F p D₁ ⟶ single_to_singleton_descent_data F p D₂ where
  hom := fun _ => f.hom
  comm := by
    intro Y q i₁ i₂ g₁ g₂ hg₁ hg₂
    cases i₁; cases i₂
    have h : g₁ ≫ p = g₂ ≫ p := by
      rw [hg₁, hg₂]
    simpa using (single_to_singleton_hom_aux_comm (F := F) p f g₁ g₂ h)

/-- Convert a morphism of singleton-family descent data to single-morphism descent data. -/
def singleton_to_single_hom
    {D₁ D₂ : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))}
    (f : D₁ ⟶ D₂) :
    singleton_to_single_descent_data F p D₁ ⟶ singleton_to_single_descent_data F p D₂ :=
  ⟨f.hom PUnit.unit, by
    simp only [singleton_to_single_descent_data]
    have hf₁ : p2 p ≫ p = p1 p ≫ p := by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm
    have hf₂ : p1 p ≫ p = p1 p ≫ p := rfl
    simpa [CategoryTheory.Pseudofunctor.DescentData.iso] using
      (f.comm (q := (p1 p ≫ p)) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (f₁ := p2 p) (f₂ := p1 p) hf₁ hf₂).symm⟩

end

end Descent.Pseudofunctor.Descent
