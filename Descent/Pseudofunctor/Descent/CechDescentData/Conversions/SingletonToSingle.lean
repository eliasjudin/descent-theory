/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.CategoryTheory.Sites.Descent.SingleMorphism

/-!
# Singleton-to-single conversions for Čech descent data

This file contains the transport lemmas and cocycle/unit verifications needed
to recover single-morphism Čech descent data from singleton-family descent
data.
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

/-!
## Transport lemmas for singleton-family descent data
-/

omit [Limits.HasPullbacks C] in
private lemma descent_data_hom_congr
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) {Y : C}
    (q : Y ⟶ B) {f₁ f₁' f₂ f₂' : Y ⟶ E} (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) (hf₁' : f₁' ≫ p = q)
    (hf₂' : f₂' ≫ p = q) (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') :
    eqToHom
          (by
            simpa using
              (congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₁).symm) ≫
        D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
            (by simpa using hf₁) (by simpa using hf₂) ≫
      eqToHom
          (by
            simpa using congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₂) =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁' f₂'
          (by simpa using hf₁') (by simpa using hf₂') := by
  cases h₁
  cases h₂
  simp

omit [Limits.HasPullbacks C] in
private lemma descent_data_hom_congr'
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) {Y : C}
    (q : Y ⟶ B) {f₁ f₁' f₂ f₂' : Y ⟶ E} (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) (h₁ : f₁ = f₁')
    (h₂ : f₂ = f₂') :
    eqToHom
          (by
            simpa using
              (congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₁).symm) ≫
        D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
            (by simpa using hf₁) (by simpa using hf₂) ≫
      eqToHom
          (by
            simpa using congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₂) =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁' f₂'
          (by simpa [h₁] using hf₁) (by simpa [h₂] using hf₂) := by
  cases h₁
  cases h₂
  simp

/-!
## Verifying the Čech unit and cocycle conditions
-/

private lemma singleton_to_single_unit
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) :
    (diag_iso_p2 (F := F) p (D.obj PUnit.unit)).inv ≫
        (reindex F (Limits.pullback.diagonal p)).map
            (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p)
              (by
                simpa using (p1_comp_p_eq_p2_comp_p p).symm)
              (by rfl)) ≫
        (diag_iso_p1 (F := F) p (D.obj PUnit.unit)).hom =
      𝟙 (D.obj PUnit.unit) := by
  simp [diag_iso_p1, diag_iso_p2, reindex_comp_iso_obj, reindex_obj_iso_of_eq, reindex_id_iso_obj]
  set φ :=
    D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p)
      (by
        simpa using (p1_comp_p_eq_p2_comp_p p).symm)
      (by rfl) with hφ
  have hmap :
      (reindex F (Limits.pullback.diagonal p)).map φ =
        (F.mapComp (p2 p).op.toLoc (Limits.pullback.diagonal p).op.toLoc).inv.toNatTrans.app
            (D.obj PUnit.unit) ≫
          CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
            (φ := φ) (g := Limits.pullback.diagonal p)
            (gf₁ := Limits.pullback.diagonal p ≫ p2 p)
            (gf₂ := Limits.pullback.diagonal p ≫ p1 p)
            (hgf₁ := rfl) (hgf₂ := rfl) ≫
          (F.mapComp (p1 p).op.toLoc (Limits.pullback.diagonal p).op.toLoc).hom.toNatTrans.app
            (D.obj PUnit.unit) := by
    simpa [reindex, CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp] using
      (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom (F := F) (φ := φ)
        (g := Limits.pullback.diagonal p)
        (gf₁ := Limits.pullback.diagonal p ≫ p2 p)
        (gf₂ := Limits.pullback.diagonal p ≫ p1 p)
        (hgf₁ := (rfl : Limits.pullback.diagonal p ≫ p2 p = Limits.pullback.diagonal p ≫ p2 p))
        (hgf₂ := (rfl : Limits.pullback.diagonal p ≫ p1 p = Limits.pullback.diagonal p ≫ p1 p)))
  rw [hmap]
  simp [Category.assoc]
  have hq : Limits.pullback.diagonal p ≫ (p1 p ≫ p) = p := by
    simp
  have hpull :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
          (g := Limits.pullback.diagonal p)
          (gf₁ := Limits.pullback.diagonal p ≫ p2 p)
          (gf₂ := Limits.pullback.diagonal p ≫ p1 p)
          (hgf₁ := rfl) (hgf₂ := rfl) =
        D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (Limits.pullback.diagonal p ≫ p2 p) (Limits.pullback.diagonal p ≫ p1 p)
          (by
            simp)
          (by
            simp) := by
    simpa [φ, hq] using
      (D.pullHom_hom (g := Limits.pullback.diagonal p)
        (q := p1 p ≫ p) (q' := p) (hq := hq)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (f₁ := p2 p) (f₂ := p1 p)
        (hf₁ := by
          simpa using (p1_comp_p_eq_p2_comp_p p).symm)
        (hf₂ := by rfl)
        (gf₁ := Limits.pullback.diagonal p ≫ p2 p)
        (gf₂ := Limits.pullback.diagonal p ≫ p1 p)
        (hgf₁ := rfl) (hgf₂ := rfl))
  rw [hpull]
  have hself :
      D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 E) (𝟙 E)
          (by simp) (by simp) =
        𝟙 _ := by
    simpa using
      (D.hom_self (q := p) (i := PUnit.unit) (g := 𝟙 E) (by simp))
  have hhom :
      eqToHom
            (by
              simp) ≫
          D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit)
              (Limits.pullback.diagonal p ≫ p2 p) (Limits.pullback.diagonal p ≫ p1 p)
              (by
                simp)
              (by
                simp) ≫
        eqToHom
            (by
              simp) =
        D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 E) (𝟙 E)
            (by simp) (by simp) := by
    simpa using
      (descent_data_hom_congr (F := F) (p := p) (D := D) (q := p)
        (f₁ := Limits.pullback.diagonal p ≫ p2 p) (f₁' := 𝟙 E)
        (f₂ := Limits.pullback.diagonal p ≫ p1 p) (f₂' := 𝟙 E)
        (hf₁ := by
          simp)
        (hf₂ := by
          simp)
        (hf₁' := by
          simp)
        (hf₂' := by
          simp)
        (h₁ := by simp) (h₂ := by simp))
  simpa [hself] using congrArg (fun t =>
    (F.mapId { as := op E }).inv.toNatTrans.app (D.obj PUnit.unit) ≫ t ≫
      (F.mapId { as := op E }).hom.toNatTrans.app (D.obj PUnit.unit)) hhom

private lemma singleton_to_single_cocycle
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) :
  xi23 (F := F) p
        (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
          (by rfl)
          (by
            simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom ≫
      xi12 (F := F) p
        (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
          (by rfl)
          (by
            simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
      xi13 (F := F) p
        (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
          (by rfl)
          (by
            simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom := by
  let q0 : cechKernelPair p ⟶ B := p1 p ≫ p
  let q3 : cechTripleOverlap p ⟶ B := p12 p ≫ q0
  have hq23 : p23 p ≫ q0 = q3 := by
    dsimp [q0, q3]
    have h₁ : p23 p ≫ p1 p ≫ p = p12 p ≫ p2 p ≫ p := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun k => k ≫ p) (p12_p2_eq_p23_p1 (p := p)).symm
    have h₂ : p12 p ≫ p2 p ≫ p = p12 p ≫ p1 p ≫ p := by
      calc
        p12 p ≫ p2 p ≫ p = p12 p ≫ (p2 p ≫ p) := rfl
        _ = p12 p ≫ (p1 p ≫ p) := by
          exact congrArg (fun k => p12 p ≫ k) (p1_comp_p_eq_p2_comp_p (p := p)).symm
        _ = p12 p ≫ p1 p ≫ p := rfl
    exact h₁.trans h₂
  have hq13 : p13 p ≫ q0 = q3 := by
    dsimp [q0, q3]
    simp [Category.assoc]
  have hf12_1 : (p12 p ≫ p2 p) ≫ p = q3 := by
    dsimp [q0, q3]
    calc
      (p12 p ≫ p2 p) ≫ p = p12 p ≫ p2 p ≫ p := by
        exact Category.assoc (p12 p) (p2 p) p
      _ = p12 p ≫ (p2 p ≫ p) := rfl
      _ = p12 p ≫ (p1 p ≫ p) := by
        exact congrArg (fun k => p12 p ≫ k) (p1_comp_p_eq_p2_comp_p (p := p)).symm
      _ = p12 p ≫ p1 p ≫ p := rfl
  have hf12_2 : (p12 p ≫ p1 p) ≫ p = q3 := by
    dsimp [q0, q3]
    simp [Category.assoc]
  have hf23_1 : (p23 p ≫ p2 p) ≫ p = q3 := by
    have hq23' : p23 p ≫ (p1 p ≫ p) = q3 := by simpa [q0, Category.assoc] using hq23
    have h :
        p23 p ≫ (p2 p ≫ p) = p23 p ≫ (p1 p ≫ p) := by
      simpa using congrArg (fun k => p23 p ≫ k) (p1_comp_p_eq_p2_comp_p (p := p)).symm
    simpa [Category.assoc] using h.trans hq23'
  have hf23_2 : (p23 p ≫ p1 p) ≫ p = q3 := by
    simpa [q0, Category.assoc] using hq23
  have hf13_1 : (p13 p ≫ p2 p) ≫ p = q3 := by
    have hq13' : p13 p ≫ (p1 p ≫ p) = q3 := by simpa [q0, Category.assoc] using hq13
    have h :
        p13 p ≫ (p2 p ≫ p) = p13 p ≫ (p1 p ≫ p) := by
      simpa using congrArg (fun k => p13 p ≫ k) (p1_comp_p_eq_p2_comp_p (p := p)).symm
    simpa [Category.assoc] using h.trans hq13'
  have hf13_2 : (p13 p ≫ p1 p) ≫ p = q3 := by
    simpa [q0, Category.assoc] using hq13
  set φ :
      (F.map (p2 p).op.toLoc).toFunctor.obj (D.obj PUnit.unit) ⟶
        (F.map (p1 p).op.toLoc).toFunctor.obj (D.obj PUnit.unit) :=
    D.hom q0 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p)
      (by simpa [q0] using (p1_comp_p_eq_p2_comp_p p).symm)
      (by rfl) with hφ

  have hx12_pull :
      xi12 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
          (g := p12 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) := by
    simp [xi12, reindex, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, CategoryTheory.Pseudofunctor.DescentData.iso,
      hφ, q0]

  have hx23_pull :
      xi23 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p2 p) (hgf₁ := rfl)
            (hgf₂ := by simp) := by
    simp [xi23, reindex, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, CategoryTheory.Pseudofunctor.DescentData.iso,
      hφ, q0]

  have hx13_pull :
      xi13 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p13 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p)
            (hgf₁ := by simp)
            (hgf₂ := by simp) := by
    simp [xi13, reindex, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      CategoryTheory.Pseudofunctor.DescentData.iso, hφ, q0]

  have hcomp :
      D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
            (by simpa using hf23_1) (by simpa using hf12_1) ≫
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf12_1) (by simpa using hf12_2) =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf23_1) (by simpa using hf12_2) := by
    simp [D.hom_comp]

  calc
    xi23 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom ≫
        xi12 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
            (by simpa using hf23_1) (by simpa using hf12_1) ≫
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf12_1) (by simpa using hf12_2) := by
      have hx23 :
          xi23 (F := F) p
                (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                      (by rfl)
                      (by
                        simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
            D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
              (by simpa using hf23_1) (by simpa using hf12_1) := by
        have hpull :
            CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
                (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p2 p) (hgf₁ := rfl)
                (hgf₂ := by simp) =
              D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
                (by simpa using hf23_1) (by simpa using hf12_1) := by
          have hq : p23 p ≫ q0 = q3 := hq23
          simpa [φ, hq] using
            (D.pullHom_hom (g := p23 p) (q := q0) (q' := q3) (hq := hq)
              (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
              (hf₁ := by
                simpa [q0] using (p1_comp_p_eq_p2_comp_p p).symm)
              (hf₂ := by rfl)
              (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p2 p) (hgf₁ := rfl)
              (hgf₂ := by simp))
        simpa [hx23_pull] using hpull
      have hx12 :
          xi12 (F := F) p
                (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                      (by rfl)
                      (by
                        simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
            D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
              (by simpa using hf12_1) (by simpa using hf12_2) := by
        have hpull :
            CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
                (g := p12 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl)
                (hgf₂ := rfl) =
              D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
                (by simpa using hf12_1) (by simpa using hf12_2) := by
          have hq : p12 p ≫ q0 = q3 := rfl
          simpa [φ] using
            (D.pullHom_hom (g := p12 p) (q := q0) (q' := q3) (hq := hq)
              (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
              (hf₁ := by
                simpa [q0] using (p1_comp_p_eq_p2_comp_p p).symm)
              (hf₂ := by rfl)
              (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl)
              (hgf₂ := rfl))
        simpa [hx12_pull] using hpull
      calc
        xi23 (F := F) p
              (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                    (by rfl)
                    (by
                      simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom ≫
            xi12 (F := F) p
              (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                    (by rfl)
                    (by
                      simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
              (by simpa using hf23_1) (by simpa using hf12_1) ≫
            xi12 (F := F) p
              (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                    (by rfl)
                    (by
                      simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom := by
          rw [hx23]
        _ =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
              (by simpa using hf23_1) (by simpa using hf12_1) ≫
            D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
              (by simpa using hf12_1) (by simpa using hf12_2) := by
          rw [hx12]
    _ =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf23_1) (by simpa using hf12_2) := hcomp
    _ =
        xi13 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom := by
      have hpull :
          CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
              (g := p13 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p)
              (hgf₁ := by simp)
              (hgf₂ := by simp) =
            D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
              (by simpa using hf23_1) (by simpa using hf12_2) := by
        have hq : p13 p ≫ q0 = q3 := hq13
        simpa [φ, hq] using
          (D.pullHom_hom (g := p13 p) (q := q0) (q' := q3) (hq := hq)
            (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
            (hf₁ := by
              simpa [q0] using (p1_comp_p_eq_p2_comp_p p).symm)
            (hf₂ := by rfl)
            (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p)
            (hgf₁ := by simp)
            (hgf₂ := by simp))
      simpa [hx13_pull] using hpull.symm

/-!
## Object-level conversion
-/

/-- Convert singleton-family descent data to single-morphism Čech descent data. -/
def singleton_to_single_descent_data
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) :
    CechDescentData (F := F) p where
  obj := D.obj PUnit.unit
  ξ := by
    exact
      (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
            (by
              simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom
  unit := by
    simpa using (singleton_to_single_unit (F := F) p D)
  cocycle := by
    simpa using (singleton_to_single_cocycle (F := F) p D)

end

end Descent.Pseudofunctor.Descent
