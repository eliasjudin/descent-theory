/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.CategoryTheory.Sites.Descent.SingleMorphism

/-!
# Single-to-singleton conversions for Čech descent data

This file contains the auxiliary pullback morphisms used to convert
single-morphism Čech descent data into singleton-family descent data,
together with the resulting object-level conversion.
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
## Pulling back the Čech gluing isomorphism
-/

/-- Induced map between pullbacks along `f₁ f₂ : Y ⟶ E` with `f₁ ≫ p = f₂ ≫ p`. -/
def single_to_singleton_hom_aux (D : CechDescentData (F := F) p) {Y : C} (f₁ f₂ : Y ⟶ E)
    (h : f₁ ≫ p = f₂ ≫ p) :
    (F.map f₁.op.toLoc).toFunctor.obj D.obj ⟶ (F.map f₂.op.toLoc).toFunctor.obj D.obj := by
  let u : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ h
  have hu1 : u ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu2 : u ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
  exact CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
    (φ := inv D.ξ) u f₁ f₂ hu1 hu2

private lemma single_to_singleton_hom_aux_comp
    (D : CechDescentData (F := F) p) {Y : C} (f₁ f₂ f₃ : Y ⟶ E)
    (h12 : f₁ ≫ p = f₂ ≫ p) (h23 : f₂ ≫ p = f₃ ≫ p) (h13 : f₁ ≫ p = f₃ ≫ p) :
    single_to_singleton_hom_aux F p D f₁ f₂ h12 ≫
        single_to_singleton_hom_aux F p D f₂ f₃ h23 =
      single_to_singleton_hom_aux F p D f₁ f₃ h13 := by
  let u12 : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ h12
  let u23 : Y ⟶ cechKernelPair p := Limits.pullback.lift f₂ f₃ h23
  let u13 : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₃ h13
  have hu12_1 : u12 ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu12_2 : u12 ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
  have hu23_1 : u23 ≫ p1 p = f₂ := Limits.pullback.lift_fst _ _ _
  have hu23_2 : u23 ≫ p2 p = f₃ := Limits.pullback.lift_snd _ _ _
  have hu13_1 : u13 ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu13_2 : u13 ≫ p2 p = f₃ := Limits.pullback.lift_snd _ _ _
  let v : Y ⟶ cechTripleOverlap p := Limits.pullback.lift u12 u23 (by
    simp [hu12_2, hu23_1])
  have hv12 : v ≫ p12 p = u12 := Limits.pullback.lift_fst _ _ _
  have hv23 : v ≫ p23 p = u23 := Limits.pullback.lift_snd _ _ _
  have hv12_p1 : v ≫ p12 p ≫ p1 p = f₁ := by
    calc
      v ≫ p12 p ≫ p1 p = (v ≫ p12 p) ≫ p1 p := by simp [Category.assoc]
      _ = u12 ≫ p1 p := by simp [hv12]
      _ = f₁ := hu12_1
  have hv12_p2 : v ≫ p12 p ≫ p2 p = f₂ := by
    calc
      v ≫ p12 p ≫ p2 p = (v ≫ p12 p) ≫ p2 p := by simp [Category.assoc]
      _ = u12 ≫ p2 p := by simp [hv12]
      _ = f₂ := hu12_2
  have hv23_p1 : v ≫ p23 p ≫ p1 p = f₂ := by
    calc
      v ≫ p23 p ≫ p1 p = (v ≫ p23 p) ≫ p1 p := by simp [Category.assoc]
      _ = u23 ≫ p1 p := by simp [hv23]
      _ = f₂ := hu23_1
  have hv23_p2 : v ≫ p23 p ≫ p2 p = f₃ := by
    calc
      v ≫ p23 p ≫ p2 p = (v ≫ p23 p) ≫ p2 p := by simp [Category.assoc]
      _ = u23 ≫ p2 p := by simp [hv23]
      _ = f₃ := hu23_2
  have hv13 : v ≫ p13 p = u13 := by
    apply Limits.pullback.hom_ext <;>
      simp [Category.assoc, hv12_p1, hv23_p2, hu13_1, hu13_2]
  letI : IsIso (xi12 (F := F) p D.ξ) := by
    dsimp [xi12, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  letI : IsIso (xi23 (F := F) p D.ξ) := by
    dsimp [xi23, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  letI : IsIso (xi13 (F := F) p D.ξ) := by
    dsimp [xi13, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  have hmapInv {Y : C} (g : Y ⟶ cechKernelPair p) :
      (F.map g.op.toLoc).toFunctor.map (inv D.ξ) =
        inv ((F.map g.op.toLoc).toFunctor.map D.ξ) := by
    simp
  have hphi12 :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv D.ξ) (g := p12 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p12 p ≫ p2 p)
          (hgf₁ := by simp) (hgf₂ := by simp) =
        inv (xi12 (F := F) p D.ξ) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, xi12, reindex,
      CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, IsIso.inv_comp, Category.assoc,
      hmapInv (g := p12 p)]
  have hphi23 :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv D.ξ) (g := p23 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p23 p ≫ p2 p)
          (hgf₁ := by simp) (hgf₂ := by simp) =
        inv (xi23 (F := F) p D.ξ) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, xi23, reindex,
      CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.PrelaxFunctor.map₂_eqToHom,
      IsIso.inv_comp, Category.assoc, hmapInv (g := p23 p)]
    have hα :
        inv ((F.mapComp (p1 p).op.toLoc (p23 p).op.toLoc).inv.toNatTrans.app D.obj) =
          (F.mapComp (p1 p).op.toLoc (p23 p).op.toLoc).hom.toNatTrans.app D.obj := by
      apply IsIso.inv_eq_of_hom_inv_id
      simp
    have hβ :
        inv ((F.mapComp (p2 p).op.toLoc (p23 p).op.toLoc).hom.toNatTrans.app D.obj) =
          (F.mapComp (p2 p).op.toLoc (p23 p).op.toLoc).inv.toNatTrans.app D.obj := by
      apply IsIso.inv_eq_of_inv_hom_id
      simp
    simp [hα, hβ]
  have hphi13 :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv D.ξ) (g := p13 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p23 p ≫ p2 p)
          (hgf₁ := by simp) (hgf₂ := by simp) =
        inv (xi13 (F := F) p D.ξ) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, xi13, reindex,
      CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.PrelaxFunctor.map₂_eqToHom,
      IsIso.inv_comp, Category.assoc, hmapInv (g := p13 p)]
    have hα :
        inv ((F.mapComp (p1 p).op.toLoc (p13 p).op.toLoc).inv.toNatTrans.app D.obj) =
          (F.mapComp (p1 p).op.toLoc (p13 p).op.toLoc).hom.toNatTrans.app D.obj := by
      apply IsIso.inv_eq_of_hom_inv_id
      simp
    have hβ :
        inv ((F.mapComp (p2 p).op.toLoc (p13 p).op.toLoc).hom.toNatTrans.app D.obj) =
          (F.mapComp (p2 p).op.toLoc (p13 p).op.toLoc).inv.toNatTrans.app D.obj := by
      apply IsIso.inv_eq_of_inv_hom_id
      simp
    simp [hα, hβ]
  have haux12 :
      single_to_singleton_hom_aux F p D f₁ f₂ h12 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi12 (F := F) p D.ξ)) (g := v) (gf₁ := f₁) (gf₂ := f₂)
          (hgf₁ := hv12_p1) (hgf₂ := hv12_p2) := by
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := inv D.ξ) (g := p12 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p12 p ≫ p2 p)
      (g' := v) (g'f₁ := f₁) (g'f₂ := f₂)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p1) (hg'f₂ := hv12_p2))
    simpa [single_to_singleton_hom_aux, u12, hv12, hphi12] using h.symm
  have haux23 :
      single_to_singleton_hom_aux F p D f₂ f₃ h23 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi23 (F := F) p D.ξ)) (g := v) (gf₁ := f₂) (gf₂ := f₃)
          (hgf₁ := hv12_p2) (hgf₂ := hv23_p2) := by
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := inv D.ξ) (g := p23 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p23 p ≫ p2 p)
      (g' := v) (g'f₁ := f₂) (g'f₂ := f₃)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p2) (hg'f₂ := hv23_p2))
    simpa [single_to_singleton_hom_aux, u23, hv23, hphi23] using h.symm
  have haux13 :
      single_to_singleton_hom_aux F p D f₁ f₃ h13 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi13 (F := F) p D.ξ)) (g := v) (gf₁ := f₁) (gf₂ := f₃)
          (hgf₁ := hv12_p1) (hgf₂ := hv23_p2) := by
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := inv D.ξ) (g := p13 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p23 p ≫ p2 p)
      (g' := v) (g'f₁ := f₁) (g'f₂ := f₃)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p1) (hg'f₂ := hv23_p2))
    simpa [single_to_singleton_hom_aux, u13, hv13, hphi13] using h.symm
  have hcomp_pull :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi12 (F := F) p D.ξ)) (g := v) (gf₁ := f₁) (gf₂ := f₂)
          (hgf₁ := hv12_p1) (hgf₂ := hv12_p2) ≫
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi23 (F := F) p D.ξ)) (g := v) (gf₁ := f₂) (gf₂ := f₃)
          (hgf₁ := hv12_p2) (hgf₂ := hv23_p2) =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi12 (F := F) p D.ξ) ≫ inv (xi23 (F := F) p D.ξ)) (g := v)
          (gf₁ := f₁) (gf₂ := f₃)
          (hgf₁ := hv12_p1) (hgf₂ := hv23_p2) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp,
      Category.assoc]
  have h_cocycle_inv :
      inv (xi12 (F := F) p D.ξ) ≫ inv (xi23 (F := F) p D.ξ) =
        inv (xi13 (F := F) p D.ξ) := by
    have hinv : inv (xi23 (F := F) p D.ξ ≫ xi12 (F := F) p D.ξ) = inv (xi13 (F := F) p D.ξ) := by
      simp [D.cocycle]
    simpa [IsIso.inv_comp] using hinv
  simp [haux12, haux23, haux13, hcomp_pull, h_cocycle_inv]

private lemma single_to_singleton_hom_aux_self
    (D : CechDescentData (F := F) p) {Y : C} (g : Y ⟶ E) :
    single_to_singleton_hom_aux F p D g g (by rfl) = 𝟙 _ := by
  let f := single_to_singleton_hom_aux F p D g g (by rfl)
  have hcomp : f ≫ f = f := by
    simpa [f] using
      (single_to_singleton_hom_aux_comp (F := F) (p := p) D g g g (by rfl) (by rfl) (by rfl))
  letI : IsIso f := by
    dsimp [f, single_to_singleton_hom_aux, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  simpa [Category.assoc] using congrArg (fun t => inv f ≫ t) hcomp

private lemma single_to_singleton_hom_aux_p1_p2
    (D : CechDescentData (F := F) p) :
    single_to_singleton_hom_aux F p D (p1 p) (p2 p) (p1_comp_p_eq_p2_comp_p p) = inv D.ξ := by
  let u : cechKernelPair p ⟶ cechKernelPair p :=
    Limits.pullback.lift (p1 p) (p2 p) (p1_comp_p_eq_p2_comp_p p)
  have hu : u = 𝟙 _ := by
    apply Limits.pullback.hom_ext <;> simp [u]
  simp [single_to_singleton_hom_aux, u, hu]

/-- On the kernel pair, the auxiliary pullback map recovers the Čech gluing isomorphism. -/
lemma single_to_singleton_hom_aux_swap
    (D : CechDescentData (F := F) p) :
    D.ξ =
      single_to_singleton_hom_aux F p D (p2 p) (p1 p)
        (by simpa using (p1_comp_p_eq_p2_comp_p p).symm) := by
  have h12 : p1 p ≫ p = p2 p ≫ p := p1_comp_p_eq_p2_comp_p p
  have h21 : p2 p ≫ p = p1 p ≫ p := by simpa using h12.symm
  have hB :
      single_to_singleton_hom_aux F p D (p1 p) (p2 p) h12 = inv D.ξ := by
    simpa using (single_to_singleton_hom_aux_p1_p2 (F := F) p D)
  have hcomp :
      single_to_singleton_hom_aux F p D (p2 p) (p1 p) h21 ≫
          single_to_singleton_hom_aux F p D (p1 p) (p2 p) h12 = 𝟙 _ := by
    simpa [single_to_singleton_hom_aux_self (F := F) p D (p2 p)] using
      (single_to_singleton_hom_aux_comp (F := F) (p := p) D (p2 p) (p1 p) (p2 p) h21 h12 rfl)
  have hcomp' :
      single_to_singleton_hom_aux F p D (p2 p) (p1 p) h21 ≫ inv D.ξ = 𝟙 _ := by
    simpa [hB] using hcomp
  have hinv :
      inv (inv D.ξ) =
        single_to_singleton_hom_aux F p D (p2 p) (p1 p) h21 :=
    (IsIso.inv_eq_of_inv_hom_id (f := inv D.ξ)
      (g := single_to_singleton_hom_aux F p D (p2 p) (p1 p) h21)
      hcomp')
  simpa using hinv

/-!
## Object-level conversion
-/

/-- Convert single-morphism descent data to singleton-family descent data. -/
def single_to_singleton_descent_data (D : CechDescentData (F := F) p) :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p)) where
  obj := fun _ => D.obj
  hom := fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ => by
    cases i₁; cases i₂
    have h : f₁ ≫ p = f₂ ≫ p := by
      rw [hf₁, hf₂]
    exact single_to_singleton_hom_aux (F := F) p D f₁ f₂ h
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    cases i₁; cases i₂
    have hf₁' : f₁ ≫ p = f₂ ≫ p := by
      rw [hf₁, hf₂]
    have hgf₁' : gf₁ ≫ p = gf₂ ≫ p := by
      have hf₁q : f₁ ≫ p = q := by simpa using hf₁
      have hf₂q : f₂ ≫ p = q := by simpa using hf₂
      have h₁ : gf₁ ≫ p = q' := by
        calc
          gf₁ ≫ p = (g ≫ f₁) ≫ p := by simp [hgf₁]
          _ = g ≫ (f₁ ≫ p) := by simp
          _ = g ≫ q := by simp [hf₁q]
          _ = q' := hq
      have h₂ : gf₂ ≫ p = q' := by
        calc
          gf₂ ≫ p = (g ≫ f₂) ≫ p := by simp [hgf₂]
          _ = g ≫ (f₂ ≫ p) := by simp
          _ = g ≫ q := by simp [hf₂q]
          _ = q' := hq
      exact h₁.trans h₂.symm
    let u : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ hf₁'
    let u' : Y' ⟶ cechKernelPair p := Limits.pullback.lift gf₁ gf₂ hgf₁'
    have hu1 : u ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
    have hu2 : u ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
    have hu1' : u' ≫ p1 p = gf₁ := Limits.pullback.lift_fst _ _ _
    have hu2' : u' ≫ p2 p = gf₂ := Limits.pullback.lift_snd _ _ _
    have hg_u : g ≫ u = u' := by
      apply Limits.pullback.hom_ext <;>
        simp [u, u', hu1, hu2, hu1', hu2', hgf₁, hgf₂, Category.assoc]
    simp [single_to_singleton_hom_aux, u, u', hg_u]
  hom_self := by
    intro Y q i g hg
    cases i
    simpa using (single_to_singleton_hom_aux_self (F := F) p D g)
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    cases i₁; cases i₂; cases i₃
    simpa using
      (single_to_singleton_hom_aux_comp (F := F) p D f₁ f₂ f₃
        (by rw [hf₁, hf₂]) (by rw [hf₂, hf₃]) (by rw [hf₁, hf₃]))

end

end Descent.Pseudofunctor.Descent
