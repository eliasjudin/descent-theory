/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.CategoryTheory.Sites.Descent.SingleMorphism

/-!
# Singleton-cover conversions for Čech descent data

This file contains the conversion layer between
`CechDescentData (F := F) p` and Mathlib's singleton-family
`CategoryTheory.Pseudofunctor.DescentData`.
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
## Helper: pulling back the Čech gluing isomorphism
-/

/-- Given Čech-style descent data `D` for `p : E ⟶ B`, this is the induced morphism
`f₁^* D.obj ⟶ f₂^* D.obj` for any `f₁ f₂ : Y ⟶ E` with `f₁ ≫ p = f₂ ≫ p`.

We define it by pulling back `inv D.ξ : π₁^* D.obj ⟶ π₂^* D.obj` along the canonical
map `Y ⟶ E ×_B E`. -/
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

/-!
## Forward direction: Single → Singleton
-/

  /-- Convert a single morphism descent datum to Mathlib's descent data for the singleton family.

The key mapping:
- `obj ()` := `D.obj`
- `hom q f₁ f₂` at Y mapping to E comes from `D.ξ` transported appropriately -/
def single_to_singleton_descent_data (D : CechDescentData (F := F) p) :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p)) where
  obj := fun _ => D.obj
  hom := fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ => by
    cases i₁; cases i₂ -- Both are PUnit.unit
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

/-!
## Helper: transport for `DescentData.hom`

`simp` does not rewrite inside the dependent expression `D.hom q f₁ f₂`, since its type depends on
`f₁` and `f₂`. We use the standard `eqToHom` transports instead.
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
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) {Y : C} (q : Y ⟶ B)
    {f₁ f₁' f₂ f₂' : Y ⟶ E} (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) (h₁ : f₁ = f₁')
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

/-- Convert Mathlib's descent data for the singleton family to a single morphism descent datum. -/
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

/-!
## Morphisms
-/

/-- Convert a morphism of single-morphism descent data to a morphism of mathlib descent data. -/
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

/-- Convert a morphism of mathlib descent data to a morphism of single-morphism descent data. -/
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
