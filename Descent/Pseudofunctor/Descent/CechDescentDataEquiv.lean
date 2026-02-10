/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
import Descent.Pseudofunctor.Descent.CechDescentData
import Descent.CategoryTheory.Sites.Descent.SingleMorphism

/-!
# Equivalence with Mathlib's descent data

Relates `CechDescentData` for `p : E ⟶ B` to Mathlib's
`Pseudofunctor.DescentData` for the singleton family `fun _ : PUnit.{1} ↦ p`.
Main definitions: `single_to_singleton_descent_data`, `singleton_to_single_descent_data`,
`single_to_singleton_functor`, `singleton_to_single_functor`, `single_singleton_descent_data_equiv`.
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
  -- Build the Čech 3-fold overlap map induced by (f₁,f₂,f₃).
  let u12 : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ h12
  let u23 : Y ⟶ cechKernelPair p := Limits.pullback.lift f₂ f₃ h23
  let u13 : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₃ h13
  have hu12_1 : u12 ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu12_2 : u12 ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
  have hu23_1 : u23 ≫ p1 p = f₂ := Limits.pullback.lift_fst _ _ _
  have hu23_2 : u23 ≫ p2 p = f₃ := Limits.pullback.lift_snd _ _ _
  have hu13_1 : u13 ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu13_2 : u13 ≫ p2 p = f₃ := Limits.pullback.lift_snd _ _ _
  have h_u12_u23 : u12 ≫ p2 p = u23 ≫ p1 p := by simp [hu12_2, hu23_1]
  let v : Y ⟶ cechTripleOverlap p := Limits.pullback.lift u12 u23 h_u12_u23
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
  -- Provide `IsIso` instances for the Čech morphisms.
  letI : IsIso (xi12 (F := F) p D.ξ) := by
    dsimp [xi12, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  letI : IsIso (xi23 (F := F) p D.ξ) := by
    dsimp [xi23, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  letI : IsIso (xi13 (F := F) p D.ξ) := by
    dsimp [xi13, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  -- Identify the pullbacks of the Čech morphisms.
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
    -- Turn inverses of the `mapComp` components into the expected components.
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
    -- Turn inverses of the `mapComp` components into the expected components.
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
  -- Rewrite the three auxiliary morphisms as pullbacks along `v`.
  have haux12 :
      single_to_singleton_hom_aux F p D f₁ f₂ h12 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi12 (F := F) p D.ξ)) (g := v) (gf₁ := f₁) (gf₂ := f₂)
          (hgf₁ := hv12_p1) (hgf₂ := hv12_p2) := by
    -- Pull back along `v ≫ p12 = u12`.
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := inv D.ξ) (g := p12 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p12 p ≫ p2 p)
      (g' := v) (g'f₁ := f₁) (g'f₂ := f₂)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p1) (hg'f₂ := hv12_p2))
    -- Use `hphi12` to identify the inner pullback.
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
  -- Composition of pullbacks along `v`.
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
  -- Invert the cocycle.
  have h_cocycle_inv :
      inv (xi12 (F := F) p D.ξ) ≫ inv (xi23 (F := F) p D.ξ) =
        inv (xi13 (F := F) p D.ξ) := by
    have hinv : inv (xi23 (F := F) p D.ξ ≫ xi12 (F := F) p D.ξ) = inv (xi13 (F := F) p D.ξ) := by
      simp [D.cocycle]
    simpa [IsIso.inv_comp] using hinv
  -- Assemble.
  simp [haux12, haux23, haux13, hcomp_pull, h_cocycle_inv]

private lemma single_to_singleton_hom_aux_self
    (D : CechDescentData (F := F) p) {Y : C} (g : Y ⟶ E) :
    single_to_singleton_hom_aux F p D g g (by rfl) = 𝟙 _ := by
  -- Use idempotence + isomorphism to deduce identity.
  let f := single_to_singleton_hom_aux F p D g g (by rfl)
  have hcomp : f ≫ f = f := by
    simpa [f] using
      (single_to_singleton_hom_aux_comp (F := F) (p := p) D g g g (by rfl) (by rfl) (by rfl))
  have hIso : IsIso f := by
    dsimp [f, single_to_singleton_hom_aux, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  letI : IsIso f := hIso
  have h' := congrArg (fun t => inv f ≫ t) hcomp
  simpa [Category.assoc] using h'

private lemma single_to_singleton_hom_aux_p1_p2
    (D : CechDescentData (F := F) p) :
    single_to_singleton_hom_aux F p D (p1 p) (p2 p) (p1_comp_p_eq_p2_comp_p p) = inv D.ξ := by
  let u : cechKernelPair p ⟶ cechKernelPair p :=
    Limits.pullback.lift (p1 p) (p2 p) (p1_comp_p_eq_p2_comp_p p)
  have hu : u = 𝟙 _ := by
    apply Limits.pullback.hom_ext <;> simp [u]
  simp [single_to_singleton_hom_aux, u, hu]

private lemma single_to_singleton_hom_aux_swap
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
  -- Rewrite `f.comm` in terms of `inv ξ`.
  have hcomm_inv :
      (F.map (p1 p).op.toLoc).toFunctor.map f.hom ≫ inv D₂.ξ =
        inv D₁.ξ ≫ (F.map (p2 p).op.toLoc).toFunctor.map f.hom := by
    have := congrArg (fun t => inv D₁.ξ ≫ t ≫ inv D₂.ξ) f.comm
    simpa [Descent.Pseudofunctor.reindex, Category.assoc] using this
  -- Expand `single_to_singleton_hom_aux` and reduce to coherence for `mapComp'`.
  simp [single_to_singleton_hom_aux, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Category.assoc]
  -- Apply the compatibility relation after reindexing along `u`.
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
  -- Cancel the leading `mapComp'` component and rewrite using `hmap'`.
  rw [cancel_epi
    ((F.mapComp' (p1 p).op.toLoc (Limits.pullback.lift g₁ g₂ h).op.toLoc g₁.op.toLoc (by
        have hu1 : Limits.pullback.lift g₁ g₂ h ≫ p1 p = g₁ :=
          Limits.pullback.lift_fst _ _ _
        have hu1' : (p1 p).op ≫ (Limits.pullback.lift g₁ g₂ h).op = g₁.op := by
          have hu1op : (Limits.pullback.lift g₁ g₂ h ≫ p1 p).op = g₁.op :=
            congrArg (fun k => k.op) hu1
          -- rewrite `(f ≫ g).op` as `g.op ≫ f.op`
          rw [op_comp] at hu1op
          exact hu1op
        have hu1Loc : ((p1 p).op ≫ (Limits.pullback.lift g₁ g₂ h).op).toLoc = g₁.op.toLoc :=
          congrArg (fun k => k.toLoc) hu1'
        -- rewrite `toLoc` of a composite
        simpa [Quiver.Hom.comp_toLoc] using hu1Loc)).hom.toNatTrans.app
      D₁.obj)]
  -- reassociate to expose the left-composite `(_ ≫ _)` for rewriting
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
    -- Expand the definition of `hom` on both sides.
    -- Both sides are pullbacks of `D.ξ.inv` along the corresponding maps into `cechKernelPair p`.
    have hf₁' : f₁ ≫ p = f₂ ≫ p := by
      rw [hf₁, hf₂]
    have hgf₁' : gf₁ ≫ p = gf₂ ≫ p := by
      -- both are equal to `q'`
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
    -- Use functoriality of `pullHom` and the equality `g ≫ u = u'`.
    -- `pullHom_pullHom` rewrites the double pullback as a single pullback along `g ≫ u`.
    -- Then we rewrite by `hg_u` to match the definition of `hom` for `q'`.
    simp [single_to_singleton_hom_aux, u, u', hg_u]
  hom_self := by
    intro Y q i g hg
    cases i
    simpa using (single_to_singleton_hom_aux_self (F := F) p D g)
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    cases i₁; cases i₂; cases i₃
    have h12 : f₁ ≫ p = f₂ ≫ p := by
      rw [hf₁, hf₂]
    have h23 : f₂ ≫ p = f₃ ≫ p := by
      rw [hf₂, hf₃]
    have h13 : f₁ ≫ p = f₃ ≫ p := by
      rw [hf₁, hf₃]
    simpa using (single_to_singleton_hom_aux_comp (F := F) p D f₁ f₂ f₃ h12 h23 h13)

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
  -- Expand the diagonal isomorphisms.
  simp [diag_iso_p1, diag_iso_p2, reindex_comp_iso_obj, reindex_obj_iso_of_eq, reindex_id_iso_obj]
  -- Abbreviate the kernel-pair transition morphism.
  set φ :=
    D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p)
      (by
        simpa using (p1_comp_p_eq_p2_comp_p p).symm)
      (by rfl) with hφ
  -- Rewrite the action of `diag^*` on `φ` using `map_eq_pullHom`.
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
  -- Cancel the `mapComp` isomorphisms.
  simp [Category.assoc]
  -- Identify the pullback of `φ` along the diagonal.
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
  -- Reduce to `hom_self` after simplifying the diagonal composites.
  have hself :
      D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 E) (𝟙 E)
          (by simp) (by simp) =
        𝟙 _ := by
    simpa using
      (D.hom_self (q := p) (i := PUnit.unit) (g := 𝟙 E) (by simp))
  -- Transport the remaining `D.hom` along the diagonal equalities.
  have hdiag2 : Limits.pullback.diagonal p ≫ p2 p = 𝟙 E := by
    simp
  have hdiag1 : Limits.pullback.diagonal p ≫ p1 p = 𝟙 E := by
    simp
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
        (h₁ := hdiag2) (h₂ := hdiag1))
  -- Finish using `hom_self` and pseudofunctor coherence for `mapId`.
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
        -- Avoid `simp`: the lemma `p12_p2_eq_p23_p1` is a simp lemma and would rewrite the goal.
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

  -- Rewrite the three overlap morphisms as `DescentData.hom` on the triple overlap.
  have hx12 :
      xi12 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
          (by simpa using hf12_1) (by simpa using hf12_2) := by
    -- `pullHom` along `p12`.
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p12 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf12_1) (by simpa using hf12_2) := by
      have hq : p12 p ≫ q0 = q3 := rfl
      simpa [φ] using
        (D.pullHom_hom (g := p12 p) (q := q0) (q' := q3) (hq := hq)
          (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
          (hf₁ := by
            simpa [q0] using (p1_comp_p_eq_p2_comp_p p).symm)
          (hf₂ := by rfl)
          (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl))
    simpa [hx12_pull] using hpull

  have hx23 :
      xi23 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
          (by simpa using hf23_1) (by simpa using hf12_1) := by
    -- `pullHom` along `p23`, taking advantage of the fact that `xi23` already uses the transported
    -- leg `p12 ≫ p2`.
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p2 p) (hgf₁ := rfl)
            (hgf₂ := by simp) =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
            (by simpa using hf23_1) (by simpa using hf12_1) := by
      -- `D.pullHom_hom` gives `pullHom ... = D.hom ...` after rewriting along `hq23`.
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

  have hx13 :
      xi13 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf23_1) (by simpa using hf12_2) := by
    -- `pullHom` along `p13`, taking advantage of the fact that `xi13` already uses the transported
    -- legs `p23 ≫ p2` and `p12 ≫ p1`.
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
    simpa [hx13_pull] using hpull

  -- Final cocycle via `D.hom_comp`.
  have hcomp :
      D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
            (by simpa using hf23_1) (by simpa using hf12_1) ≫
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf12_1) (by simpa using hf12_2) =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf23_1) (by simpa using hf12_2) := by
    simp [D.hom_comp]

  -- Rewrite using the three identifications.
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
      simp only [hx23, hx12]
    _ =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa using hf23_1) (by simpa using hf12_2) := hcomp
    _ =
        xi13 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa using (p1_comp_p_eq_p2_comp_p p).symm)).symm.hom := by
      simp only [hx13]

/-- Convert Mathlib's descent data for the singleton family to a single morphism descent datum. -/
def singleton_to_single_descent_data
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) :
    CechDescentData (F := F) p where
  obj := D.obj PUnit.unit
  ξ := by
    -- `D.iso` gives an isomorphism `π₁^* D.obj ≅ π₂^* D.obj`; we store the morphism `π₂^* ⟶ π₁^*`.
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
    -- The compatibility condition follows from f.hom_hom at π₁, π₂
    have hf₁ : p2 p ≫ p = p1 p ≫ p := by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm
    have hf₂ : p1 p ≫ p = p1 p ≫ p := rfl
    -- `f.comm` gives the compatibility for `D₁.hom`/`D₂.hom`; our gluing map is the
    -- corresponding `iso` reversed, hence we take `.symm`.
    simpa [CategoryTheory.Pseudofunctor.DescentData.iso] using
      (f.comm (q := (p1 p ≫ p)) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (f₁ := p2 p) (f₂ := p1 p) hf₁ hf₂).symm⟩

/-!
## Functors
-/

/-- The functor from single-morphism descent data to mathlib descent data. -/
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

/-- The functor from mathlib descent data to single-morphism descent data. -/
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

/-!
## Equivalence
-/

/-- The unit of the equivalence: `D ≅ singletonToSingle (singleToSingleton D)`. -/
def single_singleton_unit (D : CechDescentData (F := F) p) :
    D ≅ (single_to_singleton_functor F p ⋙ singleton_to_single_functor F p).obj D where
  hom := ⟨𝟙 D.obj, by
        -- The ξ's should match up to coherence
    simpa [single_to_singleton_functor, singleton_to_single_functor, single_to_singleton_descent_data,
      singleton_to_single_descent_data] using
        (single_to_singleton_hom_aux_swap (F := F) (p := p) D)⟩
  inv := ⟨𝟙 D.obj, by
    simpa [single_to_singleton_functor, singleton_to_single_functor, single_to_singleton_descent_data,
      singleton_to_single_descent_data] using
        (single_to_singleton_hom_aux_swap (F := F) (p := p) D).symm⟩
  hom_inv_id := by
    apply CechDescentData.Hom.ext
    simp [CechDescentData.instCategory]
  inv_hom_id := by
    apply CechDescentData.Hom.ext
    simp [CechDescentData.instCategory, single_to_singleton_functor, singleton_to_single_functor,
      single_to_singleton_descent_data, singleton_to_single_descent_data, Functor.comp_obj]

private lemma singleton_to_single_inv_ξ
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) :
    inv (singleton_to_single_descent_data (F := F) p D).ξ =
      D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
        (by
          simpa using (p1_comp_p_eq_p2_comp_p p).symm) := by
  have hf_p2 : p2 p ≫ p = (p1 p ≫ p) := by
    simpa using (p1_comp_p_eq_p2_comp_p (p := p)).symm
  simp [singleton_to_single_descent_data, CategoryTheory.Pseudofunctor.DescentData.iso]
  apply IsIso.inv_eq_of_hom_inv_id
  have hcomp :
      D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p) hf_p2 (by rfl) ≫
          D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl) hf_p2 =
        D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p2 p) hf_p2 hf_p2 := by
    exact
      (D.hom_comp (q := (p1 p ≫ p)) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (i₃ := PUnit.unit)
        (f₁ := p2 p) (f₂ := p1 p) (f₃ := p2 p) hf_p2 rfl hf_p2)
  have hself :
      D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p2 p) hf_p2 hf_p2 = 𝟙 _ := by
    exact (D.hom_self (q := (p1 p ≫ p)) (i := PUnit.unit) (g := p2 p) hf_p2)
  simp [hcomp, hself]

private lemma singleton_to_single_pullHom_hom
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p)))
    {Y : C} {q : Y ⟶ B} (f₁ f₂ : Y ⟶ E) (g : Y ⟶ cechKernelPair p)
    (hgf₁ : g ≫ p1 p = f₁) (hgf₂ : g ≫ p2 p = f₂) (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) :
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
          (by
            simpa using (p1_comp_p_eq_p2_comp_p p).symm))
        g f₁ f₂ hgf₁ hgf₂ =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂ hf₁ hf₂ := by
  have hq : g ≫ (p1 p ≫ p) = q := by
    rw [← Category.assoc, hgf₁, hf₁]
  simpa using
    (D.pullHom_hom (g := g) (q := p1 p ≫ p) (q' := q) (hq := hq)
      (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (f₁ := p1 p) (f₂ := p2 p)
      (hf₁ := by rfl)
      (hf₂ := by
        simpa using (p1_comp_p_eq_p2_comp_p p).symm)
      (gf₁ := f₁) (gf₂ := f₂)
      (hgf₁ := hgf₁)
      (hgf₂ := hgf₂))

/-- The counit of the equivalence: `singleToSingleton (singletonToSingle D) ≅ D`. -/
def single_singleton_counit
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) :
    (singleton_to_single_functor F p ⋙ single_to_singleton_functor F p).obj D ≅ D where
  hom := ⟨fun _ => 𝟙 (D.obj PUnit.unit), by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    cases i₁; cases i₂
    let g : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ (by rw [hf₁, hf₂])
    have hinvξ :
        inv (singleton_to_single_descent_data (F := F) p D).ξ =
          D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
            (by
              simpa using (p1_comp_p_eq_p2_comp_p p).symm) :=
      singleton_to_single_inv_ξ (F := F) (p := p) D
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
              (by
                simpa using (p1_comp_p_eq_p2_comp_p p).symm))
            g f₁ f₂
            (by simp [g])
            (by simp [g]) =
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              hf₁
              hf₂ := by
      simpa using
        (singleton_to_single_pullHom_hom (F := F) (p := p) D (f₁ := f₁) (f₂ := f₂) (g := g)
          (hgf₁ := by simp [g]) (hgf₂ := by simp [g]) (hf₁ := hf₁) (hf₂ := hf₂))
    have hmap₁ :
        (F.map f₁.op.toLoc).toFunctor.map (𝟙 (D.obj PUnit.unit)) =
          𝟙 ((F.map f₁.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) := by
      simp
    have hmap₂ :
        (F.map f₂.op.toLoc).toFunctor.map (𝟙 (D.obj PUnit.unit)) =
          𝟙 ((F.map f₂.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) := by
      simp
    -- Simplify away the identity components of the morphism of descent data.
    simp [single_to_singleton_functor, singleton_to_single_functor, single_to_singleton_descent_data,
      single_to_singleton_hom_aux, hinvξ, hmap₁, hmap₂]
    let pull :=
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
            (by
              simpa using (p1_comp_p_eq_p2_comp_p p).symm))
          g f₁ f₂
          (by simp [g])
          (by simp [g])
    have hcore : D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
        hf₁
        hf₂ = pull := by
      simpa [pull] using hpull.symm
    calc
      𝟙 ((F.map f₁.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) ≫
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              hf₁
              hf₂ =
            D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              hf₁
              hf₂ := by
        simp
      _ = pull := hcore
      _ = pull ≫ 𝟙 ((F.map f₂.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) := by
        simp⟩
  inv := ⟨fun _ => 𝟙 (D.obj PUnit.unit), by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    cases i₁; cases i₂
    let g : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ (by rw [hf₁, hf₂])
    have hinvξ :
        inv (singleton_to_single_descent_data (F := F) p D).ξ =
          D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
            (by
              simpa using (p1_comp_p_eq_p2_comp_p p).symm) :=
      singleton_to_single_inv_ξ (F := F) (p := p) D
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
              (by
                simpa using (p1_comp_p_eq_p2_comp_p p).symm))
            g f₁ f₂
            (by simp [g])
            (by simp [g]) =
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              hf₁
              hf₂ := by
      simpa using
        (singleton_to_single_pullHom_hom (F := F) (p := p) D (f₁ := f₁) (f₂ := f₂) (g := g)
          (hgf₁ := by simp [g]) (hgf₂ := by simp [g]) (hf₁ := hf₁) (hf₂ := hf₂))
    simpa [single_to_singleton_functor, singleton_to_single_functor, single_to_singleton_descent_data,
      single_to_singleton_hom_aux, g, hinvξ] using hpull⟩
  hom_inv_id := by
    ext i
    cases i
    simp only [CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom, Functor.comp_obj,
      single_to_singleton_functor, singleton_to_single_functor, single_to_singleton_descent_data,
      singleton_to_single_descent_data, Category.comp_id]
  inv_hom_id := by
    ext i
    cases i
    simp

/-- The equivalence between single-morphism descent data and Mathlib's descent data
for the singleton family. -/
def single_singleton_descent_data_equiv :
    CechDescentData (F := F) p ≌
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := fun _ : PUnit.{1} ↦ p) where
  functor := single_to_singleton_functor F p
  inverse := singleton_to_single_functor F p
  unitIso := NatIso.ofComponents (single_singleton_unit F p) (fun {_ _} f ↦ by
    apply CechDescentData.Hom.ext
    simp [CechDescentData.instCategory, single_to_singleton_functor,
      singleton_to_single_functor, single_singleton_unit, single_to_singleton_hom,
      singleton_to_single_hom, single_to_singleton_descent_data, singleton_to_single_descent_data,
      Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
      Category.id_comp, Category.comp_id])
  counitIso := NatIso.ofComponents (single_singleton_counit F p) (fun {_ _} f ↦ by
    ext i
    cases i
    simp only [single_to_singleton_functor, singleton_to_single_functor, single_singleton_counit,
      single_to_singleton_hom, singleton_to_single_hom, single_to_singleton_descent_data,
      singleton_to_single_descent_data, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map, CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      Category.id_comp, Category.comp_id])
  functor_unitIso_comp X := by
    ext i
    cases i
    simp only [single_to_singleton_functor, singleton_to_single_functor, single_singleton_unit,
      single_singleton_counit, single_to_singleton_hom, single_to_singleton_descent_data,
      singleton_to_single_descent_data, Functor.comp_obj, Functor.id_obj,
      NatIso.ofComponents_hom_app, Category.comp_id,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom]

/-- The comparison functor `Φₚ : F(B) ⥤ Des_F(p)` from the paper (Facets of Descent II, §3.2),
landing in the Čech-style descent data defined in `CechDescentData.lean`.

It is defined as `F.toDescentData` for the singleton family, followed by the (inverse) functor
from Mathlib's descent data to our Čech-style descent data. -/
noncomputable def single_morphism_comparison_functor :
    F.obj (.mk (op B)) ⥤ CechDescentData (F := F) p :=
  (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := (fun _ : PUnit.{1} ↦ p))) ⋙
    singleton_to_single_functor (F := F) p

/-- `p` is a descent morphism for `F` if the comparison functor `Φₚ` is fully faithful
(Facets of Descent II, §3.2). -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (single_morphism_comparison_functor (F := F) p).FullyFaithful

/-- `p` is an effective descent morphism for `F` if the comparison functor `Φₚ` is an equivalence
of categories (Facets of Descent II, §3.2). -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (single_morphism_comparison_functor (F := F) p).IsEquivalence

/-!
## Relation with Mathlib's `IsPrestackFor`/`IsStackFor` for `Presieve.singleton p`

Mathlib’s descent theory is formulated for arbitrary presieves `R` via the functor
`F.toDescentData (fun (f : R.category) ↦ f.obj.hom)`. In the singleton case, the presieve
`Presieve.singleton p` is (definitionally) the same as `Presieve.ofArrows _ (fun _ : PUnit.{1} ↦ p)`,
see `CategoryTheory.Presieve.ofArrows_pUnit`.

The functor `single_morphism_comparison_functor` differs from `F.toDescentData` only by postcomposition
with the (inverse) equivalence `singleton_to_single_functor`, so it has the same “fully faithful” and
“is equivalence” properties.
-/

theorem is_descent_morphism_iff_to_descent_data_fully_faithful :
    IsDescentMorphism (F := F) p ↔
      Nonempty (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).FullyFaithful := by
  let e := single_singleton_descent_data_equiv (F := F) p
  let G := CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)
  let H := singleton_to_single_functor (F := F) p
  have hH : H.FullyFaithful := by
    simpa [H, e, single_singleton_descent_data_equiv] using e.fullyFaithfulInverse
  haveI : H.Faithful := by
    simpa [H, e, single_singleton_descent_data_equiv] using (show e.inverse.Faithful from inferInstance)
  refine ⟨fun ⟨hGH⟩ ↦ ?_, fun ⟨hG⟩ ↦ ?_⟩
  ·
    refine ⟨CategoryTheory.Functor.FullyFaithful.ofCompFaithful (F := G) (G := H) ?_⟩
    simpa [single_morphism_comparison_functor, G, H] using hGH
  ·
    refine ⟨?_⟩
    simpa [single_morphism_comparison_functor, G, H] using hG.comp hH

theorem is_effective_descent_morphism_iff_to_descent_data_equivalence :
    IsEffectiveDescentMorphism (F := F) p ↔
      (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).IsEquivalence := by
  let e := single_singleton_descent_data_equiv (F := F) p
  let G := CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)
  let H := singleton_to_single_functor (F := F) p
  haveI : H.IsEquivalence := by
    simpa [H, e, single_singleton_descent_data_equiv] using (show e.inverse.IsEquivalence from inferInstance)
  refine ⟨fun hGH ↦ ?_, fun hG ↦ ?_⟩
  ·
    have : (G ⋙ H).IsEquivalence := by simpa [single_morphism_comparison_functor, G, H] using hGH
    -- cancel the equivalence `H` on the right
    haveI : (G ⋙ H).IsEquivalence := this
    exact CategoryTheory.Functor.isEquivalence_of_comp_right G H
  ·
    haveI : G.IsEquivalence := hG
    -- composition with an equivalence is an equivalence
    have : (G ⋙ H).IsEquivalence := by infer_instance
    simpa [single_morphism_comparison_functor, G, H] using this

theorem is_prestack_for_singleton_iff_descent_morphism :
    CategoryTheory.Pseudofunctor.IsPrestackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
      IsDescentMorphism (F := F) p := by
  have hPresieve :
      CategoryTheory.Presieve.ofArrows (fun _ : PUnit.{1} ↦ E) (fun _ : PUnit.{1} ↦ p) =
        CategoryTheory.Presieve.singleton p := by
    simpa using (CategoryTheory.Presieve.ofArrows_pUnit (f := p))
  have h :
      CategoryTheory.Pseudofunctor.IsPrestackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
        Nonempty (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).FullyFaithful := by
    simpa [hPresieve] using
      (CategoryTheory.Pseudofunctor.isPrestackFor_ofArrows_iff (F := F) (S := B)
        (f := fun _ : PUnit.{1} ↦ p))
  let hd := is_descent_morphism_iff_to_descent_data_fully_faithful (F := F) p
  refine ⟨fun hstack ↦ ?_, fun hdesc ↦ ?_⟩
  · exact hd.2 (h.1 hstack)
  · exact h.2 (hd.1 hdesc)

theorem is_stack_for_singleton_iff_effective_descent_morphism :
    CategoryTheory.Pseudofunctor.IsStackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
      IsEffectiveDescentMorphism (F := F) p := by
  have hPresieve :
      CategoryTheory.Presieve.ofArrows (fun _ : PUnit.{1} ↦ E) (fun _ : PUnit.{1} ↦ p) =
        CategoryTheory.Presieve.singleton p := by
    simpa using (CategoryTheory.Presieve.ofArrows_pUnit (f := p))
  have h :
      CategoryTheory.Pseudofunctor.IsStackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
        (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := fun _ : PUnit.{1} ↦ p)).IsEquivalence := by
    simpa [hPresieve] using
      (CategoryTheory.Pseudofunctor.isStackFor_ofArrows_iff (F := F) (S := B)
        (f := fun _ : PUnit.{1} ↦ p))
  let he := is_effective_descent_morphism_iff_to_descent_data_equivalence (F := F) p
  refine ⟨fun hstack ↦ ?_, fun hdesc ↦ ?_⟩
  · exact he.2 (h.1 hstack)
  · exact h.2 (he.1 hdesc)

end

end Descent.Pseudofunctor.Descent
