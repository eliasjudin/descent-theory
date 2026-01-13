/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
import Descent.Pseudofunctor.Descent.SingleMorphism

/-!
# Equivalence with mathlib's descent data

Relates `SingleMorphismDescentData` for `p : E ⟶ B` to mathlib's
`Pseudofunctor.DescentData` for the singleton family `fun _ : PUnit => p`.
Main definitions: `singleToSingletonDescentDatum`, `singletonToSingleDescentDatum`,
`singleToSingletonFunctor`, `singletonToSingleFunctor`, `singleSingletonDescentDataEquiv`.

## TODO (Facets of Descent, II)

* [RESEARCH] Define “absolutely effective descent” as in §3.2: `p` is an effective descent morphism
  for every `C`-indexed category (pseudofunctor) `A : Cᵒᵖ ⥤ CAT`, and connect this to the
  fibered-category formulation via Grothendieck fibrations (cf. §3.3).
* [RESEARCH] Prove Theorem 3.5 (split epis ↔ absolutely effective descent):
  - “if”: for a section `s : B ⟶ E` of `p`, show the comparison functor `Φₚ` is an equivalence for all
    indexed categories (following the paper via the internal-category equivalence `p̄ : Eq(p) ≃ B`,
    or by a direct construction avoiding `cat(C)`).
  - “only if”: formalize the indexed category `A_p` from the proof (objects `C(X,E)` with morphisms
    given by the relation `p u = p v`) and use essential surjectivity/full faithfulness of `Φₚ` to
    extract a section of `p`.
* [RESEARCH] Implement the basic equivalence diagram (BED) from §4.1–§4.2 for a commutative square (20), and
  define what it means for an indexed category to respect a BED (§4.4). Use this to prove the
  composition-cancellation theorem (Theorem 4.5) for effective descent morphisms.
* [RESEARCH] Define `A`-locally-split epimorphisms (§5.1) and prove Theorem 5.2 using composition-cancellation.
  Connect §5.3 to Mathlib’s `IsStack`/`IsPrestack` API on sites by expressing the paper’s “stack”
  hypothesis in those terms.
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

open Opposite
open Descent.Cech
open Descent.Pseudofunctor

universe v' v u' u

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

variable {E B : C} (p : E ⟶ B)

/-- The singleton morphism family `∀ i, E ⟶ B` mapping everything to `p`. -/
abbrev singletonMorphism : ∀ (_ : PUnit.{1}), E ⟶ B := fun _ => p

/-!
## Helper: pulling back the Čech glueing isomorphism
-/

/-- Given Čech-style descent data `D` for `p : E ⟶ B`, this is the induced morphism
`f₁^* D.obj ⟶ f₂^* D.obj` for any `f₁ f₂ : Y ⟶ E` with `f₁ ≫ p = f₂ ≫ p`.

We define it by pulling back `D.ξ.inv : π₁^* D.obj ⟶ π₂^* D.obj` along the canonical
map `Y ⟶ E ×_B E`. -/
def singleToSingletonHomAux (D : SingleMorphismDescentData (F := F) p) {Y : C} (f₁ f₂ : Y ⟶ E)
    (h : f₁ ≫ p = f₂ ≫ p) :
    (F.map f₁.op.toLoc).toFunctor.obj D.obj ⟶ (F.map f₂.op.toLoc).toFunctor.obj D.obj := by
  let u : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ h
  have hu1 : u ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu2 : u ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
  exact CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
    (φ := D.ξ.inv) u f₁ f₂ hu1 hu2

private lemma singleToSingletonHomAux_comp
    (D : SingleMorphismDescentData (F := F) p) {Y : C} (f₁ f₂ f₃ : Y ⟶ E)
    (h12 : f₁ ≫ p = f₂ ≫ p) (h23 : f₂ ≫ p = f₃ ≫ p) (h13 : f₁ ≫ p = f₃ ≫ p) :
    singleToSingletonHomAux F p D f₁ f₂ h12 ≫
        singleToSingletonHomAux F p D f₂ f₃ h23 =
      singleToSingletonHomAux F p D f₁ f₃ h13 := by
  classical
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
  have hv12_p1 : v ≫ (p12 p ≫ p1 p) = f₁ := by simpa [Category.assoc, hv12] using hu12_1
  have hv12_p2 : v ≫ (p12 p ≫ p2 p) = f₂ := by simpa [Category.assoc, hv12] using hu12_2
  have hv23_p1 : v ≫ (p23 p ≫ p1 p) = f₂ := by simpa [Category.assoc, hv23] using hu23_1
  have hv23_p2 : v ≫ (p23 p ≫ p2 p) = f₃ := by simpa [Category.assoc, hv23] using hu23_2
  have hv13 : v ≫ p13 p = u13 := by
    apply Limits.pullback.hom_ext <;>
      simp [Category.assoc, hv12, hv23, hu12_1, hu23_2, hu13_1, hu13_2]
  -- Provide `IsIso` instances for the Čech morphisms.
  letI : IsIso (xi12 (F := F) p D.ξ) := by
    dsimp [xi12]
    infer_instance
  letI : IsIso (xi23 (F := F) p D.ξ) := by
    dsimp [xi23]
    infer_instance
  letI : IsIso (xi13 (F := F) p D.ξ) := by
    dsimp [xi13]
    infer_instance
  -- Identify the pullbacks of the Čech morphisms.
  have hmapInv {Y : C} (g : Y ⟶ cechKernelPair p) :
      (F.map g.op.toLoc).toFunctor.map D.ξ.inv =
        inv ((F.map g.op.toLoc).toFunctor.map D.ξ.hom) := by
    simpa using
      (Functor.map_inv (F := (F.map g.op.toLoc).toFunctor) (f := D.ξ.hom))
  have hphi12 :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := D.ξ.inv) (g := p12 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p12 p ≫ p2 p)
          (hgf₁ := by simp) (hgf₂ := by simp) =
        inv (xi12 (F := F) p D.ξ) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, xi12, reindexCompIsoObj,
      reindex, CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, IsIso.inv_comp, Category.assoc,
      hmapInv (g := p12 p)]
  have hphi23 :
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := D.ξ.inv) (g := p23 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p23 p ≫ p2 p)
          (hgf₁ := by simp) (hgf₂ := by simp) =
        inv (xi23 (F := F) p D.ξ) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, xi23, reindexCompIsoObj,
      reindex, CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.PrelaxFunctor.map₂_eqToHom,
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
          (φ := D.ξ.inv) (g := p13 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p23 p ≫ p2 p)
          (hgf₁ := by simp) (hgf₂ := by simp) =
        inv (xi13 (F := F) p D.ξ) := by
    simp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom, xi13, reindexCompIsoObj,
      reindex, CategoryTheory.Pseudofunctor.mapComp', CategoryTheory.PrelaxFunctor.map₂_eqToHom,
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
      singleToSingletonHomAux F p D f₁ f₂ h12 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi12 (F := F) p D.ξ)) (g := v) (gf₁ := f₁) (gf₂ := f₂)
          (hgf₁ := hv12_p1) (hgf₂ := hv12_p2) := by
    -- Pull back along `v ≫ p12 = u12`.
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := D.ξ.inv) (g := p12 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p12 p ≫ p2 p)
      (g' := v) (g'f₁ := f₁) (g'f₂ := f₂)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p1) (hg'f₂ := hv12_p2))
    -- Use `hphi12` to identify the inner pullback.
    simpa [singleToSingletonHomAux, u12, hv12, hphi12] using h.symm
  have haux23 :
      singleToSingletonHomAux F p D f₂ f₃ h23 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi23 (F := F) p D.ξ)) (g := v) (gf₁ := f₂) (gf₂ := f₃)
          (hgf₁ := hv12_p2) (hgf₂ := hv23_p2) := by
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := D.ξ.inv) (g := p23 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p23 p ≫ p2 p)
      (g' := v) (g'f₁ := f₂) (g'f₂ := f₃)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p2) (hg'f₂ := hv23_p2))
    simpa [singleToSingletonHomAux, u23, hv23, hphi23] using h.symm
  have haux13 :
      singleToSingletonHomAux F p D f₁ f₃ h13 =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
          (φ := inv (xi13 (F := F) p D.ξ)) (g := v) (gf₁ := f₁) (gf₂ := f₃)
          (hgf₁ := hv12_p1) (hgf₂ := hv23_p2) := by
    have h := (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
      (φ := D.ξ.inv) (g := p13 p) (gf₁ := p12 p ≫ p1 p) (gf₂ := p23 p ≫ p2 p)
      (g' := v) (g'f₁ := f₁) (g'f₂ := f₃)
      (hgf₁ := by simp) (hgf₂ := by simp)
      (hg'f₁ := hv12_p1) (hg'f₂ := hv23_p2))
    simpa [singleToSingletonHomAux, u13, hv13, hphi13] using h.symm
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
    simpa [IsIso.inv_comp] using congrArg (fun t => inv t) D.cocycle
  -- Assemble.
  simp [haux12, haux23, haux13, hcomp_pull, h_cocycle_inv]

private lemma singleToSingletonHomAux_self
    (D : SingleMorphismDescentData (F := F) p) {Y : C} (g : Y ⟶ E) :
    singleToSingletonHomAux F p D g g (by rfl) = 𝟙 _ := by
  -- Use idempotence + isomorphism to deduce identity.
  let f := singleToSingletonHomAux F p D g g (by rfl)
  have hcomp : f ≫ f = f := by
    simpa [f] using
      (singleToSingletonHomAux_comp (F := F) (p := p) D g g g (by rfl) (by rfl) (by rfl))
  have hIso : IsIso f := by
    dsimp [f, singleToSingletonHomAux, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance
  letI : IsIso f := hIso
  have h' := congrArg (fun t => inv f ≫ t) hcomp
  simpa [Category.assoc] using h'

private lemma singleToSingletonHomAux_p1_p2
    (D : SingleMorphismDescentData (F := F) p) :
    singleToSingletonHomAux F p D (p1 p) (p2 p) (p1_comp_p_eq_p2_comp_p p) = D.ξ.inv := by
  classical
  let u : cechKernelPair p ⟶ cechKernelPair p :=
    Limits.pullback.lift (p1 p) (p2 p) (p1_comp_p_eq_p2_comp_p p)
  have hu : u = 𝟙 _ := by
    apply Limits.pullback.hom_ext <;> simp [u]
  simp [singleToSingletonHomAux, u, hu]

private lemma singleToSingletonHomAux_swap
    (D : SingleMorphismDescentData (F := F) p) :
    D.ξ.hom =
      singleToSingletonHomAux F p D (p2 p) (p1 p)
        (by simpa using (p1_comp_p_eq_p2_comp_p p).symm) := by
  have h12 : p1 p ≫ p = p2 p ≫ p := p1_comp_p_eq_p2_comp_p p
  have h21 : p2 p ≫ p = p1 p ≫ p := by simpa using h12.symm
  have hB :
      singleToSingletonHomAux F p D (p1 p) (p2 p) h12 = D.ξ.inv := by
    simpa using (singleToSingletonHomAux_p1_p2 (F := F) p D)
  have hcomp :
      singleToSingletonHomAux F p D (p2 p) (p1 p) h21 ≫
          singleToSingletonHomAux F p D (p1 p) (p2 p) h12 = 𝟙 _ := by
    simpa [singleToSingletonHomAux_self (F := F) p D (p2 p)] using
      (singleToSingletonHomAux_comp (F := F) (p := p) D (p2 p) (p1 p) (p2 p) h21 h12 rfl)
  have hcomp' :
      singleToSingletonHomAux F p D (p2 p) (p1 p) h21 ≫ D.ξ.inv = 𝟙 _ := by
    simpa [hB] using hcomp
  have hinv :
      inv D.ξ.inv =
        singleToSingletonHomAux F p D (p2 p) (p1 p) h21 :=
    (IsIso.inv_eq_of_inv_hom_id
      (f := D.ξ.inv)
      (g := singleToSingletonHomAux F p D (p2 p) (p1 p) h21)
      hcomp')
  simpa using hinv

private lemma singleToSingletonHomAux_comm {D₁ D₂ : SingleMorphismDescentData (F := F) p}
    (f : D₁ ⟶ D₂) {Y : C} (g₁ g₂ : Y ⟶ E) (h : g₁ ≫ p = g₂ ≫ p) :
    (F.map g₁.op.toLoc).toFunctor.map f.hom ≫ singleToSingletonHomAux F p D₂ g₁ g₂ h =
      singleToSingletonHomAux F p D₁ g₁ g₂ h ≫
        (F.map g₂.op.toLoc).toFunctor.map f.hom := by
  classical
  -- Rewrite `f.comm` in terms of `ξ.inv`.
  have hcomm_inv :
      (F.map (p1 p).op.toLoc).toFunctor.map f.hom ≫ D₂.ξ.inv =
        D₁.ξ.inv ≫ (F.map (p2 p).op.toLoc).toFunctor.map f.hom := by
    have := congrArg (fun t => D₁.ξ.inv ≫ t ≫ D₂.ξ.inv) f.comm
    simpa [Descent.Pseudofunctor.reindex, Category.assoc] using this
  -- Expand `singleToSingletonHomAux` and reduce to coherence for `mapComp'`.
  simp [singleToSingletonHomAux, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Category.assoc]
  -- Apply the compatibility relation after reindexing along `u`.
  have hmap :
      (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
            ((F.map (p1 p).op.toLoc).toFunctor.map f.hom) ≫
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map D₂.ξ.inv =
        (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map D₁.ξ.inv ≫
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
            ((F.map (p2 p).op.toLoc).toFunctor.map f.hom) := by
    have :=
      congrArg
        (fun t =>
          (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map t)
        hcomm_inv
    simpa [Functor.map_comp] using this
  -- Finish using `mapComp'_inv_naturality` (simp lemma) and associativity.
  rw [← Category.assoc
    (f :=
      (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map
        ((F.map (p1 p).op.toLoc).toFunctor.map f.hom))
    (g := (F.map (Limits.pullback.lift g₁ g₂ h).op.toLoc).toFunctor.map D₂.ξ.inv)]
  rw [hmap]
  simp [Category.assoc]

/-!
## Forward direction: Single → Singleton
-/

/-- Convert a single morphism descent datum to mathlib's descent data for the singleton family.

The key mapping:
- `obj ()` := `D.obj`
- `hom q f₁ f₂` at Y mapping to E comes from `D.ξ` transported appropriately -/
def singleToSingletonDescentDatum (D : SingleMorphismDescentData (F := F) p) :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  obj := fun _ => D.obj
  hom := fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ => by
    cases i₁; cases i₂ -- Both are PUnit.unit
    have h : f₁ ≫ p = f₂ ≫ p := by
      simp only [singletonMorphism] at hf₁ hf₂
      rw [hf₁, hf₂]
    exact singleToSingletonHomAux (F := F) p D f₁ f₂ h
  pullHom_hom := by
    intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    cases i₁; cases i₂
    -- Expand the definition of `hom` on both sides.
    -- Both sides are pullbacks of `D.ξ.inv` along the corresponding maps into `cechKernelPair p`.
    have hf₁' : f₁ ≫ p = f₂ ≫ p := by
      simp only [singletonMorphism] at hf₁ hf₂
      rw [hf₁, hf₂]
    have hgf₁' : gf₁ ≫ p = gf₂ ≫ p := by
      -- both are equal to `q'`
      simp only [singletonMorphism] at hf₁ hf₂
      have h₁ : gf₁ ≫ p = q' := by simpa [Category.assoc, hgf₁, hf₁] using hq
      have h₂ : gf₂ ≫ p = q' := by simpa [Category.assoc, hgf₂, hf₂] using hq
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
    simp [singleToSingletonHomAux, u, u', hg_u]
  hom_self := by
    intro Y q i g hg
    cases i
    simpa using (singleToSingletonHomAux_self (F := F) p D g)
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    cases i₁; cases i₂; cases i₃
    have h12 : f₁ ≫ p = f₂ ≫ p := by
      simp [singletonMorphism] at hf₁ hf₂
      rw [hf₁, hf₂]
    have h23 : f₂ ≫ p = f₃ ≫ p := by
      simp [singletonMorphism] at hf₂ hf₃
      rw [hf₂, hf₃]
    have h13 : f₁ ≫ p = f₃ ≫ p := by
      simp [singletonMorphism] at hf₁ hf₃
      rw [hf₁, hf₃]
    simpa using (singleToSingletonHomAux_comp (F := F) p D f₁ f₂ f₃ h12 h23 h13)

/-!
## Helper: transport for `DescentData.hom`

`simp` does not rewrite inside the dependent expression `D.hom q f₁ f₂`, since its type depends on
`f₁` and `f₂`. We use the standard `eqToHom` transports instead.
-/

omit [Limits.HasPullbacks C] in
private lemma descentData_hom_congr
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) {Y : C}
    (q : Y ⟶ B) {f₁ f₁' f₂ f₂' : Y ⟶ E} (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) (hf₁' : f₁' ≫ p = q)
    (hf₂' : f₂' ≫ p = q) (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') :
    eqToHom
          (by
            simpa using
              (congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₁).symm) ≫
        D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
            (by simpa [singletonMorphism] using hf₁) (by simpa [singletonMorphism] using hf₂) ≫
      eqToHom
          (by
            simpa using congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₂) =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁' f₂'
          (by simpa [singletonMorphism] using hf₁') (by simpa [singletonMorphism] using hf₂') := by
  cases h₁
  cases h₂
  simp

omit [Limits.HasPullbacks C] in
private lemma descentData_hom_congr'
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) {Y : C} (q : Y ⟶ B)
    {f₁ f₁' f₂ f₂' : Y ⟶ E} (hf₁ : f₁ ≫ p = q) (hf₂ : f₂ ≫ p = q) (h₁ : f₁ = f₁')
    (h₂ : f₂ = f₂') :
    eqToHom
          (by
            simpa using
              (congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₁).symm) ≫
        D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
            (by simpa [singletonMorphism] using hf₁) (by simpa [singletonMorphism] using hf₂) ≫
      eqToHom
          (by
            simpa using congrArg (fun k => (F.map k.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) h₂) =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁' f₂'
          (by simpa [h₁, singletonMorphism] using hf₁) (by simpa [h₂, singletonMorphism] using hf₂) := by
  cases h₁
  cases h₂
  simp

private lemma singletonToSingle_unit
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
    (diagIsoP2 (F := F) p (D.obj PUnit.unit)).inv ≫
        (reindex F (Limits.pullback.diagonal p)).map
            (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p)
              (by
                simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)
              (by rfl)) ≫
        (diagIsoP1 (F := F) p (D.obj PUnit.unit)).hom =
      𝟙 (D.obj PUnit.unit) := by
  classical
  -- Expand the diagonal isomorphisms.
  simp [diagIsoP1, diagIsoP2, reindexCompIsoObj, reindexObjIsoOfEq, reindexIdIsoObj]
  -- Abbreviate the kernel-pair transition morphism.
  set φ :=
    D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p2 p) (p1 p)
      (by
        simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)
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
            simp [singletonMorphism])
          (by
            simp [singletonMorphism]) := by
    simpa [φ, hq] using
      (D.pullHom_hom (g := Limits.pullback.diagonal p)
        (q := p1 p ≫ p) (q' := p) (hq := hq)
        (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (f₁ := p2 p) (f₂ := p1 p)
        (hf₁ := by
          simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)
        (hf₂ := by rfl)
        (gf₁ := Limits.pullback.diagonal p ≫ p2 p)
        (gf₂ := Limits.pullback.diagonal p ≫ p1 p)
        (hgf₁ := rfl) (hgf₂ := rfl))
  rw [hpull]
  -- Reduce to `hom_self` after simplifying the diagonal composites.
  have hself :
      D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 E) (𝟙 E)
          (by simp [singletonMorphism]) (by simp [singletonMorphism]) =
        𝟙 _ := by
    simpa using
      (D.hom_self (q := p) (i := PUnit.unit) (g := 𝟙 E) (by simp [singletonMorphism]))
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
                simp [singletonMorphism])
              (by
                simp [singletonMorphism]) ≫
        eqToHom
            (by
              simp) =
        D.hom p (i₁ := PUnit.unit) (i₂ := PUnit.unit) (𝟙 E) (𝟙 E)
            (by simp [singletonMorphism]) (by simp [singletonMorphism]) := by
    simpa using
      (descentData_hom_congr (F := F) (p := p) (D := D) (q := p)
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
  simpa [singletonMorphism, hself] using congrArg (fun t =>
    (F.mapId { as := op E }).inv.toNatTrans.app (D.obj PUnit.unit) ≫ t ≫
      (F.mapId { as := op E }).hom.toNatTrans.app (D.obj PUnit.unit)) hhom

private lemma singletonToSingle_cocycle
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
  xi23 (F := F) p
        (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
          (by rfl)
          (by
            simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm ≫
      xi12 (F := F) p
        (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
          (by rfl)
          (by
            simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
      xi13 (F := F) p
        (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
          (by rfl)
          (by
            simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm := by
  classical
  let q0 : cechKernelPair p ⟶ B := p1 p ≫ p
  let q3 : cechTripleOverlap p ⟶ B := p12 p ≫ q0
  have hq23 : p23 p ≫ q0 = q3 := by
    dsimp [q0, q3]
    have h₁ : (p23 p ≫ p1 p) ≫ p = (p12 p ≫ p2 p) ≫ p := by
      simpa using congrArg (fun k => k ≫ p) (p12_p2_eq_p23_p1 (p := p)).symm
    have h₂ : (p12 p ≫ p2 p) ≫ p = (p12 p ≫ p1 p) ≫ p := by
      -- rewrite `p2 ≫ p` to `p1 ≫ p` using the kernel-pair condition
      have :
          p12 p ≫ (p2 p ≫ p) = p12 p ≫ (p1 p ≫ p) := by
        simpa using congrArg (fun k => p12 p ≫ k) (p1_comp_p_eq_p2_comp_p (p := p)).symm
      simpa [Category.assoc] using this
    simpa [Category.assoc] using h₁.trans h₂
  have hq13 : p13 p ≫ q0 = q3 := by
    dsimp [q0, q3]
    simp [Category.assoc]
  have hf12_1 : (p12 p ≫ p2 p) ≫ p = q3 := by
    dsimp [q0, q3]
    simpa [Category.assoc] using
      congrArg (fun k => p12 p ≫ k) (p1_comp_p_eq_p2_comp_p (p := p)).symm
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
      (by simpa [singletonMorphism, q0] using (p1_comp_p_eq_p2_comp_p p).symm)
      (by rfl) with hφ

  have hx12_pull :
      xi12 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
          (g := p12 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) := by
    simp [xi12, reindexCompIsoObj, reindex, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, CategoryTheory.Pseudofunctor.DescentData.iso, hφ, q0]

  have hx23_pull :
      xi23 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p23 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) ≫
          (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom := by
    simp [xi23, reindexCompIsoObj, reindex, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, CategoryTheory.Pseudofunctor.DescentData.iso, hφ, q0,
      reindexObjIsoOfEq_hom]

  have hx13_pull :
      xi13 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom ≫
          CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p13 p) (gf₁ := p13 p ≫ p2 p) (gf₂ := p13 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) ≫
            (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom := by
    simp [xi13, reindexCompIsoObj, reindex, CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      CategoryTheory.Pseudofunctor.mapComp'_eq_mapComp, CategoryTheory.Pseudofunctor.DescentData.iso, hφ, q0,
      reindexObjIsoOfEq_hom]

  -- Rewrite the three overlap morphisms as `DescentData.hom` on the triple overlap.
  have hx12 :
      xi12 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
          (by simpa [singletonMorphism] using hf12_1) (by simpa [singletonMorphism] using hf12_2) := by
    -- `pullHom` along `p12`.
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p12 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf12_1) (by simpa [singletonMorphism] using hf12_2) := by
      have hq : p12 p ≫ q0 = q3 := rfl
      simpa [φ] using
        (D.pullHom_hom (g := p12 p) (q := q0) (q' := q3) (hq := hq)
          (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
          (hf₁ := by
            simpa [singletonMorphism, q0] using (p1_comp_p_eq_p2_comp_p p).symm)
          (hf₂ := by rfl)
          (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl))
    simpa [hx12_pull] using hpull

  have hx23 :
      xi23 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
          (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_1) := by
    -- `pullHom` along `p23` and transport the codomain using `p12_p2_eq_p23_p1`.
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p23 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p23 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf23_2) := by
      simpa [φ, hq23] using
        (D.pullHom_hom (g := p23 p) (q := q0) (q' := q3) (hq := hq23)
          (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
          (hf₁ := by
            simpa [singletonMorphism, q0] using (p1_comp_p_eq_p2_comp_p p).symm)
          (hf₂ := by rfl)
          (gf₁ := p23 p ≫ p2 p) (gf₂ := p23 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl))
    -- Now absorb the final `eqToHom` transport into `DescentData.hom`.
    have htrans :
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p23 p ≫ p1 p)
              (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf23_2) ≫
            (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
              (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_1) := by
      -- Transport along the equality `p23 ≫ p1 = p12 ≫ p2`.
      have h₂ : p23 p ≫ p1 p = p12 p ≫ p2 p := (p12_p2_eq_p23_p1 (p := p)).symm
      simpa [reindexObjIsoOfEq_hom, Category.assoc] using
        (descentData_hom_congr' (F := F) (p := p) (D := D) (q := q3) (f₁ := p23 p ≫ p2 p)
          (f₂ := p23 p ≫ p1 p) (f₁' := p23 p ≫ p2 p) (f₂' := p12 p ≫ p2 p) (hf₁ := hf23_1)
          (hf₂ := hf23_2) (h₁ := rfl) (h₂ := h₂))
    -- Put everything together.
    calc
      xi23 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
          CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
              (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p23 p ≫ p1 p) (hgf₁ := rfl)
              (hgf₂ := rfl) ≫
            (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom := hx23_pull
      _ =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p23 p ≫ p1 p)
              (by simpa [singletonMorphism] using hf23_1)
              (by simpa [singletonMorphism] using hf23_2) ≫
            (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom := by
          simp [hpull]
      _ =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
              (by simpa [singletonMorphism] using hf23_1)
              (by simpa [singletonMorphism] using hf12_1) := by
          simpa [Category.assoc] using htrans

  have hx13 :
      xi13 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
          (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_2) := by
    -- `pullHom` along `p13` and transport domain/codomain using `p13_p2` and `p13_p1`.
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
            (g := p13 p) (gf₁ := p13 p ≫ p2 p) (gf₂ := p13 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl) =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p13 p ≫ p2 p) (p13 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf13_1) (by simpa [singletonMorphism] using hf13_2) := by
      simpa [φ, hq13] using
        (D.pullHom_hom (g := p13 p) (q := q0) (q' := q3) (hq := hq13)
          (i₁ := PUnit.unit) (i₂ := PUnit.unit) (f₁ := p2 p) (f₂ := p1 p)
          (hf₁ := by
            simpa [singletonMorphism, q0] using (p1_comp_p_eq_p2_comp_p p).symm)
          (hf₂ := by rfl)
          (gf₁ := p13 p ≫ p2 p) (gf₂ := p13 p ≫ p1 p) (hgf₁ := rfl) (hgf₂ := rfl))
    -- Transport both legs.
    have htrans :
        (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom ≫
            D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p13 p ≫ p2 p) (p13 p ≫ p1 p)
                (by simpa [singletonMorphism] using hf13_1)
                (by simpa [singletonMorphism] using hf13_2) ≫
              (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
                (by simpa [singletonMorphism] using hf23_1)
                (by simpa [singletonMorphism] using hf12_2) := by
      have h₁ : p13 p ≫ p2 p = p23 p ≫ p2 p := by simp
      have h₂ : p13 p ≫ p1 p = p12 p ≫ p1 p := by simp
      simpa [reindexObjIsoOfEq_hom, Category.assoc] using
        (descentData_hom_congr' (F := F) (p := p) (D := D) (q := q3) (f₁ := p13 p ≫ p2 p)
          (f₂ := p13 p ≫ p1 p) (f₁' := p23 p ≫ p2 p) (f₂' := p12 p ≫ p1 p) (hf₁ := hf13_1)
          (hf₂ := hf13_2) (h₁ := h₁) (h₂ := h₂))
    -- Assemble `hx13`.
    calc
      xi13 (F := F) p
            (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                  (by rfl)
                  (by
                    simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
          (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom ≫
            CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := φ)
                (g := p13 p) (gf₁ := p13 p ≫ p2 p) (gf₂ := p13 p ≫ p1 p) (hgf₁ := rfl)
                (hgf₂ := rfl) ≫
              (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom := hx13_pull
      _ =
          (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom ≫
            D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p13 p ≫ p2 p) (p13 p ≫ p1 p)
                (by simpa [singletonMorphism] using hf13_1)
                (by simpa [singletonMorphism] using hf13_2) ≫
              (reindexObjIsoOfEq (F := F) (a := D.obj PUnit.unit) (by simp)).hom := by
          simp [hpull]
      _ =
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
                (by simpa [singletonMorphism] using hf23_1)
                (by simpa [singletonMorphism] using hf12_2) := by
          simpa [Category.assoc] using htrans

  -- Final cocycle via `D.hom_comp`.
  have hcomp :
      D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
            (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_1) ≫
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf12_1) (by simpa [singletonMorphism] using hf12_2) =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_2) := by
    simp [D.hom_comp]

  -- Rewrite using the three identifications.
  calc
    xi23 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm ≫
        xi12 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p2 p)
            (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_1) ≫
          D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p12 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf12_1) (by simpa [singletonMorphism] using hf12_2) := by
      simp [hx23, hx12]
    _ =
        D.hom q3 (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p23 p ≫ p2 p) (p12 p ≫ p1 p)
            (by simpa [singletonMorphism] using hf23_1) (by simpa [singletonMorphism] using hf12_2) := hcomp
    _ =
        xi13 (F := F) p
          (D.iso (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p)
                (by rfl)
                (by
                  simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)).symm := by
      simp [hx13]

/-- Convert mathlib's descent data for the singleton family to a single morphism descent datum. -/
def singletonToSingleDescentDatum
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
    SingleMorphismDescentData (F := F) p where
  obj := D.obj PUnit.unit
  ξ := by
    -- We need: π₂^* (D.obj ()) ≅ π₁^* (D.obj ())
    -- D.iso gives us: for f₁ f₂ : Y ⟶ E with f₁ ≫ p = f₂ ≫ p,
    --   f₁^* (D.obj ()) ≅ f₂^* (D.obj ())
    -- Take f₁ = π₁, f₂ = π₂ at Y = cechKernelPair p
    -- Then D.iso gives π₁^* (D.obj ()) ≅ π₂^* (D.obj ())
    -- We need the inverse direction for our ξ : π₂^* → π₁^*
    have h : p1 p ≫ p = p2 p ≫ p := p1_comp_p_eq_p2_comp_p p
    exact (D.iso (p1 p ≫ p) (p1 p) (p2 p) rfl h.symm).symm
  unit := by
    simpa using (singletonToSingle_unit (F := F) p D)
  cocycle := by
    simpa using (singletonToSingle_cocycle (F := F) p D)

/-!
## Morphisms
-/

/-- Convert a morphism of single-morphism descent data to a morphism of mathlib descent data. -/
def singleToSingletonHom {D₁ D₂ : SingleMorphismDescentData (F := F) p}
    (f : D₁ ⟶ D₂) :
    singleToSingletonDescentDatum F p D₁ ⟶ singleToSingletonDescentDatum F p D₂ where
  hom := fun _ => (f : SingleMorphismDescentData.Hom D₁ D₂).hom
  comm := by
    intro Y q i₁ i₂ g₁ g₂ hg₁ hg₂
    cases i₁; cases i₂
    have h : g₁ ≫ p = g₂ ≫ p := by
      simp [singletonMorphism] at hg₁ hg₂
      rw [hg₁, hg₂]
    simpa using (singleToSingletonHomAux_comm (F := F) p f g₁ g₂ h)

/-- Convert a morphism of mathlib descent data to a morphism of single-morphism descent data. -/
def singletonToSingleHom
    {D₁ D₂ : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)}
    (f : D₁ ⟶ D₂) :
    singletonToSingleDescentDatum F p D₁ ⟶ singletonToSingleDescentDatum F p D₂ :=
  ⟨f.hom PUnit.unit, by
    simp only [singletonToSingleDescentDatum]
    -- The compatibility condition follows from f.hom_hom at π₁, π₂
    have hf₁ : p2 p ≫ p = p1 p ≫ p := by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm
    have hf₂ : p1 p ≫ p = p1 p ≫ p := rfl
    -- `f.comm` gives the compatibility for `D₁.hom`/`D₂.hom`; our glueing map is the
    -- corresponding `iso` reversed, hence we take `.symm`.
    simpa [CategoryTheory.Pseudofunctor.DescentData.iso] using
      (f.comm (q := (p1 p ≫ p)) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
        (f₁ := p2 p) (f₂ := p1 p) hf₁ hf₂).symm⟩

/-!
## Functors
-/

/-- The functor from single-morphism descent data to mathlib descent data. -/
def singleToSingletonFunctor :
    SingleMorphismDescentData (F := F) p ⥤
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  obj := singleToSingletonDescentDatum F p
  map := singleToSingletonHom F p
  map_id := fun D => by
    ext i
    cases i
    simp [singleToSingletonHom, singleToSingletonDescentDatum]
  map_comp := fun f g => by
    ext i
    cases i
    simp [singleToSingletonHom, singleToSingletonDescentDatum,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom]

/-- The functor from mathlib descent data to single-morphism descent data. -/
def singletonToSingleFunctor :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) ⥤
      SingleMorphismDescentData (F := F) p where
  obj := singletonToSingleDescentDatum F p
  map := singletonToSingleHom F p
  map_id := fun D => by
    ext
    simp [singletonToSingleHom, singletonToSingleDescentDatum]
  map_comp := fun f g => by
    ext
    simp [singletonToSingleHom, singletonToSingleDescentDatum,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom]

/-!
## Equivalence
-/

/-- The unit of the equivalence: `D ≅ singletonToSingle (singleToSingleton D)`. -/
def singleSingletonUnit (D : SingleMorphismDescentData (F := F) p) :
    D ≅ (singleToSingletonFunctor F p ⋙ singletonToSingleFunctor F p).obj D where
  hom := ⟨𝟙 D.obj, by
    -- The ξ's should match up to coherence
    simpa [singleToSingletonFunctor, singletonToSingleFunctor, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum] using
        (singleToSingletonHomAux_swap (F := F) (p := p) D)⟩
  inv := ⟨𝟙 D.obj, by
    simpa [singleToSingletonFunctor, singletonToSingleFunctor, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum] using
        (singleToSingletonHomAux_swap (F := F) (p := p) D).symm⟩
  hom_inv_id := by
    ext
    dsimp only [SingleMorphismDescentData.instCategory]
    simp
  inv_hom_id := by
    ext
    simp only [SingleMorphismDescentData.instCategory, singleToSingletonFunctor,
      singletonToSingleFunctor, singleToSingletonDescentDatum, singletonToSingleDescentDatum,
      Functor.comp_obj, SingleMorphismDescentData.Hom.comp_hom,
      SingleMorphismDescentData.Hom.id_hom, Category.comp_id]

/-- The counit of the equivalence: `singleToSingleton (singletonToSingle D) ≅ D`. -/
def singleSingletonCounit
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
    (singletonToSingleFunctor F p ⋙ singleToSingletonFunctor F p).obj D ≅ D where
  hom := ⟨fun _ => 𝟙 (D.obj PUnit.unit), by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    cases i₁; cases i₂
    have hf₁' : f₁ ≫ p = q := by simpa [singletonMorphism] using hf₁
    have hf₂' : f₂ ≫ p = q := by simpa [singletonMorphism] using hf₂
    have h : f₁ ≫ p = f₂ ≫ p := by rw [hf₁', hf₂']
    let g : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ h
    have hq : g ≫ (p1 p ≫ p) = q := by
      simpa [g, Category.assoc] using hf₁'
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
              (by
                simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm))
            g f₁ f₂
            (by simp [g])
            (by simp [g]) =
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              (by simpa [singletonMorphism] using hf₁)
              (by simpa [singletonMorphism] using hf₂) := by
      simpa [g] using
        (D.pullHom_hom (g := g) (q := p1 p ≫ p) (q' := q) (hq := hq)
          (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (f₁ := p1 p) (f₂ := p2 p)
          (hf₁ := by rfl)
          (hf₂ := by
            simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)
          (gf₁ := f₁) (gf₂ := f₂)
          (hgf₁ := by simp [g])
          (hgf₂ := by simp [g]))
    simpa [singleToSingletonFunctor, singletonToSingleFunctor, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, singleToSingletonHomAux, g] using hpull.symm⟩
  inv := ⟨fun _ => 𝟙 (D.obj PUnit.unit), by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    cases i₁; cases i₂
    have hf₁' : f₁ ≫ p = q := by simpa [singletonMorphism] using hf₁
    have hf₂' : f₂ ≫ p = q := by simpa [singletonMorphism] using hf₂
    have h : f₁ ≫ p = f₂ ≫ p := by rw [hf₁', hf₂']
    let g : Y ⟶ cechKernelPair p := Limits.pullback.lift f₁ f₂ h
    have hq : g ≫ (p1 p ≫ p) = q := by
      simpa [g, Category.assoc] using hf₁'
    have hpull :
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (D.hom (p1 p ≫ p) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (p1 p) (p2 p) (by rfl)
              (by
                simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm))
            g f₁ f₂
            (by simp [g])
            (by simp [g]) =
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              (by simpa [singletonMorphism] using hf₁)
              (by simpa [singletonMorphism] using hf₂) := by
      simpa [g] using
        (D.pullHom_hom (g := g) (q := p1 p ≫ p) (q' := q) (hq := hq)
          (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (f₁ := p1 p) (f₂ := p2 p)
          (hf₁ := by rfl)
          (hf₂ := by
            simpa [singletonMorphism] using (p1_comp_p_eq_p2_comp_p p).symm)
          (gf₁ := f₁) (gf₂ := f₂)
          (hgf₁ := by simp [g])
          (hgf₂ := by simp [g]))
    simpa [singleToSingletonFunctor, singletonToSingleFunctor, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, singleToSingletonHomAux, g] using hpull⟩
  hom_inv_id := by
    ext i
    cases i
    simp only [CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom, Functor.comp_obj,
      singleToSingletonFunctor, singletonToSingleFunctor, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, Category.comp_id]
  inv_hom_id := by
    ext i
    cases i
    simp

/-- The equivalence between single-morphism descent data and mathlib's descent data
for the singleton family. -/
def singleSingletonDescentDataEquiv :
    SingleMorphismDescentData (F := F) p ≌
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  functor := singleToSingletonFunctor F p
  inverse := singletonToSingleFunctor F p
  unitIso := NatIso.ofComponents (singleSingletonUnit F p) (by
    intro D₁ D₂ f
    ext
    simp [SingleMorphismDescentData.instCategory, singleToSingletonFunctor,
      singletonToSingleFunctor, singleSingletonUnit, singleToSingletonHom, singletonToSingleHom,
      singleToSingletonDescentDatum, singletonToSingleDescentDatum, Functor.comp_obj,
      Functor.id_obj, Functor.comp_map, Functor.id_map,
      SingleMorphismDescentData.Hom.comp_hom, Category.id_comp, Category.comp_id])
  counitIso := NatIso.ofComponents (singleSingletonCounit F p) (by
    intro D₁ D₂ f
    ext i
    cases i
    simp only [singleToSingletonFunctor, singletonToSingleFunctor, singleSingletonCounit,
      singleToSingletonHom, singletonToSingleHom, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map, CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      Category.id_comp, Category.comp_id])
  functor_unitIso_comp X := by
    ext i
    cases i
    simp only [singleToSingletonFunctor, singletonToSingleFunctor, singleSingletonUnit,
      singleSingletonCounit, singleToSingletonHom, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, Functor.comp_obj, Functor.id_obj,
      NatIso.ofComponents_hom_app, Category.comp_id,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom]

/-- The comparison functor `Φₚ : F(B) ⥤ Des_F(p)` from the paper (Facets of Descent II, §3.2),
landing in the Čech-style descent data defined in `SingleMorphism.lean`.

It is defined as `F.toDescentData` for the singleton family, followed by the (inverse) functor
from mathlib's descent data to our Čech-style descent data. -/
noncomputable def singleMorphismComparisonFunctor :
    F.obj (.mk (op B)) ⥤ SingleMorphismDescentData (F := F) p :=
  (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)) ⋙
    singletonToSingleFunctor (F := F) p

/-- `p` is a descent morphism for `F` if the comparison functor `Φₚ` is fully faithful
(Facets of Descent II, §3.2). -/
abbrev IsDescentMorphism : Prop :=
  Nonempty (singleMorphismComparisonFunctor (F := F) p).FullyFaithful

/-- `p` is an effective descent morphism for `F` if the comparison functor `Φₚ` is an equivalence
of categories (Facets of Descent II, §3.2). -/
abbrev IsEffectiveDescentMorphism : Prop :=
  (singleMorphismComparisonFunctor (F := F) p).IsEquivalence

/-!
## Relation with Mathlib's `IsPrestackFor`/`IsStackFor` for `Presieve.singleton p`

Mathlib’s descent theory is formulated for arbitrary presieves `R` via the functor
`F.toDescentData (fun (f : R.category) ↦ f.obj.hom)`. In the singleton case, the presieve
`Presieve.singleton p` is (definitionally) the same as `Presieve.ofArrows _ (fun _ : PUnit => p)`,
see `CategoryTheory.Presieve.ofArrows_pUnit`.

The functor `singleMorphismComparisonFunctor` differs from `F.toDescentData` only by postcomposition
with the (inverse) equivalence `singletonToSingleFunctor`, so it has the same “fully faithful” and
“is equivalence” properties.
-/

theorem isDescentMorphism_iff_nonempty_toDescentData_fullyFaithful :
    IsDescentMorphism (F := F) p ↔
      Nonempty (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)).FullyFaithful := by
  classical
  let e := singleSingletonDescentDataEquiv (F := F) p
  let G := CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)
  let H := singletonToSingleFunctor (F := F) p
  have hH : H.FullyFaithful := by
    simpa [H, e, singleSingletonDescentDataEquiv] using e.fullyFaithfulInverse
  haveI : H.Faithful := by
    simpa [H, e, singleSingletonDescentDataEquiv] using (show e.inverse.Faithful from inferInstance)
  constructor
  · rintro ⟨hGH⟩
    refine ⟨CategoryTheory.Functor.FullyFaithful.ofCompFaithful (F := G) (G := H) ?_⟩
    simpa [singleMorphismComparisonFunctor, G, H] using hGH
  · rintro ⟨hG⟩
    refine ⟨?_⟩
    simpa [singleMorphismComparisonFunctor, G, H] using hG.comp hH

theorem isEffectiveDescentMorphism_iff_toDescentData_isEquivalence :
    IsEffectiveDescentMorphism (F := F) p ↔
      (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)).IsEquivalence := by
  classical
  let e := singleSingletonDescentDataEquiv (F := F) p
  let G := CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)
  let H := singletonToSingleFunctor (F := F) p
  haveI : H.IsEquivalence := by
    simpa [H, e, singleSingletonDescentDataEquiv] using (show e.inverse.IsEquivalence from inferInstance)
  constructor
  · intro hGH
    have : (G ⋙ H).IsEquivalence := by simpa [singleMorphismComparisonFunctor, G, H] using hGH
    -- cancel the equivalence `H` on the right
    haveI : (G ⋙ H).IsEquivalence := this
    exact CategoryTheory.Functor.isEquivalence_of_comp_right G H
  · intro hG
    haveI : G.IsEquivalence := hG
    -- composition with an equivalence is an equivalence
    have : (G ⋙ H).IsEquivalence := by infer_instance
    simpa [singleMorphismComparisonFunctor, G, H] using this

theorem isPrestackFor_singleton_iff_isDescentMorphism :
    CategoryTheory.Pseudofunctor.IsPrestackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
      IsDescentMorphism (F := F) p := by
  have hPresieve :
      CategoryTheory.Presieve.ofArrows (fun _ : PUnit => E) (singletonMorphism p) =
        CategoryTheory.Presieve.singleton p := by
    simpa [singletonMorphism] using (CategoryTheory.Presieve.ofArrows_pUnit (f := p))
  have h :
      CategoryTheory.Pseudofunctor.IsPrestackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
        Nonempty (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)).FullyFaithful := by
    simpa [hPresieve] using
      (CategoryTheory.Pseudofunctor.isPrestackFor_ofArrows_iff (F := F) (S := B) (f := singletonMorphism p))
  exact h.trans (isDescentMorphism_iff_nonempty_toDescentData_fullyFaithful (F := F) p).symm

theorem isStackFor_singleton_iff_isEffectiveDescentMorphism :
    CategoryTheory.Pseudofunctor.IsStackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
      IsEffectiveDescentMorphism (F := F) p := by
  have hPresieve :
      CategoryTheory.Presieve.ofArrows (fun _ : PUnit => E) (singletonMorphism p) =
        CategoryTheory.Presieve.singleton p := by
    simpa [singletonMorphism] using (CategoryTheory.Presieve.ofArrows_pUnit (f := p))
  have h :
      CategoryTheory.Pseudofunctor.IsStackFor (F := F) (S := B) (CategoryTheory.Presieve.singleton p) ↔
        (CategoryTheory.Pseudofunctor.toDescentData (F := F) (f := singletonMorphism p)).IsEquivalence := by
    simpa [hPresieve] using
      (CategoryTheory.Pseudofunctor.isStackFor_ofArrows_iff (F := F) (S := B) (f := singletonMorphism p))
  exact h.trans (isEffectiveDescentMorphism_iff_toDescentData_isEquivalence (F := F) p).symm

end

end Descent.Pseudofunctor.Descent
