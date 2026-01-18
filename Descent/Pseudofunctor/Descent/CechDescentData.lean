/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.Pseudofunctor.Reindexing
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Čech descent data along a single morphism (pseudofunctor)

Defines descent data for a pseudofunctor along `p : E ⟶ B` using Čech overlaps,
with cocycle convention `ξ₂₃ ≫ ξ₁₂ = ξ₁₃` and unit along the diagonal. Main
definitions are `CechDescentData` and `singleMorphismComparisonXi`.

We follow the paper (*Facets of Descent, II*, §3.3) and Mathlib’s `Pseudofunctor.DescentData`:
the gluing map is stored as a morphism `π₂^* C ⟶ π₁^* C`, and `IsIso` is derived from the axioms.
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

open Opposite
open Descent.Cech
open Descent.Pseudofunctor

universe v' v u' u

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private lemma pullHom_id_of_id_comp
    {X : C} {M : F.obj (.mk (op X))} {Y : C} (g : Y ⟶ X) :
    pullHom (F := F) (φ := 𝟙 ((reindex F (𝟙 X)).obj M)) (g := g) (gf₁ := g) (gf₂ := g)
        (hgf₁ := by simp) (hgf₂ := by simp) =
      𝟙 ((reindex F g).obj M) := by
  classical
  -- Unfolding `pullHom` is safe here: the `id_comp` coherence reduces to `mapId`.
  dsimp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp [CategoryTheory.Pseudofunctor.mapComp'_id_comp_hom_app,
    CategoryTheory.Pseudofunctor.mapComp'_id_comp_inv_app]
  -- Reduce to functoriality applied to `inv_hom_id` for `mapId`.
  rw [(F.map g.op.toLoc).toFunctor.map_id ((reindex F (𝟙 X)).obj M)]
  -- Unfold `reindex` (and simplify away the inserted identity morphism).
  simp [reindex]
  rw [← Functor.map_comp]
  rw [Cat.Hom.inv_hom_id_toNatTrans_app (F.mapId { as := op X }) M]
  simp

private lemma pullHom_comp
    {X₁ X₂ X₃ : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (φ : (reindex F f₁).obj M₁ ⟶ (reindex F f₂).obj M₂)
    (ψ : (reindex F f₂).obj M₂ ⟶ (reindex F f₃).obj M₃)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom (F := F) (φ := φ ≫ ψ) g gf₁ gf₃ hgf₁ hgf₃ =
      pullHom (F := F) (φ := φ) g gf₁ gf₂ hgf₁ hgf₂ ≫
        pullHom (F := F) (φ := ψ) g gf₂ gf₃ hgf₂ hgf₃ := by
  -- A direct computation from the definition of `pullHom`.
  classical
  dsimp [CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp [Functor.map_comp, Category.assoc, ← reassoc_of% Cat.Hom₂.comp_app]

section HasPullbacks

variable [Limits.HasPullbacks C]

/-!
## Auxiliary isomorphisms for the diagonal
-/

/-- The canonical isomorphism `diag^*(π₁^* a) ≅ a`. -/
def diagIsoP1 {E B : C} (p : E ⟶ B) (a : F.obj (.mk (op E))) :
    (reindex F (Limits.pullback.diagonal p)).obj ((reindex F (p1 p)).obj a) ≅ a := by
  refine
    (reindexCompIsoObj F (g := Limits.pullback.diagonal p) (f := p1 p) a).symm ≪≫
      (reindexObjIsoOfEq F (f := Limits.pullback.diagonal p ≫ p1 p) (g := 𝟙 E)
        (by simp) a) ≪≫
        reindexIdIsoObj F a

/-- The canonical isomorphism `diag^*(π₂^* a) ≅ a`. -/
def diagIsoP2 {E B : C} (p : E ⟶ B) (a : F.obj (.mk (op E))) :
    (reindex F (Limits.pullback.diagonal p)).obj ((reindex F (p2 p)).obj a) ≅ a := by
  refine
    (reindexCompIsoObj F (g := Limits.pullback.diagonal p) (f := p2 p) a).symm ≪≫
      (reindexObjIsoOfEq F (f := Limits.pullback.diagonal p ≫ p2 p) (g := 𝟙 E)
        (by simp) a) ≪≫
        reindexIdIsoObj F a

/-!
## Descent data for a single morphism
-/

/-- The morphism on the `(1,2)`-overlap induced from `ξ`. -/
def xi12 {E B : C} (p : E ⟶ B) {C₀ : F.obj (.mk (op E))}
    (ξ : (reindex F (p2 p)).obj C₀ ⟶ (reindex F (p1 p)).obj C₀) :
    (reindex F (p12 p ≫ p2 p)).obj C₀ ⟶ (reindex F (p12 p ≫ p1 p)).obj C₀ := by
  exact
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := ξ)
      (g := p12 p) (gf₁ := p12 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p)
      (hgf₁ := by simp) (hgf₂ := by simp)

/-- The morphism on the `(2,3)`-overlap induced from `ξ`, transported so that its codomain
is the `(1,2)`-pullback. -/
def xi23 {E B : C} (p : E ⟶ B) {C₀ : F.obj (.mk (op E))}
    (ξ : (reindex F (p2 p)).obj C₀ ⟶ (reindex F (p1 p)).obj C₀) :
    (reindex F (p23 p ≫ p2 p)).obj C₀ ⟶ (reindex F (p12 p ≫ p2 p)).obj C₀ := by
  exact
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := ξ)
      (g := p23 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p2 p)
    (hgf₁ := by simp)
    (hgf₂ := by simp)

/-- The morphism on the `(1,3)`-overlap induced from `ξ`, transported so that its domain and
codomain match those of `xi23` and `xi12`. -/
def xi13 {E B : C} (p : E ⟶ B) {C₀ : F.obj (.mk (op E))}
    (ξ : (reindex F (p2 p)).obj C₀ ⟶ (reindex F (p1 p)).obj C₀) :
    (reindex F (p23 p ≫ p2 p)).obj C₀ ⟶ (reindex F (p12 p ≫ p1 p)).obj C₀ := by
  exact
    CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) (φ := ξ)
      (g := p13 p) (gf₁ := p23 p ≫ p2 p) (gf₂ := p12 p ≫ p1 p)
    (hgf₁ := by simp)
    (hgf₂ := by simp)

/-- Descent data for `F` relative to `p : E ⟶ B` using the Čech kernel pair. -/
structure CechDescentData {E B : C} (p : E ⟶ B) where
  /-- The object over `E`. -/
  obj : F.obj (.mk (op E))
  /-- The gluing morphism `π₂^* obj ⟶ π₁^* obj` over `E ×_B E`. -/
  ξ : (reindex F (p2 p)).obj obj ⟶ (reindex F (p1 p)).obj obj
  /-- Unit condition: restricting along the diagonal yields the identity. -/
  unit :
    (diagIsoP2 (F := F) p obj).inv ≫
        (reindex F (Limits.pullback.diagonal p)).map ξ ≫
          (diagIsoP1 (F := F) p obj).hom =
      𝟙 obj
  /-- Cocycle condition on triple overlaps. -/
  cocycle :
    xi23 (F := F) p ξ ≫ xi12 (F := F) p ξ = xi13 (F := F) p ξ

namespace CechDescentData

variable {F}
variable {E B : C} {p : E ⟶ B}

/-!
### Invertibility of the gluing morphism

For descent data along the kernel pair, the Čech cocycle and unit axioms imply that the gluing
morphism `ξ` is invertible. This matches the situation in the paper (§3.3), where `Eq(p)` is an
internal groupoid, so actions automatically involve isomorphisms.
-/

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-!
#### The swap map and the induced candidate inverse
-/

/-- The symmetry of the kernel pair `E ×_B E`, swapping the two projections. -/
def swap {E B : C} (p : E ⟶ B) : cechKernelPair p ⟶ cechKernelPair p :=
  Limits.pullback.lift (p2 p) (p1 p) (by
    simpa using (p1_comp_p_eq_p2_comp_p p).symm)

@[simp] lemma swap_p1 {E B : C} (p : E ⟶ B) : swap p ≫ p1 p = p2 p := by
  simp [swap]

@[simp] lemma swap_p2 {E B : C} (p : E ⟶ B) : swap p ≫ p2 p = p1 p := by
  simp [swap]

/-- The candidate inverse of `ξ`, obtained by pulling back along the swap map. -/
noncomputable def xiInv (D : CechDescentData (F := F) p) :
    (reindex F (p1 p)).obj D.obj ⟶ (reindex F (p2 p)).obj D.obj :=
  pullHom (F := F) (φ := D.ξ) (g := swap p) (gf₁ := p1 p) (gf₂ := p2 p)
    (hgf₁ := by simp)
    (hgf₂ := by simp)

/-!
#### Swap maps into the triple overlap
-/

/-- The map `E ×_B E ⟶ E ×_B E ×_B E` corresponding to `(id, swap)`. -/
def swapLeft {E B : C} (p : E ⟶ B) : cechKernelPair p ⟶ cechTripleOverlap p :=
  Limits.pullback.lift (𝟙 _) (swap p) (by simp)

@[simp] lemma swapLeft_p12 {E B : C} (p : E ⟶ B) : swapLeft p ≫ p12 p = 𝟙 _ := by
  simp [swapLeft]

@[simp] lemma swapLeft_p23 {E B : C} (p : E ⟶ B) : swapLeft p ≫ p23 p = swap p := by
  simp [swapLeft]

@[simp] lemma swapLeft_p12_p1 {E B : C} (p : E ⟶ B) :
    swapLeft p ≫ p12 p ≫ p1 p = p1 p := by
  calc
    swapLeft p ≫ p12 p ≫ p1 p = (swapLeft p ≫ p12 p) ≫ p1 p := by
      simpa using (Category.assoc (swapLeft p) (p12 p) (p1 p)).symm
    _ = p1 p := by simp

@[simp] lemma swapLeft_p12_p2 {E B : C} (p : E ⟶ B) :
    swapLeft p ≫ p12 p ≫ p2 p = p2 p := by
  calc
    swapLeft p ≫ p12 p ≫ p2 p = (swapLeft p ≫ p12 p) ≫ p2 p := by
      simpa using (Category.assoc (swapLeft p) (p12 p) (p2 p)).symm
    _ = p2 p := by simp

@[simp] lemma swapLeft_p23_p2 {E B : C} (p : E ⟶ B) :
    swapLeft p ≫ p23 p ≫ p2 p = p1 p := by
  calc
    swapLeft p ≫ p23 p ≫ p2 p = (swapLeft p ≫ p23 p) ≫ p2 p := by
      simpa using (Category.assoc (swapLeft p) (p23 p) (p2 p)).symm
    _ = p1 p := by simp

@[simp] lemma swapLeft_p23_p1 {E B : C} (p : E ⟶ B) :
    swapLeft p ≫ p23 p ≫ p1 p = p2 p := by
  calc
    swapLeft p ≫ p23 p ≫ p1 p = (swapLeft p ≫ p23 p) ≫ p1 p := by
      simpa using (Category.assoc (swapLeft p) (p23 p) (p1 p)).symm
    _ = p2 p := by simp

@[simp] lemma swapLeft_p13 {E B : C} (p : E ⟶ B) : swapLeft p ≫ p13 p = p1 p ≫ diag p := by
  apply Limits.pullback.hom_ext <;> simp

/-- The map `E ×_B E ⟶ E ×_B E ×_B E` corresponding to `(swap, id)`. -/
def swapRight {E B : C} (p : E ⟶ B) : cechKernelPair p ⟶ cechTripleOverlap p :=
  Limits.pullback.lift (swap p) (𝟙 _) (by simp)

@[simp] lemma swapRight_p12 {E B : C} (p : E ⟶ B) : swapRight p ≫ p12 p = swap p := by
  simp [swapRight]

@[simp] lemma swapRight_p23 {E B : C} (p : E ⟶ B) : swapRight p ≫ p23 p = 𝟙 _ := by
  simp [swapRight]

@[simp] lemma swapRight_p12_p1 {E B : C} (p : E ⟶ B) :
    swapRight p ≫ p12 p ≫ p1 p = p2 p := by
  calc
    swapRight p ≫ p12 p ≫ p1 p = (swapRight p ≫ p12 p) ≫ p1 p := by
      simpa using (Category.assoc (swapRight p) (p12 p) (p1 p)).symm
    _ = p2 p := by simp

@[simp] lemma swapRight_p12_p2 {E B : C} (p : E ⟶ B) :
    swapRight p ≫ p12 p ≫ p2 p = p1 p := by
  calc
    swapRight p ≫ p12 p ≫ p2 p = (swapRight p ≫ p12 p) ≫ p2 p := by
      simpa using (Category.assoc (swapRight p) (p12 p) (p2 p)).symm
    _ = p1 p := by simp

@[simp] lemma swapRight_p23_p2 {E B : C} (p : E ⟶ B) :
    swapRight p ≫ p23 p ≫ p2 p = p2 p := by
  calc
    swapRight p ≫ p23 p ≫ p2 p = (swapRight p ≫ p23 p) ≫ p2 p := by
      simpa using (Category.assoc (swapRight p) (p23 p) (p2 p)).symm
    _ = p2 p := by simp

@[simp] lemma swapRight_p23_p1 {E B : C} (p : E ⟶ B) :
    swapRight p ≫ p23 p ≫ p1 p = p1 p := by
  calc
    swapRight p ≫ p23 p ≫ p1 p = (swapRight p ≫ p23 p) ≫ p1 p := by
      simpa using (Category.assoc (swapRight p) (p23 p) (p1 p)).symm
    _ = p1 p := by simp

@[simp] lemma swapRight_p13 {E B : C} (p : E ⟶ B) : swapRight p ≫ p13 p = p2 p ≫ diag p := by
  apply Limits.pullback.hom_ext <;> simp

/-!
#### Pullback of the unit along the diagonal
-/

private lemma pullHom_diag_eq_id (D : CechDescentData (F := F) p) :
    pullHom (F := F) (φ := D.ξ) (g := Limits.pullback.diagonal p) (gf₁ := 𝟙 _) (gf₂ := 𝟙 _)
        (hgf₁ := by simp) (hgf₂ := by simp) =
      𝟙 ((reindex F (𝟙 _)).obj D.obj) := by
  -- Rewrite `D.unit` as a conjugation statement for `pullHom` along the diagonal.
  have hu :
      (reindexIdIsoObj F D.obj).inv ≫
          pullHom (F := F) (φ := D.ξ) (g := Limits.pullback.diagonal p) (gf₁ := 𝟙 _) (gf₂ := 𝟙 _)
              (hgf₁ := by simp) (hgf₂ := by simp) ≫
            (reindexIdIsoObj F D.obj).hom =
        𝟙 D.obj := by
    -- `simp` after unfolding the diagonal comparison isomorphisms.
    simpa [diagIsoP1, diagIsoP2, pullHom, reindexCompIsoObj, reindex, reindexObjIsoOfEq,
      CategoryTheory.Pseudofunctor.mapComp', PrelaxFunctor.map₂_eqToHom, Category.assoc] using D.unit
  -- Cancel the outer `reindexIdIsoObj` isomorphisms.
  have hu' := congrArg (fun t =>
    (reindexIdIsoObj F D.obj).hom ≫ t ≫ (reindexIdIsoObj F D.obj).inv) hu
  simpa [Category.assoc] using hu'


private lemma pullHom_p1_diag_eq_id (D : CechDescentData (F := F) p) :
    pullHom (F := F) (φ := D.ξ) (g := p1 p ≫ diag p) (gf₁ := p1 p) (gf₂ := p1 p)
        (hgf₁ := by simp) (hgf₂ := by simp) =
      𝟙 ((reindex F (p1 p)).obj D.obj) := by
  -- Pull back the diagonal identity along `p1`.
  have hpull :=
    (pullHom_pullHom (F := F) (φ := D.ξ) (g := Limits.pullback.diagonal p) (gf₁ := 𝟙 _) (gf₂ := 𝟙 _)
      (g' := p1 p) (g'f₁ := p1 p) (g'f₂ := p1 p)
      (hgf₁ := by simp) (hgf₂ := by simp) (hg'f₁ := by simp) (hg'f₂ := by simp))
  have hId :
      pullHom (F := F)
          (φ := pullHom (F := F) (φ := D.ξ) (g := Limits.pullback.diagonal p) (gf₁ := 𝟙 _)
            (gf₂ := 𝟙 _) (hgf₁ := by simp) (hgf₂ := by simp))
          (g := p1 p) (gf₁ := p1 p) (gf₂ := p1 p) =
        𝟙 _ := by
    -- Rewrite the inner pullback using `D.unit` and finish by `simp`.
    rw [pullHom_diag_eq_id (F := F) (p := p) (D := D)]
    simpa using (pullHom_id_of_id_comp (F := F) (g := p1 p) (M := D.obj))
  -- `hpull` identifies the goal's LHS with the pullback of the diagonal identity.
  -- Rewrite along `hpull` and apply `hId` to avoid heavy definitional reductions in `Eq.trans`.
  rw [← hpull]
  exact hId

private lemma pullHom_p2_diag_eq_id (D : CechDescentData (F := F) p) :
    pullHom (F := F) (φ := D.ξ) (g := p2 p ≫ diag p) (gf₁ := p2 p) (gf₂ := p2 p)
        (hgf₁ := by simp) (hgf₂ := by simp) =
      𝟙 ((reindex F (p2 p)).obj D.obj) := by
  have hpull :=
    (pullHom_pullHom (F := F) (φ := D.ξ) (g := Limits.pullback.diagonal p) (gf₁ := 𝟙 _) (gf₂ := 𝟙 _)
      (g' := p2 p) (g'f₁ := p2 p) (g'f₂ := p2 p)
      (hgf₁ := by simp) (hgf₂ := by simp) (hg'f₁ := by simp) (hg'f₂ := by simp))
  have hId :
      pullHom (F := F) (φ := pullHom (F := F) (φ := D.ξ) (g := Limits.pullback.diagonal p) (gf₁ := 𝟙 _)
          (gf₂ := 𝟙 _) (hgf₁ := by simp) (hgf₂ := by simp))
          (g := p2 p) (gf₁ := p2 p) (gf₂ := p2 p) =
        𝟙 _ := by
    rw [pullHom_diag_eq_id (F := F) (p := p) (D := D)]
    simpa using (pullHom_id_of_id_comp (F := F) (g := p2 p) (M := D.obj))
  rw [← hpull]
  exact hId

/-!
#### The inverse laws
-/


lemma xiInv_comp_xi (D : CechDescentData (F := F) p) :
    xiInv (F := F) (p := p) D ≫ D.ξ = 𝟙 _ := by
  classical
  -- Pull back the cocycle along `swapLeft : E ×_B E ⟶ E ×_B E ×_B E`.
  have hc :=
      congrArg
        (fun t =>
          pullHom (F := F) (φ := t) (g := swapLeft p) (gf₁ := p1 p) (gf₂ := p1 p)
            (hgf₁ := by simp) (hgf₂ := by simp))
        (D.cocycle (p := p))

  -- Rewrite the pullback of the composite using `pullHom_comp`.
  have hcomp :
      pullHom (F := F) (φ := xi23 (F := F) p D.ξ ≫ xi12 (F := F) p D.ξ) (g := swapLeft p)
          (gf₁ := p1 p) (gf₂ := p1 p) (hgf₁ := by simp)
          (hgf₂ := by simp) =
        pullHom (F := F) (φ := xi23 (F := F) p D.ξ) (g := swapLeft p)
            (gf₁ := p1 p) (gf₂ := p2 p) (hgf₁ := by simp)
            (hgf₂ := by simp) ≫
          pullHom (F := F) (φ := xi12 (F := F) p D.ξ) (g := swapLeft p)
            (gf₁ := p2 p) (gf₂ := p1 p) (hgf₁ := by simp)
            (hgf₂ := by simp) := by
    simpa using
      (pullHom_comp (F := F) (φ := xi23 (F := F) p D.ξ) (ψ := xi12 (F := F) p D.ξ)
        (g := swapLeft p) (gf₁ := p1 p) (gf₂ := p2 p) (gf₃ := p1 p)
        (hgf₁ := by simp) (hgf₂ := by simp)
        (hgf₃ := by simp))

  have hc' :
      pullHom (F := F) (φ := xi23 (F := F) p D.ξ) (g := swapLeft p)
            (gf₁ := p1 p) (gf₂ := p2 p) (hgf₁ := by simp)
            (hgf₂ := by simp) ≫
          pullHom (F := F) (φ := xi12 (F := F) p D.ξ) (g := swapLeft p)
            (gf₁ := p2 p) (gf₂ := p1 p) (hgf₁ := by simp)
            (hgf₂ := by simp) =
        pullHom (F := F) (φ := xi13 (F := F) p D.ξ) (g := swapLeft p)
          (gf₁ := p1 p) (gf₂ := p1 p) (hgf₁ := by simp)
          (hgf₂ := by simp) := by
    simpa [hcomp] using hc

  -- Identify the three pulled-back morphisms.
  have h23 :
      pullHom (F := F) (φ := xi23 (F := F) p D.ξ) (g := swapLeft p)
            (gf₁ := p1 p) (gf₂ := p2 p) (hgf₁ := by simp)
            (hgf₂ := by simp) =
        xiInv (F := F) (p := p) D := by
    simp [xi23, xiInv, swapLeft_p23, pullHom_pullHom]

  have h12 :
      pullHom (F := F) (φ := xi12 (F := F) p D.ξ) (g := swapLeft p)
            (gf₁ := p2 p) (gf₂ := p1 p) (hgf₁ := by simp)
            (hgf₂ := by simp) =
        D.ξ := by
    simp [xi12, swapLeft_p12, pullHom_pullHom, pullHom_id]

  have h13 :
      pullHom (F := F) (φ := xi13 (F := F) p D.ξ) (g := swapLeft p)
          (gf₁ := p1 p) (gf₂ := p1 p) (hgf₁ := by simp)
          (hgf₂ := by simp) =
        𝟙 _ := by
    simp [xi13, swapLeft_p13, pullHom_pullHom, pullHom_p1_diag_eq_id]

  -- Conclude.
  simpa [h23, h12, h13, Category.assoc] using hc'

lemma xi_comp_xiInv (D : CechDescentData (F := F) p) :
    D.ξ ≫ xiInv (F := F) (p := p) D = 𝟙 _ := by
  classical
  have hc :=
      congrArg
        (fun t =>
          pullHom (F := F) (φ := t) (g := swapRight p) (gf₁ := p2 p) (gf₂ := p2 p)
            (hgf₁ := by simp) (hgf₂ := by simp))
        (D.cocycle (p := p))

  have hcomp :
      pullHom (F := F) (φ := xi23 (F := F) p D.ξ ≫ xi12 (F := F) p D.ξ) (g := swapRight p)
          (gf₁ := p2 p) (gf₂ := p2 p) (hgf₁ := by simp)
          (hgf₂ := by simp) =
        pullHom (F := F) (φ := xi23 (F := F) p D.ξ) (g := swapRight p)
            (gf₁ := p2 p) (gf₂ := p1 p) (hgf₁ := by simp)
            (hgf₂ := by simp) ≫
          pullHom (F := F) (φ := xi12 (F := F) p D.ξ) (g := swapRight p)
            (gf₁ := p1 p) (gf₂ := p2 p) (hgf₁ := by simp)
            (hgf₂ := by simp) := by
    simpa using
      (pullHom_comp (F := F) (φ := xi23 (F := F) p D.ξ) (ψ := xi12 (F := F) p D.ξ)
        (g := swapRight p) (gf₁ := p2 p) (gf₂ := p1 p) (gf₃ := p2 p)
        (hgf₁ := by simp) (hgf₂ := by simp)
        (hgf₃ := by simp))

  have hc' :
      pullHom (F := F) (φ := xi23 (F := F) p D.ξ) (g := swapRight p)
            (gf₁ := p2 p) (gf₂ := p1 p) (hgf₁ := by simp)
            (hgf₂ := by simp) ≫
          pullHom (F := F) (φ := xi12 (F := F) p D.ξ) (g := swapRight p)
            (gf₁ := p1 p) (gf₂ := p2 p) (hgf₁ := by simp)
            (hgf₂ := by simp) =
        pullHom (F := F) (φ := xi13 (F := F) p D.ξ) (g := swapRight p)
          (gf₁ := p2 p) (gf₂ := p2 p) (hgf₁ := by simp)
          (hgf₂ := by simp) := by
    simpa [hcomp] using hc

  have h23 :
      pullHom (F := F) (φ := xi23 (F := F) p D.ξ) (g := swapRight p)
            (gf₁ := p2 p) (gf₂ := p1 p) (hgf₁ := by simp)
            (hgf₂ := by simp) =
        D.ξ := by
    -- `swapRight ≫ p23 = 𝟙`.
    simp [xi23, swapRight_p23, pullHom_id, pullHom_pullHom]

  have h12 :
      pullHom (F := F) (φ := xi12 (F := F) p D.ξ) (g := swapRight p)
            (gf₁ := p1 p) (gf₂ := p2 p) (hgf₁ := by simp)
            (hgf₂ := by simp) =
        xiInv (F := F) (p := p) D := by
    -- `swapRight ≫ p12 = swap`, giving `xiInv`.
    simp [xi12, xiInv, swapRight_p12, pullHom_pullHom]

  have h13 :
      pullHom (F := F) (φ := xi13 (F := F) p D.ξ) (g := swapRight p)
          (gf₁ := p2 p) (gf₂ := p2 p) (hgf₁ := by simp)
          (hgf₂ := by simp) =
        𝟙 _ := by
    simp [xi13, swapRight_p13, pullHom_pullHom, pullHom_p2_diag_eq_id]

  simpa [h23, h12, h13, Category.assoc] using hc'

instance (D : CechDescentData (F := F) p) : IsIso D.ξ :=
  ⟨⟨xiInv (F := F) (p := p) D, xi_comp_xiInv (F := F) (p := p) D,
      xiInv_comp_xi (F := F) (p := p) D⟩⟩

/-- Morphisms of descent data are morphisms compatible with the gluing isomorphisms. -/
structure Hom (D D' : CechDescentData (F := F) p) where
  /-- The underlying morphism over `E`. -/
  hom : D.obj ⟶ D'.obj
  /-- Compatibility with the gluing isomorphisms. -/
  comm :
    D.ξ ≫ (reindex F (p1 p)).map hom =
      (reindex F (p2 p)).map hom ≫ D'.ξ

@[ext]
lemma Hom.ext {D D' : CechDescentData (F := F) p} {f g : Hom D D'} (h : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of descent data. -/
@[simps]
def Hom.id (D : CechDescentData (F := F) p) : Hom D D where
  hom := 𝟙 D.obj
  comm := by simp

/-- Composition of morphisms of descent data. -/
@[simps]
def Hom.comp {D₁ D₂ D₃ : CechDescentData (F := F) p} (f : Hom D₁ D₂)
    (g : Hom D₂ D₃) : Hom D₁ D₃ where
  hom := f.hom ≫ g.hom
  comm := by
    simp [Functor.map_comp]
    calc
      D₁.ξ ≫ (reindex F (p1 p)).map f.hom ≫ (reindex F (p1 p)).map g.hom =
          (reindex F (p2 p)).map f.hom ≫ D₂.ξ ≫
            (reindex F (p1 p)).map g.hom := by
        simpa [Category.assoc] using congrArg (· ≫ (reindex F (p1 p)).map g.hom) f.comm
      _ =
          (reindex F (p2 p)).map f.hom ≫ (reindex F (p2 p)).map g.hom ≫
            D₃.ξ := by
        simpa [Category.assoc] using congrArg ((reindex F (p2 p)).map f.hom ≫ ·) g.comm

instance instCategory : Category (CechDescentData (F := F) p) where
  Hom D D' := Hom D D'
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

end CechDescentData

/-- The canonical descent isomorphism on `p^* a`. -/
def singleMorphismComparisonXi {E B : C} (p : E ⟶ B) (a : F.obj (.mk (op B))) :
    (reindex F (p2 p)).obj ((reindex F p).obj a) ≅
      (reindex F (p1 p)).obj ((reindex F p).obj a) := by
  refine
    (reindexCompIsoObj F (g := p2 p) (f := p) a).symm ≪≫ ?_ ≪≫
      (reindexCompIsoObj F (g := p1 p) (f := p) a)
  exact
    reindexObjIsoOfEq F (f := p2 p ≫ p) (g := p1 p ≫ p) (a := a) (by
      simpa using (p1_comp_p_eq_p2_comp_p p).symm)

end HasPullbacks

end

end Descent.Pseudofunctor.Descent
