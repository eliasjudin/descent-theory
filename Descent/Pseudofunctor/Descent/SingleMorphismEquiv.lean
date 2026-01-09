/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
import Descent.Pseudofunctor.Descent.SingleMorphism

/-!
# Equivalence with mathlib's descent data

Relates `SingleMorphismDescentDatum` for `p : E ⟶ B` to mathlib's
`Pseudofunctor.DescentData` for the singleton family `fun _ : PUnit => p`.
Main definitions: `singleToSingletonDescentDatum`, `singletonToSingleDescentDatum`,
`singleToSingletonFunctor`, `singletonToSingleFunctor`, `singleSingletonDescentDataEquiv`.
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
abbrev singletonMorphism : ∀ (_ : PUnit), E ⟶ B := fun _ => p

/-!
## Helper: pulling back the Čech glueing isomorphism
-/

/-- Given Čech-style descent data `D` for `p : E ⟶ B`, this is the induced morphism
`f₁^* D.obj ⟶ f₂^* D.obj` for any `f₁ f₂ : Y ⟶ E` with `f₁ ≫ p = f₂ ≫ p`.

We define it by pulling back `D.ξ.inv : π₁^* D.obj ⟶ π₂^* D.obj` along the canonical
map `Y ⟶ E ×_B E`. -/
def singleToSingletonHomAux (D : SingleMorphismDescentDatum (F := F) p) {Y : C} (f₁ f₂ : Y ⟶ E)
    (h : f₁ ≫ p = f₂ ≫ p) :
    (F.map f₁.op.toLoc).toFunctor.obj D.obj ⟶ (F.map f₂.op.toLoc).toFunctor.obj D.obj := by
  let u : Y ⟶ cechTwo p := Limits.pullback.lift f₁ f₂ h
  have hu1 : u ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
  have hu2 : u ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
  exact CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
    (φ := D.ξ.inv) u f₁ f₂ hu1 hu2

/-!
## Forward direction: Single → Singleton
-/

/-- Convert a single morphism descent datum to mathlib's descent data for the singleton family.

The key mapping:
- `obj ()` := `D.obj`
- `hom q f₁ f₂` at Y mapping to E comes from `D.ξ` transported appropriately -/
def singleToSingletonDescentDatum (D : SingleMorphismDescentDatum (F := F) p) :
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
    -- Both sides are pullbacks of `D.ξ.inv` along the corresponding maps into `cechTwo p`.
    have hf₁' : f₁ ≫ p = f₂ ≫ p := by
      simp only [singletonMorphism] at hf₁ hf₂
      rw [hf₁, hf₂]
    have hgf₁' : gf₁ ≫ p = gf₂ ≫ p := by
      -- both are equal to `q'`
      simp only [singletonMorphism] at hf₁ hf₂
      have h₁ : gf₁ ≫ p = q' := by
        calc
          gf₁ ≫ p = (g ≫ f₁) ≫ p := by simpa [hgf₁, Category.assoc]
          _ = g ≫ (f₁ ≫ p) := by simp [Category.assoc]
          _ = g ≫ q := by simp [hf₁]
          _ = q' := by simpa using hq
      have h₂ : gf₂ ≫ p = q' := by
        calc
          gf₂ ≫ p = (g ≫ f₂) ≫ p := by simpa [hgf₂, Category.assoc]
          _ = g ≫ (f₂ ≫ p) := by simp [Category.assoc]
          _ = g ≫ q := by simp [hf₂]
          _ = q' := by simpa using hq
      exact h₁.trans h₂.symm
    let u : Y ⟶ cechTwo p := Limits.pullback.lift f₁ f₂ hf₁'
    let u' : Y' ⟶ cechTwo p := Limits.pullback.lift gf₁ gf₂ hgf₁'
    have hu1 : u ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
    have hu2 : u ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
    have hu1' : u' ≫ p1 p = gf₁ := Limits.pullback.lift_fst _ _ _
    have hu2' : u' ≫ p2 p = gf₂ := Limits.pullback.lift_snd _ _ _
    have hg_u : g ≫ u = u' := by
      apply Limits.pullback.hom_ext
      · simp [u, u', hu1, hu1', hgf₁, Category.assoc]
      · simp [u, u', hu2, hu2', hgf₂, Category.assoc]
    -- Use functoriality of `pullHom` and the equality `g ≫ u = u'`.
    -- `pullHom_pullHom` rewrites the double pullback as a single pullback along `g ≫ u`.
    -- Then we rewrite by `hg_u` to match the definition of `hom` for `q'`.
    simpa [singleToSingletonHomAux, u, u', hg_u, hu1, hu2, hu1', hu2'] using
      (CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom (F := F)
        (φ := D.ξ.inv) (g := u) (gf₁ := f₁) (gf₂ := f₂) (g' := g) (g'f₁ := gf₁) (g'f₂ := gf₂)
        (hgf₁ := hu1) (hgf₂ := hu2) (hg'f₁ := hgf₁) (hg'f₂ := hgf₂))
  hom_self := by
    intro Y q i g hg
    cases i
    -- TODO: prove from `D.unit`.
    -- The goal reduces to a statement about pulling back `D.ξ.inv` along the diagonal.
    sorry
  hom_comp := by
    intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    cases i₁; cases i₂; cases i₃
    -- TODO: prove from `D.cocycle`.
    sorry

/-- Convert mathlib's descent data for the singleton family to a single morphism descent datum. -/
def singletonToSingleDescentDatum
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
    SingleMorphismDescentDatum (F := F) p where
  obj := D.obj PUnit.unit
  ξ := by
    -- We need: π₂^* (D.obj ()) ≅ π₁^* (D.obj ())
    -- D.iso gives us: for f₁ f₂ : Y ⟶ E with f₁ ≫ p = f₂ ≫ p,
    --   f₁^* (D.obj ()) ≅ f₂^* (D.obj ())
    -- Take f₁ = π₁, f₂ = π₂ at Y = cechTwo p
    -- Then D.iso gives π₁^* (D.obj ()) ≅ π₂^* (D.obj ())
    -- We need the inverse direction for our ξ : π₂^* → π₁^*
    have h : p1 p ≫ p = p2 p ≫ p := p1_comp_p_eq_p2_comp_p p
    exact (D.iso (p1 p ≫ p) (p1 p) (p2 p) rfl h.symm).symm
  unit := by
    -- TODO: prove from `D.hom_self` for the diagonal.
    sorry
  cocycle := by
    -- TODO: prove from `D.hom_comp` for triple overlaps.
    sorry

/-!
## Morphisms
-/

/-- Convert a morphism of single-morphism descent data to a morphism of mathlib descent data. -/
def singleToSingletonHom {D₁ D₂ : SingleMorphismDescentDatum (F := F) p}
    (f : D₁ ⟶ D₂) :
    singleToSingletonDescentDatum F p D₁ ⟶ singleToSingletonDescentDatum F p D₂ where
  hom := fun _ => (f : SingleMorphismDescentDatum.Hom D₁ D₂).hom
  comm := by
    intro Y q i₁ i₂ g₁ g₂ hg₁ hg₂
    cases i₁; cases i₂
    -- TODO: prove using `f.comm` and functoriality of `pullHom`.
    sorry

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
    SingleMorphismDescentDatum (F := F) p ⥤
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  obj := singleToSingletonDescentDatum F p
  map := singleToSingletonHom F p
  map_id := fun D => by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToSingletonHom, singleToSingletonDescentDatum]
    rfl
  map_comp := fun f g => by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToSingletonHom, singleToSingletonDescentDatum,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom]
    rfl

/-- The functor from mathlib descent data to single-morphism descent data. -/
def singletonToSingleFunctor :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) ⥤
      SingleMorphismDescentDatum (F := F) p where
  obj := singletonToSingleDescentDatum F p
  map := singletonToSingleHom F p
  map_id := fun D => by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [singletonToSingleHom, singletonToSingleDescentDatum]
    rfl
  map_comp := fun f g => by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [singletonToSingleHom, singletonToSingleDescentDatum,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom]
    rfl

/-!
## Equivalence
-/

/-- The unit of the equivalence: `D ≅ singletonToSingle (singleToSingleton D)`. -/
def singleSingletonUnit (D : SingleMorphismDescentDatum (F := F) p) :
    D ≅ (singleToSingletonFunctor F p ⋙ singletonToSingleFunctor F p).obj D where
  hom := ⟨𝟙 D.obj, by
    simp only [Functor.comp_obj, singleToSingletonFunctor, singletonToSingleFunctor,
               singletonToSingleDescentDatum, singleToSingletonDescentDatum]
    -- The ξ's should match up to coherence
    sorry⟩
  inv := ⟨𝟙 D.obj, by
    simp only [Functor.comp_obj, singleToSingletonFunctor, singletonToSingleFunctor,
               singletonToSingleDescentDatum, singleToSingletonDescentDatum]
    sorry⟩
  hom_inv_id := by
    apply SingleMorphismDescentDatum.Hom.ext
    dsimp only [SingleMorphismDescentDatum.instCategory]
    simp
  inv_hom_id := by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [SingleMorphismDescentDatum.instCategory, singleToSingletonFunctor,
      singletonToSingleFunctor, singleToSingletonDescentDatum, singletonToSingleDescentDatum,
      Functor.comp_obj, SingleMorphismDescentDatum.Hom.comp_hom,
      SingleMorphismDescentDatum.Hom.id_hom, Category.comp_id]

/-- The counit of the equivalence: `singleToSingleton (singletonToSingle D) ≅ D`. -/
def singleSingletonCounit
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
    (singletonToSingleFunctor F p ⋙ singleToSingletonFunctor F p).obj D ≅ D where
  hom := ⟨fun _ => 𝟙 (D.obj PUnit.unit), fun q g₁ g₂ hg₁ hg₂ => by
    cases ‹PUnit›; cases ‹PUnit›
    simp only [Functor.comp_obj, singletonToSingleFunctor, singleToSingletonFunctor,
               singleToSingletonDescentDatum, singletonToSingleDescentDatum]
    -- Should follow from coherence
    sorry⟩
  inv := ⟨fun _ => 𝟙 (D.obj PUnit.unit), fun q g₁ g₂ hg₁ hg₂ => by
    cases ‹PUnit›; cases ‹PUnit›
    sorry⟩
  hom_inv_id := by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom, Functor.comp_obj,
      singleToSingletonFunctor, singletonToSingleFunctor, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, Category.comp_id]
  inv_hom_id := by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp

/-- The equivalence between single-morphism descent data and mathlib's descent data
for the singleton family. -/
def singleSingletonDescentDataEquiv :
    SingleMorphismDescentDatum (F := F) p ≌
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  functor := singleToSingletonFunctor F p
  inverse := singletonToSingleFunctor F p
  unitIso := NatIso.ofComponents (singleSingletonUnit F p) (by
    intro D₁ D₂ f
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [SingleMorphismDescentDatum.instCategory, singleToSingletonFunctor,
      singletonToSingleFunctor, singleSingletonUnit, singleToSingletonHom, singletonToSingleHom,
      singleToSingletonDescentDatum, singletonToSingleDescentDatum, Functor.comp_obj,
      Functor.id_obj, Functor.comp_map, Functor.id_map,
      SingleMorphismDescentDatum.Hom.comp_hom, Category.id_comp, Category.comp_id])
  counitIso := NatIso.ofComponents (singleSingletonCounit F p) (by
    intro D₁ D₂ f
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToSingletonFunctor, singletonToSingleFunctor, singleSingletonCounit,
      singleToSingletonHom, singletonToSingleHom, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map, CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      Category.id_comp, Category.comp_id])
  functor_unitIso_comp X := by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToSingletonFunctor, singletonToSingleFunctor, singleSingletonUnit,
      singleSingletonCounit, singleToSingletonHom, singleToSingletonDescentDatum,
      singletonToSingleDescentDatum, Functor.comp_obj, Functor.id_obj,
      NatIso.ofComponents_hom_app, Category.comp_id,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom]

end

end Descent.Pseudofunctor.Descent
