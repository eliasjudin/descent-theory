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
Main definitions: `singleToMathlibDescentDatum`, `mathlibToSingleDescentDatum`,
`singleToMathlibFunctor`, `mathlibToSingleFunctor`, `singleMathlibDescentDataEquiv`.
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
## Forward direction: Single → Mathlib
-/

/-- Convert a single morphism descent datum to mathlib's descent data for the singleton family.

The key mapping:
- `obj ()` := `D.obj`
- `hom q f₁ f₂` at Y mapping to E comes from `D.ξ` transported appropriately -/
def singleToMathlibDescentDatum (D : SingleMorphismDescentDatum (F := F) p) :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  obj := fun _ => D.obj
  hom := fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ => by
    cases i₁; cases i₂ -- Both are PUnit.unit
    -- The lift u : Y ⟶ cechTwo p satisfies u ≫ π₁ = f₁ and u ≫ π₂ = f₂
    have h : f₁ ≫ p = f₂ ≫ p := by simp only [singletonMorphism] at hf₁ hf₂; rw [hf₁, hf₂]
    let u : Y ⟶ cechTwo p := Limits.pullback.lift f₁ f₂ h
    have hu1 : u ≫ p1 p = f₁ := Limits.pullback.lift_fst _ _ _
    have hu2 : u ≫ p2 p = f₂ := Limits.pullback.lift_snd _ _ _
    -- D.ξ : π₂^* D.obj ≅ π₁^* D.obj
    -- We need: f₁^* D.obj ⟶ f₂^* D.obj
    -- Use coherence isos to connect f₁^* with (u ≫ π₁)^* and f₂^* with (u ≫ π₂)^*
    exact (reindex_objIsoOfEq F hu1.symm D.obj).hom ≫
          (reindex_comp_iso_obj F u (p1 p) D.obj).hom ≫
          (reindex F u).map D.ξ.inv ≫
          (reindex_comp_iso_obj F u (p2 p) D.obj).inv ≫
          (reindex_objIsoOfEq F hu2 D.obj).hom
  pullHom_hom := fun g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ => by
    cases ‹PUnit›; cases ‹PUnit›
    -- This requires coherence of mapComp
    sorry
  hom_self := fun q g hg => by
    cases ‹PUnit›
    -- When f₁ = f₂ = g, the lift factors through the diagonal
    -- D.unit gives the result
    sorry
  hom_comp := fun q f₁ f₂ f₃ hf₁ hf₂ hf₃ => by
    cases ‹PUnit›; cases ‹PUnit›; cases ‹PUnit›
    -- This follows from D.cocycle
    sorry

/-- Convert mathlib's descent data for the singleton family to a single morphism descent datum. -/
def mathlibToSingleDescentDatum
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
    -- This follows from D.hom_self for the diagonal
    sorry
  cocycle := by
    -- This follows from D.hom_comp for triple overlaps
    sorry

/-!
## Morphisms
-/

/-- Convert a morphism of single-morphism descent data to a morphism of mathlib descent data. -/
def singleToMathlibHom {D₁ D₂ : SingleMorphismDescentDatum (F := F) p}
    (f : D₁ ⟶ D₂) :
    singleToMathlibDescentDatum F p D₁ ⟶ singleToMathlibDescentDatum F p D₂ where
  hom := fun _ => (f : SingleMorphismDescentDatum.Hom D₁ D₂).hom
  comm := fun q g₁ g₂ hg₁ hg₂ => by
    cases ‹PUnit›; cases ‹PUnit›
    simp only [singleToMathlibDescentDatum]
    -- Need to show compatibility with ξ transport
    sorry

/-- Convert a morphism of mathlib descent data to a morphism of single-morphism descent data. -/
def mathlibToSingleHom
    {D₁ D₂ : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)}
    (f : D₁ ⟶ D₂) :
    mathlibToSingleDescentDatum F p D₁ ⟶ mathlibToSingleDescentDatum F p D₂ :=
  ⟨f.hom PUnit.unit, by
    simp only [mathlibToSingleDescentDatum]
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
def singleToMathlibFunctor :
    SingleMorphismDescentDatum (F := F) p ⥤
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  obj := singleToMathlibDescentDatum F p
  map := singleToMathlibHom F p
  map_id := fun D => by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToMathlibHom, singleToMathlibDescentDatum]
    rfl
  map_comp := fun f g => by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToMathlibHom, singleToMathlibDescentDatum,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom]
    rfl

/-- The functor from mathlib descent data to single-morphism descent data. -/
def mathlibToSingleFunctor :
    CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) ⥤
      SingleMorphismDescentDatum (F := F) p where
  obj := mathlibToSingleDescentDatum F p
  map := mathlibToSingleHom F p
  map_id := fun D => by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [mathlibToSingleHom, mathlibToSingleDescentDatum]
    rfl
  map_comp := fun f g => by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [mathlibToSingleHom, mathlibToSingleDescentDatum,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom]
    rfl

/-!
## Equivalence
-/

/-- The unit of the equivalence: D ≅ mathlibToSingle (singleToMathlib D). -/
def singleMathlibUnit (D : SingleMorphismDescentDatum (F := F) p) :
    D ≅ (singleToMathlibFunctor F p ⋙ mathlibToSingleFunctor F p).obj D where
  hom := ⟨𝟙 D.obj, by
    simp only [Functor.comp_obj, singleToMathlibFunctor, mathlibToSingleFunctor,
               mathlibToSingleDescentDatum, singleToMathlibDescentDatum]
    -- The ξ's should match up to coherence
    sorry⟩
  inv := ⟨𝟙 D.obj, by
    simp only [Functor.comp_obj, singleToMathlibFunctor, mathlibToSingleFunctor,
               mathlibToSingleDescentDatum, singleToMathlibDescentDatum]
    sorry⟩
  hom_inv_id := by
    apply SingleMorphismDescentDatum.Hom.ext
    dsimp only [SingleMorphismDescentDatum.instCategory]
    simp
  inv_hom_id := by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [SingleMorphismDescentDatum.instCategory, singleToMathlibFunctor,
      mathlibToSingleFunctor, singleToMathlibDescentDatum, mathlibToSingleDescentDatum,
      Functor.comp_obj, SingleMorphismDescentDatum.Hom.comp_hom,
      SingleMorphismDescentDatum.Hom.id_hom, Category.comp_id]

/-- The counit of the equivalence: singleToMathlib (mathlibToSingle D) ≅ D. -/
def singleMathlibCounit
    (D : CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p)) :
    (mathlibToSingleFunctor F p ⋙ singleToMathlibFunctor F p).obj D ≅ D where
  hom := ⟨fun _ => 𝟙 (D.obj PUnit.unit), fun q g₁ g₂ hg₁ hg₂ => by
    cases ‹PUnit›; cases ‹PUnit›
    simp only [Functor.comp_obj, mathlibToSingleFunctor, singleToMathlibFunctor,
               singleToMathlibDescentDatum, mathlibToSingleDescentDatum]
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
      singleToMathlibFunctor, mathlibToSingleFunctor, singleToMathlibDescentDatum,
      mathlibToSingleDescentDatum, Category.comp_id]
  inv_hom_id := by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp

/-- The equivalence between single-morphism descent data and mathlib's descent data
for the singleton family. -/
def singleMathlibDescentDataEquiv :
    SingleMorphismDescentDatum (F := F) p ≌
      CategoryTheory.Pseudofunctor.DescentData (F := F) (f := singletonMorphism p) where
  functor := singleToMathlibFunctor F p
  inverse := mathlibToSingleFunctor F p
  unitIso := NatIso.ofComponents (singleMathlibUnit F p) (by
    exact fun D₁ D₂ f ↦ by
    apply SingleMorphismDescentDatum.Hom.ext
    simp only [SingleMorphismDescentDatum.instCategory, singleToMathlibFunctor,
          mathlibToSingleFunctor, singleMathlibUnit, singleToMathlibHom, mathlibToSingleHom,
          singleToMathlibDescentDatum, mathlibToSingleDescentDatum, Functor.comp_obj,
          Functor.id_obj, Functor.comp_map, Functor.id_map,
          SingleMorphismDescentDatum.Hom.comp_hom, Category.id_comp, Category.comp_id])
  counitIso := NatIso.ofComponents (singleMathlibCounit F p) (by
    exact fun D₁ D₂ f ↦ by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToMathlibFunctor, mathlibToSingleFunctor, singleMathlibCounit,
      singleToMathlibHom, mathlibToSingleHom, singleToMathlibDescentDatum,
      mathlibToSingleDescentDatum, Functor.comp_obj, Functor.id_obj, Functor.comp_map,
      Functor.id_map, CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      Category.id_comp, Category.comp_id])
  functor_unitIso_comp X := by
    apply CategoryTheory.Pseudofunctor.DescentData.Hom.ext
    funext i; cases i
    simp only [singleToMathlibFunctor, mathlibToSingleFunctor, singleMathlibUnit,
      singleMathlibCounit, singleToMathlibHom, singleToMathlibDescentDatum,
      mathlibToSingleDescentDatum, Functor.comp_obj, Functor.id_obj,
      NatIso.ofComponents_hom_app, Category.comp_id,
      CategoryTheory.Pseudofunctor.DescentData.comp_hom,
      CategoryTheory.Pseudofunctor.DescentData.id_hom]

end

end Descent.Pseudofunctor.Descent
