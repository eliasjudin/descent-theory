/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Pseudofunctor.Descent.CechDescentData.Functors

/-!
# Equivalence with singleton-family descent data
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
## Equivalence
-/

/-- The unit of the equivalence: `D ≅ singletonToSingle (singleToSingleton D)`. -/
def single_singleton_unit (D : CechDescentData (F := F) p) :
    D ≅ (single_to_singleton_functor F p ⋙ singleton_to_single_functor F p).obj D where
  hom := ⟨𝟙 D.obj, by
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
  simpa [hcomp] using
    (D.hom_self (q := (p1 p ≫ p)) (i := PUnit.unit) (g := p2 p) hf_p2)

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
    calc
      𝟙 ((F.map f₁.op.toLoc).toFunctor.obj (D.obj PUnit.unit)) ≫
          D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              hf₁
              hf₂ =
            D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) f₁ f₂
              hf₁
              hf₂ := by
        simp
      _ = pull := by
        simpa [pull] using hpull.symm
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

end

end Descent.Pseudofunctor.Descent
