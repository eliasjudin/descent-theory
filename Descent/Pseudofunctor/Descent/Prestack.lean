/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.Over

/-!
# Prestacks: fully faithfulness of the comparison functor

We show that for a prestack `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`, the comparison functor
`Pseudofunctor.toDescentData` attached to a covering family is fully faithful.
-/

open CategoryTheory

namespace Descent.Pseudofunctor.Descent

open Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Prestack

universe t v' v u' u

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

noncomputable section

private def overObj (i : ι) : Over S := Over.mk (f i)

private def overMap (i : ι) : overObj (f := f) i ⟶ Over.mk (𝟙 S) :=
  Over.homMk (f i)

private lemma overEquiv_symm_ofArrows :
    (Sieve.overEquiv (Over.mk (𝟙 S))).symm (Sieve.ofArrows X f) =
      Sieve.ofArrows (Y := fun i => overObj (f := f) i) (overMap (f := f)) := by
  ext Z g
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · have hg' : Sieve.ofArrows X f g.left :=
      (Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 S)) (S := Sieve.ofArrows X f) (f := g)).1 hg
    rcases (Sieve.mem_ofArrows_iff (Y := X) (f := f) (g := g.left)).1 hg' with ⟨i, a, ha⟩
    refine (Sieve.mem_ofArrows_iff (Y := fun i => overObj (f := f) i) (f := overMap (f := f))
      (g := g)).2 ?_
    refine ⟨i, Over.homMk a ?_, ?_⟩
    · have hleft : g.left = Z.hom := by simpa using (Over.w g)
      calc
        a ≫ (overObj (f := f) i).hom = a ≫ f i := by simp [overObj]
        _ = g.left := by simp [ha]
        _ = Z.hom := hleft
    · ext
      change g.left = a ≫ (overMap (f := f) i).left
      simp [ha, overMap]
  · rcases (Sieve.mem_ofArrows_iff (Y := fun i => overObj (f := f) i) (f := overMap (f := f))
      (g := g)).1 hg with ⟨i, a, ha⟩
    have hleft : g.left = a.left ≫ f i := by
      simpa using congrArg (·.left) ha
    refine (Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 S)) (S := Sieve.ofArrows X f) (f := g)).2 ?_
    exact (Sieve.mem_ofArrows_iff (Y := X) (f := f) (g := g.left)).2 ⟨i, a.left, hleft⟩

private lemma overMap_comp_toLoc {Z : Over S} {i : ι} (gi : Z ⟶ overObj (f := f) i) :
    (f i).op.toLoc ≫ gi.left.op.toLoc = Z.hom.op.toLoc := by
  have hgi : gi.left ≫ f i = Z.hom := by
    simpa [overObj] using (Over.w gi)
  simpa using congrArg (·.toLoc) (congrArg Quiver.Hom.op hgi)

private lemma presheafHom_isSheafFor_over
    (J : GrothendieckTopology C) [F.IsPrestack J]
    (hf : Sieve.ofArrows X f ∈ J S) (M N : F.obj (.mk (op S))) :
    Presieve.IsSheafFor (F.presheafHom M N)
      (Presieve.ofArrows (fun i => overObj (f := f) i) (overMap (f := f))) := by
  have hcover :
      Sieve.ofArrows (Y := fun i => overObj (f := f) i) (overMap (f := f)) ∈
        (J.over S) (Over.mk (𝟙 S)) := by
    have hcover' :
        (Sieve.overEquiv (Over.mk (𝟙 S))).symm (Sieve.ofArrows X f) ∈
          (J.over S) (Over.mk (𝟙 S)) :=
      GrothendieckTopology.overEquiv_symm_mem_over (J := J) (Y := Over.mk (𝟙 S))
        (S := Sieve.ofArrows X f) hf
    have hcover'' :
        Sieve.ofArrows (Y := fun i => overObj (f := f) i) (overMap (f := f)) =
          (Sieve.overEquiv (Over.mk (𝟙 S))).symm (Sieve.ofArrows X f) := by
      symm
      exact overEquiv_symm_ofArrows (f := f)
    simpa [hcover''] using hcover'
  have hSheafSieve :
      Presieve.IsSheafFor (F.presheafHom M N)
        (Sieve.ofArrows (Y := fun i => overObj (f := f) i) (overMap (f := f)) :
          Presieve (Over.mk (𝟙 S))) := by
    simpa using
      (Presheaf.IsSheaf.isSheafFor (hP := (Pseudofunctor.IsPrestack.isSheaf (F := F) (J := J) M N))
        (S := Sieve.ofArrows (Y := fun i => overObj (f := f) i) (overMap (f := f)))
        hcover)
  refine (Presieve.isSheafFor_iff_generate
      (P := F.presheafHom M N)
      (R := Presieve.ofArrows (fun i => overObj (f := f) i) (overMap (f := f)))).2 ?_
  simpa using hSheafSieve

private lemma pullHom_overMap_eq
    (M N : F.obj (.mk (op S))) (i : ι)
    (t : (F.map (𝟙 S).op.toLoc).obj M ⟶ (F.map (𝟙 S).op.toLoc).obj N) :
    pullHom t (overMap (f := f) i).left (overObj (f := f) i).hom
        (overObj (f := f) i).hom =
      (F.map (f i).op.toLoc).map
        ((F.mapId (.mk (op S))).inv.app M ≫ t ≫ (F.mapId (.mk (op S))).hom.app N) := by
  simp [pullHom, overMap, overObj, Functor.map_comp,
    Pseudofunctor.mapComp'_id_comp_hom_app, Pseudofunctor.mapComp'_id_comp_inv_app]

private lemma presheafHom_map_overMap_eq
    (M N : F.obj (.mk (op S))) (i : ι)
    (t : (F.map (𝟙 S).op.toLoc).obj M ⟶ (F.map (𝟙 S).op.toLoc).obj N) :
    (F.presheafHom M N).map (overMap (f := f) i).op t =
      (F.map (f i).op.toLoc).map
        ((F.mapId (.mk (op S))).inv.app M ≫ t ≫ (F.mapId (.mk (op S))).hom.app N) := by
  simpa [Pseudofunctor.presheafHom] using
    pullHom_overMap_eq (f := f) (M := M) (N := N) (i := i) (t := t)

/-- If `F` is a prestack, the comparison functor for a covering family is fully faithful. -/
noncomputable def toDescentData_fullyFaithful
    (J : GrothendieckTopology C) [F.IsPrestack J]
    (hf : Sieve.ofArrows X f ∈ J S) :
    (Pseudofunctor.toDescentData (F := F) (f := f)).FullyFaithful := by
  refine
    { preimage := ?preimage
      map_preimage := ?map_preimage
      preimage_map := ?preimage_map }
  · intro M N φ
    -- Use the sheaf condition on `F.presheafHom M N` over the over-category.
    have hSheaf :=
      presheafHom_isSheafFor_over (F := F) (f := f) (J := J) (hf := hf) M N
    -- The family given by the components of `φ` is compatible.
    have hcompat :
        Presieve.Arrows.Compatible (P := F.presheafHom M N)
          (π := overMap (f := f)) (fun i => φ.hom i) := by
      intro i j Z gi gj _
      -- Expand the presheaf map; the descent data compatibility gives the equality.
      -- `Z` is an object of `Over S`, so `Z.hom` is the common composite to `S`.
      have hgi : gi.left ≫ f i = Z.hom := by
        simpa [overObj] using (Over.w gi)
      have hgj : gj.left ≫ f j = Z.hom := by
        simpa [overObj] using (Over.w gj)
      have hgi_op : (f i).op.toLoc ≫ gi.left.op.toLoc = Z.hom.op.toLoc :=
        overMap_comp_toLoc (f := f) gi
      have hgj_op : (f j).op.toLoc ≫ gj.left.op.toLoc = Z.hom.op.toLoc :=
        overMap_comp_toLoc (f := f) gj
      -- Apply the compatibility condition in `DescentData.Hom.comm`, then cancel the
      -- comparison isomorphisms.
      have hcomm :=
        (φ.comm (q := Z.hom) (f₁ := gi.left) (f₂ := gj.left) (i₁ := i) (i₂ := j)
          (hf₁ := hgi) (hf₂ := hgj))
      have hcomm' :
          (F.map gi.left.op.toLoc).map (φ.hom i) ≫
              (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).inv.app N ≫
                (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).hom.app N =
            (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).inv.app M ≫
              (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).hom.app M ≫
                (F.map gj.left.op.toLoc).map (φ.hom j) := by
        simpa [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, overObj] using hcomm
      have hcomm'' :=
        congrArg (fun k =>
          (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).hom.app M ≫
            k ≫
          (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).inv.app N)
          hcomm'
      simpa [Pseudofunctor.presheafHom, pullHom, overObj, hgi, hgj,
        Category.assoc] using hcomm''
    -- Use the explicit sheaf condition on arrows to get the unique amalgamation.
    have hex :
        ∃! t, ∀ i, (F.presheafHom M N).map (overMap (f := f) i).op t = φ.hom i := by
      -- `isSheafFor_arrows_iff` gives the unique amalgamation for compatible families.
      have := (Presieve.isSheafFor_arrows_iff (P := F.presheafHom M N)
        (X := fun i => overObj (f := f) i) (π := overMap (f := f))).1 hSheaf
      simpa using this (fun i => φ.hom i) hcompat
    -- Transport along `mapId` to get a morphism `M ⟶ N`.
    let ηM := (F.mapId (.mk (op S))).app M
    let ηN := (F.mapId (.mk (op S))).app N
    exact ηM.inv ≫ hex.choose ≫ ηN.hom
  · intro M N φ
    -- The image of the chosen amalgamation is the original morphism.
    ext i
    have hSheaf :=
      presheafHom_isSheafFor_over (F := F) (f := f) (J := J) (hf := hf) M N
    have hcompat :
        Presieve.Arrows.Compatible (P := F.presheafHom M N)
          (π := overMap (f := f)) (fun i => φ.hom i) := by
      intro i j Z gi gj _
      have hgi : gi.left ≫ f i = Z.hom := by
        simpa [overObj] using (Over.w gi)
      have hgj : gj.left ≫ f j = Z.hom := by
        simpa [overObj] using (Over.w gj)
      have hgi_op : (f i).op.toLoc ≫ gi.left.op.toLoc = Z.hom.op.toLoc :=
        overMap_comp_toLoc (f := f) gi
      have hgj_op : (f j).op.toLoc ≫ gj.left.op.toLoc = Z.hom.op.toLoc :=
        overMap_comp_toLoc (f := f) gj
      have hcomm :=
        (φ.comm (q := Z.hom) (f₁ := gi.left) (f₂ := gj.left) (i₁ := i) (i₂ := j)
          (hf₁ := hgi) (hf₂ := hgj))
      have hcomm' :
          (F.map gi.left.op.toLoc).map (φ.hom i) ≫
              (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).inv.app N ≫
                (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).hom.app N =
            (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).inv.app M ≫
              (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).hom.app M ≫
                (F.map gj.left.op.toLoc).map (φ.hom j) := by
        simpa [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, overObj] using hcomm
      have hcomm'' :=
        congrArg (fun k =>
          (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).hom.app M ≫
            k ≫
          (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).inv.app N)
          hcomm'
      simpa [Pseudofunctor.presheafHom, pullHom, overObj, hgi, hgj,
        Category.assoc] using hcomm''
    have hex :
        ∃! t, ∀ i, (F.presheafHom M N).map (overMap (f := f) i).op t = φ.hom i := by
      have := (Presieve.isSheafFor_arrows_iff (P := F.presheafHom M N)
        (X := fun i => overObj (f := f) i) (π := overMap (f := f))).1 hSheaf
      simpa using this (fun i => φ.hom i) hcompat
    let ηM := (F.mapId (.mk (op S))).app M
    let ηN := (F.mapId (.mk (op S))).app N
    simpa [ηM, ηN, pullHom_overMap_eq (f := f) (M := M) (N := N) (i := i)]
      using (hex.choose_spec.1 i)
  · intro M N φ
    -- The amalgamation of the family coming from a morphism is the morphism itself.
    have hSheaf :=
      presheafHom_isSheafFor_over (F := F) (f := f) (J := J) (hf := hf) M N
    have hcompat :
        Presieve.Arrows.Compatible (P := F.presheafHom M N)
          (π := overMap (f := f)) (fun i => (F.map (f i).op.toLoc).map φ) := by
      intro i j Z gi gj _
      have hgi : gi.left ≫ f i = Z.hom := by
        simpa [overObj] using (Over.w gi)
      have hgj : gj.left ≫ f j = Z.hom := by
        simpa [overObj] using (Over.w gj)
      have hgi_op : (f i).op.toLoc ≫ gi.left.op.toLoc = Z.hom.op.toLoc :=
        overMap_comp_toLoc (f := f) gi
      have hgj_op : (f j).op.toLoc ≫ gj.left.op.toLoc = Z.hom.op.toLoc :=
        overMap_comp_toLoc (f := f) gj
      -- This is the commutativity condition for the comparison functor.
      have hcomm :=
        ((F.toDescentData f).map φ).comm (q := Z.hom) (f₁ := gi.left) (f₂ := gj.left)
          (i₁ := i) (i₂ := j) (hf₁ := hgi) (hf₂ := hgj)
      have hcomm' :
          (F.map gi.left.op.toLoc).map ((F.map (f i).op.toLoc).map φ) ≫
              (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).inv.app N ≫
                (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).hom.app N =
            (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).inv.app M ≫
              (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).hom.app M ≫
                (F.map gj.left.op.toLoc).map ((F.map (f j).op.toLoc).map φ) := by
        convert hcomm using 1
        simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, overObj]
      have hcomm'' :=
        congrArg (fun k =>
          (F.mapComp' (f i).op.toLoc gi.left.op.toLoc Z.hom.op.toLoc hgi_op).hom.app M ≫
            k ≫
          (F.mapComp' (f j).op.toLoc gj.left.op.toLoc Z.hom.op.toLoc hgj_op).inv.app N)
          hcomm'
      simp [Pseudofunctor.presheafHom, pullHom, overObj, Category.assoc] at hcomm'' ⊢
    have hex :
        ∃! t, ∀ i, (F.presheafHom M N).map (overMap (f := f) i).op t =
          (F.map (f i).op.toLoc).map φ := by
      have := (Presieve.isSheafFor_arrows_iff (P := F.presheafHom M N)
        (X := fun i => overObj (f := f) i) (π := overMap (f := f))).1 hSheaf
      simpa using this (fun i => (F.map (f i).op.toLoc).map φ) hcompat
    let ηM := (F.mapId (.mk (op S))).app M
    let ηN := (F.mapId (.mk (op S))).app N
    -- The family coming from `φ` is an amalgamation.
    have hφ :
        ∀ i, (F.presheafHom M N).map (overMap (f := f) i).op
          (ηM.hom ≫ φ ≫ ηN.inv) =
          (F.map (f i).op.toLoc).map φ := by
      intro i
      simp [ηM, ηN, Category.assoc,
        pullHom_overMap_eq (f := f) (M := M) (N := N) (i := i)]
    have ht : hex.choose = ηM.hom ≫ φ ≫ ηN.inv :=
      (hex.choose_spec.2 _ hφ).symm
    calc
      ηM.inv ≫ hex.choose ≫ ηN.hom =
          ηM.inv ≫ (ηM.hom ≫ φ ≫ ηN.inv) ≫ ηN.hom := by
            simp [ht, Category.assoc]
      _ = φ := by
        simp [Category.assoc]

end

end Prestack

end Descent.Pseudofunctor.Descent
