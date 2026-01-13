/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.FiberedCategory.HasFibers
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Reindexing on fibers of a fibered category

Defines reindexing functors `f^* : Fiber pA S ⥤ Fiber pA R` for a fibered category
`pA : 𝒜 ⥤ C`, together with the basic coherence isomorphisms for composition and identity.

## TODO (Facets of Descent, II)

* [RESEARCH] Relate this reindexing construction to the pseudofunctor viewpoint `A : Cᵒᵖ ⥤ CAT` (indexed
  categories) used in the paper, i.e. show that `X ↦ Fiber pA X` defines a `C`-indexed category and
  that the resulting pullback functors match `reindex` up to coherent isomorphism (cf. §3.3).
* [RESEARCH] Use that bridge to transport the paper’s results stated for indexed categories to the fibered
  category API in `Descent/FiberedCategory/Descent/`.
-/

open CategoryTheory Functor Category

namespace Descent.FiberedCategory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {𝒜 : Type w} [Category.{v} 𝒜] (pA : 𝒜 ⥤ C) [pA.IsFibered]

noncomputable section

open CategoryTheory.Functor

/-!
## Reindexing on standard fibers
-/

/-- Reindexing (pullback) functor on the standard fibers of a fibered category. -/
noncomputable def reindex {R S : C} (f : R ⟶ S) : Fiber pA S ⥤ Fiber pA R where
  obj a :=
    ⟨IsPreFibered.pullbackObj (p := pA) a.2 f,
      IsPreFibered.pullbackObj_proj (p := pA) a.2 f⟩
  map {a b} φ := by
    haveI : pA.IsHomLift (𝟙 S) φ.1 := φ.2
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1) := by
      simpa using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1))
    refine
      ⟨IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) b.2 f)
          (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1),
        inferInstance⟩
  map_id a := by
    apply Fiber.hom_ext
    change
        IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) a.2 f)
            (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (𝟙 a.1))
          = 𝟙 (IsPreFibered.pullbackObj (p := pA) a.2 f)
    simp
  map_comp {a b c} φ ψ := by
    apply Fiber.hom_ext
    -- Make the lifts available for elaboration.
    haveI : pA.IsHomLift (𝟙 S) φ.1 := φ.2
    haveI : pA.IsHomLift (𝟙 S) ψ.1 := ψ.2
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1) := by
      simpa using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1))
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1) := by
      simpa using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1))
    haveI : pA.IsHomLift (𝟙 S) (φ.1 ≫ ψ.1) := by
      simpa using (inferInstance : pA.IsHomLift (𝟙 S ≫ 𝟙 S) (φ.1 ≫ ψ.1))
    haveI : pA.IsHomLift f (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)) := by
      simpa [Category.assoc] using
        (inferInstance :
          pA.IsHomLift (f ≫ 𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)))
    change
        IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) c.2 f)
            (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1))
          =
          IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) b.2 f)
              (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1)
            ≫
            IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) c.2 f)
              (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1)
    let θ :=
      IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) b.2 f)
          (IsPreFibered.pullbackMap (p := pA) a.2 f ≫ φ.1)
        ≫
        IsCartesian.map pA f (IsPreFibered.pullbackMap (p := pA) c.2 f)
          (IsPreFibered.pullbackMap (p := pA) b.2 f ≫ ψ.1)
    haveI : pA.IsHomLift (𝟙 R) θ := by
      dsimp [θ]
      infer_instance
    symm
    apply
      (IsCartesian.map_uniq (p := pA) (f := f)
        (φ := IsPreFibered.pullbackMap (p := pA) c.2 f)
        (φ' := IsPreFibered.pullbackMap (p := pA) a.2 f ≫ (φ.1 ≫ ψ.1)) θ)
    dsimp [θ]
    simp [Category.assoc]

/-- The object part of `reindex`. -/
abbrev reindexObj {R S : C} (f : R ⟶ S) (a : Fiber pA S) : Fiber pA R :=
  (reindex (pA := pA) f).obj a

/-!
## Auxiliary isomorphisms
-/

/-- Lift an isomorphism in the total category to an isomorphism in a fiber. -/
noncomputable def fiberIso {S : C} {a b : Fiber pA S} (i : a.1 ≅ b.1)
    (hi : pA.IsHomLift (𝟙 S) i.hom) : a ≅ b where
  hom := ⟨i.hom, hi⟩
  inv :=
    ⟨i.inv, by
      haveI : pA.IsHomLift (𝟙 S) i.hom := hi
      infer_instance⟩
  hom_inv_id := by
    apply Fiber.hom_ext
    change i.hom ≫ i.inv = 𝟙 a.1
    exact i.hom_inv_id
  inv_hom_id := by
    apply Fiber.hom_ext
    change i.inv ≫ i.hom = 𝟙 b.1
    exact i.inv_hom_id

/-- If `f = g`, then `f^* a ≅ g^* a`. -/
noncomputable def reindexObjIsoOfEq {R S : C} {f g : R ⟶ S} (h : f = g) (a : Fiber pA S) :
    reindexObj (pA := pA) f a ≅ reindexObj (pA := pA) g a := by
  subst h
  exact Iso.refl _

lemma reindexObjIsoOfEq_hom_naturality {R S : C} {f g : R ⟶ S} (h : f = g)
    {a b : Fiber pA S} (φ : a ⟶ b) :
    (reindexObjIsoOfEq (pA := pA) (f := f) (g := g) h a).hom ≫
        (reindex (pA := pA) g).map φ =
      (reindex (pA := pA) f).map φ ≫
        (reindexObjIsoOfEq (pA := pA) (f := f) (g := g) h b).hom := by
  subst h
  simp [reindexObjIsoOfEq]

lemma reindexObjIsoOfEq_inv_naturality {R S : C} {f g : R ⟶ S} (h : f = g)
    {a b : Fiber pA S} (φ : a ⟶ b) :
    (reindex (pA := pA) g).map φ ≫
        (reindexObjIsoOfEq (pA := pA) (f := f) (g := g) h b).inv =
      (reindexObjIsoOfEq (pA := pA) (f := f) (g := g) h a).inv ≫
        (reindex (pA := pA) f).map φ := by
  subst h
  simp [reindexObjIsoOfEq]

/-- The canonical isomorphism `(g ≫ f)^* a ≅ g^* (f^* a)`. -/
noncomputable def reindexCompIsoObj {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : Fiber pA S) :
    reindexObj (pA := pA) (g ≫ f) a ≅
      reindexObj (pA := pA) g (reindexObj (pA := pA) f a) := by
  refine
    fiberIso (pA := pA) (S := T)
      (Functor.IsFibered.pullbackPullbackIso (p := pA) a.2 f g) ?_
  dsimp [Functor.IsFibered.pullbackPullbackIso]
  infer_instance

/-- A simp-lemma characterizing the defining property of `pullbackPullbackIso`. -/
@[simp, reassoc]
lemma pullbackPullbackIso_hom_comp {R S T : C} {a : 𝒜} (ha : pA.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
    (Functor.IsFibered.pullbackPullbackIso (p := pA) ha f g).hom ≫
        IsPreFibered.pullbackMap (p := pA) (IsPreFibered.pullbackObj_proj (p := pA) ha f) g ≫
          IsPreFibered.pullbackMap (p := pA) ha f =
      IsPreFibered.pullbackMap (p := pA) ha (g ≫ f) := by
  dsimp [Functor.IsFibered.pullbackPullbackIso, IsCartesian.domainUniqueUpToIso]
  simp

/-- A simp-lemma characterizing the defining property of the inverse of `pullbackPullbackIso`. -/
@[simp, reassoc]
lemma pullbackPullbackIso_inv_comp {R S T : C} {a : 𝒜} (ha : pA.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
    (Functor.IsFibered.pullbackPullbackIso (p := pA) ha f g).inv ≫
        IsPreFibered.pullbackMap (p := pA) ha (g ≫ f) =
      IsPreFibered.pullbackMap (p := pA) (IsPreFibered.pullbackObj_proj (p := pA) ha f) g ≫
        IsPreFibered.pullbackMap (p := pA) ha f := by
  dsimp [Functor.IsFibered.pullbackPullbackIso, IsCartesian.domainUniqueUpToIso]
  simp

/-- Naturality of `reindexCompIsoObj` with respect to morphisms in the fiber. -/
lemma reindexCompIsoObj_hom_naturality {T R S : C} (g : T ⟶ R) (f : R ⟶ S)
    {a b : Fiber pA S} (φ : a ⟶ b) :
    (reindexCompIsoObj (pA := pA) (g := g) (f := f) a).hom ≫
        (reindex (pA := pA) g).map ((reindex (pA := pA) f).map φ) =
      (reindex (pA := pA) (g ≫ f)).map φ ≫
        (reindexCompIsoObj (pA := pA) (g := g) (f := f) b).hom := by
  -- Reduce to the total category and use the universal property of a Cartesian lift.
  apply Fiber.hom_ext
  -- Consider the composite Cartesian arrow `g^*(f^* b) ⟶ b` over `g ≫ f`.
  let φb :
      (reindexObj (pA := pA) g (reindexObj (pA := pA) f b)).1 ⟶ b.1 :=
    IsPreFibered.pullbackMap (p := pA) (IsPreFibered.pullbackObj_proj (p := pA) b.2 f) g ≫
      IsPreFibered.pullbackMap (p := pA) b.2 f
  haveI : IsCartesian pA (g ≫ f) φb := by
    dsimp [φb]
    infer_instance
  -- It suffices to compare after postcomposition with `φb`.
  apply IsCartesian.ext (p := pA) (f := g ≫ f) (φ := φb)
  -- Compute both composites using the defining `fac` lemmas.
  dsimp [φb, reindex, reindexCompIsoObj, fiberIso, Functor.IsFibered.pullbackPullbackIso]
  -- Reduce `fiberInclusion.map` and use the `IsCartesian.fac` simp-lemmas.
  simp [Fiber.fiberInclusion, Category.assoc]
  -- Finish by applying `IsCartesian.fac_assoc` to the remaining `IsCartesian.map`.
  simpa [Category.assoc] using
    (IsCartesian.fac_assoc (p := pA) (f := g ≫ f)
        (φ :=
          IsPreFibered.pullbackMap (p := pA) (IsPreFibered.pullbackObj_proj (p := pA) a.2 f) g ≫
            IsPreFibered.pullbackMap (p := pA) a.2 f)
        (φ' := IsPreFibered.pullbackMap (p := pA) a.2 (g ≫ f)) (h := φ.1))

/-- Naturality of the inverse of `reindexCompIsoObj`. -/
lemma reindexCompIsoObj_inv_naturality {T R S : C} (g : T ⟶ R) (f : R ⟶ S)
    {a b : Fiber pA S} (φ : a ⟶ b) :
    (reindex (pA := pA) g).map ((reindex (pA := pA) f).map φ) ≫
        (reindexCompIsoObj (pA := pA) (g := g) (f := f) b).inv =
      (reindexCompIsoObj (pA := pA) (g := g) (f := f) a).inv ≫
        (reindex (pA := pA) (g ≫ f)).map φ := by
  -- Derive from naturality of the `hom` by canceling the isomorphisms.
  have h :=
    reindexCompIsoObj_hom_naturality (pA := pA) (g := g) (f := f) (a := a) (b := b) φ
  -- `simp` takes care of rewriting with the `Iso` identities.
  simpa [Category.assoc] using
    congrArg (fun k => (reindexCompIsoObj (pA := pA) (g := g) (f := f) a).inv ≫ k ≫
        (reindexCompIsoObj (pA := pA) (g := g) (f := f) b).inv) h

/-- The canonical isomorphism `((𝟙 S)^* a) ≅ a`. -/
noncomputable def reindexIdIso {S : C} (a : Fiber pA S) : reindexObj (pA := pA) (𝟙 S) a ≅ a := by
  haveI : IsIso (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S)) := by
    have : pA.IsStronglyCartesian (𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S)) := by
      infer_instance
    exact
      IsStronglyCartesian.isIso_of_base_isIso (p := pA) (f := 𝟙 S)
        (φ := IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S))
  refine
    fiberIso (pA := pA) (S := S)
      (a := reindexObj (pA := pA) (𝟙 S) a)
      (b := a)
      (asIso (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S))) ?_
  change pA.IsHomLift (𝟙 S) (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S))
  infer_instance

/-- The natural isomorphism `reindex (𝟙 S) ≅ 𝟭 _`. -/
noncomputable def reindexIdIsoNatIso {S : C} :
    reindex (pA := pA) (𝟙 S) ≅ 𝟭 (Fiber pA S) := by
  refine NatIso.ofComponents (fun a => reindexIdIso (pA := pA) a) fun {a b} φ ↦ ?_
  haveI : pA.IsHomLift (𝟙 S) φ.1 := φ.2
  haveI :
      pA.IsHomLift (𝟙 S)
        (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S) ≫ φ.1) := by
    simpa using
      (inferInstance :
        pA.IsHomLift (𝟙 S ≫ 𝟙 S)
          (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S) ≫ φ.1))
  apply Fiber.hom_ext
  -- Use the defining property of the cartesian lift of `𝟙 S`.
  change
      (IsCartesian.map pA (𝟙 S) (IsPreFibered.pullbackMap (p := pA) b.2 (𝟙 S))
          (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S) ≫ φ.1)) ≫
        (IsPreFibered.pullbackMap (p := pA) b.2 (𝟙 S)) =
      (IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S)) ≫ φ.1
  simp

/-- The natural isomorphism `(g ≫ f)^* ≅ g^* ⋙ f^*` on fibers. -/
noncomputable def reindexCompIso {T R S : C} (g : T ⟶ R) (f : R ⟶ S) :
    reindex (pA := pA) (g ≫ f) ≅ (reindex (pA := pA) f) ⋙ (reindex (pA := pA) g) := by
  refine
    NatIso.ofComponents
      (fun a ↦ reindexCompIsoObj (pA := pA) (g := g) (f := f) a)
      (fun {a b} φ ↦
        (reindexCompIsoObj_hom_naturality (pA := pA) (g := g) (f := f)
            (a := a) (b := b) φ).symm)

@[simp]
lemma reindexIdIsoNatIso_hom_app {S : C} (a : Fiber pA S) :
    (reindexIdIsoNatIso (pA := pA) (S := S)).hom.app a =
      (reindexIdIso (pA := pA) a).hom := rfl

@[simp]
lemma reindexIdIsoNatIso_inv_app {S : C} (a : Fiber pA S) :
    (reindexIdIsoNatIso (pA := pA) (S := S)).inv.app a =
      (reindexIdIso (pA := pA) a).inv := rfl

@[simp]
lemma reindexCompIso_hom_app {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : Fiber pA S) :
    (reindexCompIso (pA := pA) (g := g) (f := f)).hom.app a =
      (reindexCompIsoObj (pA := pA) (g := g) (f := f) a).hom := rfl

@[simp]
lemma reindexCompIso_inv_app {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : Fiber pA S) :
    (reindexCompIso (pA := pA) (g := g) (f := f)).inv.app a =
      (reindexCompIsoObj (pA := pA) (g := g) (f := f) a).inv := rfl

/-!
## Coherence laws

We record the standard coherence conventions for reindexing on fibers and
their interaction with the chosen Cartesian lifts.
-/

/-- Explicit statement of the reindexing convention: `(g ≫ f)^*` is naturally isomorphic
to `f^* ⋙ g^*` (note: `f^*` first, then `g^*`). -/
def reindexCompIsoCompReindex {T R S : C} (g : T ⟶ R) (f : R ⟶ S) :
    ∀ a : Fiber pA S,
      reindexObj (pA := pA) (g ≫ f) a ≅
        reindexObj (pA := pA) g (reindexObj (pA := pA) f a) :=
  fun a => reindexCompIsoObj (pA := pA) (g := g) (f := f) a

/-- The composition coherence isomorphism factors through the underlying Cartesian lifts.

This lemma characterizes `reindexCompIsoObj` in terms of the universal property:
the hom component, when composed with the iterated Cartesian lifts, equals the
Cartesian lift for the composed morphism. -/
@[simp]
lemma reindexCompIsoObj_hom_comp_pullback {T R S : C} (g : T ⟶ R) (f : R ⟶ S)
    (a : Fiber pA S) :
    (reindexCompIsoObj (pA := pA) g f a).hom.1 ≫
      IsPreFibered.pullbackMap (p := pA)
          (IsPreFibered.pullbackObj_proj (p := pA) a.2 f) g ≫
        IsPreFibered.pullbackMap (p := pA) a.2 f =
    IsPreFibered.pullbackMap (p := pA) a.2 (g ≫ f) := by
  simp [reindexCompIsoObj, fiberIso, reindexObj,
    Functor.IsFibered.pullbackPullbackIso, IsCartesian.domainUniqueUpToIso]

/-- The inverse of the composition coherence isomorphism. -/
@[simp]
lemma reindexCompIsoObj_inv_comp_pullback {T R S : C} (g : T ⟶ R) (f : R ⟶ S)
    (a : Fiber pA S) :
    (reindexCompIsoObj (pA := pA) g f a).inv.1 ≫
      IsPreFibered.pullbackMap (p := pA) a.2 (g ≫ f) =
    IsPreFibered.pullbackMap (p := pA)
        (IsPreFibered.pullbackObj_proj (p := pA) a.2 f) g ≫
      IsPreFibered.pullbackMap (p := pA) a.2 f := by
  simp [reindexCompIsoObj, fiberIso, reindexObj,
    Functor.IsFibered.pullbackPullbackIso, IsCartesian.domainUniqueUpToIso]

/-- The identity coherence `reindexIdIso` sends the chosen pullback along `𝟙 S` to the identity.

Specifically, `(reindexIdIso a).hom.1` is the Cartesian lift along `𝟙 S`. -/
lemma reindexIdIso_hom_eq {S : C} (a : Fiber pA S) :
    (reindexIdIso (pA := pA) a).hom.1 = IsPreFibered.pullbackMap (p := pA) a.2 (𝟙 S) := by
  simp [reindexIdIso, fiberIso]

end

end Descent.FiberedCategory
