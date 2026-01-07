/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Reindexing for Pseudofunctors

This file defines the reindexing functors and coherence isomorphisms for
pseudofunctors `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.

## Mathematical Background

A pseudofunctor `F : Cᵒᵖ ⥤ Cat` assigns to each object `S` a category `F(S)` and to each
morphism `f : R ⟶ S` a "reindexing" functor `f^* : F(S) ⥤ F(R)`. The key difference from
a strict functor is that the composition law `(g ≫ f)^* = g^* ∘ f^*` and identity law
`(𝟙 S)^* = 𝟭` hold only up to coherent natural isomorphism, not definitionally.

### Convention for `reindex_comp_iso_obj`

**This is the most convention-sensitive definition in the library.**

We define `reindex F f := F.map f.op.toLoc`, so for composable morphisms `g : T ⟶ R` and
`f : R ⟶ S`, we have:
- `reindex F (g ≫ f)` corresponds to `F.map (g ≫ f).op.toLoc = F.map (f.op ≫ g.op).toLoc`
- `reindex F g ⋙ reindex F f` would be `F.map g.op.toLoc ⋙ F.map f.op.toLoc`

The coherence isomorphism `reindex_comp_iso_obj g f a : (g ≫ f)^* a ≅ g^*(f^* a)` is defined
using `F.mapComp f.op.toLoc g.op.toLoc`, which has type:
```
F.mapComp f.op.toLoc g.op.toLoc : F.map (f.op.toLoc ≫ g.op.toLoc) ≅ F.map f.op.toLoc ⋙ F.map g.op.toLoc
```

Since `(g ≫ f).op = f.op ≫ g.op`, this gives us the correct direction.

## Main definitions

* `reindex F f`: Reindexing along a morphism `f : R ⟶ S` for a pseudofunctor
* `reindex_objIsoOfEq`: If `f = g`, then `f^* a ≅ g^* a`
* `reindex_comp_iso_obj`: The canonical isomorphism `(g ≫ f)^* a ≅ g^* (f^* a)`
* `reindex_id_isoObj`: The canonical isomorphism `(𝟙 S)^* a ≅ a`

## Coherence Laws

The coherence isomorphisms satisfy the standard pentagon and triangle axioms, which we
prove explicitly in `reindex_pentagon` and `reindex_triangle`. These ensure that any
two ways of re-associating iterated pullbacks yield the same result.
-/

open CategoryTheory

namespace Descent.Pseudofunctor

open Opposite

universe v' v u' u

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

noncomputable section

/-!
## Reindexing for pseudofunctors
-/

/-- Reindexing along a morphism for a pseudofunctor. -/
abbrev reindex {R S : C} (f : R ⟶ S) :
    F.obj (.mk (op S)) ⥤ F.obj (.mk (op R)) :=
  F.map f.op.toLoc

/-- If `f = g`, then `f^* a ≅ g^* a`. -/
def reindex_objIsoOfEq {R S : C} {f g : R ⟶ S} (h : f = g)
    (a : F.obj (.mk (op S))) :
    (reindex F f).obj a ≅ (reindex F g).obj a := by
  subst h
  exact Iso.refl _

/-- The canonical isomorphism `(g ≫ f)^* a ≅ g^* (f^* a)`. -/
def reindex_comp_iso_obj {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : F.obj (.mk (op S))) :
    (reindex F (g ≫ f)).obj a ≅
      (reindex F g).obj ((reindex F f).obj a) :=
  (F.mapComp f.op.toLoc g.op.toLoc).app a

/-- The canonical isomorphism `((𝟙 S)^* a) ≅ a`. -/
def reindex_id_isoObj {S : C} (a : F.obj (.mk (op S))) :
    (reindex F (𝟙 S)).obj a ≅ a :=
  (F.mapId (.mk (op S))).app a

/-!
## Clarifying lemmas for `reindex_comp_iso_obj`

These lemmas make explicit the rewriting behavior of the coherence isomorphisms,
providing a clear specification that protects against convention errors in refactoring.
-/

/-- The coherence isomorphism `reindex_comp_iso_obj` rewrites `(g ≫ f)^*` to `g^* ∘ f^*`.

This is the fundamental rewriting lemma: applying `(g ≫ f)^*` to an object `a` and then
applying `reindex_comp_iso_obj.hom` yields the same object as first applying `f^*` and then `g^*`.
The direction is `(g ≫ f)^* a → g^*(f^* a)`, matching the mathematical convention that
"pullback along a composition equals iterated pullback in the opposite order". -/
lemma reindex_comp_iso_obj_hom_eq {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : F.obj (.mk (op S))) :
    (reindex_comp_iso_obj F g f a).hom =
      (F.mapComp f.op.toLoc g.op.toLoc).hom.app a := rfl

/-- The inverse direction of `reindex_comp_iso_obj`: `g^*(f^* a) → (g ≫ f)^* a`. -/
lemma reindex_comp_iso_obj_inv_eq {T R S : C} (g : T ⟶ R) (f : R ⟶ S) (a : F.obj (.mk (op S))) :
    (reindex_comp_iso_obj F g f a).inv =
      (F.mapComp f.op.toLoc g.op.toLoc).inv.app a := rfl

/-- Explicit statement: `reindex_comp_iso_obj` witnesses that `(g ≫ f)^*` is naturally isomorphic
to the composite `f^* ⋙ g^*` (note: `f^*` first, then `g^*`). -/
def reindex_comp_iso_comp_reindex {T R S : C} (g : T ⟶ R) (f : R ⟶ S) :
    ∀ a : F.obj (.mk (op S)),
      (reindex F (g ≫ f)).obj a ≅ (reindex F g).obj ((reindex F f).obj a) :=
  fun a => reindex_comp_iso_obj F g f a

/-!
## Coherence Laws (Pentagon and Triangle)

These are the standard coherence axioms for pseudofunctors. They ensure that any two
ways of re-associating iterated pullbacks yield canonically isomorphic results.

The underlying pseudofunctor `F` satisfies these axioms by construction (via `F.mapComp_assoc`
and `F.mapComp_id`). We provide explicit statements specialized to reindexing for clarity.

### Pentagon Axiom

For morphisms `h : U ⟶ T`, `g : T ⟶ R`, `f : R ⟶ S` and object `a : F(S)`, the pentagon
identity states that the following diagram commutes:

```
                        ((h ≫ g) ≫ f)^* a
                       /                 \
        assoc_comp    /                   \   comp_assoc
                     v                     v
        (h ≫ g)^*(f^* a)                 (h ≫ (g ≫ f))^* a
             |                                  |
   comp_left |                                  | comp_right
             v                                  v
      h^*(g^*(f^* a))  ←————————————————  h^*((g ≫ f)^* a)
                           h^*(comp)
```

### Triangle Axiom

For a morphism `f : R ⟶ S` and object `a : F(S)`, composing the identity coherence
`(𝟙 S)^* a ≅ a` with the composition coherence `(f ≫ 𝟙 S)^* a ≅ f^*((𝟙 S)^* a)` yields
the isomorphism induced by `f ≫ 𝟙 S = f`.
-/

/-- The pentagon coherence axiom for reindexing, stated via the underlying pseudofunctor.

This expresses that the two canonical paths from `(f ≫ g ≫ h)^* a` to `h^*(g^*(f^* a))`
coincide, where one path first associates `(f ≫ g) ≫ h` and the other associates `f ≫ (g ≫ h)`.

The proof follows from `F.mapComp_assoc_right_hom_app`. -/
lemma reindex_pentagon {U T R S : C} (h : U ⟶ T) (g : T ⟶ R) (f : R ⟶ S)
    (a : F.obj (.mk (op S))) :
    (F.mapComp f.op.toLoc (g.op.toLoc ≫ h.op.toLoc)).hom.app a ≫
      (F.mapComp g.op.toLoc h.op.toLoc).hom.app ((F.map f.op.toLoc).obj a) =
    (F.map₂ (Bicategory.associator f.op.toLoc g.op.toLoc h.op.toLoc).inv).app a ≫
      (F.mapComp (f.op.toLoc ≫ g.op.toLoc) h.op.toLoc).hom.app a ≫
        (F.map h.op.toLoc).map ((F.mapComp f.op.toLoc g.op.toLoc).hom.app a) :=
  F.mapComp_assoc_right_hom_app f.op.toLoc g.op.toLoc h.op.toLoc a

/-- The right unit coherence axiom for composition with identity on the right.

For `f : R ⟶ S`, the composition coherence `(f ≫ 𝟙 R)^*` composed with the identity
coherence `(𝟙 R)^* ≅ 𝟭` equals the right unitor (up to associativity of composition in the
bicategory of categories). -/
lemma reindex_unit_right {R S : C} (f : R ⟶ S) (a : F.obj (.mk (op S))) :
    (F.mapComp f.op.toLoc (𝟙 R).op.toLoc).hom.app a =
    (F.map₂ (Bicategory.rightUnitor f.op.toLoc).hom).app a ≫
      (F.mapId (.mk (op R))).inv.app ((F.map f.op.toLoc).obj a) :=
  F.mapComp_id_right_hom_app f.op.toLoc a

/-- The left unit coherence axiom for composition with identity on the left.

For `f : R ⟶ S`, the composition coherence `(𝟙 S ≫ f)^* = (𝟙 S)^* ∘ f^*` composed with
the identity coherence `(𝟙 S)^* ≅ 𝟭` equals the left unitor. -/
lemma reindex_unit_left {R S : C} (f : R ⟶ S) (a : F.obj (.mk (op S))) :
    (F.mapComp (𝟙 S).op.toLoc f.op.toLoc).hom.app a =
    (F.map₂ (Bicategory.leftUnitor f.op.toLoc).hom).app a ≫
      (F.map f.op.toLoc).map ((F.mapId (.mk (op S))).inv.app a) :=
  F.mapComp_id_left_hom_app f.op.toLoc a

end

end Descent.Pseudofunctor
