# Mathlib4 PR — Ready to Submit

The mathlib4 PR is fully prepared and committed locally at `/tmp/mathlib4` on branch
`eliasjudin/fibered-reindexing-pseudofunctor-descent`.

## To push and create the PR

```bash
cd /tmp/mathlib4
git push -u https://github.com/eliasjudin/mathlib4.git \
  eliasjudin/fibered-reindexing-pseudofunctor-descent
```

Then create the PR at:
https://github.com/leanprover-community/mathlib4/compare/master...eliasjudin:mathlib4:eliasjudin/fibered-reindexing-pseudofunctor-descent

Or use the GitHub CLI:
```bash
gh pr create \
  --repo leanprover-community/mathlib4 \
  --title "feat(CategoryTheory): reindexing functor, pseudofunctor of fibers, internal categories, single-morphism descent" \
  --body "$(cat <<'PREOF'
## Summary

This PR upstreams four self-contained modules from
[`eliasjudin/descent-theory`](https://github.com/eliasjudin/descent-theory),
a formalization of Čech-style descent along a single morphism (Apache 2.0).

### New files

**`Mathlib/CategoryTheory/FiberedCategory/Reindexing.lean`**

Defines the *reindexing functor* `f^* : Fiber pA S ⥤ Fiber pA R` for a fibered functor
`pA : 𝒜 ⥤ C`, together with:
- `reindex_comp_iso`: natural isomorphism `(g ≫ f)^* ≅ f^* ⋙ g^*`
- `reindex_id_iso`: natural isomorphism `(𝟙 S)^* ≅ 𝟭`
- coherence lemmas relating these isos to the chosen Cartesian lifts

**`Mathlib/CategoryTheory/FiberedCategory/PseudofunctorOfFibers.lean`**

Packages the reindexing data into a pseudofunctor
`pseudofunctor_of_fibers : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat`
via `pseudofunctorOfIsLocallyDiscrete`. Provides explicit associator and
left/right unitor coherence proofs.

**`Mathlib/CategoryTheory/InternalCategory/Basic.lean`**

A minimal `structure InternalCategory` for category objects in a category with pullbacks.
Uses `pullback dom cod` as the composable-pairs object. This fills a gap: Mathlib does not
currently have a general internal-category theory.

**`Mathlib/CategoryTheory/Sites/Descent/SingleMorphism.lean`**

Abbreviations for the singleton-family special case of descent:
- `SingleMorphismDescentData`: the descent-data category for `p : E ⟶ B`
- `single_morphism_comparison_functor`: the comparison functor from `F.obj (op B)`
- `IsDescentMorphism`: the comparison functor is fully faithful
- `IsEffectiveDescentMorphism`: the comparison functor is an equivalence

### Dependencies

- `Reindexing` ← `Mathlib.CategoryTheory.FiberedCategory.HasFibers`
- `PseudofunctorOfFibers` ← `Reindexing` + `Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete`
- `InternalCategory.Basic` ← `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `SingleMorphism` ← `Mathlib.CategoryTheory.Sites.Descent.DescentData`

### Origin

These modules were developed in
[`eliasjudin/descent-theory`](https://github.com/eliasjudin/descent-theory)
at commit `fe17c8d`, targeting mathlib4 commit `0ee01d5` and `leanprover/lean4:v4.27.0-rc1`.
The code has been adapted to mathlib4's `module`/`public import` syntax.

### AI disclosure

This PR was prepared with assistance from Claude Code (Anthropic).

### Notes for reviewers

- Naming: `snake_case` (e.g. `pseudofunctor_of_fibers`, `reindex_comp_iso`) may need
  renaming to `camelCase` per mathlib style
- `InternalCategory` is intentionally minimal; additional API left for follow-up PRs
- May need minor API adjustments for Lean `v4.29.0-rc3` vs the development `v4.27.0-rc1`
PREOF
)"
```

## What was committed

The local `/tmp/mathlib4` branch contains 5 changed files:

| File | Status |
|------|--------|
| `Mathlib.lean` | Modified (4 new `public import` lines added) |
| `Mathlib/CategoryTheory/FiberedCategory/Reindexing.lean` | New |
| `Mathlib/CategoryTheory/FiberedCategory/PseudofunctorOfFibers.lean` | New |
| `Mathlib/CategoryTheory/InternalCategory/Basic.lean` | New |
| `Mathlib/CategoryTheory/Sites/Descent/SingleMorphism.lean` | New |

## Key adaptations from descent-theory

All 4 files were adapted from `Descent/CategoryTheory/**` to `Mathlib/CategoryTheory/**`:

1. **Module syntax**: `import Mathlib.xxx` → `module\n\npublic import Mathlib.xxx`
2. **Section wrapper**: Added `@[expose] public section` after each module docstring
3. **Import fix** (PseudofunctorOfFibers only): `Descent.CategoryTheory.FiberedCategory.Reindexing`
   → `Mathlib.CategoryTheory.FiberedCategory.Reindexing`
