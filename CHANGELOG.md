# Changelog

All notable changes to this project are documented in this file.

## Unreleased

### Changed

- Moved Čech core declarations from `CategoryTheory.Cech` to `Descent.Cech` ownership.
- Simplified `Descent/Cech.lean` to a direct import entry point (removed re-export shim layer).
- Updated `Descent.Pseudofunctor.Descent.single_morphism_comparison_functor` to reuse
  `CategoryTheory.Pseudofunctor.single_morphism_comparison_functor`.
- Added project release/integration documentation:
  `CONTRIBUTING.md`, `MATHLIB_INTEGRATION.md`, and this changelog.
- Reorganized regression examples to use focused pseudofunctor Čech descent imports.
- Expanded bridge/singleton regression checks with additional convention and criteria sanity checks.
- Split `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean` into focused modules under
  `Descent/Pseudofunctor/Descent/CechDescentData/` and retained `CechDescentDataEquiv.lean` as
  a compatibility aggregator.
- Split fibered reindexing and singleton-cover conversion internals into focused submodules under
  `Descent/CategoryTheory/FiberedCategory/Reindexing/` and
  `Descent/Pseudofunctor/Descent/CechDescentData/Conversions/`, while preserving the stable
  `Reindexing.lean` and `Conversions.lean` umbrellas.
- Added fibered-side criteria bridge theorems in
  `Descent/FiberedCategory/Descent/SingleMorphismComparison.lean`.
- Aligned package organization with mathlib-style root/topic modules by making `Descent.lean` the
  user-facing umbrella, removing the repository-wide `Descent/API.lean` and `Descent/All.lean`
  aggregators, keeping regression wiring in `DescentTestDriver.lean` with direct example imports,
  and updating CI/docs accordingly.
