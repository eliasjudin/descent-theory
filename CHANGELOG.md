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
- Added `Descent.All` as a full-project import aggregator and wired CI/docs to build
  `Descent.All` explicitly for maintained-module coverage.
- Reorganized regression examples to use focused pseudofunctor Čech descent imports.
- Expanded bridge/singleton regression checks with additional convention and criteria sanity checks.
- Split `Descent/Pseudofunctor/Descent/CechDescentDataEquiv.lean` into focused modules under
  `Descent/Pseudofunctor/Descent/CechDescentData/` and retained `CechDescentDataEquiv.lean` as
  a compatibility aggregator.
- Added fibered-side criteria bridge theorems in
  `Descent/FiberedCategory/Descent/SingleMorphismComparison.lean`.
- Added `Descent/API.lean` as the canonical downstream API aggregator, and aligned public docs
  with the `Descent` (core), `Descent.API` (consumer API), `Descent.All` (maintenance coverage)
  import split.
