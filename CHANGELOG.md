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
