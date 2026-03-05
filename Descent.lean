/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Cech
import Descent.Cech.Eq
import Descent.FiberedCategory
import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor
import Descent.Pseudofunctor.Descent.CechDescentDataEquiv

/-!
# Descent theory

This is the main entry point for the `Descent` library.

The library develops Čech-style descent along a single morphism `p : E ⟶ B`, both for fibered
categories (`pA : 𝒜 ⥤ C` with `pA.IsFibered`) and for pseudofunctors
(`F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`).

Import `Descent` for the full user-facing library.

For lighter imports, use the topic entry points:

- `Descent.Cech` for the Čech overlap conventions
- `Descent.Cech.Eq` for the Čech groupoid `Eq(p)`
- `Descent.FiberedCategory` for fibered-category descent
- `Descent.Pseudofunctor` for pseudofunctor descent

This root module also includes the comparison/equivalence layers:

- `Descent.FiberedCategory.Descent.PseudofunctorEquiv`
- `Descent.Pseudofunctor.Descent.CechDescentDataEquiv`
-/
