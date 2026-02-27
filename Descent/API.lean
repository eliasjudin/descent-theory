/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent
import Descent.Cech.Eq
import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor.Descent.CechDescentDataEquiv

/-!
# Canonical public API

`Descent.API` is the canonical consumer-facing import for this repository.

It includes:

- core Čech conventions and single-morphism descent APIs via `Descent`
- the Čech groupoid API (`Descent.Cech.Eq`)
- bridge equivalences between fibered and pseudofunctor viewpoints
- singleton-cover compatibility modules

Use this module for downstream projects that want the public API surface
without importing development-only aggregators such as `Descent.All`.
-/
