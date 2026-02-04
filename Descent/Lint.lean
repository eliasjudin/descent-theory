/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent
import Descent.Cech.Eq
import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor.Descent.CechDescentDataEquiv
import Mathlib.Tactic.Linter

/-!
# Lint

This module is intended to be built in CI to enforce Mathlib-style linter expectations for
the `Descent` package.

We keep `Descent.lean` as a minimal entry point. In contrast, this lint module explicitly
imports heavier/bridge modules (e.g. `Eq(p)` and the singleton-cover equivalence) so that the
linters see the whole library.
-/

#lint in Descent
#lint in CategoryTheory.FiberedCategory
