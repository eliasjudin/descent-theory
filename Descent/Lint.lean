/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent

/-!
# Lint

This module is intended to be built in CI to enforce mathlib-style linter expectations for the
`Descent` package.

`Descent.lean` is the public umbrella for the user-facing library, so importing `Descent` here is
enough to lint the exposed API surface.
-/

#lint in Descent
#lint in CategoryTheory.FiberedCategory
