/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent
import Descent.Cech.Eq
import Descent.CategoryTheory.FiberedCategory.PseudofunctorOfFibers
import Descent.CategoryTheory.InternalCategory.Basic
import Descent.CategoryTheory.Sites.Descent.SingleMorphism
import Descent.FiberedCategory.Descent.PseudofunctorEquiv
import Descent.Pseudofunctor.Descent.CechDescentDataEquiv
import Descent.Test

/-!
# Full project aggregator

`Descent.All` imports the full public library, examples/regression modules, and the
upstream-candidate category-theory modules that are not necessarily reached by the default
`Descent` target.

CI builds this module to ensure all maintained Lean files remain compilation-checked.
-/
