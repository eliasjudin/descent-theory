/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Examples.BridgeSanity
import Descent.Examples.Cech
import Descent.Examples.FiberedCategory
import Descent.Examples.FiberedPseudofunctorBridge
import Descent.Examples.Pseudofunctor
import Descent.Examples.SingletonEquiv

/-!
# Test Driver

This executable is used as the Lake `testDriver`.
Compiling this module compiles the repository's regression examples directly, without adding a
library-level umbrella outside the mathlib-style `Descent` import tree.
-/

def main : IO Unit := pure ()
