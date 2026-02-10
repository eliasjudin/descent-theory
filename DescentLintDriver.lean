/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.Lint

/-!
# Lint Driver

This executable is used as the Lake `lintDriver`.
Compiling this module compiles `Descent.Lint`, which runs `#lint` checks.
-/

def main : IO Unit := pure ()
