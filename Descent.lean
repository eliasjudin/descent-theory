/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin

# Descent Theory Library

Entry point for the descent theory development in this repository. It re-exports
the Čech kernel pair utilities, fibered-category descent data, and pseudofunctor
descent data (including prestacks and stacks).
-/

-- Basic / shared definitions
import Descent.Cech

-- Fibered category approach
import Descent.FiberedCategory.Reindexing
import Descent.FiberedCategory.Descent.SingleMorphism

-- Pseudofunctor approach
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Descent.Pseudofunctor.Reindexing
import Descent.Pseudofunctor.Descent.SingleMorphism
-- NOTE: The singleton-cover equivalence to Mathlib descent data is not imported by default
-- (it is heavier and more experimental); import it explicitly when needed.
