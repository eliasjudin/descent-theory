/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin

# Descent Theory Library

Entry point for the descent theory development in this repository. It re-exports
the Čech kernel pair utilities, fibered-category descent data, and pseudofunctor
descent data (including prestacks and stacks).

## TODO (Facets of Descent, II)

This project currently formalizes the Čech-style definitions from §3.1–§3.3 (kernel pair
conventions, descent data for a single morphism, and comparison with Mathlib’s singleton-cover
`Pseudofunctor.DescentData`).

The upstream-facing singleton-family interface (as a thin layer over Mathlib’s
`CategoryTheory.Pseudofunctor.DescentData`) is provided in
`Descent.CategoryTheory.Sites.Descent.SingleMorphism`.

Remaining work needed to match the paper more fully:
- [RESEARCH] §1–§2: internal categories `cat(C)` and the extension `A : cat(C)ᵒᵖ ⥤ CAT` (Theorem 2.5),
  plus invariance under internal-category equivalences (Lemma 3.4).
- [RESEARCH] §3.5: split epimorphisms ↔ absolutely effective descent morphisms.
- [RESEARCH] §4: basic equivalence diagrams (BEDs) and composition-cancellation (Theorem 4.5).
- [RESEARCH] §5: (regular) `A`-locally-split epimorphisms and Theorem 5.2 (incl. §5.3 applications).
-/

-- Basic / shared definitions
import Descent.Cech
import Descent.Cech.Eq

-- Fibered category approach
import Descent.FiberedCategory.Reindexing
import Descent.FiberedCategory.Descent.SingleMorphism

-- Pseudofunctor approach
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Descent.CategoryTheory.Sites.Descent.SingleMorphism
import Descent.Pseudofunctor.Reindexing
import Descent.Pseudofunctor.Descent.SingleMorphism
-- NOTE: The singleton-cover equivalence to Mathlib descent data is not imported by default
-- (it is heavier and more experimental); import it explicitly when needed.
