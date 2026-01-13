/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.CategoryTheory.Sites.Descent.Cech

/-!
# Čech kernel pair conventions (compatibility wrapper)

This module re-exports the Čech overlap API from `CategoryTheory.Cech`, which lives in the
Mathlib-shaped file `Descent/CategoryTheory/Sites/Descent/Cech.lean` so it can be upstreamed
with minimal path churn.

For the kernel-pair internal category `Eq(p)` (paper *Facets of Descent, II*, §3.1),
see `Descent.Cech.Eq`.
-/

open CategoryTheory

namespace Descent.Cech

export CategoryTheory.Cech
    (cechKernelPair p1 p2 diag diag_p1 diag_p2 p1_comp_p_eq_p2_comp_p
    cechTripleOverlap p12 p23 p12_p2_eq_p23_p1 p1_ p2_ p3_ p13 p13_p1 p13_p2)

end Descent.Cech
