/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.CategoryTheory.Sites.Descent.Cech

/-!
# Čech kernel pair conventions

This module re-exports the Čech overlap API from `CategoryTheory.Cech` in the namespace
`Descent.Cech`.

For the Čech groupoid data `Eq(p)`, see `Descent.Cech.Eq`.
-/

open CategoryTheory

namespace Descent.Cech

export CategoryTheory.Cech
  (cechKernelPair
    p1 p2 diag diag_p1 diag_p2 p1_comp_p_eq_p2_comp_p
    cechTripleOverlap
    p12 p23 p12_p2_eq_p23_p1
    p1Triple p2Triple p3Triple
    p13 p13_p1 p13_p2)

end Descent.Cech
