/-
Copyright (c) 2024 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/

import Descent.CategoryTheory.FiberedCategory.Reindexing

/-!
# Reindexing on fibers of a fibered category

This file re-exports the upstream-candidate reindexing API from
`Descent.CategoryTheory.FiberedCategory.Reindexing` into the `Descent.FiberedCategory` namespace.
-/

open CategoryTheory
open CategoryTheory.Functor

namespace Descent.FiberedCategory

export CategoryTheory.FiberedCategory
  (reindex
    reindexObj
    fiberIso
    reindexObjIsoOfEq
    reindexObjIsoOfEq_hom_eqToHom
    reindexObjIsoOfEq_inv_eqToHom
    reindexObjIsoOfEq_hom_naturality
    reindexObjIsoOfEq_inv_naturality
    reindexCompIsoObj
    pullbackPullbackIso_hom_comp
    pullbackPullbackIso_inv_comp
    reindexCompIsoObj_hom_naturality
    reindexCompIsoObj_inv_naturality
    reindexIdIso
    reindexIdIsoNatIso
    reindexCompIso
    reindexIdIsoNatIso_hom_app
    reindexIdIsoNatIso_inv_app
    reindexCompIso_hom_app
    reindexCompIso_inv_app
    reindexCompIsoCompReindex
    reindexCompIsoObj_hom_comp_pullback
    reindexCompIsoObj_inv_comp_pullback
    reindexIdIso_hom_eq)

end Descent.FiberedCategory
