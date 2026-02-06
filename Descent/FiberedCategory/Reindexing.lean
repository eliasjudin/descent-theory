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
    fiber_iso
    reindex_obj_iso_of_eq
    reindex_obj_iso_of_eq_hom_eq_to_hom
    reindex_obj_iso_of_eq_inv_eq_to_hom
    reindex_obj_iso_of_eq_hom_naturality
    reindex_obj_iso_of_eq_inv_naturality
    reindex_comp_iso_obj
    pullback_pullback_iso_hom_comp
    pullback_pullback_iso_inv_comp
    reindex_comp_iso_obj_hom_naturality
    reindex_comp_iso_obj_inv_naturality
    reindex_id_iso
    reindex_id_iso_nat_iso
    reindex_comp_iso
    reindex_id_iso_nat_iso_hom_app
    reindex_id_iso_nat_iso_inv_app
    reindex_comp_iso_hom_app
    reindex_comp_iso_inv_app
    reindex_comp_iso_comp_reindex
    reindex_comp_iso_obj_hom_comp_pullback
    reindex_comp_iso_obj_inv_comp_pullback
    reindex_id_iso_hom_eq)

end Descent.FiberedCategory
