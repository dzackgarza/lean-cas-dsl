module

import CasCatalogue.Semantic
import LeanCategories.Catalogue
meta import CasCatalogue.Semantic
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCatalogue

/- Reader failure classification over the upstream catalogue. No semantic rows, leaf
implementations or mathematical expected values are introduced by this engineering probe. -/
run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "the mathematical ring category is absent"
  let receiver ← mkConstWithFreshMVarLevels ``CasCatalogue.Algebra.NamedRings.ringIntegers
  let failure ← try
      discard <| Semantic.property "is_commutative" receiver category
      pure none
    catch error => pure (some error)
  let some failure := failure
    | throwError "a ring's unresolved multiplicative/additive property routes were accepted"
  unless CasCatalogue.Exception.isSemanticAmbiguity failure do
    throwError "a ring's unresolved property routes were not classified as ambiguous"

run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "the mathematical ring category is absent"
  let receiver ← mkConstWithFreshMVarLevels ``CasCatalogue.Algebra.NamedRings.ringIntegers
  let rejected ← try
      discard <| Semantic.method "this_operation_is_not_registered" receiver category
      pure false
    catch error =>
      if CasCatalogue.Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "an unknown method lost its invalid-call stratum"
  let rejected ← try
      discard <| Semantic.property "this_property_is_not_registered" receiver category
      pure false
    catch error =>
      if CasCatalogue.Exception.stratum? error == some .invalid then pure true else throw error
  unless rejected do throwError "an unknown property lost its invalid-call stratum"

run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id.raw == "cat.rings")
    | throwError "the mathematical ring category is absent"
  let receiver ← mkConstWithFreshMVarLevels ``CasCatalogue.Algebra.NamedRings.ringIntegers
  let ambiguous ← try
      discard <| Semantic.method "units" receiver category
      pure false
    catch error =>
      if CasCatalogue.Exception.isSemanticAmbiguity error then pure true else throw error
  unless ambiguous do throwError "unresolved method routes were not classified as ambiguous"
  let ambiguous ← try
      reportResolution "units" "cat.rings" #[]
      pure false
    catch error =>
      if CasCatalogue.Exception.isSemanticAmbiguity error then pure true else throw error
  unless ambiguous do throwError "resolution reporting collapsed an unresolved method choice"
