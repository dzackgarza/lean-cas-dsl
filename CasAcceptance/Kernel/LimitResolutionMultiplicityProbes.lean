/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Semantic
meta import CasCatalogue.Semantic
import LeanCategories.Catalogue.Semantics.Limits.Lifts
meta import LeanCategories.Catalogue.Semantics.Limits.Lifts

open Lean Meta Elab Term CasCatalogue

/-! Immutable copies of accepted rows exercise multiplicity independently of
storage order. No new mathematical declaration or global registration is made. -/

private def ambiguousCandidates (result : Except LimitResolutionError LimitResolution) :
    TermElabM (Array LimitResolution) := do
  match result with
  | .error (.ambiguous _ _ _ candidates) => return candidates
  | _ => throwError "several accepted construction choices were not reported as ambiguity"

run_elab do
  let state ← registryState
  let some original := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "the accepted lower presentation is absent"
  let some lift := state.lifts.find? (·.id == LiftId.finiteSetsPullbacks)
    | throwError "the accepted creation lift is absent"
  let some edge := state.structuralEdge? lift.edge
    | throwError "the accepted creation edge is absent"
  let some source := state.category? edge.source
    | throwError "the accepted source category is absent"
  let .ok unique := state.resolveLimitDetailed source.id original.shape
    | throwError "the original accepted creation route is not unique"
  unless unique == { limit := original.id, lift := some lift.id } do
    throwError "the original creation route changed its full selected construction"
  let aliasRow : LimitEntry := { original with id := ⟨"engineering.limit.accepted_alias"⟩ }
  validateLimit state.toSemanticState aliasRow
  let expanded : RegistryState := { state with limits := state.limits.push aliasRow }
  let expected := #[{ limit := original.id, lift := some lift.id : LimitResolution },
    { limit := aliasRow.id, lift := some lift.id }]
  for ordered in #[expanded, { expanded with limits := expanded.limits.reverse }] do
    let candidates ← ambiguousCandidates (ordered.resolveLimitDetailed source.id original.shape)
    unless candidates.size == expected.size && expected.all candidates.contains do
      throwError "creation resolution dropped an accepted target presentation"
    let direct ← ambiguousCandidates (ordered.resolveLimitDetailed original.category original.shape)
    unless direct.size == 2 && direct.all (·.lift.isNone) &&
        direct.any (·.limit == original.id) && direct.any (·.limit == aliasRow.id) do
      throwError "direct presentation ambiguity changed its complete choices"
  let liftAlias : LiftEntry := { lift with id := ⟨"engineering.lift.accepted_alias"⟩ }
  validateLift expanded.toSemanticState liftAlias
  let doubled : RegistryState := { expanded with lifts := expanded.lifts.push liftAlias }
  let expected := expected ++ #[{ limit := original.id, lift := some liftAlias.id },
    { limit := aliasRow.id, lift := some liftAlias.id }]
  let reversed : RegistryState := {
    doubled with
    limits := doubled.limits.reverse
    lifts := doubled.lifts.reverse }
  for ordered in #[doubled, reversed] do
    let candidates ← ambiguousCandidates (ordered.resolveLimitDetailed source.id original.shape)
    unless candidates.size == expected.size && expected.all candidates.contains do
      throwError "creation resolution did not retain every lift/presentation pair"
    let failure := LimitResolutionError.ambiguous source.id original.shape false candidates
    let refused ← try
      Semantic.limitResolutionFailure (α := Unit) failure
      pure false
    catch error => pure (Exception.isSemanticAmbiguity error)
    unless refused do throwError "construction ambiguity was collapsed into invalid input"
  let absent : RegistryState := { state with limits := #[] }
  let .error (.missing ..) := absent.resolveLimitDetailed source.id original.shape
    | throwError "a missing construction acquired a presentation"
  let refused ← try
    Semantic.limitResolutionFailure (α := Unit) (.missing source.id original.shape false)
    pure false
  catch error => pure (Exception.interpretationKind error == .invalid)
  unless refused do throwError "missing mathematical construction has the wrong failure stratum"
