/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for complete parameter presentations after reduction has
removed the literal functor-application syntax. These fixtures inspect data flow,
full selected structures, and ownership; they supply no mathematical answers. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def dataNode (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

-- The original source is a literal child of the reduced whole object. An equal
-- cached action result is deliberately foreign and must never replace that child.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.commutative_rings.integers_mod")
    | throwError "the accepted source fixture is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let edge := EdgeRef.functor FunctorId.commutativeRingsRings
  let action ← Semantic.edgeFunctor state edge
  let image ← Semantic.objOf action source
  let action ← instantiateMVars action
  Trace.record (some trace) image
    (.retainedRoute row.category CategoryId.rings #[edge] #[action] source)
  let actual ← elabTermAndSynthesize
    (← `(RingCat.of (↑$(← exprToSyntax source)))) none
  unless actual != image && (← trace.node? actual).isNone &&
      (← withTransparency .all <| isDefEq actual image) do
    throwError "the reduced parameter fixture lost its distinct full-object presentation"
  let some recovered ← FunctorActionData.retainedParameterAction? trace actual
    | throwError "the complete retained parameter action was not recovered"
  unless recovered.receiver == source && recovered.route == #[edge] &&
      recovered.applications == #[action] do
    throwError "recovery changed the actual source occurrence or complete selected action"
  let callbackUsed ← IO.mkRef false
  let cyclic ← try
    discard <| FunctorActionData.encodeRetainedParameterAction? (Dependency := Unit) trace actual
      (fun _ => do callbackUsed.set true; return (Json.null, #[]))
      (fun _ _ => do callbackUsed.set true; return (Json.null, #[])) #[actual]
    pure false
  catch error => pure (Exception.stratum? error == some .noImplementation)
  unless cyclic && !(← callbackUsed.get) do
    throwError "a cyclic parameter recovery reached its source or action-data callback"
  let expectedPortable := dataNode "functorAction" #[
    dataNode FunctorId.commutativeRingsRings.raw #[],
    dataNode row.id.raw #[toJson (5 : Nat)]]
  unless (← parameterData trace actual) == expectedPortable do
    throwError "the reduced closed parameter lost its complete public presentation"
  let original : Wire := {
    form := .object row
    payload := .computed source (.owned "actual-parameter-source" 311
      (dataNode "opaqueData" #[toJson "the original parameter packet"])) }
  let foreign : Wire := { original with
    payload := .computed image (.owned "unrelated-equal-result" 312
      (dataNode "opaqueData" #[toJson "an unrelated equal cached result"])) }
  let harness ← Harness.empty
  harness.results.modify (fun cache => (cache.insert source original).insert image foreign)
  let (parameters, dependencies) ← realizedParameters harness trace #[actual]
  let #[parameter] := parameters | throwError "the recovered parameter lost its complete data"
  let .ok ("functorAction", #[descriptor, sourceData]) :=
      ComputationalData.envelope parameter
    | throwError "the reduced parameter erased its declared object action"
  unless descriptor == dataNode FunctorId.commutativeRingsRings.raw #[] &&
      sourceData == original.json && dependencies.any (fun wire =>
        wire.value == source && wire.json == original.json && wire.owner? == original.owner?) &&
      !dependencies.any (·.owner? == foreign.owner?) do
    throwError "the reduced parameter replaced its actual source packet or session owner"
  let combined := { original with payload := ← combinedPayload actual parameter dependencies }
  unless combined.owner? == original.owner? do
    throwError "the complete parameter action dropped its retained source owner"
  -- If this exact requested child already has actual data, it keeps priority.
  let requested := { original with
    payload := .computed actual (.owned "exact-requested-result" 313
      (dataNode "opaqueData" #[toJson "the exact requested parameter packet"])) }
  harness.results.modify (·.insert actual requested)
  let (exactData, exactDependencies) ← realizedParameters harness trace #[actual]
  let #[exactDependency] := exactDependencies
    | throwError "the exact requested parameter lost its actual dependency"
  unless exactData == #[requested.json] && exactDependency.owner? == requested.owner? do
    throwError "presentation recovery replaced an exact previously computed parameter"

-- Two literal source occurrences with distinct retained provenance remain
-- ambiguous. Repeated records of one exact source/action remain one alternative.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.commutative_rings.integers_mod")
    | throwError "the accepted ambiguity fixture is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let wrapped ← mkAppM ``id #[source]
  let edge := EdgeRef.functor FunctorId.commutativeRingsRings
  let action ← Semantic.edgeFunctor state edge
  let first ← Semantic.objOf action source
  let second ← Semantic.objOf action wrapped
  let action ← instantiateMVars action
  let originalNode := Node.retainedRoute row.category CategoryId.rings #[edge] #[action] source
  Trace.record (some trace) first originalNode
  Trace.record (some trace) (← mkAppM ``id #[first]) originalNode
  let actual ← elabTermAndSynthesize
    (← `(RingCat.of (↑$(← exprToSyntax wrapped)))) none
  let some unique ← FunctorActionData.retainedParameterAction? trace actual
    | throwError "duplicate records discarded the one actual source action"
  unless unique.receiver == source do
    throwError "duplicate records changed the original selected source"
  Trace.record (some trace) second
    (.retainedRoute row.category CategoryId.rings #[edge] #[action] wrapped)
  let rejected ← try
    discard <| FunctorActionData.retainedParameterAction? trace actual
    pure false
  catch error => pure (Exception.stratum? error == some .ambiguousRealization)
  unless rejected do
    throwError "distinct retained source occurrences were chosen by trace or cache order"

-- Equal carriers cannot stand in for a full selected structure. The ordinary
-- multiplicative monoid and the additive monoid written multiplicatively have
-- the same carrier, but different full accepted structure dictionaries.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the accepted full-structure fixture is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[]
  let edge := EdgeRef.functor ⟨"fun.rings.multiplicative_monoid"⟩
  let action ← Semantic.edgeFunctor state edge
  let image ← Semantic.objOf action source
  let action ← instantiateMVars action
  let some targetCategory := state.categories.find?
      (fun row => row.id.raw == "cat.monoids")
    | throwError "the accepted target category is absent"
  Trace.record (some trace) image
    (.retainedRoute row.category targetCategory.id #[edge] #[action] source)
  let different ← elabTermAndSynthesize
    (← `(MonCat.of (Multiplicative (↑$(← exprToSyntax source))))) none
  let imageCarrier ← elabTermAndSynthesize
    (← `((↑$(← exprToSyntax image) : Type))) none
  let differentCarrier ← elabTermAndSynthesize
    (← `((↑$(← exprToSyntax different) : Type))) none
  unless (← withTransparency .all <| isDefEq imageCarrier differentCarrier) &&
      !(← withTransparency .all <| isDefEq image different) do
    throwError "the wrong-structure fixture does not distinguish full dictionaries"
  unless (← FunctorActionData.retainedParameterAction? trace different).isNone do
    throwError "parameter recovery selected mathematics from its carrier alone"

end
