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
  let (parameters, dependencies) ← realizedParameterData harness trace #[actual]
  let #[parameter] := parameters | throwError "the recovered parameter lost its complete data"
  let .ok ("functorAction", #[descriptor, sourceData]) :=
      ComputationalData.envelope parameter.json
    | throwError "the reduced parameter erased its declared object action"
  -- Capture retains the complete action as its dependency. Its source packet
  -- and supplying owner must still be the original selected occurrence's.
  let #[dependency] := dependencies
    | throwError "the recovered parameter lost its complete action dependency"
  unless descriptor == dataNode FunctorId.commutativeRingsRings.raw #[] &&
      sourceData == original.json && dependency.value == actual &&
      dependency.fragment == parameter && dependency.owner? == original.owner? &&
      !dependencies.any (·.owner? == foreign.owner?) do
    throwError "the reduced parameter replaced its actual source packet or session owner"
  let combined := { original with payload := ← combinedPayload actual parameter dependencies }
  unless combined.owner? == original.owner? do
    throwError "the complete parameter action dropped its retained source owner"
  -- Direct realization must use the same retained source/action boundary. The
  -- parameter encoder above does not exercise realizeFresh's missing-node path.
  let directCycle ← try
    discard <| realize { harness with parameterRecovery := #[actual] } trace
      "the cyclic reduced selected object" actual
    pure false
  catch error => pure (Exception.stratum? error == some .noImplementation)
  unless directCycle && ((← harness.results.get)[actual]?).isNone do
    throwError "cyclic direct recovery computed or cached a selected object"
  let direct ← realize harness trace "the reduced selected object" actual
  unless direct.value == actual && direct.json == parameter.json &&
      direct.owner? == original.owner? && direct.owner? != foreign.owner? do
    throwError "direct recovery changed the complete object, source packet or owner"
  let some directContext := direct.categoryContext
    | throwError "direct recovery lost the complete target category context"
  let (_, targetBundle) ← functorCategoryBundles (← Semantic.asFunctor action)
  unless ← withTransparency .all <| isDefEq directContext.bundle targetBundle do
    throwError "direct recovery changed the complete target category dictionary"
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
  let exactDirect ← realize harness trace "the exact cached selected object" actual
  unless exactDirect.json == requested.json && exactDirect.owner? == requested.owner? do
    throwError "direct recovery replaced the exact previously computed object"

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
  -- The literal full action already selects its exact source occurrence. The
  -- inner source must not compete merely because its image has the same value.
  let explicit ← mkAppM ``CategoryTheory.Functor.obj #[action, wrapped]
  for selected in #[explicit, second] do
    let some recovered ← FunctorActionData.retainedParameterAction? trace selected
      | throwError "a literal object action lost its selected retained source"
    unless recovered.receiver == wrapped && recovered.route == #[edge] &&
        recovered.applications == #[action] do
      throwError "a literal object action selected an equal nested source instead"
  unless (← parameterData trace explicit) == (← parameterData trace second) do
    throwError "the public functor projections changed the selected parameter data"
  let rejected ← try
    discard <| FunctorActionData.retainedParameterAction? trace actual
    pure false
  catch error => pure (Exception.stratum? error == some .ambiguousRealization)
  unless rejected do
    throwError "distinct retained source occurrences were chosen by trace or cache order"
  let harness ← Harness.empty
  let directRejected ← try
    discard <| realize harness trace "the ambiguous reduced selected object" actual
    pure false
  catch error => pure (Exception.stratum? error == some .ambiguousRealization)
  unless directRejected do
    throwError "direct recovery selected one of several retained source actions"
  -- This ambiguity must not choose the presentation of an anonymous endpoint
  -- whose complete object and context are already fixed by its actual callable.
  let some category := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the callable endpoint fixture has no complete target category"
  let context ← CategoryContext.ofNamed category actual
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[actual]
  CategoryContext.checkMorphism context identity actual actual
  let callable : Wire := {
    form := .canonicalMorphism category
    payload := .computed identity (.owned "original-callable" 314
      (dataNode "opaqueData" #[toJson "the actual complete callable"]))
    categoryContext := some context }
  let endpoint ← realizeCallableEndpoint harness trace callable actual true (some context)
  let expected := Backend.MorphismEndpoint.encode { callable := callable.json, source := true }
  unless endpoint.value == actual && endpoint.json == expected &&
      endpoint.owner? == callable.owner? && ((← harness.results.get)[actual]?).isNone do
    throwError "optional endpoint framing selected an action or lost its actual callable owner"
  let some endpointContext := endpoint.categoryContext
    | throwError "optional endpoint framing lost its selected complete context"
  unless endpointContext.expression.syntacticEq context.expression &&
      (← withTransparency .all <| isDefEq endpointContext.bundle context.bundle) do
    throwError "optional endpoint framing changed its complete selected category"

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
  let sourceCarrier ← withTransparency .all <| mkAppM ``RingCat.carrier #[source]
  let sourceRing ← mkAppM ``RingCat.ring #[source]
  let different ← withTransparency .all <| elabTermAndSynthesize
    (← `(letI : Ring $(← exprToSyntax sourceCarrier) := $(← exprToSyntax sourceRing)
         MonCat.of (Multiplicative $(← exprToSyntax sourceCarrier)))) none
  let imageCarrier ← withTransparency .all <| mkAppM ``MonCat.carrier #[image]
  let differentCarrier ← withTransparency .all <| mkAppM ``MonCat.carrier #[different]
  unless (← withTransparency .all <| isDefEq imageCarrier differentCarrier) &&
      !(← withTransparency .all <| isDefEq image different) do
    throwError "the wrong-structure fixture does not distinguish full dictionaries"
  unless (← FunctorActionData.retainedParameterAction? trace different).isNone do
    throwError "parameter recovery selected mathematics from its carrier alone"
  let harness ← Harness.empty
  let directRejected ← try
    discard <| realize harness trace "the incompatible complete selected object" different
    pure false
  catch error => pure (Exception.stratum? error == some .noImplementation)
  unless directRejected do
    throwError "direct recovery substituted an equal-carrier structure dictionary"

-- Both public object projections retain nested and composed actions even without
-- an exact trace key. The actual source packet must survive every action.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.commutative_rings.integers_mod")
    | throwError "the complete nested-action source is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let firstEdge := EdgeRef.functor FunctorId.commutativeRingsRings
  let secondEdge := EdgeRef.functor ⟨"fun.rings.multiplicative_monoid"⟩
  let first ← Semantic.asFunctor (← Semantic.edgeFunctor state firstEdge)
  let middle ← Semantic.objOf first source
  let second ← Semantic.asFunctor (← Semantic.edgeFunctor state secondEdge)
  let nested ← Semantic.objOf second middle
  let first ← instantiateMVars first
  let second ← instantiateMVars second
  Trace.record (some trace) nested
    (.retainedRoute row.category ⟨"cat.monoids"⟩ #[firstEdge, secondEdge]
      #[first, second] source)
  let explicit ← mkAppM ``CategoryTheory.Functor.obj #[second, middle]
  let composed ← mkAppM ``CategoryTheory.Functor.obj
    #[← Semantic.compositeOfApplications #[first, second], source]
  unless (← trace.node? explicit).isNone && (← trace.node? composed).isNone do
    throwError "the nested-action control unexpectedly has an exact trace key"
  let original : Wire := {
    form := .object row
    payload := .computed source (.owned "nested-action-original" 315
      (dataNode "opaqueData" #[toJson "the original complete nested source"])) }
  let harness ← Harness.empty
  harness.results.modify (·.insert source original)
  let expected := dataNode "functorAction" #[
    dataNode "fun.rings.multiplicative_monoid" #[],
    dataNode "functorAction" #[dataNode FunctorId.commutativeRingsRings.raw #[], original.json]]
  for selected in #[explicit, composed] do
    let actual ← realize harness trace "the literal nested selected action" selected
    unless actual.value == selected && actual.json == expected &&
        actual.owner? == original.owner? do
      throwError "literal action recovery changed its source, whole action or original owner"

-- A literal parameter presentation remains selected even when an equal earlier
-- occurrence appears in an ignored beta argument. No cached equal parameter is substituted.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.rings.integers_mod")
    | throwError "the declared-action parameter source is absent"
  let some edge := state.functors.find? (·.id.raw == "fun.modules.fibre_inclusion")
    | throwError "the parameterized declared action is absent"
  let trace ← Trace.new
  let source ← objectAt trace row #[mkNatLit 5]
  let wrapped ← mkAppM ``id #[source]
  let declaration := Lean.mkConst edge.declaration
    ((← getConstInfo edge.declaration).levelParams.map fun _ => Level.zero)
  let first := mkApp declaration source
  let second := mkApp declaration wrapped
  let actionType ← inferType first
  let chooseSecond ← withLocalDeclD `ignored actionType fun ignored =>
    withLocalDeclD `selected actionType fun selected =>
      mkLambdaFVars #[ignored, selected] selected
  let beta := mkAppN chooseSecond #[first, second]
  let original : Wire := {
    form := .object row
    payload := .computed source (.owned "ignored-parameter" 316
      (dataNode "opaqueData" #[toJson "the ignored parameter packet"])) }
  let selected : Wire := { original with
    payload := .computed wrapped (.owned "selected-parameter" 317
      (dataNode "opaqueData" #[toJson "the selected parameter packet"])) }
  let harness ← Harness.empty
  harness.results.modify (fun cache => (cache.insert source original).insert wrapped selected)
  for action in #[second, beta] do
    let some accepted ← FunctorActionData.registeredAction? state action
      | throwError "the literal complete declared application was lost"
    unless accepted.edge == .functor edge.id && accepted.declarationApplication == second do
      throwError "declared action selection substituted a different parameter occurrence"
    let (data, dependencies) ← realizedEdgeDescriptor harness trace accepted.edge
      accepted.declarationApplication
    unless data == dataNode edge.id.raw #[selected.json] &&
        dependencies.any (·.owner? == selected.owner?) &&
        !dependencies.any (·.owner? == original.owner?) do
      throwError "the declaration descriptor changed the actual selected parameter owner"

end
