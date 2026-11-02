/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for dependent map formation. The mathematical domains,
inclusions and evidence procedures are the independent published registrations.
The checks concern complete types, retained original maps and data ownership. -/

open Lean Meta Elab Command Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_cmd liftTermElabM <| withoutErrToSorry do
  for (termSyntax, projection) in #[
      ((← `(ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)), false),
      ((← `((ℚ × ℚ) →ₗ[ℚ] ℚ)), true)] do
    let expected ← elabTermAndSynthesize termSyntax none
    let some plan ← DeclaredAdmission.resolve? CategoryId.sets expected projection
      | throwError "the complete demanded type has no registered admission"
    unless plan.entry.admission.isSome && plan.entry.evidence.isSome &&
        !plan.application.value.hasMVar && !plan.application.value.hasLevelMVar &&
        plan.projections.isEmpty == !projection do
      throwError "the admission planner lost its exact full type or declared data projection"
  let pair ← elabTermAndSynthesize (← `(((1 : ℤ), (2 : ℤ)))) none
  let scalar ← elabTermAndSynthesize (← `(ℤ)) none
  if (← DeclaredAdmission.projectedValue? pair scalar).isSome then
    throwError "a multi-field record supplied an unchosen data projection"

run_cmd liftTermElabM <| withoutErrToSorry do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "x ↦ x"
    | throwError "the ordinary typed parameter did not parse"
  for termSyntax in #[(← `(ℤ → ℤ)), (← `((ℤ : Type) ⟶ (ℤ : Type)))] do
    let expected ← elabTermAndSynthesize termSyntax none
    let trace ← Trace.new
    let value ← (selectedTypedParameter {} expected parsed).run { trace := some trace }
    unless ← withTransparency .all <| isDefEq (← inferType value) expected do
      throwError "the ordinary map parameter changed its demanded signature"
    if (← trace.get).toArray.any (fun (_, node) => match node with
        | .admittedPoint .. => true | _ => false) then
      throwError "an ordinary map parameter acquired an extra admission condition"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let mut scope : Language.Scope := {}
  for (name, text) in #[("R", "ℤ in Rings"), ("M", "RegularModule(R)")] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the selected map input did not parse"
    scope := scope.insert name.toName parsed
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term
    "(m ↦ m + m) in M → M"
    | throwError "the full selected map did not parse"
  let trace ← Trace.new
  let value ← (eval scope parsed).run { trace := some trace }
  let (hom, source, target, context, _, _) ← (morphismContext value).run {}
  let selected ← (eval scope (← `(cas_term| M))).run {}
  let selectedContext ← (objectContext selected).run {}
  unless context.expression.syntacticEq selectedContext.expression &&
      (← withTransparency .all <| isDefEq context.bundle selectedContext.bundle) do
    throwError "the lambda replaced its selected full category"
  CategoryContext.checkMorphism context hom source target
  let representation ← withTransparency .all <| whnf (← inferType hom)
  let wrapped ← mkExpectedTypeHint hom representation
  let retainedSource ← CategoryContext.morphismDomain context wrapped target (some source)
  unless ← withTransparency .all <| isDefEq retainedSource source do
    throwError "an admitted Hom wrapper changed its independently supplied complete domain"
  let carried ← (carrierMorphism value).run { trace := some trace }
  let (plain, _, _, _, _, _) ← (morphismContext carried).run {}
  let acceptedCarrier ← try
    discard <| CategoryContext.morphismDomain context plain target (some source)
    pure true
  catch error =>
    if Exception.interpretationKind error == .invalid then pure false else throw error
  if acceptedCarrier then
    throwError "a carrier function was mistaken for the original structured Hom"
  unless (← trace.get).toArray.any (fun (_, node) => match node with
      | .admittedPoint _ _ _ original _ _ _ => original != hom
      | _ => false) do
    throwError "the typed map lost its registered admission or original computational map"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let expected ← elabTermAndSynthesize (← `((ℚ × ℚ) →ₗ[ℚ] ℚ)) none
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "((a, b) ↦ a)"
    | throwError "the typed destructured parameter did not parse"
  let trace ← Trace.new
  let value ← (selectedTypedParameter {} expected parsed).run { trace := some trace }
  unless !value.hasMVar && !value.hasLevelMVar && (← isTypeCorrect value) &&
      (← withTransparency .all <| isDefEq (← inferType value) expected) do
    throwError "the destructured map parameter lost its complete declared type"
  let some (.elementValue point target _) ← trace.node? value
    | throwError "the declared wrapper projection dropped its original admitted point"
  let action ← functionOf point
  let original := mkApp action (← globalPoint.run {})
  unless ← withTransparency .all <| isDefEq (← inferType original) target do
    throwError "the projected parameter changed its original admitted point type"
  let some projected ← DeclaredAdmission.projectedValue? original expected
    | throwError "the parameter no longer has the public single-data-field extraction"
  unless ← withTransparency .all <| isDefEq projected value do
    throwError "the retained point supplies a different complete typed parameter"
  let opaquePacket := Json.mkObj [("ctor", "opaqueData"), ("args", Json.arr #["declared-map-data"])]
  let harness ← Harness.empty
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the point parameter has no declared data category"
  let source : Wire := {
    form := .canonicalMorphism sets
    payload := .computed point (.owned "retained-map-session" 19 opaquePacket) }
  harness.results.modify (·.insert point source)
  let actual ← realize harness trace "the projected actual callable parameter" value
  let .ok ("element", #[_, pointData]) := ComputationalData.envelope actual.json
    | throwError "the projected parameter lost its public element frame"
  let .ok ("point", #[actualSource]) := ComputationalData.envelope pointData
    | throwError "the projected parameter lost its retained point frame"
  unless actual.owner? == source.owner? && actualSource == opaquePacket do
    throwError "the typed wrapper projection lost its actual opaque data or owner"


/-! Admission parameter observation uses the same typed children as the selected
object. An enclosing admission must not suppress those producers, while a child
explicitly retained by its own capture remains inert. The existing map admission
and functor protocol provide the fixture; no mathematical answer is tested. -/

namespace CasCatalogue.AdmissionParameterObservationProbes
meta section

private def admissionNode (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def admissionUnavailable (action : TermElabM α) : TermElabM Bool := do
  try
    discard action
    return false
  catch error => return Exception.stratum? error == some .unavailable

/-- Change only the supplier of an existing actual packet for a rejection
control. No lifecycle record or completion flag is manufactured. -/
private def changedAdmissionSupplier (wire : Wire) : TermElabM Wire := do
  let change := fun (data : DataOwnership.Data) =>
    { data with ownership := data.ownership.map fun binding =>
      { binding with owner := (binding.owner.1, binding.owner.2 + 1) } }
  let payload : WirePayload ← match wire.payload with
    | .computed value (.opaque backend session token) =>
        pure (.computed value (.opaque backend (session + 1) token))
    | .computed value (.owned backend session data) =>
        pure (.computed value (.owned backend (session + 1) data))
    | .computed value (.scoped data) => pure (.computed value (.scoped (change data)))
    | .computed value (.recipe data) => pure (.computed value (.recipe (change data)))
    | _ => throwError "the admission supplier control has no actual owned parameter"
  let changed := { wire with payload }
  unless changed.json == wire.json && changed.value == wire.value &&
      changed.completedData == wire.completedData && changed.ownership != wire.ownership do
    throwError "the admission supplier control changed more than its actual supplier"
  return changed

run_elab do
  let state ← registryState
  let some action := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the admission observation control lost its existing object action"
  let some row := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the admission observation control lost its existing source"
  let some sourceCategory := state.categories.find? (·.id == row.category)
    | throwError "the admission observation control lost its source category"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the admission observation control lost its selected set category"
  let some maps := state.objects.find? (·.id.raw == "obj.sets.maps")
    | throwError "the admission observation control lost its registered map object"
  unless maps.admission.isSome && maps.evidence.isSome do
    throwError "the admission observation control has no published admission"
  let trace ← Trace.new
  let source ← Semantic.object row #[] (some trace)
  let sourceContext ← CategoryContext.ofNamed sourceCategory source
  let (image, _) ← Semantic.applyRegisteredFunctor action source #[] (some trace)
  let context ← CategoryContext.ofNamed sets image
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[image]
  Trace.record (some trace) identity (.contextualIdentity context image)
  let selected ← Semantic.object maps #[← quoteExpr image, ← quoteExpr image] (some trace)
  let imageValue : Language.Value := .object image sets none none none
  let selectedValue : Language.Value :=
    .object selected sets (some (maps, #[imageValue, imageValue])) none none
  let originalValue : Language.Value := .morphism identity image image sets none
  let admitted ← (Language.admit selectedValue originalValue).run { trace := some trace }
  let .element point _ := admitted
    | throwError "the existing map admission did not return its original point"
  unless (Trace.producerAnchor? point).isSome do
    throwError "the interpreted admission did not retain its original selected producer"
  let some (.admittedPoint owner category parameters original originalCategory
      originalSource originalTarget) ← trace.node? point
    | throwError "the existing map admission lost its retained original producer"
  unless owner == maps.id && category == sets.id && originalCategory == sets.id &&
      parameters.size == 2 && original == identity &&
      (← withoutModifyingState (withTransparency .all <|
        isDefEq originalSource image <&&> isDefEq originalTarget image)) do
    throwError "the map admission changed its original telescope, category or callable"
  -- Two public admissions of the same complete input are distinct producers,
  -- even though Lean identifies their full mathematical values and types.
  let secondAdmission ← (Language.admit selectedValue originalValue).run { trace := some trace }
  let .element secondPoint _ := secondAdmission
    | throwError "the second public admission did not return its original point"
  let some firstAnchor := Trace.producerAnchor? point
    | throwError "the first admission lost its selected producer address"
  let some secondAnchor := Trace.producerAnchor? secondPoint
    | throwError "the second admission lost its selected producer address"
  let some firstNode ← trace.node? point
    | throwError "the first admission lost its complete producer record"
  let some secondNode ← trace.node? secondPoint
    | throwError "the second admission lost its complete producer record"
  Trace.checkProducerRecord point firstNode
  Trace.checkProducerRecord secondPoint secondNode
  unless point != secondPoint && firstAnchor.occurrence != secondAnchor.occurrence &&
      firstNode == secondNode &&
      (← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType point) (← inferType secondPoint) <&&>
          isDefEq point secondPoint)) do
    throwError "fresh public admissions merged producers or changed their original complete input"
  let supplied := admissionNode row.id.raw #[]
  let originalSourceWire : Wire := {
    form := .object row
    payload := .computed source (.inline supplied)
    categoryContext := some sourceContext }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "admission-parameter-probe", command := "python3",
      args := #["probe_functor_execution.py", "action", action.id.raw, "--opaque-objects"] }]
    registrations := #[{
      operation := action.id.raw, input := action.inputAddress,
      backend := "admission-parameter-probe" }] }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with dispatches := some calls }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 && !harness.demandObjectActions do
    throwError "the admission control changed its one registered action or capture policy"
  try
    harness.results.modify (·.insert source originalSourceWire)
    let pending ← realizeUnobserved harness trace "the original registered admission" point
    let some assembly ← currentIntrinsicAssembly? pending
      | throwError "the original admission lost its typed parameter assembly"
    let oldParameter ← checkedFragment
      (pending.fragment.project #[.field "args", .index 1, .index 0])
    unless !pending.completedData && (← calls.get).isEmpty do
      throwError "capturing the admission executed an original parameter producer"
    -- Capture the second selected admission before the equal-formal cache
    -- replacement, retaining the very same original parameter action input.
    let secondPending ← realizeUnobserved harness trace
      "the second original registered admission" secondPoint
    unless !secondPending.completedData && secondPending.fragment == pending.fragment &&
        (← calls.get).isEmpty do
      throwError "capturing a distinct admission changed its original data or executed a child"

    -- Preserve both original typed children. The wrapper case retains both
    -- slots and forbids any active callback, so equal-child memoization cannot
    -- hide an illegal traversal. The role case leaves the second child active.
    -- Neither the array nor the admission chooses a different child role.
    for retainedWrapper in #[true, false] do
      let expectedChild ← IO.mkRef (none : Option (ActionDataRole × Wire))
      let reader := fun (h : Harness) (t : Trace) (actualParameters : Array Expr) => do
        unless actualParameters == parameters do
          throwError "the admission capture callback changed the original parameter telescope"
        let captured ← capturedParameterData h t actualParameters
        let #[first@(.wire _ child), second@(.wire role secondChild)] := captured
          | throwError "the admission control lost its two original typed parameter slots"
        unless role == .parameter || role == .object do
          throwError "the original admission parameter lost its active producer role"
        expectedChild.set (some (role, secondChild))
        let first := if retainedWrapper then ActionDataTemplate.retained first
          else ActionDataTemplate.wire .retained child
        let second := if retainedWrapper then ActionDataTemplate.wire .retained secondChild
          else second
        return #[first, second]
      let retained ← realizeFreshWithParameters reader harness trace
        "the admission with one explicitly retained child" point
      unless retained.fragment == pending.fragment do
        throwError "retaining one admission child changed the original public data or suppliers"
      let visited ← IO.mkRef (#[] : Array (ActionDataRole × Wire))
      let actual ← observeCurrentIntrinsicAssemblyWith
        (fun role child => do
          visited.modify (·.push (role, child))
          if role == .retained then
            observeActionDataWire { harness with demandObjectActions := true } trace role child
          else pure child)
        (fun child selectedContext => capturedMapEndpoints harness trace child selectedContext)
        harness retained
      let some (role, child) ← expectedChild.get
        | throwError "the admission control did not invoke its original parameter reader"
      let demanded := (← visited.get).filter fun (actualRole, actualChild) =>
        actualRole == role && sameCompleteWireContext actualChild child
      unless demanded.size == (if retainedWrapper then 0 else 1) &&
          actual.fragment == retained.fragment &&
          (← calls.get).isEmpty do
        throwError "admission traversal suppressed an active child or demanded a retained child"

    -- Equal-formal cache replacement cannot supply the captured action input.
    harness.results.modify (·.insert source { originalSourceWire with
      payload := .computed source
        (.inline (admissionNode "obj.linear_orders.integers" #[])) })
    let observed ← realizeArrowObservation harness trace pending
    let #[event] := (← calls.get)
      | throwError "the admission did not observe its one retained parameter action exactly once"
    let .ok request := event.getObjVal? "request"
      | throwError "the admission action lost its actual request"
    unless (request.getObjVal? "receiver").toOption == some supplied do
      throwError "the admission replaced its captured parameter input from an equal-formal cache entry"
    let #[receipt] := (← harness.actions.get)
      | throwError "the admission lost its actual parameter action receipt"
    unless receipt.operation == action.id.raw &&
        sameActionOperand receipt.input originalSourceWire && !receipt.result.ownership.isEmpty &&
        receipt.result.fragment != oldParameter do
      throwError "the admission control did not produce distinct actual owned parameter data"
    let expectedTarget ← scopedNode maps.id.raw #[receipt.result.fragment, receipt.result.fragment]
    for index in [:2] do
      let parameter ← checkedFragment
        (observed.fragment.project #[.field "args", .index 1, .index index])
      let targetParameter ← checkedFragment
        (observed.fragment.project #[.field "args", .index 4, .field "args", .index index])
      unless parameter == receipt.result.fragment && targetParameter == parameter do
        throwError "an admitted parameter retained a stale recipe or lost its selected target supplier"
    let selectedTarget ← checkedFragment
      (observed.fragment.project #[.field "args", .index 4])
    unless selectedTarget == expectedTarget && observed.value == point &&
        (← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType observed.value) (← inferType pending.value))) do
      throwError "observing admission parameters changed the complete selected object or point type"
    let some pointContext := observed.categoryContext
      | throwError "the observed admission lost its complete point category"
    let some (actualDomain, actualTarget) ← retainedCallableEndpoints? observed pointContext
      | throwError "the observed admission lost its current endpoint receipt"
    let publicDomain ← checkedFragment
      (observed.fragment.project #[.field "args", .index 2])
    unless actualDomain.fragment == publicDomain && actualTarget.fragment == selectedTarget do
      throwError "the refreshed admission data differ from their complete endpoint occurrences"

    -- A second supplied assembly cannot replace a declaration slot, dictionary,
    -- or supplier merely because the outer formal point and public JSON agree.
    let some actualAssembly ← currentIntrinsicAssembly? observed
      | throwError "the observed admission lost its current producer selection"
    let .ctor "admittedPoint" #[id, .array actualParameters, domain, input, target, datum] :=
        actualAssembly.template
      | throwError "the observed admission lost its ordered published fields"
    let #[.wire role first, second] := actualParameters
      | throwError "the observed admission lost its original typed parameter positions"
    let wrongContext := { first with categoryContext := some sourceContext }
    let wrongSupplier ← changedAdmissionSupplier first
    let beforeInvocations ← harness.invocations.get
    let visits ← IO.mkRef (0 : Nat)
    for changedParameters in #[
        #[.wire role wrongContext, second],
        #[.wire role wrongSupplier, second],
        #[second], actualParameters.push second] do
      let changed := { actualAssembly with
        template := .ctor "admittedPoint" #[id, .array changedParameters, domain, input, target, datum] }
      unless ← admissionUnavailable (observeIntrinsicAssemblyWith
          (fun _ child => do
            visits.modify (· + 1)
            pure child)
          (fun child selectedContext => capturedMapEndpoints harness trace child selectedContext)
          harness observed changed) do
        throwError "an admission observation accepted changed ordered parameters, context or suppliers"
    unless (← visits.get) == 0 && (← calls.get).size == 1 &&
        (← harness.invocations.get).size == beforeInvocations.size do
      throwError "an invalid admission selection reached a child or allocated an invocation"
    let reused ← realizeArrowObservation harness trace pending
    unless sameCompleteWireContext observed reused &&
        observed.serviceHandles == reused.serviceHandles && (← calls.get).size == 1 do
      let details := Json.mkObj [
        ("sameCompleteWireContext", toJson (sameCompleteWireContext observed reused)),
        ("sameServiceHandles", toJson (observed.serviceHandles == reused.serviceHandles)),
        ("dispatchCount", toJson (← calls.get).size),
        ("invocationCountBefore", toJson beforeInvocations.size),
        ("invocationCountAfter", toJson (← harness.invocations.get).size),
        ("originalPending", operationEndpointDiagnosticSummary pending),
        ("resultComparison", operationEndpointDiagnosticComparison observed reused),
        ("originalResultHandles", toJson observed.serviceHandles),
        ("reusedResultHandles", toJson reused.serviceHandles)]
      throwError "reusing the same admission replaced its actual complete result or repeated an action; {details.compress}"

    -- Fresh admission producers own separate preparations and outer operand
    -- references. Their identical original parameter action is still one actual
    -- selected computation, with the same complete input and supplied result.
    let secondObserved ← realizeArrowObservation harness trace secondPending
    unless secondObserved.fragment == observed.fragment &&
        secondObserved.serviceHandles != observed.serviceHandles && (← calls.get).size == 1 do
      throwError "distinct admission producers merged preparations or repeated their shared action"
    let records ← harness.invocations.get
    let #[firstOwner] := records.filter (·.input.value == point)
      | throwError "the first admission has no unique canonical preparation"
    let #[secondOwner] := records.filter (·.input.value == secondPoint)
      | throwError "the second admission has no unique canonical preparation"
    let some firstResult := firstOwner.result
      | throwError "the first admission lost its actual canonical result"
    let some secondResult := secondOwner.result
      | throwError "the second admission lost its actual canonical result"
    unless !(firstOwner.prepared.same secondOwner.prepared) &&
        firstOwner.captured.occurrence != secondOwner.captured.occurrence &&
        sameIntrinsicObservationInput firstOwner.input pending &&
        sameIntrinsicObservationInput secondOwner.input secondPending &&
        sameCompleteWireContext firstResult observed &&
        firstResult.serviceHandles == observed.serviceHandles &&
        sameCompleteWireContext secondResult secondObserved &&
        secondResult.serviceHandles == secondObserved.serviceHandles do
      throwError "an admission owner replaced its exact pending input, preparation or result"
    let firstAgain ← realizeArrowObservation harness trace pending
    let secondAgain ← realizeArrowObservation harness trace secondPending
    let #[sharedAction] := (← harness.actions.get)
      | throwError "distinct admissions lost their one original parameter action"
    unless sameCompleteWireContext firstAgain observed &&
        firstAgain.serviceHandles == observed.serviceHandles &&
        sameCompleteWireContext secondAgain secondObserved &&
        secondAgain.serviceHandles == secondObserved.serviceHandles &&
        sameActionOperand sharedAction.input originalSourceWire &&
        sameCompleteWireContext sharedAction.result receipt.result &&
        (← harness.invocations.get).size == records.size && (← calls.get).size == 1 do
      throwError "reusing distinct admissions changed an owner or replayed their original action"

    -- Actual owned parameter data remain tied to the live supplying session.
    let connections ← harness.connections.get
    harness.connections.set {}
    try
      unless ← admissionUnavailable (realizeArrowObservation harness trace pending) do
        throwError "an admission reused actual parameter data after its supplier became unavailable"
      unless ← admissionUnavailable (realizeArrowObservation harness trace secondPending) do
        throwError "a distinct admission reused data after its shared supplier became unavailable"
      unless (← calls.get).size == 1 do
        throwError "unavailable admission parameter data dispatched before owner rejection"
    finally harness.connections.set connections
    logInfo "PASS: admission parameters refresh through original typed slots and retain inert roles, complete contexts and suppliers"
  finally harness.stop

end
end CasCatalogue.AdmissionParameterObservationProbes
