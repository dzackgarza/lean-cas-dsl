/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import CasAcceptance.Kernel.ProtocolFixtureData
meta import CasCatalogue.Realize
meta import CasAcceptance.Kernel.ProtocolFixtureData
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions

/-! Optional engineering checks against the independently published extension input.
This module is built with that mathematical input's isolated package override. Opaque
packets test framing and reuse; no packet establishes a mathematical value or law. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue CasCatalogue.Language

private def parse (text : String) : TermElabM Syntax := do
  let .ok result := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the public composite lift form did not parse: {text}"
  return result

private def envelope (name : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson name), ("args", Json.arr arguments)]

private def opaqueField (name : String) : Json := envelope "opaqueData" #[toJson name]

private def recordSelection (trace : Trace) (plan : SelectedLift.Plan) : TermElabM Expr := do
  let selected ← SelectedLift.retainSelection plan.ports[0]!
  Trace.recordProduced (some trace) selected
    (.selectedLift plan.entry.id plan.parameters plan.source plan.inclusion plan.monic)

private def originalPacket (plan : SelectedLift.Plan)
    (label : String) (source base : Json) :
    TermElabM Realize.LiftExecution := do
  let state ← registryState
  let .functor id ← SelectedLift.innerEdge state plan.entry
    | throwError "the accepted fixture no longer has its published inner action"
  let parameters := (List.range plan.parameters.size).toArray.map fun i =>
    opaqueField s!"{label}: complete parameter {i}"
  let action := envelope id.raw parameters
  let object := opaqueField s!"{label}: actual returned object"
  let image := envelope "functorAction" #[action, object]
  let .ok baseFields := LiftedSubobjectData.subobjectFields base
    | throwError "the fixture lost its full actual base packet"
  let typed (source target : Json) (name : String) :=
    envelope "typedMap" #[source, target, opaqueField s!"{label}: {name}"]
  let outputs := #[object, typed object source "actual defining map",
    typed image baseFields[0]! "actual forward", typed baseFields[0]! image "actual backward"]
  if let .error message ← LiftedSubobjectData.validateSelectionPrefix
      plan action source base outputs then
    throwError "the complete retained fixture is malformed: {message}"
  let execution : Realize.LiftExecution := {
    selections := #[plan], actions := #[action], parameters := #[parameters],
    sources := #[source], bases := #[base], outputs := #[outputs] }
  return execution

private def originalPacketData (execution : Realize.LiftExecution) : Json :=
  Json.arr #[Json.arr execution.actions, Json.arr (execution.parameters.map Json.arr),
    Json.arr execution.sources, Json.arr execution.bases,
    Json.arr (execution.outputs.map Json.arr)]

/-- Receive each parameter at its original ordered position. Equal formal
parameters do not identify independently supplied packets. -/
private def positionedParameters (form : Form) (parameters : Array Expr)
    (data : DataOwnership.Data) : TermElabM (Array Realize.ActionDataTemplate) := do
  let .arr fields := data.json
    | throwError "the retained fixture lost its ordered parameter packet"
  let mut computational := #[]
  for parameter in parameters do
    unless ← isProp (← inferType parameter) do
      computational := computational.push parameter
  unless computational.size == fields.size do
    throwError "the retained fixture changed its declared parameter positions"
  computational.mapIdxM fun index parameter => do
    let fragment ← Realize.checkedFragment (data.project #[.index index])
    let value : Realize.Wire := {
      form, payload := ← Realize.scopedPayload parameter fragment }
    let value ← Realize.retainCompletedResultInterface value (.value (← inferType parameter))
    return .wire .parameter value

/-- The exact arbitrary packets above are received first. Their original
positions then pass through the same typed stage fold and canonical completion
owner as a direct lift, without expression-keyed parameter reconstruction. -/
private def cachePacket (harness : Realize.Harness) (trace : Trace)
    (plan : SelectedLift.Plan) (formal : Expr) (execution : Realize.LiftExecution)
    (received : DataOwnership.Data) : TermElabM Unit := do
  Realize.checkDataOwners harness received
  unless received.json == originalPacketData execution do
    throwError "the retained fixture changed its complete original stage packet"
  let state ← registryState
  let some form := state.liftInputForm? plan.entry.inputAddress
    | throwError "the accepted fixture lost its published input form"
  let context ← SelectedLift.context plan
  let baseContext ← SelectedLift.context plan true
  let actionData ← Realize.checkedFragment (received.project #[.index 0, .index 0])
  let parameterData ← Realize.checkedFragment (received.project #[.index 1, .index 0])
  let sourceData ← Realize.checkedFragment (received.project #[.index 2, .index 0])
  let baseData ← Realize.checkedFragment (received.project #[.index 3, .index 0])
  let outputData ← Realize.checkedFragment (received.project #[.index 4, .index 0])
  let source ← Realize.liftOperand plan.source context form sourceData false true
  let baseSourceData ← Realize.checkedFragment (baseData.project #[.field "args", .index 0])
  let baseTargetData ← Realize.checkedFragment (baseData.project #[.field "args", .index 1])
  let inclusionData ← Realize.checkedFragment (baseData.project #[.field "args", .index 2])
  let inclusion ← if ← Realize.stagedLiftNode trace plan.inclusion then do
      let value ← Realize.realize { harness with demandObjectActions := true } trace
        "the original retained inner defining map" plan.inclusion
      unless value.fragment == inclusionData do
        throwError "the retained outer stage replaced its original inner defining map"
      pure value
    else do
      let (source, target) ← Realize.contextualMorphismEndpoints baseContext plan.inclusion
      let source ← Realize.liftOperand source baseContext form baseSourceData false true
      let target ← Realize.liftOperand target baseContext form baseTargetData false true
      let inclusion ← Realize.liftOperand plan.inclusion baseContext form inclusionData true true
      Realize.retainCallableEndpoints inclusion source target baseContext
  let originalContext := inclusion.categoryContext.getD baseContext
  let some (originalSource, originalTarget) ←
      Realize.retainedCallableEndpoints? inclusion originalContext
    | throwError "the retained original base lost its complete endpoint occurrences"
  -- The caller may name the same complete category bundle differently. Keep
  -- each original occurrence as a typed child of its explicitly checked view.
  let contextualObject := fun (original : Realize.Wire) => do
    let viewed ← Realize.captureDeclaredObjectInput original baseContext
    if Realize.sameCompleteWireContext viewed original then return original
    let viewed ← Realize.retainIntrinsicAssembly viewed .object baseContext
      (.retained (.wire .object original))
    let some selected ← Realize.retainedIntrinsicAssembly? viewed .object
      | throwError "the endpoint context view lost its original typed producer"
    let .retained (.wire .object child) := selected.template
      | throwError "the endpoint context view changed its original child role"
    unless Realize.sameCompleteWireContext child original &&
        Realize.sameRetainedServiceHandles child original && viewed.fragment == original.fragment do
      throwError "the endpoint context view replaced an original occurrence or supplier"
    pure viewed
  let baseSource ← contextualObject originalSource
  let baseTarget ← contextualObject originalTarget
  let inclusion ← if originalContext.expression.syntacticEq baseContext.expression &&
      Realize.sameCompleteWireContext baseSource originalSource &&
      Realize.sameCompleteWireContext baseTarget originalTarget then pure inclusion else do
    discard <| Realize.framingContext (some baseContext) inclusion.categoryContext
    let viewed := { inclusion with categoryContext := some baseContext }
    let viewed ← Realize.retainIntrinsicAssembly viewed .map baseContext
      (.retained (.wire .map inclusion))
      #[{ context := originalContext, source := originalSource,
          target := originalTarget, callable := inclusion }]
    let viewed ← Realize.retainCallableEndpoints viewed baseSource baseTarget baseContext
    let some selected ← Realize.retainedIntrinsicAssembly? viewed .map
      | throwError "the base context view lost its original whole-map producer"
    let .retained (.wire .map child) := selected.template
      | throwError "the base context view changed its original whole-map child"
    unless Realize.sameCompleteWireContext child inclusion &&
        Realize.sameRetainedServiceHandles child inclusion && viewed.fragment == inclusion.fragment do
      throwError "the base context view replaced its original whole map or supplier"
    pure viewed
  unless baseSource.fragment == baseSourceData && baseTarget.fragment == baseTargetData do
    throwError "the retained original base replaced an endpoint packet or supplier"
  let inner ← SelectedLift.innerEdge state plan.entry
  let .functor id := inner
    | throwError "the accepted fixture no longer has its published inner action"
  Realize.checkExecutableEdgeAction state inner (← Semantic.asFunctor plan.action)
  let descriptorParameters ← Realize.actionDeclarationParameters state inner plan.action true
  let descriptorFields ← Realize.checkedFragment (actionData.project #[.field "args"])
  let descriptor : Realize.ActionDataTemplate := .ctor id.raw
    (← positionedParameters form descriptorParameters descriptorFields)
  let parameters ← positionedParameters form plan.parameters parameterData
  let (action, _) ← Realize.renderCapturedActionData descriptor
  let parameterFields ← parameters.mapM Realize.renderCapturedActionData
  let parameterPacket := DataOwnership.Data.array (parameterFields.map (·.1))
  unless action == actionData && parameterPacket == parameterData do
    throwError "the retained fixture replaced a positioned action or evidence parameter"
  let operands ← IO.mkRef #[← Realize.invocationOperand .object source,
    ← Realize.invocationOperand .map inclusion]
  let capture := fun (role : Realize.ActionDataRole) (wire : Realize.Wire) => do
    let operand ← Realize.invocationOperand role wire
    operands.modify (·.push operand)
    pure wire
  discard <| Realize.mapActionTemplateWires capture descriptor
  for parameter in parameters do discard <| Realize.mapActionTemplateWires capture parameter
  let base ← Realize.scopedNode "subobject"
    #[baseSource.fragment, baseTarget.fragment, inclusion.fragment]
  unless base == baseData do
    throwError "the retained fixture changed its original complete base packet"
  let data ← LiftStageExecution.packet "monoLiftInput" plan.entry.id.raw
    parameterPacket action source.fragment base #[] (some baseTarget.fragment)
  let selected : Realize.SelectedDirectLiftInvocation := {
    formal, fragment := data, context, plan, operands := ← operands.get, descriptor, parameters }
  let pending : Realize.Wire := {
    form := Realize.contextualForm state context form,
    payload := ← Realize.recipePayload formal data, categoryContext := some context }
  let pending ← Realize.retainCapturedInvocation harness pending (.directLift selected)
  let some captured ← Realize.retainedCapturedInvocation? pending
    | throwError "the original retained lift lost its canonical preparation"
  let records := (← harness.invocations.get).zipIdx |>.filter fun (record, _) =>
    record.captured.occurrence == captured.occurrence
  let #[(record, position)] := records
    | throwError "the original retained lift lost its unique preparation owner"
  let prepared ← Realize.directLiftInputs harness selected (selected.operands.map (·.wire))
  let input := prepared.input
  let result ← LiftStageExecution.fold Realize.Wire.fragment input (fun _ => pure none)
    (fun field => do
      if field.index == 0 then
        let imageScope ← Realize.wireValidationScope .object baseTarget (mapView := .logical)
        let baseScope ← Realize.wireValidationScope .object input.base (mapView := .logical)
        if let .error message ← LiftedSubobjectData.validateSourceImageBase plan
            baseTarget.json input.base.json (some baseScope) (some imageScope) then
          throwError "the retained fixture changed its actual image ambient: {message}"
      let reply ← Realize.checkedFragment (outputData.project #[.index field.index])
      Realize.checkDataOwners harness reply
      let template := Realize.liftStageValidationTemplate input field.preceding
        "monoLiftInput" (some prepared.staticTemplates) field.comparisonImage?
      let requestScope ← Realize.templateValidationScope template (mapView := .logical)
      unless requestScope.data == field.request do
        throwError "the retained fixture changed its original positioned request or supplier"
      let replyScope : ComputationalData.InterfaceScope := { data := reply }
      let scope ← Realize.checkedFragment
        (LiftedSubobjectData.appendSelectionReplyScope requestScope replyScope)
      let comparison := LiftedSubobjectData.ComparisonImageRole.ofMetadata true
        (field.comparisonImage?.map (·.json))
      if let .error message ← LiftedSubobjectData.validateSelectionPrefixWith plan
          input.action.json input.source.json input.base.json
          ((field.preceding.map (·.json)).push reply.json) comparison (some scope) false then
        throwError "the retained original field failed its fixed prefix contract: {message}"
      let dependencies := prepared.dependencies ++ #[input.original, input.source, input.base,
        input.baseObject] ++ input.sourceImage?.toArray ++ input.sourceImageObject?.toArray ++
        field.preceding ++ field.comparisonImage?.toArray
      let handles ← Realize.retainServiceOperands harness dependencies
      let output ← Realize.liftOperand field.formal field.context form reply (field.index != 0) true
      let output := { output with
        serviceHandles := handles ++ dependencies.flatMap (·.serviceHandles) }
      match field.endpoints with
      | none => pure output
      | some (source, target) => do
        let sourceData ← Realize.checkedFragment (reply.project #[.field "args", .index 0])
        let targetData ← Realize.checkedFragment (reply.project #[.field "args", .index 1])
        let endpoint := fun (role : LiftStageExecution.EndpointRole Realize.Wire)
            (data : DataOwnership.Data) => do
          match role with
          | .retained original => Realize.liftEndpointOperand original field.context data
          | .produced formal => do
            let value ← Realize.liftOperand formal field.context form data false true
            return { value with serviceHandles := output.serviceHandles }
        let source ← endpoint source sourceData
        let target ← endpoint target targetData
        let output ← Realize.retainMapImageEndpoints output source target
        unless output.fragment == reply do
          throwError "the retained field changed an original complete output packet or supplier"
        pure output)
    Realize.liftStageEndpoints
  let value ← Realize.directLiftResult harness selected prepared result
  let some actual := value.liftExecution
    | throwError "the typed stage producer omitted its original complete execution"
  unless actual.actions == execution.actions && actual.parameters == execution.parameters &&
      actual.sources == execution.sources && actual.bases == execution.bases &&
      actual.outputs == execution.outputs do
    throwError "the typed stage producer changed an original retained execution packet"
  discard <| Realize.completeCapturedInvocation harness position record value

run_elab do
  let state ← registryState
  let some innerRow := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the accepted inner lift is absent"
  let some outerRow := state.lifts.find?
      (·.id.raw == "lift.bilin_module.change_value_restriction")
    | throwError "the independently published outer lift is absent"
  let innerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.source)) none
  let outerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.pairedSource)) none
  let inclusion ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion)) none
  let innerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstLift)) none
  let outerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.secondLift)) none
  let inner ← SelectedLift.fromEvidence innerRow innerEvidence innerSource inclusion
    (← synthInstance (← mkAppM ``CategoryTheory.Mono #[inclusion]))
  let trace ← Trace.new
  let innerKey ← recordSelection trace inner
  let innerHom ← Trace.recordProduced (some trace)
    (← StructuredProjection.retainPortValue innerKey inner.ports[1]! 1)
    (.liftProjection innerKey "hom")
  let outer ← SelectedLift.fromEvidence outerRow outerEvidence outerSource innerHom
    (← SelectedLift.homMonic inner)
  let outerKey ← recordSelection trace outer
  unless (← SelectedLift.recorded trace outerKey).plans.size == 1 &&
      (← SelectedLift.recorded trace outerKey true).plans.size == 2 do
    throwError "explicit composition changed the ordinary single-stage reading"
  let refused ← try
    SelectedLift.checkAdjacent outer { inner with source := outerSource }
    pure false
  catch error => pure (Exception.interpretationKind error == .invalid)
  unless refused do throwError "a composed selection accepted a different adjacent full context"
  let context ← SelectedLift.context outer
  let selected ← (objectInContext outerKey context).run { trace := some trace }
  let bound := [(`L, selected)]
  let composite ← (eval {} (← parse "composite_lift(L)")).run { trace := some trace, bound }
  let composedKey ← (semanticObject composite).run {}
  unless composedKey != outerKey && (← isDefEq composedKey outerKey) do
    throwError "the composed selection lost its separate administrative identity"
  let plans := (← SelectedLift.recorded trace composedKey).plans
  unless plans.size == 2 do throwError "the public composed selection lost a stage"
  let innerSourceData := opaqueField "actual intermediate source"
  let innerBase := envelope "subobject" #[opaqueField "original base apex",
    opaqueField "original base ambient", opaqueField "original base inclusion"]
  let innerExecution ← originalPacket inner "inner" innerSourceData innerBase
  let outerBase := envelope "subobject" #[(innerExecution.outputs[0]!)[0]!,
    innerSourceData, (innerExecution.outputs[0]!)[1]!]
  let outerExecution ← originalPacket outer "outer"
    (opaqueField "original complete source") outerBase
  let originalData := Json.arr #[originalPacketData innerExecution,
    originalPacketData outerExecution]
  CasAcceptance.Kernel.ProtocolFixtureData.withData "composite-probe"
      "composite-fixture-data" originalData fun harness received owner => do
    let harness := { harness with demandObjectActions := true }
    cachePacket harness trace inner innerKey innerExecution
      (← Realize.checkedFragment (received.project #[.index 0]))
    cachePacket harness trace outer outerKey outerExecution
      (← Realize.checkedFragment (received.project #[.index 1]))
    let completed ← Realize.realize harness trace "the complete composed selection" composedKey
    let some execution := completed.liftExecution
      | throwError "the composed value discarded its complete execution"
    unless completed.owner? == some owner &&
        execution.outputs == outerExecution.outputs ++ innerExecution.outputs &&
        execution.parameters == outerExecution.parameters ++ innerExecution.parameters &&
        execution.sources == outerExecution.sources ++ innerExecution.sources &&
        execution.bases == outerExecution.bases ++ innerExecution.bases &&
        execution.actions == outerExecution.actions ++ innerExecution.actions do
      throwError "composed selection replaced an actual retained input, output, action or owner"
    let (_, unchanged) ← Realize.retainedLiftExecution harness trace outerKey
    unless unchanged.selections.size == 1 && unchanged.outputs == outerExecution.outputs do
      throwError "composed reuse changed the ordinary outer selection"
    for (index, field) in #["obj", "hom", "forward", "backward"].zipIdx do
      let projected ← (eval {} (← parse s!"C.{index}()")).run
        { trace := some trace, bound := [(`C, composite)] }
      let value ← match projected with
        | .object value .. | .derivedObject value .. |
            .morphism value .. | .derivedMorphism value .. => pure value
        | _ => throwError "the composed projection lost its complete typed value"
      unless ← isDefEq value (← SelectedLift.port plans field) do
        throwError "a composed field changed its accepted full functor-map expression"
      let wire ← Realize.realize harness trace "a reused composed lift projection" value
      unless wire.owner? == completed.owner? &&
          wire.json == (← Realize.liftProjectionData execution field) do
        throwError "a composed field replayed or replaced its retained actual packet"
    let baseMap ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.baseMediator)) none
    let cone ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.pairedCone)) none
    let proof ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization)) none
    let factors ← SelectedLift.factors plans baseMap cone proof
    unless factors.size == 2 do throwError "the composed factor omitted a selected stage"
    let some (domain, _) := homEnds? (← inferType cone) | unreachable!
    let some final := factors.back? | unreachable!
    let some (actualDomain, target) := homEnds? (← inferType final.factor) | unreachable!
    unless ← isDefEq actualDomain domain <&&> isDefEq target composedKey do
      throwError "the composed factor changed the original complete cone domain or selected apex"
    for step in factors do
      unless ← Decide.kernelAccepts (← inferType step.proof) step.proof do
        throwError "a composed factor stage lost its accepted formal source equation"

-- Exercise the actual public port as well as retained-packet reuse. Arbitrary
-- opaque replies witness data flow only; the independent fixture fixes every
-- selected formal object, action, original domain and compatibility proof.
run_elab do
  let state ← registryState
  let some innerRow := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "the accepted inner lift is absent"
  let some outerRow := state.lifts.find?
      (·.id.raw == "lift.bilin_module.change_value_restriction")
    | throwError "the independently published outer lift is absent"
  let innerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.source)) none
  let outerSource ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.pairedSource)) none
  let inclusion ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion)) none
  let innerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.firstLift)) none
  let outerEvidence ← elabTermAndSynthesize
    (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.secondLift)) none
  let inner ← SelectedLift.fromEvidence innerRow innerEvidence innerSource inclusion
    (← synthInstance (← mkAppM ``CategoryTheory.Mono #[inclusion]))
  let trace ← Trace.new
  let innerKey ← recordSelection trace inner
  let innerHom ← Trace.recordProduced (some trace)
    (← StructuredProjection.retainPortValue innerKey inner.ports[1]! 1)
    (.liftProjection innerKey "hom")
  let outer ← SelectedLift.fromEvidence outerRow outerEvidence outerSource innerHom
    (← SelectedLift.homMonic inner)
  let outerKey ← recordSelection trace outer
  let context ← SelectedLift.context outer
  let selected ← (objectInContext outerKey context).run { trace := some trace }
  let composite ← (eval {} (← parse "composite_lift(L)")).run
    { trace := some trace, bound := [(`L, selected)] }
  let composedKey ← (semanticObject composite).run {}
  let rows := #[innerRow, outerRow]
  let operations := rows.flatMap fun row =>
    LiftField.all.map row.fieldAddress |>.push row.factorAddress
  let manifest : Manifest := {
    backends := #[{
      name := "lift-probe"
      command := "python3"
      args := #["probe_lift_protocol.py"] ++ operations }]
    registrations := rows.flatMap fun row =>
      (LiftField.all.map row.fieldAddress |>.push row.factorAddress).map fun operation =>
        { operation, input := row.inputAddress, backend := "lift-probe" } }
  let observations ← IO.mkRef #[]
  let harness ← Realize.Harness.ofManifest ("CasAcceptance" / "Strata") manifest
  let harness := { harness with dispatches := some observations, demandObjectActions := true }
  unless harness.rejected.isEmpty && harness.admitted.size == operations.size do
    throwError "a public selected lift address was not admitted: {reprStr harness.rejected}"
  try
    let .ok session ← harness.connection "lift-probe"
      | throwError "the protocol-only lift probe did not start"
    let owner := some ("lift-probe", session.identity)
    let some inputForm := state.liftInputForm? innerRow.inputAddress
      | throwError "the accepted input form is absent"
    let seed := fun formal label => do
      if (← harness.results.get).contains formal then return
      harness.results.modify (·.insert formal {
        form := inputForm
        payload := Realize.computedPayload formal (opaqueField label) owner })
    for plan in #[inner, outer] do
      seed plan.source s!"actual original source of {plan.entry.id.raw}"
      for (parameter, index) in plan.parameters.zipIdx do
        unless ← isProp (← inferType parameter) do
          seed parameter s!"actual selection parameter {index} of {plan.entry.id.raw}"
    let some (baseSource, baseTarget) := homEnds? (← inferType inclusion)
      | throwError "the fixed original inclusion lost its complete endpoints"
    seed inclusion "actual original inclusion"
    seed baseSource "actual original base apex"
    seed baseTarget "actual original base ambient"
    let innerWire ← Realize.realize harness trace "the first actual selection" innerKey
    let outerWire ← Realize.realize harness trace "the second actual selection" outerKey
    let some innerExecution := innerWire.liftExecution
      | throwError "the first actual selection lost its four returned fields"
    let some outerExecution := outerWire.liftExecution
      | throwError "the second actual selection lost its four returned fields"
    let calls ← observations.get
    unless calls.size == 8 do
      throwError "two selected lifts did not execute exactly their eight public field calls"
    for (execution, offset) in #[(innerExecution, 0), (outerExecution, 4)] do
      let some plan := execution.selections[0]? | unreachable!
      let original := if offset == 0 then inner else outer
      let expectedParameters ← original.parameters.filterMapM fun parameter => do
        if ← isProp (← inferType parameter) then return none
        let some actual := (← harness.results.get)[parameter]?
          | throwError "a supplied selected parameter lost its original actual data"
        return some actual.json
      unless execution.parameters[0]! == expectedParameters do
        throwError "a selected lift omitted or replaced an explicit evidence-family parameter"
      for (field, index) in LiftField.all.zipIdx do
        let call := calls[offset + index]!
        let .ok request := call.getObjVal? "request" | unreachable!
        let .ok response := call.getObjVal? "response" | unreachable!
        let .ok invocation := Backend.LiftInput.decode request (plan.entry.fieldAddress field)
          | throwError "a selected field lost its public complete request"
        unless call.getObjValAs? String "operation" ==
            .ok (plan.entry.fieldAddress field) &&
            invocation.outputs == execution.outputs[0]!.extract 0 index &&
            invocation.parameters == execution.parameters[0]! &&
            response == (execution.outputs[0]!)[index]! do
          throwError "a selected field replayed or replaced an actual preceding output or parameter"
    let .ok outerBase := LiftedSubobjectData.subobjectFields outerExecution.bases[0]!
      | throwError "the second actual lift lost its first stage base packet"
    unless outerBase[0]! == (innerExecution.outputs[0]!)[0]! &&
        outerBase[2]! == (innerExecution.outputs[0]!)[1]! do
      throwError "the second selected lift did not consume the first actual object and defining map"
    let composed ← Realize.realize harness trace "the actual composed selection" composedKey
    let some execution := composed.liftExecution
      | throwError "the actual composed selection lost a retained stage"
    unless composed.owner? == owner && execution.selections.size == 2 &&
        (← observations.get).size == 8 do
      throwError "composition reran a selected port or lost its actual owning session"
    let baseMap ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.baseMediator)) none
    let cone ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.pairedCone)) none
    let proof ← elabTermAndSynthesize
      (← `(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone_base_factorization))
      none
    let some (domain, _) := homEnds? (← inferType cone)
      | throwError "the independently selected cone lost its original generalized domain"
    seed baseMap "actual original base mediator"
    seed cone "actual original complete cone"
    seed domain "actual original generalized domain"
    let factors ← SelectedLift.factors execution.selections baseMap cone proof
    let some final := factors.back? | unreachable!
    let factor ← Trace.recordProduced (some trace) final.factor
      (.liftFactor composedKey baseMap cone proof)
    let answer ← Realize.realize harness trace "the actual composed universal factor" factor
    let calls ← observations.get
    unless calls.size == 10 do
      throwError "the composed factor did not execute exactly one declared factor per stage"
    let .ok firstRequest := calls[8]!.getObjVal? "request" | unreachable!
    let .ok secondRequest := calls[9]!.getObjVal? "request" | unreachable!
    let .ok first := Backend.LiftFactorInput.decode firstRequest innerRow.factorAddress
      | throwError "the first factor request lost its complete public frame"
    let .ok second := Backend.LiftFactorInput.decode secondRequest outerRow.factorAddress
      | throwError "the final factor request lost its complete public frame"
    let .ok firstReply := calls[8]!.getObjVal? "response" | unreachable!
    unless first.lift == innerRow.id.raw && second.lift == outerRow.id.raw &&
        first.outputs == innerExecution.outputs[0]! &&
        second.outputs == outerExecution.outputs[0]! &&
        first.parameters == innerExecution.parameters[0]! &&
        second.parameters == outerExecution.parameters[0]! &&
        second.baseMap.encode == firstReply do
      throwError "the staged factor replaced an actual previous reply, selection or parameter"
    let some actualDomain := (← harness.results.get)[domain]? | unreachable!
    let .ok finalData := Backend.TypedMap.decode answer.json
      | throwError "the final actual factor lost its complete endpoint frame"
    unless finalData.source == actualDomain.json &&
        finalData.target == (outerExecution.outputs[0]!)[0]! && answer.owner? == owner do
      throwError "the final factor changed its original complete domain, selected apex or owner"
    let again ← Realize.realize harness trace "the reused actual composed factor" factor
    unless again.json == answer.json && (← observations.get).size == 10 do
      throwError "reuse replaced the returned composite factor or executed it again"
    -- Inspect a fresh pending alias of the same already completed parent. The
    -- original ten requests above retain their ordering and every packet guard.
    let endpointContext ← SelectedLift.context inner
    let pending ← Realize.captureLiftField harness trace innerHom innerKey 1
    let (pendingSource, pendingTarget) ← Realize.capturedMapEndpoints harness trace pending endpointContext
    let some sourceCapture ← Realize.retainedCapturedInvocation? pendingSource
      | throwError "the unresolved endpoint lost its original pending callable continuation"
    let .callableEndpoint selectedEndpoint := sourceCapture.interface
      | throwError "the unresolved endpoint was not captured as its callable's exact projection"
    unless selectedEndpoint.source &&
        Realize.sameIntrinsicObservationInput selectedEndpoint.original pending do
      throwError "the endpoint continuation changed its original whole callable or direction"
    let preparedCount := (← harness.invocations.get).size
    let (sameSource, sameTarget) ← Realize.capturedMapEndpoints harness trace pending endpointContext
    unless Realize.sameIntrinsicObservationInput pendingSource sameSource &&
        Realize.sameIntrinsicObservationInput pendingTarget sameTarget &&
        (← harness.invocations.get).size == preparedCount && (← observations.get).size == 10 do
      throwError "reading a pending endpoint again changed its original occurrence or executed its producer"
    let actualSource ← Realize.realizeObjectObservation harness trace pendingSource
    let actualTarget ← Realize.realizeObjectObservation harness trace pendingTarget
    let originalStage ← Realize.retainedLiftStage harness innerExecution 0
    let some originalMap := originalStage.outputs[1]?
      | throwError "the original lift lost its returned defining map"
    let some (originalSource, originalTarget) ←
        Realize.retainedCallableEndpoints? originalMap endpointContext
      | throwError "the original returned map lost its independently selected endpoints"
    let originalSource ← Realize.forwardRetainedValue originalSource actualSource.value
    let originalTarget ← Realize.forwardRetainedValue originalTarget actualTarget.value
    unless Realize.sameIntrinsicObservationInput actualSource originalSource &&
        Realize.sameIntrinsicObservationInput actualTarget originalTarget &&
        actualSource.json == (innerExecution.outputs[0]!)[0]! &&
        actualTarget.json == innerExecution.sources[0]! &&
        (← observations.get).size == 10 do
      throwError "an endpoint continuation replaced the original result occurrence or repeated a field request"
    Realize.checkDataOwners harness actualSource.fragment
    Realize.checkDataOwners harness actualTarget.fragment
    let unavailable (active : Realize.Harness) : TermElabM Bool := do
      try
        discard <| Realize.realizeObjectObservation active trace pendingSource
        return false
      catch error => return Exception.stratum? error == some .unavailable
    unless ← unavailable (← Realize.Harness.empty) do
      throwError "the endpoint continuation escaped its original invocation owner"
    harness.stop
    unless ← unavailable harness do
      throwError "the completed endpoint continuation survived expiry of its actual supplier"
  finally
    harness.stop
