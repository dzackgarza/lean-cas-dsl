/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Realize.RuntimeSupport

@[expose] public section

/-!
# The realized reading (`specs/leaf-registration.md`)

A statement's semantic reading elaborates it into its claim (`Language.Claim`): a proposition of
the catalogue's mathematics, and the term it is about. This module decides the claim:

1. **Lean discharge first.** The proposition is decided in Lean, generically
   (`decideEvaluated`): the registered evaluations of the literal forms whose denotations occur
   in it (a literal row's `evaluation`, a `meta` procedure of `lean-categories`, run through the
   one sanctioned runner `Language.runProcedure`, LC-18) rewrite the images of literals under the
   catalogue's operations to literals, and the goal that remains is proved by
   `of_decide_eq_true (Eq.refl true)` (Lean's `mkDecideProof`, on `Decidable` instances alone,
   running no tactic of the kernel's); the proof so formed is checked by Lean's kernel,
   synchronously, within a fixed heartbeat budget; refutation is the same proof of `¬p`. If Lean
   proves it, the statement holds as proved and no leaf is consulted. If Lean refutes it, the
   assertion is refuted and reports a wrong answer. Nothing is decided by evaluation outside the
   kernel.
2. **Otherwise, realize.** The same term is evaluated bottom-up through the operations the
   semantic reading recorded (`CasCatalogue.Trace`): a named object at its parameters is its
   form, encoded by the kernel; a literal (a morphism by its graph) is its form; the receiver of
   a method or property is sent along the route the semantic reading resolved, as far as the
   catalogue's refinement rows take it (CC-TRANSPORT, `transport`); an operation applied to a
   value of a form selects the admitted registration of that operation on that form
   (`CasCatalogue.Admission`), sends the encoded input over the port, and decodes the answer in
   the operation's declared result interface. A registered limit is an operation on its diagram,
   sent in the forms of its objects and arrows. The accepted constructor supplies the complete
   computational field schema for its apex and defining maps. Missing or ill-framed fields are
   malformed; the returned maps and their laws are never promoted to mathematical evidence.
   Projections and later operations retain these actual fields and any owning session. No
   registration is a gap; two are a gap reported as ambiguous; a backend that cannot start is
   unavailable; a rejected answer is malformed.
3. **Comparison.** `assert X = L` holds when the decoded value equals `L`, by the decidable
   equality of the form's type, checked by the kernel the same way. A decision is compared as a
   three-valued answer. Nothing a leaf returned is used as evidence of anything but its own
   answer.

The kernel supplies no `Decidable` instance of its own: which propositions Lean decides is the
catalogue's and Mathlib's. (Equality of morphisms of a concrete category, decided on their
functions, is mathematics; it belongs to `lean-categories`.)
-/

open Lean Meta Elab Term

namespace CasCatalogue

namespace Realize

open Language

/-- Compact failure-only context for one already selected occurrence. Producer
ordinals are execution addresses in this question; hashes only abbreviate formal
terms. Neither summary nor equality flags select an input or observe a child. -/
def operationEndpointDiagnosticSummary (wire : Wire) : Json := Json.mkObj [
  ("producer", toJson ((Trace.producerAnchor? wire.value).map (·.occurrence))),
  ("producerDescription", toJson ((Trace.producerAnchor? wire.value).map fun anchor =>
    s!"{anchor.description.take 160}")),
  ("formalHash", toJson (toString (hash wire.value))),
  ("form", toJson wire.form.id), ("category", toJson wire.form.category.raw),
  ("contextHash", toJson (wire.categoryContext.map fun context => toString (hash context.bundle))),
  ("packetCtor", toJson ((wire.json.getObjValAs? String "ctor").toOption)),
  ("ownershipSlots", toJson wire.ownership.size),
  ("objectObserved", toJson wire.objectObserved),
  ("callableObserved", toJson wire.callableObserved),
  ("morphismFramed", toJson wire.morphismFramed),
  ("action", toJson (wire.actionRecipe.map fun recipe => Json.mkObj [
    ("owner", toJson (match recipe.owner with
      | .edge edge => edge.label
      | .construction id _ => id.raw)),
    ("morphism", toJson recipe.morphism),
    ("applicationHash", toJson (toString (hash recipe.application)))])),
  ("intrinsicAssembly", toJson wire.intrinsicAssembly.isSome),
  ("capturedInvocation", toJson (wire.capturedInvocation.map (·.occurrence))),
  ("endpointPresentation", toJson wire.endpointPresentation.isSome)]

/-- Report the same top-level components as `sameCompleteWireContext` only after
its existing guard fails. This does not unfold terms, query a trace/cache, read
endpoint data, or replace the original complete comparison. -/
def operationEndpointDiagnosticDifferences (left right : Wire) : Array String :=
  ((#[("value", left.value == right.value), ("json", left.json == right.json),
    ("ownership", left.ownership == right.ownership),
    ("serviceInputPaths", left.serviceInputPaths == right.serviceInputPaths),
    ("pointDataInterface", left.pointDataInterface == right.pointDataInterface),
    ("objectIso", left.objectIso == right.objectIso),
    ("endpointPresentation.comparison",
      left.endpointPresentation.map (·.comparison) == right.endpointPresentation.map (·.comparison)),
    ("endpointPresentation.forward",
      left.endpointPresentation.map (·.forward) == right.endpointPresentation.map (·.forward)),
    ("endpointPresentation.backward",
      left.endpointPresentation.map (·.backward) == right.endpointPresentation.map (·.backward)),
    ("endpointPresentation.forwardOwnership",
      left.endpointPresentation.map (·.forwardOwnership) == right.endpointPresentation.map (·.forwardOwnership)),
    ("endpointPresentation.backwardOwnership",
      left.endpointPresentation.map (·.backwardOwnership) == right.endpointPresentation.map (·.backwardOwnership)),
    ("endpointPresentation.maps", sameEndpointComparisonMaps
      (left.endpointPresentation.bind (·.maps)) (right.endpointPresentation.bind (·.maps))),
    ("endpointPresentation.namedRefinement", sameNamedRefinementOrigin
      (left.endpointPresentation.bind (·.namedRefinement)) (right.endpointPresentation.bind (·.namedRefinement))),
    ("productComponents", sameProductComponents left.productComponents right.productComponents),
    ("morphismFraming", sameMorphismFraming left.morphismFraming right.morphismFraming),
    ("actionRecipe", sameActionRecipe left.actionRecipe right.actionRecipe),
    ("intrinsicAssembly", sameIntrinsicAssembly left.intrinsicAssembly right.intrinsicAssembly),
    ("capturedInvocation.occurrence",
      left.capturedInvocation.map (·.occurrence) == right.capturedInvocation.map (·.occurrence)),
    ("callableEndpoints", sameCallableEndpoints left.callableEndpoints right.callableEndpoints),
    ("pointOrigin", samePointOrigin left.pointOrigin right.pointOrigin),
    ("payload", sameOperationPresentationPayload left.payload right.payload),
    ("form", sameOperationPresentationForm left.form right.form),
    ("morphismFramed", left.morphismFramed == right.morphismFramed),
    ("callableObserved", left.callableObserved == right.callableObserved),
    ("objectObserved", left.objectObserved == right.objectObserved),
    ("presentationIsos", left.presentationIsos == right.presentationIsos),
    ("category.bundle", left.categoryContext.map (·.bundle) == right.categoryContext.map (·.bundle)),
    ("category.expression", match left.categoryContext, right.categoryContext with
      | none, none => true
      | some first, some second => first.expression.syntacticEq second.expression
      | _, _ => false),
    ("constructionInputs", left.constructionInputs == right.constructionInputs),
    ("constructionInputOwnership", left.constructionInputOwnership == right.constructionInputOwnership),
    ("liftExecution", sameRetainedLiftExecution left.liftExecution right.liftExecution),
    ("proofSources", left.proofSources.length == right.proofSources.length &&
      (left.proofSources.zip right.proofSources).all (fun (first, second) =>
        sameCompleteWireContext (retainedSnapshotWire first) (retainedSnapshotWire second)))] :
      Array (String × Bool)).filterMap fun (field, same) => if same then none else some field)

def operationEndpointDiagnosticComparison (consumer argument : Wire) : Json := Json.mkObj [
  ("consumer", operationEndpointDiagnosticSummary consumer),
  ("argument", operationEndpointDiagnosticSummary argument),
  ("unequal", toJson (operationEndpointDiagnosticDifferences consumer argument))]

/-- Check an argument against its fixed complete consumer endpoints. Full
receipts retain their comparison/action selections; only the explicit native
point interface can supply endpoint data without a whole endpoint receipt.
Transparent wrappers and typed-map fields follow producer-selected positions. -/
partial def checkCapturedArgumentEndpoints (context : CategoryContext)
    (template : ActionDataTemplate) (source target : Wire) : TermElabM Bool := do
  match template with
  | .wire _ wire =>
      if let some endpoints ← retainedCallableEndpoints? wire context then
        let expectedSource ← forwardRetainedValue source endpoints.1.value
        let expectedTarget ← forwardRetainedValue target endpoints.2.value
        unless sameCompleteWireContext endpoints.1 expectedSource &&
            sameCompleteWireContext endpoints.2 expectedTarget do
          let details := Json.mkObj [
            ("argument", operationEndpointDiagnosticSummary wire),
            ("source", operationEndpointDiagnosticComparison expectedSource endpoints.1),
            ("target", operationEndpointDiagnosticComparison expectedTarget endpoints.2)]
          throwStratum .noImplementation
            m!"the observed argument requires a declared action between its complete endpoint occurrences; \
              captured argument endpoints: {details.compress}"
        return true
      if let some point := wire.pointDataInterface then
        CategoryContext.checkMorphism context wire.value point.domain point.target
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType point.domain) (← inferType source.value) <&&>
              isDefEq point.domain source.value <&&>
            isDefEq (← inferType point.target) (← inferType target.value) <&&>
              isDefEq point.target target.value) do
          throwError "the native argument changed its independently declared complete point type"
        unless point.domainData == source.fragment && point.targetData == target.fragment do
          throwStratum .noImplementation
            "the native argument requires its declared action to the consumer's endpoint packets"
        return true
      return false
  | .retained child | .logical child => checkCapturedArgumentEndpoints context child source target
  | .pointCallable selected _ _ point =>
      discard <| framingContext (some context) (some selected)
      checkCapturedArgumentEndpoints context (.wire .map point) source target
  | .inventoryMap selected actualSource actualTarget original =>
      discard <| framingContext (some context) (some selected)
      discard <| inventoryMapFrameTemplate selected actualSource actualTarget original
      unless sameCompleteWireContext actualSource
          (← forwardRetainedValue source actualSource.value) &&
          sameCompleteWireContext actualTarget
            (← forwardRetainedValue target actualTarget.value) do
        throwStratum .noImplementation
          "the inventory argument changed its original complete endpoint occurrences"
      return true
  | .ctor "typedMap" children =>
      let #[sourceTemplate, targetTemplate, body] := children
        | throwError "the captured argument changed its declared complete-map fields"
      let some actualSource := capturedTemplateWire? sourceTemplate | return false
      let some actualTarget := capturedTemplateWire? targetTemplate | return false
      let expectedSource ← callableActualEndpoint context source true
      let expectedTarget ← callableActualEndpoint context target false
      unless sameCompleteWireContext actualSource
          (← forwardRetainedValue expectedSource actualSource.value) &&
          sameCompleteWireContext actualTarget
            (← forwardRetainedValue expectedTarget actualTarget.value) do
        throwStratum .noImplementation
          "the argument's positioned endpoint views require their original complete comparison occurrences"
      checkCapturedArgumentEndpoints context body source target
  | .ctor "valueData" children =>
      let #[child] := children
        | throwError "the captured argument changed its transparent value field"
      checkCapturedArgumentEndpoints context child source target
  | .literal _ | .ctor _ _ | .array _ | .object _ | .project _ _ => return false

mutual

/-- A declaration position keeps the public role fixed by its original typed
producer. A scalar with a Hom-shaped type does not silently become a map. -/
partial def captureRoutedParameter (h : Harness) (trace : Trace)
    (slot : RoutedResultPlan.Parameter) (supplied : Option Wire := none) :
    TermElabM RoutedParameterOccurrence := do
  let parameter : SelectedCallableParameter ← match supplied with
    | some original => do
      let result ← retainedRecordInterface original
      checkCapturedResultInterface original result
      pure {
        formal := slot.formal, expectedType := slot.expectedType
        templates := #[ActionDataTemplate.wire result.role original] }
    | none => do
      let parameters ← capturedCallableParameters h trace #[slot.formal]
      let #[parameter] := parameters
        | throwError "the routed parameter lost its complete declaration occurrence"
      pure parameter
  let #[template] := parameter.templates
    | throwError "the routed parameter requires one declared computational data slot"
  unless parameter.formal == slot.formal && (← withoutModifyingState
      (withTransparency .all <| isDefEq parameter.expectedType slot.expectedType)) do
    throwError "the routed parameter changed its full declaration type"
  let (template, role) ← match actionTemplateExecution template with
    | .wire role original => do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType original.value) slot.expectedType <&&>
            isDefEq original.value slot.formal) do
        throwError "the routed data slot changed its retained formal producer"
      if (← retainedValueResultInterface? original).isSome || role == .retained then
        pure (template, RoutedResultPlan.ParameterRole.value)
      else if role == .map then do
        let some (source, target) := Language.homEnds? slot.expectedType
          | throwError "the routed map parameter lost its complete declared Hom"
        let context ← match original.categoryContext with
          | some context => pure context
          | none =>
            let some category := (← registryState).categories.find? (·.id == original.form.category)
              | throwError "the routed map parameter lost its selected complete category"
            CategoryContext.ofNamed category source
        CategoryContext.checkMorphism context original.value source target
        let whole ← captureCompleteCallable h trace original context
        pure (ActionDataTemplate.wire .map whole,
          RoutedResultPlan.ParameterRole.map context source target)
      else if role == .object then do
        let context ← routedBoundaryContext original
        CategoryContext.checkObject context original.value
        pure (template, RoutedResultPlan.ParameterRole.object context)
      else do
        let context ← match original.categoryContext with
          | some context => pure (some context)
          | none =>
            match (← registryState).categories.find? (·.id == original.form.category) with
            | none => pure none
            | some category => do
                let belongs ← withoutModifyingState do
                  let bundle ← instantiateFresh category.declaration
                  let context : CategoryContext := { expression := category.expression, bundle }
                  CategoryContext.exposeStructureParameters bundle
                  withTransparency .all <| isDefEq slot.expectedType (← CategoryContext.carrier context)
                if belongs then pure (some (← CategoryContext.ofNamed category original.value))
                else pure none
        let role ← match context with
          | none => pure RoutedResultPlan.ParameterRole.value
          | some context => do
              match ← constructionResultInterface context original.value slot.expectedType with
              | .object context => pure (RoutedResultPlan.ParameterRole.object context)
              | .map _ => throwError "a routed Hom parameter lost its declared whole-map role"
              | .value _ => pure RoutedResultPlan.ParameterRole.value
        pure (template, role)
    | _ => pure (template, RoutedResultPlan.ParameterRole.value)
  return {
    slot, template, interface := {
      actionIndex := slot.actionIndex, dataIndex := slot.dataIndex,
      formal := slot.formal, expectedType := slot.expectedType, role } }

/-- A named-base implementation receives the accepted presentation of the
original prefix image. Its local suffix indices are related to the original
route by an explicit offset; no earlier action or parameter occurrence is
removed from the invocation's complete source boundary. -/
partial def capturePresentedRoutedBoundary (trace : Trace) (source : SelectedRoutedBoundary) :
    TermElabM (Option SelectedRoutedBoundary) := do
  let .object _ := source.receiver.form | return none
  let route := source.prefixActions.map (·.1)
  let applications := source.prefixActions.map (·.2)
  unless route.size == source.descriptors.size && route.size == source.images.size do
    throwError "the named method boundary lost its complete original action positions"
  let next ← IO.mkRef 0
  let capture : CapturedActionEncoder := fun edge application => do
    let index ← next.get
    let some (expectedEdge, expected) := source.prefixActions[index]?
      | throwError "the named presentation added an unselected route action"
    unless edge == expectedEdge && (← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType application) (← inferType expected) <&&>
          isDefEq application expected)) do
      throwError "the named presentation changed an original complete action occurrence"
    let some descriptor := source.descriptors[index]?
      | throwError "the named presentation lost an original parameter occurrence"
    next.set (index + 1)
    return descriptor
  let (receiver, remaining) ← canonicalOperationInput trace source.receiver route
    none (some capture) (some applications)
  let offset := route.size - remaining.size
  if offset == 0 then return none
  unless (← next.get) == offset do
    throwError "the named presentation did not retain each consumed action occurrence"
  let .object _ := receiver.form | return none
  unless remaining == route.extract offset route.size do
    throwError "the named presentation changed the original residual route"
  let mut expected := source.receiver.value
  for application in applications.extract 0 offset do
    expected ← Semantic.objOf application expected
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType receiver.value) (← inferType expected) <&&>
        isDefEq receiver.value expected) do
    throwError "the named method presentation replaced its complete semantic receiver"
  let parameters := (source.parameters.filter (fun parameter =>
    offset <= parameter.slot.actionIndex)).map fun parameter => {
      parameter with
      slot := { parameter.slot with actionIndex := parameter.slot.actionIndex - offset },
      interface := { parameter.interface with actionIndex := parameter.interface.actionIndex - offset } }
  return some {
    receiver, context := (← routedBoundaryContext receiver),
    prefixActions := source.prefixActions.extract offset route.size,
    descriptors := source.descriptors.extract offset route.size,
    images := source.images.extract offset route.size,
    parameters, routeOffset := offset }

/-- Only the selected boundary is interpreted. Every declaration position is
captured before any action can return new data or populate an expression cache. -/
partial def captureRoutedInvocationFrom (h : Harness) (trace : Trace) (what : String)
    (formal : Expr) (id : MethodId) (route : Array EdgeRef) (receiver : Expr)
    (recordedComparisons : Array (RouteComparison × Expr))
    (interpreted : MethodApplication) (prescribed : Array LiftId) (original : Wire)
    (supplied : Option (Array RoutedParameterInput) := none) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let state ← registryState
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType original.value) (← inferType receiver) <&&>
        isDefEq original.value receiver) do
    throwError "the method changed its original typed receiver occurrence"
  let some method := state.methods.find? (·.id == id)
    | throwError "the selected method is no longer registered"
  let some functor := state.functor? method.functor
    | throwError "the selected method lost its registered functor"
  let receiverExpression := interpreted.sourceContext.expression
  discard <| framingContext (some interpreted.sourceContext) original.categoryContext
  CategoryContext.checkObject interpreted.sourceContext original.value
  let resolution ← match state.resolveMethod receiverExpression method.name with
    | .ok resolution => pure resolution
    | .error error => throwResolutionError state error
  unless resolution.method.id == id && resolution.route.refs == route && resolution.lifts == prescribed do
    throwError "the method changed its independently selected complete resolution"
  let comparisonTerms ← Semantic.validateResolutionComparisons state resolution (some receiver)
  Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses comparisonTerms recordedComparisons
  Semantic.checkMethodApplication state resolution receiver interpreted
  let fullInput := interpreted.image
  let acceptedInput := interpreted.input
  let some (application, _) ← DeclaredApplication.complete?
      functor.declaration interpreted.application true
    | throwError "the interpreted method lost its complete original declaration application"
  let F ← Semantic.asFunctor application
  let expected := interpreted.baseResult
  let baseFormal := if prescribed.isEmpty then formal else interpreted.baseResult
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType expected) (← inferType baseFormal) <&&> isDefEq expected baseFormal <&&>
        isDefEq (← inferType interpreted.result) (← inferType formal) <&&>
        isDefEq interpreted.result formal) do
    throwError "the captured method changed its complete fixed result interface"
  let context ← CategoryContext.presented interpreted.baseContext
  let allSlots ← RoutedResultPlan.parameterSlots method F
    (route.zip interpreted.routeApplications)
  if let some supplied := supplied then
    unless supplied.size == allSlots.size do
      throwStratum .malformed "the complete method omitted or added a computational parameter position"
  let allParameters ← allSlots.mapM fun slot => do
    let original ← match supplied with
      | none => pure none
      | some supplied => do
        let #[selected] := supplied.filter (fun selected =>
            selected.actionIndex == slot.actionIndex && selected.dataIndex == slot.dataIndex)
          | throwStratum .malformed "the method repeated or omitted a selected parameter occurrence"
        pure (some selected.wire)
    captureRoutedParameter h trace slot original
  -- A method's result and lift stages may expose any preceding action image.
  -- Capture the full original route before choosing a computational boundary;
  -- a presentation optimisation cannot erase those typed producer positions.
  let canonical := original
  let remaining := route
  let canonicalContext ← routedBoundaryContext canonical
  unless remaining.size ≤ route.size &&
      route.extract (route.size - remaining.size) route.size == remaining do
    throwError "the canonical method boundary changed the original ordered residual route"
  let applications := interpreted.routeApplications.extract
    (route.size - remaining.size) route.size
  let prefixActions := remaining.zip applications
  let offset := route.size - remaining.size
  let parameters := (allParameters.filter (fun parameter => offset ≤ parameter.slot.actionIndex)).map
    fun parameter => { parameter with
      slot := { parameter.slot with actionIndex := parameter.slot.actionIndex - offset },
      interface := { parameter.interface with actionIndex := parameter.interface.actionIndex - offset } }
  let descriptorAt := fun (index : Nat) (edge : EdgeRef) => do
    let arguments := parameters.filter (·.slot.actionIndex == index)
    for (argument, position) in arguments.zipIdx do
      unless argument.slot.dataIndex == position do
        throwError "the routed action changed its ordered declaration data slots"
    return routedActionDescriptor edge (arguments.map (·.template))
  let mut transported := canonical
  let mut descriptors := #[]
  let mut images := #[]
  for ((edge, application), index) in prefixActions.zipIdx do
    let descriptor ← descriptorAt index edge
    descriptors := descriptors.push descriptor
    -- A single existing route step fixes this descriptor's positional origin.
    -- Equal actions elsewhere in the route cannot choose another parameter slot.
    let capture : CapturedActionEncoder := fun selected actual => do
      unless selected == edge && (← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType actual) (← inferType application) <&&>
            isDefEq actual application)) do
        throwError "the routed step changed its independently selected complete action"
      return descriptor
    transported ← transportImage trace transported #[edge] (some #[application]) none (some capture)
    images := images.push transported
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType transported.value) (← inferType fullInput) <&&>
        isDefEq transported.value fullInput) do
    throwError "the captured route changed its complete method input"
  let transportedContext ← routedBoundaryContext transported
  let descriptor ← descriptorAt prefixActions.size (.functor functor.id)
  let directParameters := (parameters.filter (·.slot.actionIndex == prefixActions.size)).map fun parameter =>
    { parameter with
      slot := { parameter.slot with actionIndex := 0 }
      interface := { parameter.interface with actionIndex := 0 } }
  let canonicalBoundary : SelectedRoutedBoundary := {
    receiver := canonical, context := canonicalContext, prefixActions, descriptors, images, parameters }
  let presented ← capturePresentedRoutedBoundary trace canonicalBoundary
  let transportedBoundary : SelectedRoutedBoundary := {
    receiver := transported, context := transportedContext,
    prefixActions := #[], descriptors := #[], parameters := directParameters,
    routeOffset := route.size, materializeRoute := true }
  let form := match CategoryContext.named? state functor.target with
    | some target => imageForm state (.functor functor.id) target
    | none => Form.contextual functor.target canonical.form
  let (action, dependencies) ← renderCapturedActionData descriptor
  let fragment ← scopedNode "functorAction" #[action, transported.fragment]
  let wire : Wire := {
    form, categoryContext := some context,
    payload := (← combinedRecipePayload baseFormal fragment
      (#[original, canonical, transported] ++ dependencies ++
        allParameters.flatMap (fun parameter => actionTemplateInputs parameter.template))) }
  let base ← retainCapturedInvocation h wire (.routed {
    formal := baseFormal, fragment, context, form, method, functor, application := F,
    expected, acceptedInput, original,
    canonical := canonicalBoundary, transported := transportedBoundary,
    presented, descriptor, resolution, comparisonTerms })
  if prescribed.isEmpty then return base
  capturePrescribedInvocation h trace formal id interpreted original base
    ((#[original] ++ images).extract 0 route.size) images descriptors

/-- Capture the fixed ordered lift plan without dispatch. The method base is
another retained invocation, so both pure inspection and execution share it. -/
partial def capturePrescribedInvocation (h : Harness) (trace : Trace) (formal : Expr)
    (method : MethodId) (application : MethodApplication) (original base : Wire)
    (sources images : Array Wire) (descriptors : Array ActionDataTemplate) :
    TermElabM Wire := do
  let prescribed := application.lifts.map (·.id)
  let plan ← match ← LiftedSubobjectData.planIn (← inferType formal)
      application.resultContext.expression original.value prescribed application.baseResult
      (some application) with
    | .ok plan => pure plan
    | .error message => throwError "{message}"
  let parameters ← plan.components.mapM fun component =>
    capturedParameterData h trace component.selection.parameters
  unless sources.size == plan.components.size && images.size == plan.components.size &&
      descriptors.size == plan.components.size do
    throwError "the prescribed lift lost an original route source or image occurrence"
  let mut actions := #[]
  for (component, index) in plan.components.zipIdx do
    let some source := sources[index]?
      | throwError "the prescribed lift lost an original source position"
    let some image := images[index]?
      | throwError "the prescribed lift lost an original image position"
    let some descriptor := descriptors[index]?
      | throwError "the prescribed lift lost an original descriptor position"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType source.value) (← inferType component.receiver) <&&>
          isDefEq source.value component.receiver <&&>
          isDefEq image.value
            (← Semantic.objOf application.routeApplications[index]! component.receiver)) do
      throwError "the prescribed lift changed a complete original route interface"
    let .ctor "constructorMap" #[_, inner] := descriptor
      | throwError "the selected lift lost its captured complete Arrow descriptor"
    actions := actions.push inner
  let context ← CategoryContext.presented application.resultContext
  let fragment ← scopedNode "liftedSubobject" #[
    { json := toJson (prescribed.map (·.raw)) }, original.fragment, base.fragment,
    DataOwnership.Data.array #[]]
  let dependencies := #[original, base] ++ sources ++ images ++
    parameters.flatMap (fun fields => fields.flatMap actionTemplateInputs) ++
    actions.flatMap actionTemplateInputs
  let wire : Wire := {
    form := contextualForm (← registryState) context original.form,
    payload := (← combinedRecipePayload formal fragment dependencies),
    categoryContext := some context,
    serviceHandles := (← retainServiceOperands h dependencies) }
  retainCapturedInvocation h wire (.prescribed {
    formal, fragment, context, method, original, base, sources, images, plan, parameters, actions })

/-- Read only the authenticated committed base table. Captured route templates
cannot substitute another evaluation's source or image occurrence. -/
partial def actualPrescribedRouteInputs (h : Harness) (trace : Trace)
    (selected : SelectedPrescribedInvocation) (base : Wire) :
    TermElabM (Array Wire × Array Wire) := do
  let some fields ← actualRecordFields? h base
    | throwStratum .noImplementation
        "the selected prescribed base has no retained complete routed result interface"
  let access ← actualRetainedRecordReader h trace (actualRoutedKnownField h trace)
  prescribedRouteInputsWith access (observeActionDataWire h trace) selected base fields

/-- Observe the captured base and parameters, obtain the selected boundary's
exact route occurrences, then run the shared ordered lift fold. The completed
public packet retains every stage input, all four fields and their suppliers. -/
partial def observePrescribedInvocation (h : Harness) (trace : Trace)
    (selected : SelectedPrescribedInvocation)
    (routeInputs : SelectedPrescribedInvocation → Wire → TermElabM (Array Wire × Array Wire)) :
    TermElabM Wire := do
  let active := { h with demandObjectActions := true }
  let state ← registryState
  let original ← realizeObjectObservation active trace selected.original
  let base ← realizeObjectObservation active trace selected.base
  let (sources, images) ← routeInputs selected base
  let plan := selected.plan
  let e := selected.formal
  let id := selected.method
  let receiver := plan.fixedSource
  let lifts := plan.components.map (·.lift)
  let retainedBase := plan.fixedBase
  let resultExpression := selected.context.expression
  let parameters ← selected.parameters.mapM fun templates => do
    let fields ← templates.mapM (mapActionTemplateWires (observeActionDataWire active trace))
    let values ← fields.mapM renderCapturedActionData
    return (values.map Prod.fst, values.flatMap Prod.snd)
  let actionTemplates ← selected.actions.mapM
    (mapActionTemplateWires (observeActionDataWire active trace))
  let actions ← actionTemplates.mapM renderCapturedActionData
  let actionValues ← actionTemplates.zipIdx.mapM fun (template, index) => do
    let some component := plan.components[index]?
      | throwError "the retained lift action lost its selected stage"
    retainedLiftActionValue component.selection original.form template
  let actions := (actions.zip actionValues).map fun ((data, dependencies), action) =>
    (data, dependencies.push action)
  let reader ← actualRetainedRecordReader active trace (actualRoutedKnownField active trace)
  let run ← executePrescribedRetainedWith reader plan original base sources images parameters actions
    (fun _ _ => pure none)
    (fun _ input dependencies field => do
      let some form := state.liftInputForm? input.selection.entry.inputAddress
        | throwError "the selected lift lost its public input form"
      observeLiftStageField active input input.original.value form dependencies field)
  let runtime ← run.stages.mapM fun (input, result) => do
    let .ok parameters := input.parameters.json.getArr?
      | throwError "the retained lift parameters lost their ordered array"
    let some image := input.sourceImage?
      | throwError "the completed lift omitted its actual complete source image"
    return {
      parameters, action := input.action.json, source := input.original.json,
      transportedSource := image.json, base := input.base.json,
      comparisonImage := result.comparisonImage.json : LiftedSubobjectData.StageInputs }
  let lifted := run.packet
  let liftedJson := lifted.json
  let some checked ← LiftedSubobjectData.decodeIn (← inferType e) resultExpression
      receiver lifts retainedBase liftedJson
      (fun _ formal data => do ComputationalData.validatePort formal (← inferType formal) data)
      (fun _ formal data objects => do
        ComputationalData.validatePort formal (← inferType formal) data objects)
      (some (parameters.map (fun data => data.1.map (·.json)))) (some plan) (some runtime)
    | throwError "the prescribed method has no complete computational lift packet"
  let packet ← match checked with
    | .ok packet => pure packet
    | .error message => throwStratum .malformed m!"{id.raw}: {message}"
  unless ← withTransparency .all <| isDefEq packet.formalResult e do
    throwError "the independent prescribed lift changed its formal result"
  unless packet.data == liftedJson do
    throwError "the completed lift decoder changed its actual scoped packet"
  let payload ← scopedPayload e lifted
  let sourceImages ← run.stages.mapM fun (input, _) => do
    let some image := input.sourceImageObject?
      | throwError "the completed lift omitted its exact source image endpoint"
    return image.fragment
  let stageHandles ← run.stages.zipIdx.mapM fun ((input, result), index) => do
    let some action := actionValues[index]?
      | throwError "the completed lift lost its retained full action value"
    retainLiftStageHandles h input result action
  let execution : LiftExecution := {
    selections := plan.components.map (·.selection), stageHandles,
    actions := run.stages.map (·.1.action.json),
    parameters := runtime.map (·.parameters), sources := run.stages.map (·.1.source.json),
    bases := run.stages.map (·.1.base.json), outputs := packet.outputs,
    sourceImages := sourceImages.map (·.json),
    comparisonImages := run.stages.map (·.2.comparisonImage.json),
    actionOwnership := run.stages.map (·.1.action.ownership),
    parameterOwnership := run.stages.map (·.1.parameters.ownership),
    sourceOwnership := run.stages.map (·.1.source.ownership),
    baseOwnership := run.stages.map (·.1.base.ownership),
    outputOwnership := run.stages.map (fun (_, result) => result.outputs.map (·.ownership)),
    sourceImageOwnership := sourceImages.map (·.ownership),
    comparisonImageOwnership := run.stages.map (·.2.comparisonImage.ownership) }
  let handles := stageHandles.flatMap LiftStageHandles.all ++ (← retainLiftOperands h run.dependencies)
  cacheLiftFields h execution none handles
  let context := selected.context
  unless context.expression.syntacticEq resultExpression do
    throwError "the completed method changed its accepted constructed result category"
  return {
    form := match CategoryContext.named? state resultExpression with
      | some category => .subobject category
      | none => .contextual resultExpression original.form
    payload, liftExecution := some execution, categoryContext := some context
    serviceHandles := handles }

/-- Surface interpretation enters the same captured lifecycle as public service
preparation. All original inputs are fixed before the selected method is observed. -/
partial def captureRoutedInvocation (h : Harness) (trace : Trace) (what : String)
    (formal : Expr) (id : MethodId) (route : Array EdgeRef) (receiver : Expr)
    (comparisons : Array (RouteComparison × Expr)) (application : MethodApplication)
    (lifts : Array LiftId) : TermElabM Wire := do
  let original ← realizeUnobserved { h with demandObjectActions := false } trace
    s!"the original receiver of {id.raw} in {what}" receiver
  captureRoutedInvocationFrom h trace what formal id route receiver comparisons application lifts original

/-- An already selected field retains its exact value role during demand. A
Hom-shaped scalar is not promoted by the operation trace. -/
partial def observeRoutedField (h : Harness) (trace : Trace)
    (result : IntrinsicResultInterface) (wire : Wire) : TermElabM Wire := do
  match result with
  | .object _ => realizeObjectObservation h trace wire
  | .map _ => realizeArrowObservation h trace wire
  | .value _ => realizeValueObservation h trace wire

/-- Known fields of a pending method come from its pure input-origin plan.
Authenticate the producer occurrence and preserve the ordinary cycle guard;
neither a returned packet nor an available registration chooses the field. -/
partial def actualRoutedKnownField (h : Harness) (trace : Trace) (wire : Wire)
    (path : ComputationalData.RecordFieldPath) : TermElabM (Option Wire) := do
  let some captured ← retainedCapturedInvocation? wire | return none
  let some record := (← h.invocations.get).find?
      (·.captured.occurrence == captured.occurrence)
    | throwStratum .unavailable "the pending result field lost its owning invocation scope"
  let original ← forwardRetainedValue record.input wire.value
  unless sameCompleteWireContext original { wire with capturedInvocation := none } do
    throwStratum .unavailable "the pending result field changed its original producer occurrence"
  -- The ordinary observer reuses this completed canonical occurrence before
  -- consulting its cycle guard. The intrinsic pending path has no work here.
  if record.result.isSome then return none
  let .routed selected := record.captured.interface | return none
  if h.invocationStack.contains captured.occurrence then
    throwStratum .unavailable "the pending field has cyclic original operand dependencies"
  let active := { h with invocationStack := h.invocationStack.push captured.occurrence }
  let reader ← actualRetainedRecordReader active trace (actualRoutedKnownField active trace)
  routedKnownFieldWith reader (observeRoutedField active trace) selected path

/-- The complete method has one registration decision before observation. Pure
input projections use the generic field reader; returned fields use the shared
complete request and reply fold. No selected source occurrence is recaptured. -/
partial def observeRoutedInvocation (h : Harness) (trace : Trace) (wire : Wire)
    (selected : SelectedRoutedInvocation) :
    TermElabM (Wire × Option RetainedResultFields) := do
  let active := { h with demandObjectActions := true }
  let reader ← actualRetainedRecordReader active trace (actualRoutedKnownField active trace)
  if let some (result, fields) ←
      knownRoutedResultWith reader (observeRoutedField active trace) selected then
    return (result, some fields)
  let (boundary, registration) ← routedInvocationRegistrations h trace wire selected
  let plan ← routedInvocationResultPlan selected boundary
  if registration.isNone && !(← hasGroundedDerivation h selected.method.id.raw) then
    throwStratum .noImplementation
      m!"no admitted registration computes the complete selected method {selected.method.id.raw}"
  let inputs ← readSelectedRoutedInputsWith (observeActionDataWire active trace) selected boundary
    (fun receiver => computationalApexReceiver trace receiver)
  let materialized ← routedMethodRequest selected boundary inputs
  let complete := !(boundary.prefixActions.isEmpty && boundary.parameters.isEmpty)
  let reply ← sendData active selected.method.id.raw materialized.request
    selected.resolution.comparisons complete registration
  let (result, fields) ← completeRoutedResultWith validateRoutedMap reader
    active trace selected boundary materialized plan reply
  return (result, some fields)

/-- Actual and private readers share declaration paths and field assembly.
This boundary is called only after a concrete consumer selects its computation. -/
partial def actualRetainedRecordReader (h : Harness) (trace : Trace)
    (pendingField? : PendingRecordFieldReader := fun _ _ => pure none) :
    TermElabM RetainedRecordReader := do
  let active := { h with demandObjectActions := true }
  let access : RetainedRecordAccess := {
    fields := actualRecordFields? h, pendingField? := pendingField?
    observe := fun result wire => match result with
      | .object _ => realizeObjectObservation active trace wire
      | .map _ => realizeArrowObservation active trace wire
      | .value _ => realizeValueObservation active trace wire
    presentField := fun origin parent step field => do
      let action ← standaloneRecordProjectionActionWith
        (← actualRetainedRecordReader h trace pendingField?) parent step
      applyRecordFieldComparison h action parent step field none origin }
  return { readField := readRetainedRecordFieldWith access }

/-- Surface callers share the same inert public-field capture used by retained
comparison execution. The trace does not rediscover an already selected parent. -/
partial def capturePublicRecordProjection (h : Harness) (_trace : Trace) (parent : Wire)
    (path : ComputationalData.RecordFieldPath) : TermElabM Wire :=
  capturePublicRecordProjectionAt h parent path

/-- A completed field is the canonical selected occurrence itself. Observing
this pending selection neither overwrites that field's original producer nor
restarts a trace from the field's now possibly aliased formal expression. -/
partial def observeRecordProjection (h : Harness) (trace : Trace)
    (selected : SelectedRecordProjection)
    (pendingField? : PendingRecordFieldReader := fun _ _ => pure none) : TermElabM Wire := do
  let field ← (← actualRetainedRecordReader h trace pendingField?).readField selected.parent selected.path
  let field ← forwardRetainedValue field selected.formal
  checkCapturedResultInterface field selected.result
  checkDataOwners h field.fragment
  return field

/-- Surface/service selection shares this producer, retaining the exact parent
Wire even when the original source and target are definitionally equal. -/
partial def captureStructuredRecordField (h : Harness) (trace : Trace) (formal : Expr)
    (original : Wire) (context : CategoryContext) (field : String) : TermElabM Wire := do
  checkCapturedResultInterface original (.object context)
  let path ← withLocalDeclD `recordReceiver (← inferType original.value) fun symbolic => do
    let some selected ← StructuredProjection.arrow? symbolic context
      | throwStratum .invalid "the selected record has no accepted Arrow field interface"
    let (expected, _, _) ← selected.field field
    let some path ← ComputationalData.recordFieldPath? symbolic expected
      | throwError "the public record field lost its symbolic declaration path"
    return path
  let selected ← capturePublicRecordProjection h trace original path
  forwardRetainedValue selected formal

-- Closed element data comes from the formal operation trace, never from carrier matching.
partial def elementFragment (h : Harness) (trace : Trace) (e : Expr) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  if let some actual := (← h.results.get)[e]? then
    if actual.actualData || actual.callableObserved then
      return (← scopedNode "point" #[actual.fragment], #[actual])
  let state ← registryState
  let some node ← trace.node? e
    | throwStratum .noImplementation m!"the closed element has no retained construction"
  match node with
  | .operationEquivalence representative chosen candidates comparisons =>
      checkOperationEquivalence e representative chosen candidates comparisons
      elementFragment h trace representative
  | .elementNumeral n _ _ =>
      return (← scopedNode "numeral" #[{ json := toJson n }], #[])
  | .generator id params =>
      let some entry := state.objects.find? (·.id == id) | unreachable!
      unless entry.generator.isSome do throwError "the retained object has no generator"
      let (_, infos, _) ← forallMetaTelescope (← getConstInfo entry.declaration).type
      let objectArity := (infos.filter (·.isExplicit)).size
      let (index, dependencies) ← realizedParameterData h trace (params.extract objectArity params.size)
      return (← scopedNode "generator" index, dependencies)
  | .operationApply id params operands _ _ =>
      let some entry := state.operations.find? (·.id == id) | unreachable!
      unless operands.size == entry.arity do
        throwError "the retained operation expression changed its declared arity"
      let (parameters, parameterWires) ← realizedParameterData h trace params
      let arguments ← operands.mapM (elementFragment h trace)
      return (← scopedNode "operationExpression"
        #[{ json := toJson id.raw }, DataOwnership.Data.array parameters,
          DataOwnership.Data.array (arguments.map Prod.fst)],
        arguments.foldl (fun dependencies argument => dependencies ++ argument.2) parameterWires)
  -- Any other closed point `1 ⟶ X` is sent as the point it is, in its published morphism
  -- encoding (a named morphism, a composite, a mediator, an admitted point).
  | _ =>
      let point ← realize h trace "a point of a closed element" e
      return (← scopedNode "point" #[point.fragment], #[point])

/-- Capture an object's accepted route at its original runtime occurrence.
The literal/reduced selectors supply mathematics; this helper retains data only. -/
partial def captureParameterAction (h : Harness) (trace : Trace) (formal receiver : Expr)
    (route : Array EdgeRef) (applications : Array Expr) : TermElabM Wire := do
  if h.parameterRecovery.contains formal then
    throwStratum .noImplementation "the selected parameter action has cyclic data dependencies"
  let h := { h with
    demandObjectActions := false,
    parameterRecovery := h.parameterRecovery.push formal }
  let original ← realizeUnobserved h trace "the captured parameter action source" receiver
  let result ← transportImage trace original route (some applications)
    (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType result.value) (← inferType formal) <&&> isDefEq result.value formal) do
    throwError "the captured parameter action changed its complete selected result"
  return { result with payload := forwardPayload result formal result.json }

partial def capturedObjectParameter? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option Wire) := do
  let some (action, source) := FunctorActionData.objectAction? (← instantiateMVars value)
    | return none
  let some selected ← FunctorActionData.registeredComposite? (← registryState) action
    | return none
  return some (← captureParameterAction h trace value source
    (selected.map (·.edge)) (selected.map (·.application)))

partial def capturedRetainedParameter? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option Wire) := do
  let some selected ← FunctorActionData.retainedParameterAction? trace value | return none
  return some (← captureParameterAction h trace value selected.receiver
    selected.route selected.applications)

/-- Preserve the same independently selected parameter constructors and roles.
Every dynamic child is stored when its producer places it, never located later
by equal JSON or an expression-keyed cache. -/
partial def capturedParameterData (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array ActionDataTemplate) := do
  let h := { h with demandObjectActions := false }
  let mut data : Array ActionDataTemplate := #[]
  for parameter in parameters do
    if ← isProp (← inferType parameter) then continue
    let extent ← if (← trace.node? parameter).any (fun node =>
        match node with | .literal .. => true | _ => false) then
      extentOf? (← registryState) parameter
    else pure none
    if let some (power, ambient, element) := extent then
      let ambient ← realizeUnobserved h trace "the captured extent ambient" ambient
      let literal ← realizeUnobserved h trace "the captured extent literal" element
      data := data.push (.ctor "extent" #[.literal { json := toJson power.id.raw },
        .wire .parameter ambient, .wire .retained literal])
    else if (← h.results.get)[parameter]?.isSome || (← trace.node? parameter).isSome then
      let wire ← realizeUnobserved h trace "the captured complete parameter" parameter
      data := data.push (.wire .parameter wire)
    else
      let selected := (← instantiateMVars parameter).consumeMData
      let selectedFunctor := if selected.isAppOf ``CategoryTheory.Cat.Hom.toFunctor then
        selected.appArg! else selected
      let state ← registryState
      let declaration? :=
        (state.categories.find? (fun row => selected.getAppFn.constName? == some row.declaration)).map
          (fun row => ("category", row.id.raw, row.declaration, selected)) <|>
        (state.constructors.find? (fun row => selected.getAppFn.constName? == some row.semantics)).map
          (fun row => ("constructedCategory", row.id.raw, row.semantics, selected)) <|>
        (state.functors.find? (fun row => selectedFunctor.getAppFn.constName? == some row.declaration)).map
          (fun row => ("functor", row.id.raw, row.declaration, selectedFunctor))
      if let some (tag, id, declaration, application) := declaration? then
        let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
          fields.mapM (·.fvarId!.getBinderInfo)
        unless application.getAppNumArgs == infos.size do
          throwError "the selected dictionary lost its complete declaration application"
        let arguments := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
          if info.isExplicit then some argument else none
        let arguments ← capturedParameterData h trace arguments
        if tag == "constructedCategory" then
          let some constructor := state.constructor? ⟨id⟩ | unreachable!
          unless arguments.size == constructor.signature.size do
            throwError "the constructed category lost a declared ordered argument"
        data := data.push (.ctor tag #[.literal { json := toJson id }, .array arguments])
      else if let some image ← capturedObjectParameter? h trace parameter then
        data := data.push (.wire .object image)
      else if let some image ← capturedRetainedParameter? h trace parameter then
        data := data.push (.wire .object image)
      else if let some original ← retainedConstructionResult? trace parameter then
        if h.parameterRecovery.contains parameter then
          throwStratum .noImplementation "the selected construction has cyclic data dependencies"
        let actual ← realizeUnobserved
          { h with parameterRecovery := h.parameterRecovery.push parameter }
          trace "the original complete parameter construction" original
        data := data.push (.wire .parameter actual)
      else if (← recordCompleteConstruction trace parameter) ||
          (← recordCompleteNamedCategory trace parameter) ||
          (← recordCompleteUniversalObject trace parameter) then
        if h.parameterRecovery.contains parameter then
          throwStratum .noImplementation "the selected complete declaration has cyclic data dependencies"
        let actual ← realizeUnobserved
          { h with parameterRecovery := h.parameterRecovery.push parameter }
          trace "the complete selected parameter declaration" parameter
        data := data.push (.wire .parameter actual)
      else data := data.push (.literal {
        json := ← parameterData trace parameter h.parameterRecovery })
  return data

/-- Capture declaration slots at their original positions. An explicitly
retained operand overrides only its independently selected formal slot. -/
partial def capturedCallableParameters (h : Harness) (trace : Trace) (parameters : Array Expr)
    (overrides : Array (Nat × Wire) := #[]) : TermElabM (Array SelectedCallableParameter) := do
  let h := { h with demandObjectActions := false }
  let mut result := #[]
  for index in [:parameters.size] do
    let formal := parameters[index]!
    let expectedType ← instantiateMVars (← inferType formal)
    let selectedOverrides := overrides.filter (·.1 == index)
    let templates ← match selectedOverrides with
      | #[] => capturedParameterData h trace #[formal]
      | #[(_, original)] => do
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType original.value) expectedType <&&> isDefEq original.value formal) do
          throwError "the retained declaration slot changed its complete selected operand"
        unless !(← isProp expectedType) do
          throwError "a proof parameter cannot carry a computational occurrence"
        pure #[ActionDataTemplate.wire .parameter original]
      | _ => throwError "the declaration slot has several retained operand occurrences"
    -- Explicit object/retained roles and a current scalar value interface
    -- belong to their producers. Only a generic parameter slot may request a
    -- whole-map observation from its independently declared Hom input type.
    let templates ← if (Language.homEnds? expectedType).isSome then
      templates.mapM fun template => match template with
        | .wire .parameter original => do
            if (← retainedValueResultInterface? original).isSome then pure template
            else pure (.wire .map original)
        | _ => pure template
      else pure templates
    result := result.push { formal, expectedType, templates }
  for (index, _) in overrides do
    unless index < parameters.size do
      throwError "the retained declaration operand lies outside its selected telescope"
  return result

/-- All supported callable producers use this same captured invocation. The
existing OperationObservation is retained directly when that port owns dispatch;
its original Wire predates this attachment, so no recursive cycle is introduced. -/
partial def captureSelectedCallable (h : Harness) (trace : Trace) (wire : Wire)
    (address : String) (application : Expr)
    (parameters : Array SelectedCallableParameter) (descriptor : ActionDataTemplate)
    (invocationParameters : Array ActionDataTemplate)
    (context? : Option CategoryContext := none)
    (endpoints? : Option (CallableEndpointData × CallableEndpointData) := none)
    (inverse : Option Bool := none) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let some operation := state.operation? address
    | throwError "the captured callable has no accepted operation address"
  discard <| StructuredResult.checkReconstruction application
  if let some (declaration, _) := state.callable? address then
    let selected := operationApplicationBody application
    unless selected.getAppFn.constName? == some declaration do
      throwError "the captured callable changed its complete registered declaration"
    let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
      fields.mapM (·.fvarId!.getBinderInfo)
    unless selected.getAppNumArgs == infos.size do
      throwError "the captured callable lost its complete declaration application"
    let explicit := (selected.getAppArgs.zip infos).filterMap fun (value, info) =>
      if info.isExplicit then some value else none
    unless explicit.size == parameters.size do
      throwError "the captured callable lost an ordered declaration parameter"
    for (formal, retained) in explicit.zip parameters do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType formal) retained.expectedType <&&>
            isDefEq formal retained.formal) do
        throwError "the captured callable changed a complete declaration parameter"
  let (data, _) ← renderCapturedActionData descriptor
  unless data == wire.fragment do
    throwError "the callable producer changed its original descriptor occurrences"
  if let .operation entry := operation then
    unless endpoints?.isNone && inverse.isNone do
      throwError "the declared operation changed its selected whole-domain invocation role"
    let occurrences ← parameters.mapM fun parameter => do
      let rendered ← parameter.templates.mapM renderCapturedActionData
      pure ({
        formal := parameter.formal, expectedType := parameter.expectedType,
        templates := parameter.templates, data := rendered.map Prod.fst,
        dependencies := rendered.foldl (fun inputs item => inputs ++ item.2) #[] } :
          OperationParameterOccurrence)
    let owner ← realizedOperationOwner h trace entry (operationApplicationBody wire.value)
    let request ← prepareOperationObservation h trace wire entry.id (parameters.map (·.formal))
      (some owner) (initialParameters := some occurrences)
    let context ← completedCallableContext wire request.domainWire request.targetWire
    return ← retainSelectedCallableInvocation h wire {
      address, application, formal := wire.value, fragment := wire.fragment, context
      declarationParameters := parameters, descriptor, parameters := invocationParameters
      source := request.domainWire, target := request.targetWire
      sourceOrigin := .retained, targetOrigin := request.targetOrigin
      argument := request.argument, inverse, operationRequest := some request }
  let (source, target) ← match Language.homEnds? (← inferType wire.value) with
    | some endpoints => pure endpoints
    | none =>
      let signature ← whnfR (← inferType wire.value)
      unless signature.isForall && !signature.bindingBody!.hasLooseBVars do
        throwError "the captured callable has no independently fixed complete endpoints"
      pure (signature.bindingDomain!, signature.bindingBody!)
  let context ← match context? with
    | some context => pure context
    | none =>
      let some category := state.categories.find? (·.id == wire.form.category)
        | throwError "the captured callable lost its registered complete category"
      CategoryContext.ofNamed category source
  CategoryContext.checkMorphism context wire.value source target
  let (source, target) ← match endpoints? with
    | some endpoints => pure endpoints
    | none => pure (
        ← realizeCallableEndpointWithOrigin h trace wire source true (some context),
        ← realizeCallableEndpointWithOrigin h trace wire target false (some context))
  CategoryContext.checkMorphism context wire.value source.wire.value target.wire.value
  let argument ← selectedCallableIdentity context source.wire
  retainSelectedCallableInvocation h wire {
    address, application, formal := wire.value, fragment := wire.fragment, context
    declarationParameters := parameters, descriptor, parameters := invocationParameters
    source := source.wire, target := target.wire
    sourceOrigin := source.origin, targetOrigin := target.origin
    argument, inverse }

/-- The descriptor's declaration application is checked independently of data.
Only its producer-declared parameter slots can later request observation. -/
partial def capturedEdgeData (h : Harness) (trace : Trace) (edge : EdgeRef)
    (actual : Expr) : TermElabM ActionDataTemplate := do
  let state ← registryState
  checkExecutableEdgeAction state edge (← Semantic.asFunctor actual)
  if let .constructMap constructor inner := edge then
    let original ← constructorActionArgument state constructor actual
    return .ctor "constructorMap" #[.literal { json := toJson constructor.raw },
      ← capturedEdgeData h trace inner original]
  let parameters ← actionDeclarationParameters state edge actual true
  let data ← capturedParameterData h trace parameters
  match edge with
  | .functor id => return .ctor id.raw data
  | .classifierForget id =>
    return .ctor "classifierForget"
      #[.literal { json := toJson id.raw }, .array data]
  | _ => unreachable!

/-- Observe an already captured parameter occurrence through existing typed
owners. The ordinary parameter demand policy remains distinct from a whole-map
observation; inert element/admission context is not scanned for action tags. -/
partial def observeActionDataWire (h : Harness) (trace : Trace)
    (role : ActionDataRole) (wire : Wire) : TermElabM Wire := do
  if !h.demandObjectActions then return wire
  match role with
  | .retained => return wire
  | .object => realizeObjectObservation h trace wire
  | .map => realizeArrowObservation h trace wire
  | .parameter =>
      if (← retainedValueResultInterface? wire).isSome then
        return ← realizeValueObservation h trace wire
      if let some captured ← retainedCapturedInvocation? wire then
        return ← observeCapturedInvocation h trace wire captured
      let wire ← realizeValueObservation h trace wire
      let wire ← match ← trace.node? wire.value with
        | some (.operationApply ..) | some (.operationPoint ..) |
            some (.operationEquivalence ..) => realizeArrowObservation h trace wire true
        | some (.morphismTransport ..) | some (.constructionMap ..) |
            some (.contextualRoute _ _ _ _ _ true) => realizeArrowObservation h trace wire
        | _ => pure wire
      realizeObjectObservation h trace wire

partial def realizedParameterData (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array DataOwnership.Data × Array Wire) := do
  let templates ← capturedParameterData h trace parameters
  let rendered ← templates.mapM (renderActionDataWith (observeActionDataWire h trace))
  return (rendered.map Prod.fst, rendered.foldl (fun result child => result ++ child.2) #[])

partial def realizedObjectParameterData? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option (DataOwnership.Data × Array Wire)) := do
  let some wire ← capturedObjectParameter? h trace value | return none
  return some (← renderActionDataWith (observeActionDataWire h trace) (.wire .object wire))

partial def realizedRetainedParameterData? (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Option (DataOwnership.Data × Array Wire)) := do
  let some wire ← capturedRetainedParameter? h trace value | return none
  return some (← renderActionDataWith (observeActionDataWire h trace) (.wire .object wire))

partial def realizedEdgeData (h : Harness) (trace : Trace) (edge : EdgeRef)
    (actual : Expr) : TermElabM (DataOwnership.Data × Array Wire) := do
  renderActionDataWith (observeActionDataWire h trace) (← capturedEdgeData h trace edge actual)

/-- Use the shared recursive observer while the complete action executor remains independent. -/
partial def executeObjectAction (h : Harness) (trace : Trace) (operation : String)
    (action : Expr) (original template : Wire) (parameters : Array Json)
    (dependencies : Array Wire) (parameterOwnership : DataOwnership.Table := #[])
    (requestInputPaths : Option (Array (DataOwnership.Path × Nat)) := none) :
    TermElabM Wire :=
  executeObjectActionWith (realizeObjectObservation h trace) h operation action original template
    parameters dependencies parameterOwnership requestInputPaths

/-- The complete selected action determines both full contexts. Named target
schemas affect the registration address only; they never supply a dictionary. -/
partial def objectActionTemplate (h : Harness) (trace : Trace) (edge : EdgeRef)
    (action : Expr) (original : Wire) (encoder? : Option ScopedActionEncoder := none) :
    TermElabM (Wire × DataOwnership.Data × Array Wire) := do
  let state ← registryState
  let some source := state.selectedEdgeSource? edge
    | throwError "the executable action lost its registered source"
  let some target := state.selectedEdgeTarget? edge
    | throwError "the executable action lost its registered target"
  let action ← Semantic.asFunctor action
  let (sourceBundle, targetBundle) ← functorCategoryBundles action
  let sourceContext : CategoryContext := { expression := source, bundle := sourceBundle }
  CategoryContext.checkObject sourceContext original.value
  discard <| framingContext (some sourceContext) original.categoryContext
  let value ← Semantic.objOf action original.value
  let context : CategoryContext := { expression := target, bundle := targetBundle }
  CategoryContext.checkObject context value
  let (descriptor, dependencies) ← match encoder? with
    | some encoder => encoder edge action
    | none => realizedEdgeData { h with demandObjectActions := true } trace edge action
  let form := match imageCategory? state target with
    | some category => imageForm state edge category
    | none => .contextual target original.form
  let data ← scopedNode "functorAction" #[descriptor, original.fragment]
  return ({
    form, payload := (← combinedRecipePayload value data (#[original] ++ dependencies))
    categoryContext := some context
    objectIso := (← mapObjectComparison action original.value original.objectIso)
    endpointPresentation := (← mapEndpointPresentation action descriptor.json
      original.endpointPresentation descriptor.ownership)
  }, descriptor, dependencies)

/-- A primitive action executes at its own boundary. The only intrinsic object
case reads a mathematically checked projection from actual complete record fields.
All other actions need their own admitted implementation, never a target decoder. -/
partial def executeObjectEdge (h : Harness) (trace : Trace) (edge : EdgeRef)
    (action : Expr) (original : Wire) (encoder? : Option ScopedActionEncoder := none) :
    TermElabM Wire := do
  let state ← registryState
  discard <| Semantic.objOf action original.value
  let action ← instantiateMVars (← Semantic.asFunctor action)
  checkExecutableEdgeAction state edge action
  let original ← realizeObjectObservation h trace original
  if let .proofRefinement _ classifier _ := original.form then
    if edge == .classifierForget classifier then return ← proofRefinementBase trace original action
  let (template, descriptor, dependencies) ← objectActionTemplate h trace edge action original encoder?
  if let some projected ← intrinsicObjectEdgeData? trace edge action original template.value descriptor then
    let actual := { template with
      payload := (← scopedPayload template.value projected),
      objectObserved := true }
    return ← retainMappedEndpointPresentation (.edge edge) action original actual (.literal descriptor)
  let (operation, parameters) ← edgeActionDataInvocation state edge descriptor false
  let actual ← executeObjectAction h trace operation action original template (parameters.map (·.json)) dependencies
    (DataOwnership.Data.array parameters).ownership
  retainMappedEndpointPresentation (.edge edge) action original actual (.literal descriptor)

/-- Execute a prescribed composite in categorical order, retaining and reusing
each actual intermediate image. No failed primitive chooses a different route. -/
partial def executeObjectRoute (h : Harness) (trace : Trace) (original : Wire)
    (route : Array EdgeRef) (applications : Array Expr) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the executable route lost an ordered complete action"
  let mut result := original
  for (edge, action) in route.zip applications do
    result ← executeObjectEdge h trace edge action result
  return result

/-- A returned complete map owns its actual endpoint fields. Otherwise the
independently selected signature supplies the endpoint before action execution.
No named object with an equal carrier replaces an existing endpoint packet. -/
partial def actionMapEndpoint (h : Harness) (trace : Trace) (original : Wire)
    (context : Option CategoryContext) (formal : Expr) (source : Bool) : TermElabM Wire := do
  let context ← framingContext context original.categoryContext
  if let some context := context then CategoryContext.checkObject context formal
  if let some endpoint ← retainedCallableEndpoint? original formal source context then
    return endpoint
  if let some endpoint ← retainedActionEndpoint? original context formal source then
    return endpoint
  let .ok data := ComputationalData.valuePayload original.json
    | throwStratum .malformed "the complete callable has an invalid computational envelope"
  let tag := (data.getObjValAs? String "ctor").toOption.getD ""
  if original.completedData || #["typedMap", "identity", "zero", "compose", "map"].contains tag then
    let some (left, right) := Language.homEnds? (← inferType original.value)
      | throwError "the complete callable lost its independently selected hom signature"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq formal (if source then left else right)) do
      throwError "the callable endpoint differs from its complete selected signature"
    if let some context := context then
      CategoryContext.checkMorphism context original.value left right
    discard <| checkedFragment original.fragment.validate
    let recoverFormal := !original.completedData
    let .ok projection ← ComputationalData.interfaceEndpointDataWithOrigin #[] original.value
        original.fragment source recoverFormal
      | throwStratum .malformed "the complete callable lost its retained endpoint data"
    if projection.origin == .action then
      if original.completedData then
        return { (← callableEndpointReference original formal source context) with objectObserved := true }
      throwStratum .noImplementation
        "the deferred callable endpoint has no retained typed action producer"
    let endpoint := projection.data
    let completed := original.completedData && projection.origin == .projection
    if let .error message ← ComputationalData.validatePort formal (← inferType formal)
        endpoint.json then
      throwStratum .malformed m!"the source map has an incompatible complete endpoint: {message}"
    let state ← registryState
    let form ← match context with
      | some context => pure (contextualForm state context original.form)
      | none =>
        let some category := state.categories.find? (·.id == original.form.category)
          | throwError "the callable endpoint lost its complete registered category"
        pure (.diagrams category)
    -- A complete endpoint keeps its own actual data. Portable endpoint fields
    -- need no unrelated opaque callable owner, even inside a composed map.
    return {
      form
      payload := (← scopedPayload formal endpoint completed)
      categoryContext := context
      objectObserved := completed }
  let endpoint ← realizeCallableEndpoint h trace original formal source context
  realizeObjectObservation h trace endpoint

/-- Supply complete recursive endpoint observation to the independent map executor. -/
partial def executeMapAction (h : Harness) (trace : Trace) (operation : String)
    (action : Expr) (sourceContext targetContext : CategoryContext)
    (original template : Wire) (descriptor : Json) (parameters : Array Json)
    (dependencies : Array Wire) (objectImage : Wire → TermElabM Wire)
    (descriptorOwnership : DataOwnership.Table := #[])
    (parameterOwnership : DataOwnership.Table := #[])
    (endpoint? : Option ActionEndpointReader := none)
    (imageEndpoints : Option (Wire × Wire) := none)
    (requestInputPaths : Option (Array (DataOwnership.Path × Nat)) := none) : TermElabM Wire :=
  executeMapActionWithEndpoints (endpoint?.getD (actionMapEndpoint h trace))
    (fun input source target context => frameObservedMorphism h trace input source target context)
    h operation action sourceContext
    targetContext original template descriptor parameters dependencies objectImage
    descriptorOwnership parameterOwnership imageEndpoints requestInputPaths

/-- Read complete endpoints from an actual callable or a producer's exact
framing origin. Only initial preparation may consult the formal endpoint reader;
a new returned callable always projects its own packet with recovery disabled. -/
partial def capturedMapEndpoints (h : Harness) (trace : Trace) (wire : Wire)
    (context : CategoryContext) (returned : Bool := false) : TermElabM (Wire × Wire) := do
  let (source, target) ← contextualMorphismEndpoints context wire.value
  if let some left ← retainedCallableEndpoint? wire source true (some context) then
    let some right ← retainedCallableEndpoint? wire target false (some context)
      | throwError "the captured callable omitted one retained endpoint occurrence"
    return (left, right)
  if let some left ← retainedActionEndpoint? wire (some context) source true then
    let some right ← retainedActionEndpoint? wire (some context) target false
      | throwError "the captured map lost one of its ordered action endpoints"
    return (left, right)
  let retained := wire.pointDataInterface
  let tag := (wire.json.getObjValAs? String "ctor").toOption.getD ""
  let ownsEndpoints := returned || wire.completedData || retained.isSome ||
    #["typedMap", "identity", "zero", "compose", "map"].contains tag
  let endpoint := fun (formal : Expr) (isSource : Bool) => do
    if !ownsEndpoints then
      return ← realizeCallableEndpoint { h with demandObjectActions := false }
        trace wire formal isSource (some context)
    let (data, projected) ← match retained with
      | some selected => do
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq selected.domain source <&&> isDefEq selected.target target) do
            throwError "the captured point changed its independently selected endpoints"
          pure ((if isSource then selected.domainData else selected.targetData), true)
      | none => do
          let projection ← checkedFragment (← ComputationalData.interfaceEndpointDataWithOrigin
            #[] wire.value wire.fragment isSource false)
          if projection.origin == .action then
            if wire.completedData then
              let reference ← callableEndpointReference wire formal isSource (some context)
              pure (reference.fragment, true)
            else
              throwStratum .noImplementation
                "the deferred map endpoint has no retained typed action producer"
          else pure (projection.data, projection.origin == .projection)
    let completed := wire.completedData && projected
    if let .error message ← ComputationalData.validatePort formal (← inferType formal) data.json then
      throwStratum .malformed m!"the captured map has an incompatible complete endpoint: {message}"
    return ({
      form := contextualForm (← registryState) context wire.form
      payload := (← if completed then scopedPayload formal data else recipePayload formal data)
      categoryContext := some context
      objectObserved := completed } : Wire)
  return (← endpoint source true, ← endpoint target false)

/-- Supply initial endpoint capture to the shared intrinsic framing owner. -/
partial def captureCompleteCallable (h : Harness) (trace : Trace) (input : Wire)
    (context : CategoryContext) (endpoints : Option (Wire × Wire) := none)
    (publicFrame : Bool := true) : TermElabM Wire :=
  captureCompleteCallableWith
    (fun wire context => capturedMapEndpoints { h with demandObjectActions := false }
      trace wire context) input context endpoints publicFrame

/-- An original caller-supplied map can declare its endpoint occurrences before
it has a complete public frame. Once a producer or an explicit callable packet
owns that interface, its endpoints take precedence: a later formal lookup may
not replace them. The callback is used only at this initial declaration boundary;
capturing the frame neither observes its children nor asserts an action ran. -/
partial def captureDeclaredCallableInput (h : Harness) (trace : Trace) (input : Wire)
    (context : CategoryContext) (declared : Unit → TermElabM (Wire × Wire)) :
    TermElabM Wire := do
  let retained := input.callableEndpoints.isSome || input.morphismFraming.isSome ||
    input.pointDataInterface.isSome || input.actionRecipe.isSome ||
    input.intrinsicAssembly.isSome || input.capturedInvocation.isSome || input.morphismFramed
  let some body := ComputationalData.recordPayload? input.fragment
    | throwStratum .malformed "the declared callable has a malformed transparent envelope"
  let encoded := match ComputationalData.envelope body.json with
    | .ok (tag, _) => #["typedMap", "arrow", "identity", "zero", "compose", "map"].contains tag
    | .error _ => false
  if retained || encoded then return ← captureCompleteCallable h trace input context
  let (source, target) ← declared ()
  let source ← captureDeclaredObjectInput source context
  let target ← captureDeclaredObjectInput target context
  CategoryContext.checkMorphism context input.value source.value target.value
  checkDataOwners h source.fragment
  checkDataOwners h target.fragment
  let input ← retainCallableEndpoints input source target context
  let result ← captureCompleteCallable h trace input context (some (source, target))
  return { result with serviceHandles := result.serviceHandles ++
    (← retainServiceOperands h #[input, source, target]) }

/-- Whole-map reads convert only an explicit native point interface. Raw
intrinsic maps retain their producer and are framed by the caller's typed step. -/
partial def capturePointCallable (h : Harness) (trace : Trace) (input : Wire)
    (context : CategoryContext) : TermElabM Wire :=
  capturePointCallableWith
    (fun wire context => capturedMapEndpoints h trace wire context true) input context

/-- Ordinary observation consumes the assembly selected by the current Wire.
The invocation owner retains that exact input; it does not authenticate a second
copy of the same assembly before observing its canonical preparation. -/
partial def observeCurrentIntrinsicAssembly (h : Harness) (trace : Trace) (wire : Wire)
    (registeredOnly : Bool := false) : TermElabM Wire := do
  let h := { h with demandObjectActions := true }
  if !registeredOnly then
    if let some prepared ← currentIntrinsicInvocationReference? h trace wire then
      return ← observePreparedInvocation h trace prepared
  observeCurrentIntrinsicAssemblyWith
    (fun role input => match role with
      | .map => realizeArrowObservation h trace input registeredOnly
      | _ => observeActionDataWire h trace role input)
    (fun input context => capturedMapEndpoints h trace input context true) h wire

/-- A separately supplied assembly remains a checked adapter. Ordinary object,
map and value consumers use their current Wire's assembly directly. -/
partial def observeIntrinsicAssembly (h : Harness) (trace : Trace) (wire : Wire)
    (assembly : IntrinsicAssembly) (registeredOnly : Bool := false) : TermElabM Wire := do
  let h := { h with demandObjectActions := true }
  -- Restricted preparation may retain pending children. It neither reads nor
  -- installs an unrestricted completion in the actual invocation owner.
  if !registeredOnly then
    if let some prepared ← intrinsicInvocationReference? h trace wire assembly then
      let some captured := prepared.capturedInvocation
        | throwError "the intrinsic preparation omitted its retained invocation"
      return ← observeCapturedInvocation h trace prepared captured
  observeIntrinsicAssemblyWith
    (fun role input => match role with
      | .map => realizeArrowObservation h trace input registeredOnly
      | _ => observeActionDataWire h trace role input)
    (fun input context => capturedMapEndpoints h trace input context true) h wire assembly

/-- A scalar result is observed through its retained typed producer. It is
neither an object nor a map, and no category is inferred from its carrier. -/
partial def realizeValueObservation (h : Harness) (trace : Trace) (wire : Wire) :
    TermElabM Wire := do
  if wire.actualData then return wire
  if let some captured ← retainedCapturedInvocation? wire then
    if let .value _ := captured.interface.result then
      return ← observeCapturedInvocation h trace wire captured
    return wire
  unless (← retainedIntrinsicValueAssembly? wire).isSome do return wire
  observeCurrentIntrinsicAssembly h trace wire

/-- Demand one selected comparison direction through the same complete typed
reader used by request preparation and private prospective inspection. -/
partial def observeEndpointPresentation (h : Harness) (trace : Trace) (wire : Wire)
    (forward : Bool) (context : Option CategoryContext := none) : TermElabM Wire := do
  let some presentation := wire.endpointPresentation | return wire
  let context ← framingContext context wire.categoryContext
  let context ← match context with
    | some context => pure context
    | none =>
      let some category := (← registryState).categories.find? (·.id == wire.form.category)
        | throwError "the endpoint comparison lost its complete registered category"
      CategoryContext.ofNamed category wire.value
  let reader : CallablePreparationReader := {
    observe := fun context comparison => do
      let observed ← realizeArrowObservation { h with demandObjectActions := true } trace comparison
      capturePointCallable h trace observed context }
  let some selected ← prepareEndpointComparisonWith reader context wire forward
    | return wire
  let maps ← endpointPresentationMaps wire context presentation
  let maps := if forward then (selected.comparisonMap, maps.2) else (maps.1, selected.comparisonMap)
  let presentation := { presentation with
    forward := maps.1.json, backward := maps.2.json,
    forwardOwnership := maps.1.ownership, backwardOwnership := maps.2.ownership,
    maps := some maps }
  return { wire with
    endpointPresentation := some presentation,
    serviceHandles := wire.serviceHandles ++
      (← retainServiceOperands h #[selected.original, selected.comparisonMap]) }

/-- Computational framing observes exact retained comparison directions even
when an earlier frame preserved the same bytes. Whole output interfaces keep
already consumed comparisons distinct from still pending framing producers. -/
partial def frameObservedMorphism (h : Harness) (trace : Trace) (input source target : Wire)
    (context : Option CategoryContext := none) : TermElabM Wire := do
  let selected ← framingContext context input.categoryContext
  let context ← completedCallableContext input source target
  discard <| framingContext (some context) selected
  let reader : CallablePreparationReader := {
    observe := fun context wire => do
      let actual ← realizeArrowObservation { h with demandObjectActions := true } trace wire
      capturePointCallable h trace actual context
    observeData := observeActionDataWire { h with demandObjectActions := true } trace }
  let prepared ← match input.morphismFraming with
    | some frame => do
      unless sameCompleteWireContext frame.source source && sameCompleteWireContext frame.target target do
        throwStratum .unavailable "computational framing changed its retained complete endpoint occurrences"
      observeRetainedMorphismFrameWith reader input frame
    | none => prepareMorphismFrameWith reader context input source target
  let result := prepared.wire
  return { result with
    serviceHandles := result.serviceHandles ++ (← retainServiceOperands h prepared.dependencies) }

/-- Capture each complete map action before observing any selected primitive.
The original occurrence and endpoint frame remain attached to that exact step. -/
partial def captureMapRoute (h : Harness) (trace : Trace) (original : Wire)
    (route : Array EdgeRef) (applications : Array Expr) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the captured map route lost an ordered complete application"
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let mut result := original
  for (edge, application) in route.zip applications do
    let application ← instantiateMVars (← Semantic.asFunctor application)
    checkExecutableEdgeAction state edge application
    let some sourceExpression := state.selectedEdgeSource? edge
      | throwError "the captured map lost its complete source"
    let some targetExpression := state.selectedEdgeTarget? edge
      | throwError "the captured map lost its complete target"
    let (sourceBundle, targetBundle) ← functorCategoryBundles application
    let source : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let target : CategoryContext := { expression := targetExpression, bundle := targetBundle }
    let endpoints ← capturedMapEndpoints h trace result source
    let presented ← if result.pointDataInterface.isSome then pure result
      else presentMorphism result endpoints.1 endpoints.2 (some source)
    let inputData ← if let some selected := result.pointDataInterface then
      pointCallableFragment result endpoints.1.value endpoints.2.value selected
    else pure presented.fragment
    let descriptor ← capturedEdgeData h trace edge application
    let (data, dependencies) ← renderCapturedActionData descriptor
    let formal ← Semantic.mapOf application result.value
    let output : Wire := {
      form := contextualForm state target result.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map" #[data, inputData])
        (#[result, presented, endpoints.1, endpoints.2] ++ dependencies))
      morphismFramed := true
      categoryContext := some target }
    let captured ← retainActionInput true edge application result output descriptor (some endpoints)
    result ← retainActionImageEndpoints captured
  return result

/-- Direct constructions retain the same original map, endpoint occurrences
and parameter assembly as accepted structural routes. Their own registration
remains the only owner of the selected computation. -/
partial def captureConstructionMap (h : Harness) (trace : Trace) (formal : Expr)
    (selected : DirectConstruction.Action) (original : Wire) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let owner := ActionOwner.construction selected.entry.id selected.parameters
  let (source, target) ← actionOwnerContexts owner selected.functor original true
  let endpoints ← capturedMapEndpoints h trace original source
  let presented ← if original.pointDataInterface.isSome then pure original
    else presentMorphism original endpoints.1 endpoints.2 (some source)
  let inputData ← if let some interface := original.pointDataInterface then
    pointCallableFragment original endpoints.1.value endpoints.2.value interface
  else pure presented.fragment
  let descriptor := ActionDataTemplate.ctor selected.entry.id.raw
    (← capturedParameterData h trace selected.parameters)
  let (data, dependencies) ← renderCapturedActionData descriptor
  let some resultForm := (← registryState).constructionForm? selected.entry.id.raw
    | throwError "the captured construction map lost its complete result form"
  let output : Wire := {
    form := contextualForm (← registryState) target resultForm true
    payload := (← combinedRecipePayload formal (← scopedNode "map" #[data, inputData])
      (#[original, presented, endpoints.1, endpoints.2] ++ dependencies))
    morphismFramed := true, categoryContext := some target }
  let output ← retainRegisteredActionInput owner true selected.functor original output descriptor (some endpoints)
  retainActionImageEndpoints output

/-- Read only the parameter slots declared by the construction producer. -/
partial def capturedConstructionParameters (id : ConstructionId) (descriptor : DataOwnership.Data) :
    TermElabM (Array DataOwnership.Data) := do
  let .ok tag := descriptor.json.getObjValAs? String "ctor"
    | throwError "the captured construction lost its complete action descriptor"
  unless tag == id.raw do
    throwError "the captured descriptor belongs to a different construction"
  let .ok arguments := (descriptor.json.getObjVal? "args").bind (·.getArr?)
    | throwError "the captured construction lost its ordered action parameters"
  arguments.mapIdxM fun index _ =>
    checkedFragment (descriptor.project #[.field "args", .index index])

/-- Build the dependent construction's fixed image without observing its
source or selecting a port. Actual and prospective execution share this builder. -/
partial def capturedConstructionObjectTemplate (id : ConstructionId)
    (action : Expr) (target : CategoryContext)
    (descriptor : DataOwnership.Data) (dependencies : Array Wire) (input : Wire) :
    TermElabM Wire := do
  let state ← registryState
  let some resultForm := state.constructionForm? id.raw
    | throwError "the captured construction lost its complete image form"
  let value ← Semantic.objOf action input.value
  return {
    form := resultForm
    payload := (← combinedRecipePayload value (← scopedNode "functorAction"
      #[descriptor, input.fragment]) (#[input] ++ dependencies))
    categoryContext := some target
    objectIso := (← mapObjectComparison action input.value input.objectIso)
    endpointPresentation := (← mapEndpointPresentation action descriptor.json
      input.endpointPresentation descriptor.ownership) }

/-- Reuse the existing object executor at the dependent construction's own
registered address with already materialized captured parameters. -/
partial def executeCapturedConstructionObject (h : Harness) (trace : Trace)
    (id : ConstructionId) (action : Expr) (target : CategoryContext)
    (descriptor : DataOwnership.Data) (dependencies : Array Wire) (input : Wire) :
    TermElabM Wire := do
  let input ← realizeObjectObservation h trace input
  let parameters ← capturedConstructionParameters id descriptor
  let template ← capturedConstructionObjectTemplate id action target descriptor dependencies input
  executeObjectAction h trace id.raw action input template (parameters.map (·.json)) dependencies
    (DataOwnership.Data.array parameters).ownership

/-- Primitive map actions share the object-image executor. A composite is a
sequence of these complete actions, never a recipe delegated to its final user. -/
partial def executeMapRoute (h : Harness) (trace : Trace) (original : Wire)
    (route : Array EdgeRef) (applications : Array Expr)
    (encoder? : Option ScopedActionEncoder := none)
    (endpoint? : Option ActionEndpointReader := none)
    (imageEndpoints : Option (Wire × Wire) := none) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the executable map route lost an ordered complete action"
  if imageEndpoints.isSome && route.size != 1 then
    throwError "retained image endpoints belong to one exact selected action step"
  let state ← registryState
  let mut result := original
  for (edge, action) in route.zip applications do
    discard <| Semantic.mapOf action result.value
    let action ← instantiateMVars (← Semantic.asFunctor action)
    checkExecutableEdgeAction state edge action
    let some sourceExpression := state.selectedEdgeSource? edge
      | throwError "the executable map lost its complete registered source"
    let some targetExpression := state.selectedEdgeTarget? edge
      | throwError "the executable map lost its complete registered target"
    let (sourceBundle, targetBundle) ← functorCategoryBundles action
    let source : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let target : CategoryContext := { expression := targetExpression, bundle := targetBundle }
    let (descriptor, dependencies) ← match encoder? with
      | some encoder => encoder edge action
      | none => realizedEdgeData { h with demandObjectActions := true } trace edge action
    let (operation, parameters) ← edgeActionDataInvocation state edge descriptor true
    let formal ← Semantic.mapOf action result.value
    let template : Wire := {
      form := contextualForm state target result.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map" #[descriptor, result.fragment])
        (#[result] ++ dependencies))
      categoryContext := some target }
    result ← executeMapAction h trace operation action source target result template
      descriptor.json (parameters.map (·.json)) dependencies
      (fun original => executeObjectEdge h trace edge action original encoder?)
      descriptor.ownership (DataOwnership.Data.array parameters).ownership endpoint? imageEndpoints
  return result

/-- Execute only a current producer-owned step. Complete result dictionaries,
fragments and suppliers are checked before any selected parameter is observed. -/
partial def observeActionRecipe (h : Harness) (trace : Trace) (wire : Wire)
    (recipe : ActionRecipe) : TermElabM Wire := do
  checkActionRecipe wire recipe
  let h := { h with demandObjectActions := true }
  checkDataOwners h wire.fragment
  let original ← if recipe.morphism then realizeArrowObservation h trace recipe.original
    else realizeObjectObservation h trace recipe.original
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType original.value) (← inferType recipe.original.value) <&&>
        isDefEq original.value recipe.original.value) do
    throwError "observing an action input changed its complete selected source"
  discard <| framingContext (some recipe.source) original.categoryContext
  let (descriptor, dependencies) ← renderActionDataWith (observeActionDataWire h trace) recipe.descriptor
  let endpoint? : Option ActionEndpointReader ← if recipe.morphism then do
    let endpoints ← if sameCompleteWireContext original recipe.original then
      match recipe.endpoints with
      | some endpoints => pure endpoints
      | none => throwError "the captured map omitted its complete original endpoint occurrences"
    else capturedMapEndpoints h trace original recipe.source true
    let endpoint : ActionEndpointReader := fun current context formal source => do
      unless sameCompleteWireContext current original do
        throwStratum .unavailable "the selected map changed its captured complete source occurrence"
      let retained := if source then endpoints.1 else endpoints.2
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType retained.value) (← inferType formal) <&&>
            isDefEq retained.value formal) do
        throwError "the selected map changed a captured complete endpoint"
      discard <| framingContext context retained.categoryContext
      return retained
    pure (some endpoint)
  else pure none
  let imageEndpoints ← recipe.imageEndpoints.mapM fun (source, target) => do
    pure (← realizeObjectObservation h trace source, ← realizeObjectObservation h trace target)
  let actual ← match recipe.owner with
    | .edge selected => do
        let encoder : ScopedActionEncoder := fun edge action => do
          unless edge == selected && (← withoutModifyingState (withTransparency .all <|
              isDefEq (← inferType action) (← inferType recipe.application) <&&>
                isDefEq action recipe.application)) do
            throwError "the captured descriptor was requested by a different complete action"
          return (descriptor, dependencies)
        if recipe.morphism then
          executeMapRoute h trace original #[selected] #[recipe.application]
            (some encoder) endpoint? imageEndpoints
        else executeObjectEdge h trace selected recipe.application original (some encoder)
    | .construction id _ => do
        let some entry := (← registryState).constructions.find? (·.id == id)
          | throwError "the captured construction is no longer registered"
        let image := fun input => do
          let actual ← executeCapturedConstructionObject h trace id recipe.application
            recipe.target descriptor dependencies input
          retainMappedEndpointPresentation recipe.owner recipe.application input actual (.literal descriptor)
        if recipe.morphism then
          let parameters ← capturedConstructionParameters id descriptor
          executeMapAction h trace entry.mapAddress recipe.application recipe.source recipe.target
            original wire descriptor.json (parameters.map (·.json)) dependencies image
            descriptor.ownership (DataOwnership.Data.array parameters).ownership endpoint? imageEndpoints
        else image original
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType actual.value) (← inferType recipe.formal) <&&>
        isDefEq actual.value recipe.formal) do
    throwError "the observed action changed its complete retained result"
  discard <| framingContext (some recipe.target) actual.categoryContext
  let result ← forwardRetainedValue actual wire.value
  let result := { result with
    form := wire.form,
    actionRecipe := none,
    endpointPresentation := if recipe.morphism then result.endpointPresentation
      else wire.endpointPresentation <|> result.endpointPresentation }
  unless wire.value.hasMVar || wire.value.hasLevelMVar || wire.value.hasFVar || wire.value.hasLooseBVars do
    h.results.modify (·.insert wire.value result)
  return result

/-- Demand object-action data only at a computational boundary. Formal recipes
remain useful for interpretation and metadata; an unrelated target operation
never receives an unexecuted source action in place of its selected target data. -/
partial def realizeObjectObservation (h : Harness) (trace : Trace) (wire : Wire) :
    TermElabM Wire := do
  if wire.objectObserved || wire.actualData then return wire
  if let some origin := wire.endpointPresentation.bind (·.namedRefinement) then
    return ← materializeNamedRefinementWith (observeActionDataWire h trace) trace wire origin
  if let some captured ← retainedCapturedInvocation? wire then
    unless captured.interface.result.role == .object do
      throwError "an object observation cannot consume another declared result role"
    return ← observeCapturedInvocation h trace wire captured
  if (← retainedIntrinsicAssembly? wire .object).isSome then
    return ← observeCurrentIntrinsicAssembly h trace wire
  if let some recipe := wire.actionRecipe then
    if recipe.morphism then
      throwError "an object observation cannot consume a retained map-action role"
    return ← observeActionRecipe h trace wire recipe
  unless (wire.json.getObjValAs? String "ctor").toOption == some "functorAction" do return wire
  throwStratum .noImplementation
    "the pending object action has no retained typed producer occurrence"

/-- Choose an admitted computational representation of the already fixed full
operation. An exact source-form registration may implement the declared composite
in one call; a registration at the operation's owner receives every intervening
object action. Distinct admitted registrations remain peers. A single registration
address receives the complete transported packet when it accepts that packet.
No failed backend call selects a different implementation or changes meaning. -/
partial def computationalOperationReceiver (h : Harness) (trace : Trace) (operation : String)
    (original : Wire) (route : Array EdgeRef) (canonical : Wire) : TermElabM Wire := do
  let state ← registryState
  let some declared := state.operation? operation
    | throwError "the selected computational operation is no longer registered"
  -- Registered presentation prefixes remain useful to old operation implementations.
  -- The residual general action also supports arbitrary unnamed Arrow endpoints.
  let encoder := realizedEdgeData h trace
  let (prepared, remaining) ← canonicalOperationInput trace original route (some encoder)
    (some (capturedEdgeData h trace))
  unless canonical.form.id == prepared.form.id &&
      (← withTransparency .all <| isDefEq canonical.value prepared.value) do
    throwError "the operation input changed its independently normalized receiver"
  let transported ← computationalApexReceiver trace
    (← transportImage trace prepared remaining none (some encoder)
      (some (capturedEdgeData h trace)))
  -- Reuse the same prefix with its actual action parameters for source-composite
  -- registrations too; metadata-only callers cannot supply replacement data.
  let canonical ← computationalApexReceiver trace prepared
  let fullAddresses := state.inputAddresses declared transported.form
  let sourceAddresses := state.inputAddresses declared canonical.form
  let accepts := fun (input : Wire) (addresses : Array String) (deferred : Bool) (row : Admitted) =>
    row.registration.operation == operation && addresses.contains row.registration.input &&
      (deferred || (DataOwnership.owners input.ownership).all
        (fun owner => owner.1 == row.registration.backend))
  -- An executed action can export portable target data. The source owner's
  -- identity cannot silently remove a competing target registration before that
  -- boundary has run; the actual returned owner is checked again at dispatch.
  let deferred := !transported.objectObserved &&
    (transported.json.getObjValAs? String "ctor").toOption == some "functorAction"
  let mut candidates : Array (Wire × Registration) := #[]
  for row in h.admitted do
    if accepts transported fullAddresses deferred row then
      candidates := candidates.push (transported, row.registration)
    else if accepts canonical sourceAddresses false row then
      candidates := candidates.push (canonical, row.registration)
  match candidates with
  | #[(input, _)] => return input
  | #[] => return transported
  | _ =>
      let addresses := candidates.toList.map fun (_, row) =>
        s!"{row.input} by {row.backend}"
      throwStratum .ambiguousRealization m!"several admitted registrations compute \
        the selected composite {operation} ({addresses}); which one is used is a choice \
        the kernel does not make"

/-- A set formed as the extent of a subset literal (`Language.asObject`), where a set is
expected, is sent as that extent: the power object, its ambient set and the literal. -/
partial def extentFragment? (h : Harness) (trace : Trace) (p : Expr) :
    TermElabM (Option (DataOwnership.Data × Array Wire)) := do
  let some (.literal _ _) ← (trace.node? p : IO _) | return none
  let some (po, X, element) ← extentOf? (← registryState) p | return none
  let ambient ← realize h trace "the ambient set of an extent" X
  let literal ← realize h trace "the literal of an extent" element
  return some (← scopedNode "extent"
    #[{ json := toJson po.id.raw }, ambient.fragment, literal.fragment], #[ambient, literal])

/-- A declared callable endpoint is a data descriptor, not an observation of a
universal construction. The public structural product frame describes an actual
product type without demanding a cone computation. Named selected objects and
previously computed objects keep their exact presentations and live dependencies.
Only the formal type supplies this structural frame; no backend determines it. -/
partial def realizeEndpoint (h : Harness) (trace : Trace) (what : String)
    (value : Expr) (recoverAction : Bool := true) (recoverNamed : Bool := true) :
    TermElabM Wire := do
  let value ← instantiateMVars value
  unless ← stagedLiftNode trace value do
    if let some computed := (← h.results.get)[value]? then return computed
  let node ← trace.node? value
  let structural := match node with
    | some (.object ..) | some (.parameterTransport ..) | some (.retainedRoute ..) |
        some (.parameterEquivalence ..) | some (.functor ..) | some (.proofRefinement ..) |
        some (.operationEquivalence ..) |
        some (.construction ..) | some (.selectedLift ..) | some (.liftProjection ..) => false
    | _ => true
  if structural && (← whnfR (← inferType value)).isSort then
    let reduced ← withTransparency .all <| whnf value
    if reduced.isAppOfArity ``Prod 2 then
      let fields := reduced.getAppArgs
      let first ← realizeEndpoint h trace "the first declared endpoint component"
        fields[0]! recoverAction recoverNamed
      let second ← realizeEndpoint h trace "the second declared endpoint component"
        fields[1]! recoverAction recoverNamed
      let some category := (← registryState).categories.find? (·.id == CategoryId.sets)
        | throwError "the declared product endpoint has no set category"
      let context ← CategoryContext.ofNamed category value
      let template : ActionDataTemplate := .ctor "objectProduct"
        #[.wire .object first, .wire .object second]
      let (data, dependencies) ← renderCapturedActionData template
      let result : Wire := {
        form := .diagrams category
        payload := (← combinedRecipePayload value data dependencies)
        categoryContext := some context
        productComponents := #[first, second] }
      return ← retainIntrinsicAssembly result .object context template
  if node.isNone then discard <| Semantic.recordNamedObject value (some trace)
  if !recoverAction && (← trace.node? value).isNone then
    unless recoverNamed do
      throwStratum .noImplementation "the actual callable retains its own anonymous endpoint"
    -- A reduced endpoint can still be one uniquely accepted complete named
    -- object. Retained action provenance has priority, including ambiguity;
    -- this optional path must not choose between those source presentations.
    let hasRetainedAction ← try
      pure (← FunctorActionData.retainedParameterAction? trace value).isSome
    catch error =>
      if Exception.stratum? error == some .ambiguousRealization then pure true
      else throw error
    unless !hasRetainedAction && (← recordCompleteNamedObject trace value) do
      throwStratum .noImplementation "the endpoint has no separately selected computational presentation"
  realize h trace what value

/-- A complete callable supplies an endpoint descriptor even when that exact
object has no separately registered presentation. Only missing computation takes
this path; malformed values, unavailable owners and internal failures propagate. -/
partial def realizeCallableEndpointWithOrigin (h : Harness) (trace : Trace) (wire : Wire)
    (value : Expr) (source : Bool) (context : Option CategoryContext := none) :
    TermElabM CallableEndpointData := do
  let context ← framingContext context wire.categoryContext
  if let some context := context then CategoryContext.checkObject context value
  -- Current retained interfaces belong to this occurrence even before its
  -- computation completes. A formal cache entry cannot replace their fields.
  if let some endpoint ← retainedCallableEndpoint? wire value source context then
    return { wire := endpoint, origin := .retained }
  -- Actual callable/point data carries its own endpoint interface. A later
  -- expression-keyed cache entry is not a field of this returned occurrence.
  if wire.completedData then
    return { wire := ← actionMapEndpoint h trace wire context value source, origin := .retained }
  try
    -- A complete callable already fixes its anonymous endpoints. Only an exact
    -- retained or named presentation may replace that public endpoint descriptor;
    -- unrelated actions with an equal carrier do not select its presentation.
    -- Actual returned data fixes its own anonymous presentation. A newly found
    -- definitionally equal name cannot replace that computational endpoint.
    let recoverNamed := match wire.payload with | .ordinary .. => true | _ => false
    let endpoint ← realizeEndpoint h trace "the callable's complete selected endpoint"
      value false recoverNamed
    if let some context := context then
      discard <| framingContext (some context) endpoint.categoryContext
    return { wire := endpoint, origin := .retained }
  catch error =>
    unless !Exception.hasConflictingStrata error &&
        CasCatalogue.Exception.stratum? error == some .noImplementation do throw error
    return { wire := ← callableEndpointReference wire value source context, origin := .reference }

/-- Existing callers retain the endpoint-only interface. Rebuilders can also
retain which typed endpoint role the same producer selected. -/
partial def realizeCallableEndpoint (h : Harness) (trace : Trace) (wire : Wire)
    (value : Expr) (source : Bool) (context : Option CategoryContext := none) :
    TermElabM Wire := do
  return (← realizeCallableEndpointWithOrigin h trace wire value source context).wire

/-- Retain the independently selected complete endpoints of a callable before
placing it in another map expression. A symbolic point's scalar owner need not be
its selected coordinate, and an owned callable supplies data rather than a new
endpoint choice. The public typed-map frame keeps that original data unchanged. -/
partial def frameMorphismTemplate (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : Option CategoryContext := none) (pointAsMap : Bool := false) :
    TermElabM ActionDataTemplate := do
  let context ← framingContext context wire.categoryContext
  if let some context := context then
    CategoryContext.checkMorphism context wire.value source target
  if context.isNone then
    let type ← whnfR (← inferType wire.value)
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the callable lost its independently selected complete hom signature"
    let arguments := type.getAppArgs
    unless ← withTransparency .all <|
        isDefEq arguments[2]! source <&&> isDefEq arguments[3]! target do
      throwError "the callable changed its independently selected complete endpoints"
  if pointAsMap then
    if wire.pointDataInterface.isSome then
      let context ← match context with
        | some context => pure context
        | none =>
          let sourceWire ← realizeCallableEndpoint h trace wire source true
          let targetWire ← realizeCallableEndpoint h trace wire target false
          completedCallableContext wire sourceWire targetWire
      return .pointCallable context source target wire
  -- This flag records already applied endpoint presentations. Check the complete
  -- formal signature even on reuse, then preserve the already framed data.
  if wire.morphismFramed then return .wire .map wire
  let graph := wire.json.getArr?.isOk ||
    (wire.json.getObjValAs? String "ctor").toOption == some "finiteGraph"
  let state ← registryState
  let coordinatePoint ← if (wire.json.getObjValAs? String "ctor").toOption ==
      some "element" then
    withTransparency .all <| withoutModifyingState
      (isDefEq source (← closedElementDomain state))
  else pure false
  let needsPresentation := fun endpoint => do
    if let some actual := (← h.results.get)[endpoint]? then
      if actual.endpointPresentation.isSome then return true
    if let some (.object id _) ← trace.node? endpoint then
      return (state.objects.find? (·.id == id)).any (·.functorPresentation.isSome)
    return false
  unless coordinatePoint || graph || (← needsPresentation source) ||
      (← needsPresentation target) do return .wire .map wire
  for object in #[source, target] do
    if (← trace.node? object).isNone then
      discard <| Semantic.recordNamedObject object (some trace)
  let sourceWire ← realizeCallableEndpoint h trace wire source true context
  let targetWire ← realizeCallableEndpoint h trace wire target false context
  let presented ← if h.demandObjectActions then
      frameObservedMorphism h trace wire sourceWire targetWire context
    else presentMorphism wire sourceWire targetWire context
  if !graph && !coordinatePoint then return .wire .map presented
  let context ← completedCallableContext wire sourceWire targetWire
  let sourceView ← callableActualEndpoint context sourceWire true
  let targetView ← callableActualEndpoint context targetWire false
  return .ctor "typedMap" #[.wire .retained sourceView, .wire .retained targetView,
    .wire .map presented]

/-- Render the public frame from the exact typed producer selected above. -/
partial def frameMorphismFragment (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : Option CategoryContext := none) (pointAsMap : Bool := false) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  renderCapturedActionData (← frameMorphismTemplate h trace source target wire context pointAsMap)

/-- A whole callable used as one data value keeps its original complete Hom
interface. The existing framing owner applies endpoint presentations once;
this additional public frame only makes the retained endpoints explicit. -/
partial def completeCallableFragment (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : CategoryContext) :
    TermElabM (DataOwnership.Data × Array Wire) := do
  let (data, dependencies) ← frameMorphismFragment h trace source target wire
    (some context) (pointAsMap := true)
  let checkEndpoints (sourceData targetData : DataOwnership.Data) : TermElabM Unit := do
    let .ok _ := Backend.TypedMap.decode data.json
      | throwError "the complete callable lost its checked typed-map frame"
    let actualSource ← checkedFragment (data.project #[.field "args", .index 0])
    let actualTarget ← checkedFragment (data.project #[.field "args", .index 1])
    unless actualSource == sourceData && actualTarget == targetData do
      throwStratum .ambiguousRealization
        "the complete callable changed an actual scoped endpoint presentation"
  if let some selected := wire.pointDataInterface then
    -- The completed point, not a newly recovered name, owns these exact
    -- endpoint packets. The framing owner checked its full formal signature.
    checkEndpoints selected.domainData selected.targetData
    return (data, dependencies)
  let sourceWire ← realizeCallableEndpoint h trace wire source true (some context)
  let targetWire ← realizeCallableEndpoint h trace wire target false (some context)
  let dependencies := dependencies ++ #[sourceWire, targetWire]
  if (Backend.TypedMap.decode data.json).isOk then
    checkEndpoints sourceWire.fragment targetWire.fragment
    return (data, dependencies)
  return (← scopedNode "typedMap" #[sourceWire.fragment, targetWire.fragment, data],
    dependencies)

/-- Realization may name only a uniquely registered object at the complete
independently demanded type. It does not select a row by available computation. -/
partial def callableObjectPlan? (expected : Expr) :
    TermElabM (Option DeclaredAdmission.Plan) := do
  try DeclaredAdmission.resolve? CategoryId.sets expected
  catch error =>
    if Exception.interpretationKind error == .ambiguous then
      throwStratum .ambiguousRealization
        "the complete callable type has several registered object presentations"
    else throw error

/-- A function-wrapper projection is available only in the actual full Sets
category. A structured Hom never selects a function object by its carrier. -/
partial def callableHasSetsContext (context : CategoryContext) (source : Expr) :
    TermElabM Bool := withoutModifyingState do
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the callable data category is not registered"
  try
    let selected ← CategoryContext.ofNamed sets source
    withTransparency .all <| isDefEq context.bundle selected.bundle
  catch error =>
    if Exception.interpretationKind error == .invalid then pure false else throw error

/-- Prefer the exact full Hom object. Only the complete Sets dictionary permits
the declared one-data-field wrapper projection to its underlying function. -/
partial def wholeCallableObject (formal source target : Expr) (context : CategoryContext) :
    TermElabM DeclaredAdmission.Plan := do
  CategoryContext.checkMorphism context formal source target
  if let some owner ← callableObjectPlan? (← inferType formal) then return owner
  unless ← callableHasSetsContext context source do
    throwStratum .noImplementation
      "the complete structured Hom has no registered object for whole-callable observation"
  let functionType ← mkArrow source target
  let some function ← DeclaredAdmission.projectedValue? formal functionType
    | throwStratum .noImplementation "the Sets Hom has no complete declared function projection"
  let some owner ← callableObjectPlan? (← inferType function)
    | throwStratum .noImplementation "the complete function type has no registered object presentation"
  return owner

/-- Restage actual point data only through the existing registered comparison
with the language's global-point source. Other singleton objects are not given
that source's scalar convention or a fabricated computational inventory. -/
partial def pointAtAdmissionDomain (h : Harness) (trace : Trace) (wire : Wire)
    (source target domain : Expr) : TermElabM Wire := do
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the admitted point data category is not registered"
  let context ← CategoryContext.ofNamed sets source
  discard <| framingContext (some context) wire.categoryContext
  CategoryContext.checkMorphism context wire.value source target
  if ← withoutModifyingState (withTransparency .all <| isDefEq source domain) then
    return wire
  let one ← closedElementDomain (← registryState)
  unless ← withoutModifyingState (withTransparency .all <| isDefEq source one) do
    throwStratum .noImplementation
      "the admitted point has no accepted comparison from its original generalized domain"
  let comparison ← try
    (Language.operationPointComparison domain).run { trace := some trace }
  catch error =>
    if Exception.interpretationKind error == .ambiguous then
      throwStratum .ambiguousRealization
        "the admission domain has several accepted global-point comparisons"
    else throw error
  let some comparison := comparison
    | throwStratum .noImplementation "the admission domain has no accepted global-point comparison"
  let (_, _, inverse) ← (Language.constructionCoreMap comparison one domain).run
    { trace := some trace }
  -- This is a new point construction. Reuse the accepted comparison's
  -- declaration and positioned parameters, not an earlier completed map.
  let inverseWire ← realizeFresh h trace "the admission's actual inverse point-domain comparison" inverse
  unless ← withoutModifyingState (withTransparency .all <| isDefEq inverseWire.value inverse) do
    throwError "the admission changed its independently accepted point-domain comparison"
  let argument ← captureCompleteCallable h trace wire context
  let some (argumentDomain, argumentTarget) ← retainedCallableEndpoints? argument context
    | throwError "the admission lost its original complete point endpoint occurrences"
  let inverseContext ← CategoryContext.ofNamed sets domain
  let domainWire ← realizeEndpoint h trace "the admission's selected point domain" domain
  let some selected ← retainedSelectedCallableInvocation? inverseWire
    | throwError "the admission lost its selected registered comparison producer"
  let (data, dependencies) ← renderCapturedActionData selected.descriptor
  let original : Wire := {
    form := inverseWire.form
    payload := (← combinedRecipePayload inverseWire.value data dependencies)
    categoryContext := some inverseContext }
  -- The declaration's reduced endpoint can have a different expression key.
  -- Only this initial producer boundary selects the caller's actual domain;
  -- later callable reuse continues to retain the resulting complete receipt.
  let inverseWire ← captureSelectedCallable h trace original selected.address selected.application
    selected.declarationParameters selected.descriptor selected.parameters
    (some inverseContext)
    (some ({ wire := domainWire, origin := .retained },
      { wire := argumentDomain, origin := .retained })) selected.inverse
  let comparison ← captureCompleteCallable h trace inverseWire inverseContext
  let some (comparisonDomain, comparisonTarget) ← retainedCallableEndpoints? comparison inverseContext
    | throwError "the admission lost its accepted comparison endpoint occurrences"
  let comparisonTarget ← forwardRetainedValue comparisonTarget argumentDomain.value
  unless sameCompleteWireContext comparisonTarget argumentDomain do
    throwStratum .ambiguousRealization
      "the admission's point-domain comparison and original point have different complete endpoint occurrences"
  let actual ← StructuredResult.checkReconstruction
    (← mkAppM ``CategoryTheory.CategoryStruct.comp #[inverseWire.value, wire.value])
  CategoryContext.checkMorphism inverseContext actual domain target
  let template : ActionDataTemplate := .ctor "typedMap"
    #[.wire .object comparisonDomain, .wire .object argumentTarget,
      .ctor "compose" #[.wire .map comparison, .wire .map argument]]
  let (data, dependencies) ← renderCapturedActionData template
  let result : Wire := {
    form := .canonicalMorphism sets
    payload := (← combinedRecipePayload actual data dependencies)
    categoryContext := some inverseContext
    -- Each complete constituent retains its own pending execution and exact
    -- frame. The composition consumes those frames without presenting again.
    morphismFramed := true
    serviceHandles := (← retainLiftOperands h dependencies) }
  let result ← retainIntrinsicAssembly result .map inverseContext template
    #[{ context := inverseContext, source := comparisonDomain, target := comparisonTarget,
        callable := comparison },
      { context, source := argumentDomain, target := argumentTarget, callable := argument }]
    #[(comparisonTarget, argumentDomain)]
  retainCallableEndpoints result comparisonDomain argumentTarget inverseContext

/-- Instantiate the already selected callable object at its original endpoint
slots. Local slots retain declaration positions even when the two actual formal
objects coincide; substituting them never selects an equal carrier or packet. -/
partial def wholeCallableOwnerParameters (wire : Wire) (source target : Expr)
    (context : CategoryContext) (owner : DeclaredAdmission.Plan)
    (sourceWire targetWire : Wire) :
    TermElabM (DeclaredAdmission.Plan × Array (Nat × Wire)) := do
  CategoryContext.checkMorphism context wire.value source target
  let fullHom ← context.hom source target
  let full := ← withoutModifyingState (withTransparency .all <|
    isDefEq owner.application.value fullHom)
  unless full do
    unless ← callableHasSetsContext context source do
      throwStratum .noImplementation
        "the selected callable object has no full-context function projection"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq owner.application.value (← mkArrow source target)) do
      throwStratum .noImplementation
        "the selected callable object changed its original complete Hom"
  let carrier ← context.carrier
  let (application, slots) ← withLocalDeclD `sourceSlot carrier fun sourceSlot =>
    withLocalDeclD `targetSlot carrier fun targetSlot => do
      let expected ← if full then context.hom sourceSlot targetSlot
        else mkArrow sourceSlot targetSlot
      let application ← DirectConstruction.instantiate owner.entry.declaration #[]
      let some projections ← DeclaredAdmission.projectionPath? application.value expected
          (!owner.projections.isEmpty)
        | throwStratum .noImplementation
            "the retained callable object has no declared parameter interface for its endpoints"
      unless projections.size == owner.projections.size &&
          (projections.zip owner.projections).all (fun (a,b) =>
            a.structureName == b.structureName && a.field == b.field) do
        throwError "the retained callable object changed its selected projection"
      let application ← DirectConstruction.close application
      let slots := application.explicit.map fun argument =>
        if argument == sourceSlot then some true
        else if argument == targetSlot then some false else none
      let instantiate := fun (value : Expr) =>
        value.replaceFVars #[sourceSlot, targetSlot] #[source, target]
      let application : DirectConstruction.Application := {
        value := instantiate application.value
        arguments := application.arguments.map instantiate
        explicit := application.explicit.map instantiate }
      pure (application, slots)
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq application.value owner.application.value) do
    throwError "the retained callable object changed its complete selected owner"
  let application ← DirectConstruction.close application
  let sourceWire ← forwardRetainedValue sourceWire source
  let targetWire ← forwardRetainedValue targetWire target
  let overrides := (slots.zipIdx).filterMap fun (slot,index) =>
    slot.map (fun source => (index, if source then sourceWire else targetWire))
  return ({ owner with application }, overrides)

/-- Regard the actual whole callable as one point of its already selected full
function/Hom object. The constant formal point supplies only its type; every
computational byte and opaque occurrence still comes from the original wire. -/
partial def wholeCallablePoint (h : Harness) (trace : Trace) (wire : Wire)
    (source target domain : Expr) (context : CategoryContext)
    (owner : DeclaredAdmission.Plan) : TermElabM Wire := do
  CategoryContext.checkMorphism context wire.value source target
  let retainedTarget := (← h.results.get)[owner.application.value]?
  let complete ← captureCompleteCallable h trace wire context
  let some (sourceWire, targetWire) ← retainedCallableEndpoints? complete context
    | throwError "the whole callable lost its selected endpoint occurrences"
  let (owner, overrides) ← if retainedTarget.isSome then pure (owner, #[])
    else wholeCallableOwnerParameters wire source target context owner sourceWire targetWire
  let selected := owner.application.value
  let value ← if ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType wire.value) selected) then pure wire.value
    else do
      unless ← callableHasSetsContext context source do
        throwStratum .noImplementation
          "a structured Hom cannot be replaced by its erased carrier function"
      let some value ← DeclaredAdmission.projectedValue? wire.value selected
        | throwStratum .noImplementation
            "the whole callable has no data-only projection to its complete selected object"
      pure value
  let one ← closedElementDomain (← registryState)
  let function ← withLocalDeclD `point one fun point => mkLambdaFVars #[point] value
  let formal ← StructuredResult.checkReconstruction
    (← mkAppOptM ``TypeCat.ofHom #[some one, some selected, some function])
  let some sets := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the whole-callable point category is not registered"
  let pointContext ← CategoryContext.ofNamed sets one
  CategoryContext.checkMorphism pointContext formal one selected
  discard <| Semantic.recordNamedObject selected (some trace)
  let domainWire ← realizeEndpoint h trace "the whole-callable point's actual global domain" one
  let targetWire ← match retainedTarget with
    | some retained =>
        captureDeclaredObjectInput (← forwardRetainedValue retained selected) pointContext
    | none => do
        let parameters ← capturedCallableParameters h trace owner.application.explicit overrides
        let templates := parameters.flatMap (·.templates)
        realizeFreshWithParameters
          (fun _ _ requested => do
            unless requested == owner.application.explicit do
              throwError "the whole callable object changed its selected parameter positions"
            pure templates) h trace "the complete registered callable object" selected
  let template : ActionDataTemplate := .wire .map complete
  let (data, children) ← renderCapturedActionData template
  let dependencies := #[wire] ++ children ++ #[domainWire, targetWire]
  let point : Wire := {
    form := .canonicalMorphism sets
    payload := (← combinedRecipePayload formal data dependencies)
    categoryContext := some pointContext
    pointDataInterface := (← pointDataInterfaceAt one selected domainWire.fragment targetWire.fragment)
    serviceHandles := (← retainLiftOperands h dependencies) }
  let point ← retainIntrinsicAssembly point .map pointContext template #[] #[]
    (.retained, .retained)
  let point ← retainCallableEndpoints point domainWire targetWire pointContext
  pointAtAdmissionDomain h trace point one selected domain

/-- Execute a named object's published presentation only when its input parameters
already depend on actual computations. Ordinary named descriptors keep their
existing dispatch. The accepted comparison remains explicit on every later map. -/
partial def realizeObjectPresentation (h : Harness) (trace : Trace) (entry : ObjectEntry)
    (parameters : Array Expr) (data : Array DataOwnership.Data) (dependencies : Array Wire)
    (captured : Array ActionDataTemplate) :
    TermElabM (Option Wire) := do
  unless dependencies.any (fun wire => match wire.payload with
      | .ordinary .. => false | _ => true) do return none
  let some presentation ← ObjectPresentation.plan entry parameters (some trace) | return none
  let some published := entry.functorPresentation | unreachable!
  let state ← registryState
  let some functor := state.functor? published.functor | unreachable!
  if (← h.results.get)[presentation.argument]?.isNone then
    let mut sources : Array Wire := #[]
    for dependency in dependencies do
      if ← withoutModifyingState (withTransparency .all <|
          isDefEq dependency.value presentation.argument) then
        if !sources.any (fun other => other.json == dependency.json &&
            other.ownership == dependency.ownership) then
          sources := sources.push dependency
    if let #[source] := sources then
      h.results.modify (·.insert presentation.argument
        { source with payload := forwardPayload source presentation.argument source.json })
    else if sources.size > 1 then
      throwStratum .ambiguousRealization "the presentation argument has several actual supplied representations"
  discard <| realizeEndpoint h trace "the full registered presentation argument" presentation.argument
  let (image, _) ← Semantic.applyRegisteredFunctor functor presentation.argument #[] (some trace)
  let original ← realize h trace "the registered object presentation" image
  let actual ← transportImage trace original presentation.route (some presentation.applications)
    (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
  unless ← withTransparency .all <| isDefEq actual.value presentation.image do
    throwError "the computed object presentation changed its complete formal image"
  let rendered ← captured.mapM renderCapturedActionData
  unless rendered.map Prod.fst == data do
    throwError "the object presentation changed an original ordered parameter occurrence"
  let some category := state.categories.find? (·.id == entry.category)
    | throwError "the object presentation lost its complete registered category"
  let context ← CategoryContext.ofNamed category presentation.object
  let semanticTemplate := ActionDataTemplate.ctor entry.id.raw captured
  let (semanticData, semanticInputs) ← renderCapturedActionData semanticTemplate
  let semantic : Wire := {
    form := .object entry
    payload := (← combinedRecipePayload presentation.object semanticData semanticInputs)
    categoryContext := some context }
  let semantic ← retainIntrinsicAssembly semantic .object context semanticTemplate
  let retained ← actual.endpointPresentation.mapM (endpointPresentationMaps actual context)
  let initialTarget ← match retained with
    | some (forward, _) =>
      let some endpoints ← retainedCallableEndpoints? forward context
        | throwError "the original presentation lost its semantic endpoint occurrence"
      pure endpoints.1
    | none => pure actual
  let field := fun (selector : String) (source target : Wire) => do
    let formal ← ObjectPresentation.field entry selector parameters
    let template : ActionDataTemplate := .ctor "objectField"
      #[.literal { json := toJson entry.id.raw }, .literal { json := toJson selector },
        .array captured]
    let (data, inputs) ← renderCapturedActionData template
    let comparisonMap : Wire := {
      form := .canonicalMorphism category
      payload := (← combinedRecipePayload formal data inputs), categoryContext := some context,
      morphismFramed := true }
    let comparisonMap ← retainIntrinsicAssembly comparisonMap .map context template
    retainCallableEndpoints comparisonMap source target context
  let mut comparison ← mkAppM ``CategoryTheory.Iso.symm #[presentation.identification]
  let mut forward ← field "inversePresentation" semantic initialTarget
  let mut backward ← field "presentation" initialTarget semantic
  if let some (retainedForward, retainedBackward) := retained then
    let some selected := actual.endpointPresentation | unreachable!
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[comparison, selected.comparison]
    forward ← composeEndpointMaps context forward retainedForward
    backward ← composeEndpointMaps context retainedBackward backward
  let result : Wire := {
    form := .object entry
    payload := forwardPayload actual presentation.object actual.json
    objectObserved := actual.objectObserved
    serviceHandles := (← retainServiceOperands h dependencies) ++ actual.serviceHandles
    categoryContext := some context }
  -- This registered representation view preserves the exact image computation
  -- even when that image is still pending; a later named-object observation
  -- cannot restart it from the formal name.
  let result ← retainIntrinsicAssembly result .object context (.wire .object actual)
  return some (← retainEndpointPresentationMaps result context comparison forward backward)

/-- Execute exact accepted applications while retaining unnamed category contexts and
the original data owner. Both object and map actions use the same declared descriptors. -/
partial def contextualAction (h : Harness) (trace : Trace) (formal receiver : Expr)
    (source target : CategoryContext) (route : Array EdgeRef) (applications : Array Expr)
    (morphism : Bool) : TermElabM Wire := do
  unless route.size == applications.size do
    throwError "the contextual route omitted a complete selected application"
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let original ← realizeUnobserved h trace "the contextual action's complete original value" receiver
  discard <| framingContext (some source) original.categoryContext
  let mut currentContext := source
  let mut result := original
  for (step, application) in route.zip applications do
    let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state step)
    unless ← withTransparency .all <| isDefEq accepted application do
      throwError "the contextual action differs from its exact accepted declaration"
    let (sourceBundle, targetBundle) ← functorCategoryBundles application
    unless ← withTransparency .all <| isDefEq sourceBundle currentContext.bundle do
      throwError "a contextual action changed its complete source bundle"
    let some targetExpression := state.selectedEdgeTarget? step
      | throwError "a contextual action has no accepted target expression"
    let next : CategoryContext := {
      expression := targetExpression, bundle := (← instantiateMVars targetBundle) }
    if morphism then
      result ← captureMapRoute h trace result #[step] #[application]
    else
      CategoryContext.checkObject currentContext result.value
      let captured ← capturedEdgeData h trace step application
      let (descriptor, dependencies) ← renderCapturedActionData captured
      let projected ← projectObjectFragmentWithOrigin trace currentContext.expression step application
        result.value result.fragment (some descriptor)
      let data ← match projected with
        | some selected => pure selected.data
        | none => scopedNode "functorAction" #[descriptor, result.fragment]
      let completed := result.completedData && projected.any (·.isStructural)
      let value ← Semantic.objOf application result.value
      let output : Wire := {
        form := contextualForm state next result.form
        payload := (← if completed then scopedPayload value data
          else combinedRecipePayload value data (#[result] ++ dependencies))
        categoryContext := some next
        objectObserved := completed
        objectIso := (← mapObjectComparison application result.value result.objectIso)
        endpointPresentation := (← mapEndpointPresentation application descriptor.json
          result.endpointPresentation descriptor.ownership) }
      let selected ← if completed then pure output
        else retainActionInput false step application result output captured
      result ← retainMappedEndpointPresentation (.edge step) application result selected captured
    currentContext := next
  unless ← withTransparency .all <| isDefEq result.value formal <&&>
      isDefEq currentContext.bundle target.bundle do
    throwError "the contextual route changed its fixed result or full target bundle"
  unless currentContext.expression.syntacticEq target.expression do
    throwError "the contextual route changed its accepted target category expression"
  return { result with
    form := contextualForm state target original.form morphism
    payload := forwardPayload result formal result.json
    categoryContext := some target }

/-- Generic composition and selected action application retain the original full domain. -/
partial def contextualComposition (h : Harness) (trace : Trace) (formal : Expr)
    (context : CategoryContext) (first second source middle target : Expr) : TermElabM Wire := do
  let state ← registryState
  CategoryContext.checkMorphism context first source middle
  CategoryContext.checkMorphism context second middle target
  CategoryContext.checkMorphism context formal source target
  unless ← withTransparency .all <| isDefEq formal
      (← mkAppM ``CategoryTheory.CategoryStruct.comp #[first, second]) do
    throwError "the contextual composition changed its fixed categorical value"
  let a ← realize h trace "the complete first contextual map" first
  let b ← realize h trace "the complete second contextual map" second
  let (firstData, firstDependencies) ← frameMorphismFragment h trace source middle a (some context) (pointAsMap := true)
  let (secondData, secondDependencies) ← frameMorphismFragment h trace middle target b (some context) (pointAsMap := true)
  let selected ← match ← trace.node? second with
    | some (.cellComponent id params constructors inverse receiver) => do
      let some entry := state.cells.find? (·.id == id)
        | throwError "the selected component is no longer registered"
      let (parameters, dependencies) ← realizedParameterData h trace params
      let original ← realize h trace "the selected component's complete receiver" receiver
      let some inputForm := state.componentForm? (entry.componentAddress constructors)
        | throwError "the selected component has no admitted full input address"
      pure (some (entry.componentAddress constructors,
        #[DataOwnership.Data.array parameters, original.fragment, { json := toJson inverse }],
        dependencies.push original, inputForm))
    | some (.constructionMap id params _ _ _) => do
      if h.demandObjectActions then pure none
      else do
        let some entry := state.constructions.find? (·.id == id)
          | throwError "the selected construction is no longer registered"
        let (parameters, dependencies) ← realizedParameterData h trace params
        let some inputForm := state.constructionForm? entry.inputAddress
          | throwError "the selected construction has no complete input address"
        pure (some (entry.mapAddress, parameters, dependencies, inputForm))
    | some (.cartesian id params _ receiver "hom") => do
      let some entry := state.functor? id
        | throwError "the selected family reindexing is no longer registered"
      let (parameters, dependencies) ← realizedParameterData h trace params
      let original ← realize h trace "the cartesian map's original receiver" receiver
      let some inputForm := state.cartesianForm? entry.cartesianAddress
        | throwError "the cartesian map has no accepted complete input address"
      pure (some (entry.cartesianAddress, #[DataOwnership.Data.array parameters, original.fragment],
        dependencies.push original, inputForm))
    | _ => pure none
  let dependencies := #[a, b] ++ firstDependencies ++ secondDependencies
  if let some (operation, parameters, parameterWires, inputForm) := selected then
    let domainWire ← realizeEndpoint h trace "the contextual map's original domain" source
    let middleWire ← realizeEndpoint h trace "the contextual map's complete argument target" middle
    let targetWire ← realizeEndpoint h trace "the contextual map's complete result target" target
    let invocation : Backend.PointInvocation := {
      operation, parameters := parameters.map (·.json)
      arrow := secondData.json
      domain := domainWire.json
      source := middleWire.json
      target := targetWire.json
      argument := firstData.json }
    let input : Wire := {
      form := inputForm
      payload := (← combinedRecipePayload formal (← placedData invocation.encode #[
        (#[.field "args", .index 1], DataOwnership.Data.array parameters),
        (#[.field "args", .index 2], secondData),
        (#[.field "args", .index 3], domainWire.fragment),
        (#[.field "args", .index 4], middleWire.fragment),
        (#[.field "args", .index 5], targetWire.fragment),
        (#[.field "args", .index 6], firstData)])
        (dependencies ++ parameterWires ++ #[domainWire, middleWire, targetWire]))
      serviceHandles := (← retainServiceOperands h
        (dependencies ++ parameterWires ++ #[domainWire, middleWire, targetWire])) }
    let reply ← sendData h operation input (completeRequest := true)
    let answer := reply.data.json
    let backend := reply.backend
    let validation ← if ← withTransparency .all <| isDefEq source (← closedElementDomain state) then
      ComputationalData.validateElementAt target targetWire.json (← pointResultValue state formal) answer
    else ComputationalData.validateEndpointPort formal domainWire.json targetWire.json answer
    if let .error message := validation then malformed backend operation answer message
    let data ← receiveReplyData h operation reply true
    let returned : Wire := {
      form := contextualForm state context b.form true
      payload := .computed formal data
      morphismFramed := true
      pointDataInterface := (← pointInvocationInterface formal input.fragment)
      categoryContext := some context }
    return ← retainPointOrMapEndpoints returned domainWire targetWire
  let firstWire ← captureCompleteCallable h trace a context
  let secondWire ← captureCompleteCallable h trace b context
  let some (domainWire, firstTarget) ← retainedCallableEndpoints? firstWire context
    | throwError "the intrinsic contextual composition lost its first complete endpoints"
  let some (secondSource, targetWire) ← retainedCallableEndpoints? secondWire context
    | throwError "the intrinsic contextual composition lost its second complete endpoints"
  let template : ActionDataTemplate := .ctor "compose"
    #[.wire .map firstWire, .wire .map secondWire]
  let (data, inputs) ← renderCapturedActionData template
  let result : Wire := {
    form := contextualForm state context b.form true
    payload := (← combinedRecipePayload formal data inputs)
    morphismFramed := true
    categoryContext := some context }
  let result ← retainIntrinsicAssembly result .map context template #[]
    #[(firstTarget, secondSource)]
  retainCallableEndpoints result domainWire targetWire context

/-- Read the formal construction already attached to this exact parent. For a
pending invocation this uses its selected schema without asking it for data. -/
partial def capturedConstructionInterface (h : Harness) (trace : Trace) (parent : Wire)
    (receiver : Expr) : TermElabM (StructuredProjection.ConstructionPlan × Option StructuredResult.DataPlan) := do
  let context ← match parent.categoryContext with
    | some context => pure context
    | none =>
      let some category := (← registryState).categories.find? (·.id == parent.form.category)
        | throwError "the structured result lost its complete registered category"
      CategoryContext.ofNamed category receiver
  if let some assembly ← retainedIntrinsicAssembly? parent .object then
    if let .wire .object child := assembly.template then
      let forwarded ← forwardRetainedValue child parent.value
      if sameCompleteWireContext { forwarded with
          intrinsicAssembly := parent.intrinsicAssembly,
          capturedInvocation := parent.capturedInvocation } parent then
        return ← capturedConstructionInterface h trace child receiver
  let retained ← match ← retainedCapturedInvocation? parent with
    | some captured => pure (some captured)
    | none =>
      if let some captured := parent.capturedInvocation then
        let some record := (← h.invocations.get).find? (·.captured.occurrence == captured.occurrence)
          | throwStratum .unavailable "the structured result's original invocation scope has expired"
        let some actual := record.result
          | throwError "the structured result's retained invocation has not completed"
        let actual ← forwardRetainedValue actual parent.value
        unless sameCompleteWireContext actual parent do
          throwStratum .unavailable "the structured result changed its exact completed invocation occurrence"
        pure (some record.captured)
      else pure none
  if let some captured := retained then
    if let .structured selected := captured.interface then
      let diagram := if selected.creation.isSome then selected.sourceDiagram else selected.targetDiagram
      let cone ← mkAppM (if selected.row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[selected.formalPresentation]
      let construction : StructuredProjection.ConstructionPlan := {
        row := selected.row, lift := selected.creation.map (·.id), diagram,
        presentation := selected.formalPresentation, cone, apex := receiver, context }
      return (construction, some selected.plan)
  let some construction ← StructuredProjection.construction? receiver context (some trace)
    | throwStratum .invalid "the selected field has no independently retained construction"
  let plan ← if construction.lift.isSome then pure none else some <$> construction.dataPlan
  return (construction, plan)

/-- A constructor input role addresses a retained argument or one of its exact
endpoints. It never searches the result cache or locates an equal JSON packet. -/
partial def capturedUniversalRole (selected : SelectedStructuredInvocation)
    (role : StructuredResult.InputRole) : TermElabM Wire := do
  let inputs := if selected.creation.isSome then selected.sourceInputs else selected.imageInputs
  let position := match role with
    | .argument position | .source position | .target position => position
  let some input := inputs[position]?
    | throwError "the constructor schema lost an explicit input occurrence"
  let slot ← match role with
    | .argument _ => pure input.operand
    | .source _ =>
      let some endpoints := input.endpoints
        | throwError "the constructor schema selects an absent source endpoint"
      pure endpoints.1
    | .target _ =>
      let some endpoints := input.endpoints
        | throwError "the constructor schema selects an absent target endpoint"
      pure endpoints.2
  let some input := selected.operands[slot]?
    | throwError "the constructor schema points outside its captured input telescope"
  return input.wire

/-- Bind a formal constructor input to its declared original occurrence(s).
Repeated binder roles are retained together and checked after materialization. -/
partial def captureConstructionInput (h : Harness) (trace : Trace) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (binding : StructuredResult.DataBinder) (context? : Option CategoryContext := none) : TermElabM Wire := do
  let context := context?.getD construction.context
  let some formal := binding.formalValue
    | throwError "the selected constructor input has no fixed formal value"
  let result ← constructionResultInterface context formal (← inferType formal)
  let state ← registryState
  if let some captured ← retainedCapturedInvocation? parent then
    if let .structured selected := captured.interface then
      let originals ← binding.inputRoles.mapM (capturedUniversalRole selected)
      if let some first := originals[0]? then
        let first ← forwardRetainedValue first formal
        let inputOccurrences := binding.inputRoles.map fun role =>
          let (position, endpoint) := match role with
            | .argument position => (position, none)
            | .source position => (position, some true)
            | .target position => (position, some false)
          (position + (if selected.creation.isSome then 0 else selected.sourceInputs.size), endpoint)
        let mut original : Wire := {
          form := first.form,
          payload := (← combinedRecipePayload formal parent.fragment #[parent]),
          categoryContext := result.context? }
        let endpoints ← match result with
          | .map mapContext => do
              let complete ← captureCompleteCallable { h with demandObjectActions := false }
                trace first mapContext
              retainedCallableEndpoints? complete mapContext
          | _ => pure none
        if let some (source, target) := endpoints then
          original ← retainCallableEndpoints original source target context
        return ← retainCapturedInvocation h original (.projection {
          formal, fragment := parent.fragment, context, result, parent, construction, plan := some plan,
          port := none, inputOccurrences, endpoints })
  let inputs ← constructionInputFragments parent
  match selectedConstructionInput inputs formal with
  | .error message => throwStratum .ambiguousRealization message
  | .ok (some data) =>
    let form := match result with
      | .object context => contextualForm state context parent.form
      | .map context => contextualForm state context parent.form true
      | .value _ => parent.form
    let wire : Wire := {
      form, payload := (← scopedPayload formal data true),
      categoryContext := result.context?, serviceHandles := (← retainServiceOperands h #[parent]) }
    retainCompletedResultInterface wire result
  | .ok none =>
    -- This is still preparation of a formal input, never a returned-data decoder.
    discard <| Semantic.recordNamedObject formal (some trace)
    let original ← realizeUnobserved { h with demandObjectActions := false } trace
      "the constructor's fixed formal input" formal
    match result with
    | .value _ =>
        let wire : Wire := {
          form := original.form, payload := (← combinedRecipePayload formal original.fragment #[original]),
          serviceHandles := (← retainServiceOperands h #[original]) }
        retainIntrinsicResultAssembly wire result (.wire .parameter original)
    | _ => pure original

/-- A complete map may carry an opaque callable whose endpoint is exposed by
its public projection interface. Retain that map-field occurrence explicitly. -/
partial def captureConstructionEndpoint (h : Harness) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (formal : Expr) (source : Bool)
    (context : CategoryContext) : TermElabM Wire := do
  let some (domain, target) := Language.homEnds? port.expectedType
    | throwError "an endpoint projection requires a selected complete map port"
  let expected := if source then domain else target
  unless ← withoutModifyingState (withTransparency .all <| isDefEq expected formal) do
    throwError "the constructor endpoint changed its fixed formal role"
  let original : Wire := {
    form := contextualForm (← registryState) context parent.form,
    payload := (← combinedRecipePayload formal parent.fragment #[parent]),
    categoryContext := some context }
  retainCapturedInvocation h original (.projection {
    formal, fragment := parent.fragment, context := context, result := .object context,
    parent, construction, plan := some plan, port := some port, endpoint := some source })

/-- Constructor ports and endpoint binders are selected from one DataPlan. A
later field result cannot choose another parent, binder or full category. -/
partial def captureConstructionPort (h : Harness) (trace : Trace) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (ancestors : Array Nat := #[])
    (context? : Option CategoryContext := none) : TermElabM Wire := do
  let context := context?.getD construction.context
  let result ← constructionResultInterface context port.formalField port.expectedType
  let state ← registryState
  if ancestors.contains port.index then
    throwError "the accepted constructor data plan has cyclic endpoint ports"
  let ancestors := ancestors.push port.index
  let endpoint := fun (binder : Nat) => do
    let some binding := plan.binders[binder]?
      | throwError "the selected constructor field lost its endpoint binder"
    match binding.port with
    | some index =>
      let some selected := plan.ports[index]?
        | throwError "the endpoint binder points outside the selected data plan"
      captureConstructionPort h trace parent construction plan selected ancestors (some context)
    | none => captureConstructionInput h trace parent construction plan binding (some context)
  let endpoints ← match result with
    | .map mapContext => do
      let some (sourceValue, targetValue) := Language.homEnds? port.expectedType
        | throwError "the selected map result lost its declared endpoint types"
      let source ← match port.domainBinder with
        | some binder => endpoint binder
        | none => captureConstructionEndpoint h parent construction plan port sourceValue true mapContext
      let target ← match port.codomainBinder with
        | some binder => endpoint binder
        | none => captureConstructionEndpoint h parent construction plan port targetValue false mapContext
      CategoryContext.checkMorphism mapContext port.formalField source.value target.value
      pure (some (source, target))
    | _ => pure none
  let form := match result with
    | .object context => contextualForm state context parent.form
    | .map context => contextualForm state context parent.form true
    | .value _ => parent.form
  let original : Wire := {
    form,
    -- The private pending anchor is the parent's request data. It is not a
    -- fictitious cone or an already returned constructor field.
    payload := (← combinedRecipePayload port.formalField parent.fragment #[parent]),
    categoryContext := result.context? }
  let original ← match result, endpoints with
    | .map mapContext, some (source, target) => retainCallableEndpoints original source target mapContext
    | _, _ => pure original
  retainCapturedInvocation h original (.projection {
    formal := port.formalField, fragment := parent.fragment, context := context, result,
    parent, construction, plan := some plan, port := some port, endpoints })

/-- Project actual scoped data only after the exact captured parent has completed.
A returned field supplies neither a formal object nor a comparison cell. -/
partial def observeStructuredProjection (h : Harness) (trace : Trace) (_wire : Wire)
    (selected : SelectedStructuredProjection) : TermElabM Wire := do
  let parent ← realizeObjectObservation h trace selected.parent
  let .construction result _ := parent.payload
    | throwStratum .noImplementation "the structured projection has no complete returned construction"
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq result.diagram selected.construction.diagram) do
    throwError "the observed structured parent changed its selected formal diagram"
  if !selected.inputOccurrences.isEmpty then
    let retained ← h.serviceOperands.get
    let actual ← selected.inputOccurrences.mapM fun (position, endpoint) => do
      let some handle := parent.serviceHandles[position]?
        | throwError "the complete construction lost its original typed input handle"
      let some original := retained[handle]?
        | throwStratum .unavailable "the constructor input occurrence's owning scope has expired"
      let original ← match endpoint with
        | none => pure original
        | some source =>
          let some (domain, target) ← retainedCallableEndpoints? original selected.context
            | throwError "the complete constructor input lost its exact endpoint occurrences"
          pure (if source then domain else target)
      forwardRetainedValue original selected.formal
    let some first := actual[0]? | unreachable!
    unless actual.all (sameCompleteWireContext first) do
      throwStratum .noImplementation
        "one constructor binder has distinct actual input presentations without a selected comparison"
    match selected.result with
    | .value _ =>
        let wire : Wire := {
          form := first.form, payload := (← scopedPayload selected.formal first.fragment true),
          serviceHandles := (← retainServiceOperands h #[parent, first]) }
        return ← retainCompletedResultInterface wire selected.result
    | _ =>
        checkCapturedResultInterface first selected.result
        return first
  let diagramData ← checkedFragment (parent.fragment.project #[.field "args", .index 1])
  let packetData ← checkedFragment (parent.fragment.project #[.field "args", .index 2])
  let data ← match selected.port, selected.leg, result.packet with
    | some port, none, .direct _ =>
      checkedFragment (packetData.project #[.field "args", .index port.index])
    | some port, none, .created .. =>
      scopedNode "constructionField" #[{ json := toJson selected.construction.row.id.raw },
        diagramData, packetData, { json := toJson port.index }]
    | none, some _, _ =>
      let some index := selected.legData
        | throwError "the selected defining leg lost its independently encoded index"
      scopedNode "constructionLeg" #[{ json := toJson selected.construction.row.id.raw },
        diagramData, packetData, index]
    | _, _, _ => throwError "the selected projection lost its unique constructor role"
  let data ← match selected.endpoint with
    | none => pure data
    | some source =>
      placedData
        (Backend.MorphismEndpoint.encode { callable := data.json, source })
        #[(#[.field "args", .index 0], data)]
  let state ← registryState
  let form := match selected.result with
    | .object context => contextualForm state context parent.form
    | .map context => contextualForm state context parent.form true
    | .value _ => parent.form
  let resultWire : Wire := {
    form, payload := (← scopedPayload selected.formal data true),
    categoryContext := selected.result.context?,
    serviceHandles := (← retainServiceOperands h #[parent]) }
  let resultWire ← retainCompletedResultInterface resultWire selected.result
  match selected.result, selected.endpoints with
  | .map context, some (source, target) => do
    let source ← realizeObjectObservation h trace source
    let target ← realizeObjectObservation h trace target
    CategoryContext.checkMorphism context selected.formal source.value target.value
    if let .error message ← ComputationalData.validateEndpointPort selected.formal
        source.json target.json data.json then
      throwStratum .malformed m!"the projected construction map changed its complete endpoint data: {message}"
    retainMapImageEndpoints resultWire source target
  | .map _, none => throwError "the selected map projection lost its complete endpoint occurrences"
  | _, some _ => throwError "a non-map result inherited unrelated callable endpoint occurrences"
  | _, none => pure resultWire

/-- Compile the already selected defining-map algebra to ordinary typed producer
nodes. Registered map actions remain actions and are executed by their existing
observer; they do not become an opaque graph or a leaf-interpreted recipe. -/
partial def captureConstructionExpression (h : Harness) (trace : Trace) (parent : Wire)
    (construction : StructuredProjection.ConstructionPlan) (plan : StructuredResult.DataPlan)
    (projection : StructuredResult.DataProjection) (context? : Option CategoryContext := none) :
    TermElabM Wire := do
  let context := context?.getD construction.context
  let state ← registryState
  match projection with
  | .field index =>
    let some port := plan.ports[index]?
      | throwError "the defining-map expression selects an absent constructor field"
    captureConstructionPort h trace parent construction plan port #[] (some context)
  | .input formal =>
    let bindings := plan.binders.filter fun binding =>
      binding.port.isNone && binding.formalValue == some formal
    if let some binding := bindings[0]? then
      -- Every retained binder role belongs to this same formal input. No
      -- returned bytes decide which original occurrence supplied it.
      let binding := { binding with inputRoles := bindings.flatMap (·.inputRoles) }
      return ← captureConstructionInput h trace parent construction plan binding (some context)
    discard <| Semantic.recordNamedObject formal (some trace)
    realizeUnobserved { h with demandObjectActions := false } trace
      "the defining map's fixed input" formal
  | .identity object =>
    let object ← captureConstructionExpression h trace parent construction plan object (some context)
    let carrier ← CategoryContext.carrier context
    let dictionary ← CategoryContext.dictionary context
    let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
      #[some carrier, some dictionary]
    let identity ← mkAppOptM ``CategoryTheory.CategoryStruct.id
      #[some carrier, some categoryStructure, some object.value]
    let template : ActionDataTemplate := .ctor "identity"
      #[.wire .object object, .wire .object object]
    let (data, dependencies) ← renderCapturedActionData template
    let wire : Wire := {
      form := contextualForm state context parent.form true,
      payload := (← combinedRecipePayload identity data dependencies), categoryContext := some context }
    let wire ← retainIntrinsicAssembly wire .map context template
    retainCallableEndpoints wire object object context
  | .composition first second =>
    let first ← captureConstructionExpression h trace parent construction plan first (some context)
    let second ← captureConstructionExpression h trace parent construction plan second (some context)
    let first ← captureCompleteCallable h trace first context
    let second ← captureCompleteCallable h trace second context
    let some (source, middle) ← retainedCallableEndpoints? first context
      | throwError "the defining-map composite lost its first complete endpoint pair"
    let some (middle', target) ← retainedCallableEndpoints? second context
      | throwError "the defining-map composite lost its second complete endpoint pair"
    let formal ← ServiceRequest.compose context source.value middle.value target.value
      first.value second.value
    let template : ActionDataTemplate := .ctor "compose" #[.wire .map first, .wire .map second]
    let (data, dependencies) ← renderCapturedActionData template
    let wire : Wire := {
      form := contextualForm state context parent.form true,
      payload := (← combinedRecipePayload formal data dependencies), categoryContext := some context }
    let wire ← retainIntrinsicAssembly wire .map context template
      #[{ context, source, target := middle, callable := first },
        { context, source := middle', target, callable := second }] #[(middle, middle')]
    retainCallableEndpoints wire source target context
  | .map action arrow =>
    let some actions ← FunctorActionData.registeredComposite? state action
      | throwStratum .noImplementation "the defining-map action has no complete registered interface"
    let some first := actions[0]?
      | throwError "the defining-map action lost its first selected component"
    let some sourceExpression := state.selectedEdgeSource? first.edge
      | throwError "the defining-map action lost its full source category expression"
    let (sourceBundle, targetBundle) ← functorCategoryBundles (← Semantic.asFunctor action)
    unless ← withoutModifyingState (withTransparency .all <| isDefEq targetBundle context.bundle) do
      throwError "the defining-map action changed its selected full target category"
    let sourceContext : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let arrow ← captureConstructionExpression h trace parent construction plan arrow (some sourceContext)
    captureMapRoute { h with demandObjectActions := false } trace arrow
      (actions.map (·.edge)) (actions.map (·.application))

/-- Form a defining map while its universal result is still pending. Direct
constructors compile their formal DataProjection algebra; created constructions
retain their existing complete creation projection and its accepted source role. -/
partial def captureConstructionLeg (h : Harness) (trace : Trace) (formal receiver index : Expr) :
    TermElabM Wire := do
  let parent ← realizeUnobserved { h with demandObjectActions := false } trace
    "the complete construction defining this leg" receiver
  let (construction, plan) ← capturedConstructionInterface h trace parent receiver
  if construction.lift.isNone then
    let some plan := plan
      | throwError "the selected direct defining map lost its complete data plan"
    let .ok (projection, count) ← StructuredResult.dataProjection construction.row construction.diagram index
      | throwStratum .noImplementation "the accepted defining map has no complete computational projection algebra"
    unless count == plan.ports.size do
      throwError "the defining-map projection changed its selected constructor port count"
    let result ← captureConstructionExpression h trace parent construction plan projection
    return ← forwardRetainedValue result formal
  let indexType ← inferType index
  let diagramType ← withTransparency .all <| whnf (← inferType construction.diagram)
  unless diagramType.isAppOfArity ``CategoryTheory.Functor 4 &&
      (← withTransparency .all <| isDefEq indexType diagramType.getAppArgs[0]!) do
    throwError "the created defining map changed its exact diagram-index type"
  let .ok indexData ← Codec.encode index
    | throwStratum .noImplementation "the defining-map index has no public encoding"
  let maps ← mkAppM (if construction.row.colimit then ``CategoryTheory.Limits.Cocone.ι
    else ``CategoryTheory.Limits.Cone.π) #[construction.cone]
  let expected ← mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
  unless ← withoutModifyingState (withTransparency .all <| isDefEq expected formal) do
    throwError "the created defining map changed its original complete formal question"
  let some (source, target) := Language.homEnds? (← inferType formal)
    | throwError "the created defining map has no complete categorical endpoints"
  let endpoint := fun value => do
    if ← withoutModifyingState (withTransparency .all <| isDefEq value parent.value) then
      return ← forwardRetainedValue parent value
    discard <| Semantic.recordNamedObject value (some trace)
    realizeUnobserved { h with demandObjectActions := false } trace
      "the created defining map's selected endpoint" value
  let source ← endpoint source
  let target ← endpoint target
  let original : Wire := {
    form := contextualForm (← registryState) construction.context parent.form true,
    payload := (← combinedRecipePayload formal parent.fragment #[parent]),
    categoryContext := some construction.context }
  let original ← retainCallableEndpoints original source target construction.context
  retainCapturedInvocation h original (.projection {
    formal, fragment := parent.fragment, context := construction.context,
    result := .map construction.context, parent,
    construction, plan, port := none, leg := some index, legData := some { json := indexData },
    endpoints := some (source, target) })

/-- Complete ordinary result fields are projections of their retained formal schema
and actual returned packet. A computational field supplies neither a formal object
identification nor any law about the construction. -/
partial def structuredProjection (h : Harness) (trace : Trace) (formal receiver : Expr)
    (field : String) (index : Option Nat) : TermElabM Wire := do
  let state ← registryState
  let original ← realizeUnobserved { h with demandObjectActions := false } trace "the complete structured result" receiver
  let context ← match original.categoryContext with
    | some context => pure context
    | none => do
      let some category := state.categories.find? (·.id == original.form.category)
        | throwError "the structured result lost its complete category context"
      CategoryContext.ofNamed category receiver
  if let some index := index then
    let (construction, retainedPlan) ← capturedConstructionInterface h trace original receiver
    let dataPlan ← if construction.lift.isSome then construction.dataPlan else
      match retainedPlan with
      | some plan => pure plan
      | none => throwError "the selected direct construction lost its retained data plan"
    let some port := dataPlan.ports[index]?
      | throwStratum .invalid "the selected field is outside its registered constructor schema"
    unless ← withoutModifyingState (withTransparency .all <| isDefEq port.formalField formal) do
      throwError "the selected data port changed its complete formal field"
    let result ← captureConstructionPort h trace original construction dataPlan port
    return ← forwardRetainedValue result formal
  captureStructuredRecordField h trace formal original context field

/-- Read the preserved actual fields of a completed lift without rerunning its ports. -/
partial def retainedLiftExecution (h : Harness) (trace : Trace) (receiver : Expr) :
    TermElabM (Wire × LiftExecution) := do
  let wire ← realizeUnobserved h trace "the complete selected lift" receiver
  let wire ← realizeObjectObservation { h with demandObjectActions := true } trace wire
  let some execution := wire.liftExecution
    | throwError "the completed lift lost its selected computation and actual four-field outputs"
  let legacyOwner := match wire.payload with
    | .computed _ (.owned backend session _) | .computed _ (.opaque backend session _) |
        .construction _ (.owned backend session) => some (backend, session)
    | _ => none
  let execution ← scopedLiftExecution execution legacyOwner
  return (wire, execution)

/-- Explicitly compose retained stages without rerunning their four ports or replacing
the ordinary outer selection's cache. Only its recorded defining-map links form the chain. -/
partial def composedLiftExecution (h : Harness) (trace : Trace) (formal receiver : Expr) :
    TermElabM Wire := do
  let recorded ← SelectedLift.recorded trace receiver true
  let mut execution : LiftExecution := {
    selections := #[], actions := #[], parameters := #[], sources := #[], bases := #[], outputs := #[] }
  let mut dependencies := #[]
  for (segment, plans) in recorded.segments do
    let (wire, retained) ← retainedLiftExecution h trace segment
    unless retained.selections.size == plans.size do
      throwError "a composed lift packet changed the number of its selected stages"
    for (expected, actual) in plans.zip retained.selections do
      checkRetainedLiftPlan expected actual
    execution := {
      selections := execution.selections ++ retained.selections
      actions := execution.actions ++ retained.actions
      parameters := execution.parameters ++ retained.parameters
      sources := execution.sources ++ retained.sources
      bases := execution.bases ++ retained.bases
      outputs := execution.outputs ++ retained.outputs
      actionOwnership := execution.actionOwnership ++ retained.actionOwnership
      parameterOwnership := execution.parameterOwnership ++ retained.parameterOwnership
      sourceOwnership := execution.sourceOwnership ++ retained.sourceOwnership
      baseOwnership := execution.baseOwnership ++ retained.baseOwnership
      outputOwnership := execution.outputOwnership ++ retained.outputOwnership
      sourceImages := execution.sourceImages ++ retained.sourceImages
      comparisonImages := execution.comparisonImages ++ retained.comparisonImages
      sourceImageOwnership := execution.sourceImageOwnership ++ retained.sourceImageOwnership
      comparisonImageOwnership := execution.comparisonImageOwnership ++ retained.comparisonImageOwnership
      stageHandles := execution.stageHandles ++ retained.stageHandles }
    dependencies := dependencies.push wire
  let some first := execution.selections[0]?
    | throwError "the composed lift has no complete retained stage"
  let some original := dependencies[0]? | unreachable!
  unless ← withTransparency .all <| isDefEq (← SelectedLift.port execution.selections 0) formal do
    throwError "the composed lift changed its original formal object"
  let context ← SelectedLift.context first
  return {
    form := contextualForm (← registryState) context original.form
    payload := (← scopedPayload formal (← liftProjectionFragment execution 0))
    liftExecution := some execution
    categoryContext := some context
    serviceHandles := (← retainLiftOperands h dependencies) }

/-- Prepare the direct lift in the same canonical owner as every other
captured request. Preparation selects complete inputs and performs no dispatch. -/
partial def captureDirectLiftInvocation (h : Harness) (trace : Trace) (plan : SelectedLift.Plan)
    (formal : Expr) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let state ← registryState
  let context ← SelectedLift.context plan
  let targetContext ← SelectedLift.context plan true
  let source ← realizeUnobserved h trace "the selected lift's original source" plan.source
  let source ← captureDeclaredObjectInput source context
  let (baseSource, baseTarget) ← contextualMorphismEndpoints targetContext plan.inclusion
  let inclusion ← realizeUnobserved h trace "the selected lift's base inclusion" plan.inclusion
  let inclusion ← captureDeclaredCallableInput h trace inclusion targetContext fun _ => do
    pure (← realizeEndpoint h trace "the selected inclusion's source" baseSource,
      ← realizeEndpoint h trace "the selected inclusion's target" baseTarget)
  let some (baseSource, baseTarget) ← retainedCallableEndpoints? inclusion targetContext
    | throwError "the selected lift lost its original inclusion endpoints"
  let inner ← SelectedLift.innerEdge state plan.entry
  let descriptor ← capturedEdgeData h trace inner plan.action
  let parameters ← capturedParameterData h trace plan.parameters
  let operands ← IO.mkRef #[← invocationOperand .object source, ← invocationOperand .map inclusion]
  let capture := fun (role : ActionDataRole) (wire : Wire) => do
    let operand ← invocationOperand role wire
    operands.modify (·.push operand)
    pure wire
  discard <| mapActionTemplateWires capture descriptor
  for parameter in parameters do discard <| mapActionTemplateWires capture parameter
  let (action, _) ← renderCapturedActionData descriptor
  let parameterData ← parameters.mapM renderCapturedActionData
  let base ← scopedNode "subobject" #[baseSource.fragment, baseTarget.fragment, inclusion.fragment]
  let data ← LiftStageExecution.packet "monoLiftInput" plan.entry.id.raw
    (DataOwnership.Data.array (parameterData.map (·.1))) action source.fragment base #[]
    (some baseTarget.fragment)
  let wire : Wire := {
    form := contextualForm state context source.form,
    payload := (← recipePayload formal data), categoryContext := some context }
  retainCapturedInvocation h wire (.directLift {
    formal, fragment := data, context, plan, operands := ← operands.get, descriptor, parameters })

/-- A later field keeps its exact parent preparation, even before that parent
has returned. It never looks up an output by its formal expression or bytes. -/
partial def captureLiftField (h : Harness) (trace : Trace)
    (formal receiver : Expr) (index : Nat) : TermElabM Wire := do
  let plans := (← SelectedLift.recorded trace receiver).plans
  unless index < 4 && (← withoutModifyingState (withTransparency .all <|
      isDefEq (← SelectedLift.port plans index) formal)) do
    throwError "the lift projection changed its fixed selected output position"
  let some selection := if index < 2 then plans[0]? else plans.back?
    | throwError "the lift projection lost its selected stage"
  let context ← SelectedLift.context selection (index >= 2)
  let parent ← realizeUnobserved { h with demandObjectActions := false }
    trace "the lift field's original construction" receiver
  let data ← scopedNode "selectedLiftField" #[parent.fragment, { json := toJson index }]
  let result := if index == 0 then IntrinsicResultInterface.object context else .map context
  let wire : Wire := {
    form := contextualForm (← registryState) context parent.form (index != 0),
    payload := (← recipePayload formal data), categoryContext := some context }
  retainCapturedInvocation h wire (.liftField {
    formal, fragment := data, result, parent, plans, index })

/-- A factor's preparation retains complete source and base maps. The selected
construction is an operand, not a recipe to rerun when the factor is demanded. -/
partial def captureLiftFactor (h : Harness) (trace : Trace)
    (formal receiver baseMap cone proof : Expr) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let plans := (← SelectedLift.recorded trace receiver).plans
  let steps ← SelectedLift.factors plans baseMap cone proof
  let some step := steps.back? | throwError "the selected factor has no complete result"
  unless ← withoutModifyingState (withTransparency .all <| isDefEq step.factor formal) do
    throwError "the selected factor changed its independently fixed result"
  let some first := plans[0]? | throwError "the selected factor lost its first stage"
  let some last := plans.back? | throwError "the selected factor lost its last stage"
  let context ← SelectedLift.context first
  let targetContext ← SelectedLift.context last true
  let parent ← realizeUnobserved h trace "the factor's selected construction" receiver
  let coneWire ← realizeUnobserved h trace "the factor's complete source cone" cone
  let coneWire ← captureDeclaredCallableInput h trace coneWire context fun _ => do
    let (source, target) ← contextualMorphismEndpoints context cone
    pure (← realizeEndpoint h trace "the factor's declared source domain" source,
      ← realizeEndpoint h trace "the factor's declared source target" target)
  let baseWire ← realizeUnobserved h trace "the factor's complete base map" baseMap
  let baseWire ← captureDeclaredCallableInput h trace baseWire targetContext fun _ => do
    let (source, target) ← contextualMorphismEndpoints targetContext baseMap
    pure (← realizeEndpoint h trace "the factor's declared base domain" source,
      ← realizeEndpoint h trace "the factor's declared base target" target)
  let data ← scopedNode "selectedLiftFactor" #[parent.fragment, baseWire.fragment, coneWire.fragment]
  let wire : Wire := {
    form := contextualForm (← registryState) context parent.form true,
    payload := (← recipePayload formal data), categoryContext := some context }
  retainCapturedInvocation h wire (.liftFactor {
    formal, fragment := data, context, plans, proof,
    operands := #[← invocationOperand .object parent,
      ← invocationOperand .map baseWire, ← invocationOperand .map coneWire] })

/-- A complete factor owns its source-level computation. Its original arguments
are observed once; internally derived cones retain typed action plans and exact
endpoint occurrences for the factor implementation or public service to consume.
No additional object/map registration is required just to form that request. -/
partial def completeRetainedLiftFactor (h : Harness) (trace : Trace)
    (selected : SelectedLiftFactorInvocation) (liftWire baseWire coneWire : Wire)
    (execution : LiftExecution) : TermElabM Wire := do
  let active := { h with demandObjectActions := true }
  let state ← registryState
  unless execution.selections.size == selected.plans.size do
    throwError "the selected factor changed its original construction stage count"
  for (expected, actual) in selected.plans.zip execution.selections do
    checkRetainedLiftPlan expected actual
  let steps ← SelectedLift.factors execution.selections baseWire.value coneWire.value selected.proof
  let some first := execution.selections[0]?
    | throwError "the complete factor lost its selected first stage"
  let some last := execution.selections.back?
    | throwError "the complete factor lost its selected last stage"
  let sourceContext ← SelectedLift.context first
  let targetContext ← SelectedLift.context last true
  let firstStage ← retainedLiftStage h execution 0
  let lastStage ← retainedLiftStage h execution (execution.selections.size - 1)
  let some (domain, _) ← retainedCallableEndpoints? coneWire sourceContext
    | throwError "the factor cone lost its original generalized domain occurrence"
  let mut domains : Array Wire := #[]
  let mut cones : Array Wire := #[]
  let mut stages : Array RetainedLiftStage := #[]
  let mut currentDomain := domain
  let mut currentCone := coneWire
  for index in [:execution.selections.size] do
    let some selection := execution.selections[index]?
      | throwError "the factor route lost an ordered selected action"
    let stage ← retainedLiftStage h execution index
    let context ← SelectedLift.context selection
    let target ← SelectedLift.context selection true
    checkLiftFactorMapEndpoints context currentCone currentDomain stage.source
    domains := domains.push currentDomain
    cones := cones.push currentCone
    stages := stages.push stage
    let inner ← SelectedLift.innerEdge state selection.entry
    let descriptor := ActionDataTemplate.wire .parameter stage.action
    let image ← captureRegisteredObjectAction (.edge inner) selection.action currentDomain
      (← Semantic.objOf selection.action currentDomain.value)
      (contextualForm state target currentDomain.form) target descriptor
    if index + 1 == execution.selections.size then
      -- This image is used only if the original unframed base input needs its
      -- initial declared domain. A complete base map keeps its own endpoint.
      currentDomain := image
    else
      let mapped ← captureRegisteredMapAction (.edge inner) selection.action descriptor
        currentCone image stage.sourceImage
      -- The public frame preserves the original map/action producers. It is
      -- a deferred input to this complete factor, not an executed map receipt.
      currentCone ← captureCompleteCallable h trace mapped target
      let some (selectedDomain, _) ← retainedCallableEndpoints? currentCone target
        | throwError "the complete mapped factor cone lost its selected image endpoints"
      currentDomain := selectedDomain
  let some (finalDomain, _) ← retainedCallableEndpoints? baseWire targetContext
    | throwError "the factor base map lost its original complete image domain"
  currentDomain ← forwardRetainedValue finalDomain currentDomain.value
  let mut currentBase := baseWire
  let mut handles := liftWire.serviceHandles ++ execution.stageHandles.flatMap (·.all)
  for (index, step) in (List.range execution.selections.size).reverse.toArray.zip steps do
    let some selection := execution.selections[index]?
      | throwError "the factor fold lost its exact selected stage"
    let some stage := stages[index]?
      | throwError "the factor fold lost its exact typed stage operands"
    let some originalCone := cones[index]?
      | throwError "the factor fold lost its exact source cone occurrence"
    let some domain := domains[index]?
      | throwError "the factor fold lost its exact generalized domain occurrence"
    let sourceContext ← SelectedLift.context selection
    let targetContext ← SelectedLift.context selection true
    let baseForStage ← forwardRetainedValue currentBase step.baseMap
    let baseForStage ← enrichLiftMapTarget h targetContext baseForStage stage.baseObject
    let originalCone ← forwardRetainedValue originalCone step.cone
    checkLiftFactorMapEndpoints targetContext baseForStage currentDomain stage.baseObject
    checkLiftFactorMapEndpoints sourceContext originalCone domain stage.source
    let .ok baseMap := Backend.TypedMap.decode baseForStage.json
      | throwError "the retained factor input lost its complete public base map"
    let .ok cone := Backend.TypedMap.decode originalCone.json
      | throwError "the retained factor input lost its complete public cone"
    let invocation : Backend.LiftFactorInput := {
      lift := selection.entry.id.raw,
      action := (← execution.actionFragment index).json,
      source := stage.source.json, base := stage.base.json,
      outputs := stage.outputs.map (·.json),
      parameters := execution.parameters[index]!, baseMap, cone,
      sourceImage? := some stage.sourceImage.json,
      comparisonImage? := some stage.comparisonImage.json }
    let some form := state.liftInputForm? selection.entry.inputAddress
      | throwError "the retained factor has no published complete input form"
    -- Decoding checks the public map interface; re-encoding would discard
    -- admitted extra envelope fields from these exact retained occurrences.
    let requestJson := invocation.encode.setObjVal! "args" (Json.arr #[
      toJson invocation.lift, invocation.action, invocation.source, invocation.base,
      Json.arr invocation.outputs, baseForStage.json, originalCone.json])
    let request ← placedData requestJson #[
      (#[.field "parameters"], ← execution.parameterFragment index),
      (#[.field "args", .index 1], ← execution.actionFragment index),
      (#[.field "args", .index 2], stage.source.fragment),
      (#[.field "args", .index 3], stage.base.fragment),
      (#[.field "args", .index 4], DataOwnership.Data.array (stage.outputs.map (·.fragment))),
      (#[.field "args", .index 5], baseForStage.fragment),
      (#[.field "args", .index 6], originalCone.fragment),
      (#[.field "sourceImage"], stage.sourceImage.fragment),
      (#[.field "comparisonImage"], stage.comparisonImage.fragment)]
    let dependencies := #[liftWire, baseWire, coneWire, domain, currentDomain,
      baseForStage, originalCone, stage.source, stage.sourceImage, stage.base,
      stage.baseObject, stage.comparisonImage] ++ stage.outputs
    handles ← retainLiftOperands h dependencies
    let some retainedStage := execution.stageHandles[index]?
      | throwError "the factor lost its original positioned stage inputs"
    let mut positions :=
      (← liftServiceInputPositions #[.field "args", .index 2] stage.source) ++
      (← liftServiceInputPositions #[.field "args", .index 3] stage.base) ++
      (← liftServiceInputPositions #[.field "args", .index 5] baseForStage) ++
      (← liftServiceInputPositions #[.field "args", .index 6] originalCone) ++
      (← liftServiceInputPositions #[.field "sourceImage"] stage.sourceImage) ++
      (← liftServiceInputPositions #[.field "comparisonImage"] stage.comparisonImage)
    for (output, position) in stage.outputs.zipIdx do
      positions := positions ++
        (← liftServiceInputPositions #[.field "args", .index 4, .index position] output)
    let serviceInputPaths := retainedStage.staticInputPaths ++
      (← retainServiceInputPaths h request positions)
    let input : Wire := {
      form, payload := (← combinedRecipePayload step.factor request dependencies),
      serviceHandles := handles, serviceInputPaths := some serviceInputPaths }
    let operation := selection.entry.factorAddress
    let reply ← sendData active operation input
    let some object := stage.outputs[0]?
      | throwError "the factor result lost its selected lift object endpoint"
    if let .error message ← LiftedSubobjectData.validateMap step.factor
        domain.json object.json reply.data.json then
      malformed reply.backend operation reply.data.json message
    let sourceData ← checkedFragment (reply.data.project #[.field "args", .index 0])
    let targetData ← checkedFragment (reply.data.project #[.field "args", .index 1])
    let actualSource ← liftEndpointOperand domain sourceContext sourceData
    let actualTarget ← liftEndpointOperand object sourceContext targetData
    let output ← liftOperand step.factor sourceContext coneWire.form reply.data true true
    let output := { output with morphismFramed := true }
    let output ← retainCallableEndpoints output actualSource actualTarget sourceContext
    currentBase := { output with serviceHandles := handles }
    currentDomain := actualSource
  let result ← forwardRetainedValue currentBase selected.formal
  return { result with serviceHandles := handles }

/-- Evaluate the recorded term `e`, the value of `what`, to a value of a form, through the
admitted registrations. -/
partial def realize (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let e ← instantiateMVars e
  let closed := !e.hasMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars
  let staged ← stagedLiftNode trace e
  let cached ← if staged then preparedLiftReference? h trace e
    else if closed then pure ((← h.results.get)[e]?) else pure none
  let wire ← match cached with
    | some wire => pure wire
    | none => realizeFresh h trace what e
  -- An installed operation computes its own result before a later consumer sees
  -- it. A portable expression remains available when no complete registration
  -- applies; a failed or ambiguous dispatch is never retried as an expression.
  let wire ← match ← trace.node? e with
    | some (.operationApply ..) | some (.operationPoint ..) |
        some (.operationEquivalence ..) => realizeArrowObservation h trace wire true
    | some (.limit ..) => realizeObjectObservation h trace wire
    | some (.limitProjection ..) => realizeArrowObservation h trace wire
    | some (.structuredProjection _ _ (some _)) =>
      if let some captured ← retainedCapturedInvocation? wire then
        observeCapturedInvocation h trace wire captured
      else pure wire
    | some (.morphismTransport ..) | some (.constructionMap ..) |
        some (.contextualRoute _ _ _ _ _ true) =>
      if h.demandObjectActions then realizeArrowObservation h trace wire else pure wire
    | _ => pure wire
  let wire ← if h.demandObjectActions then do
      if let some captured ← retainedCapturedInvocation? wire then
        observeCapturedInvocation h trace wire captured
      else
        let wire ← realizeValueObservation h trace wire
        realizeObjectObservation h trace wire
    else pure wire
  -- A completed construction supplies its own exact apex expression. Its
  -- checked presentation can differ syntactically from the reader's original
  -- limit expression, and a subsequent selected action is applied to this
  -- actual apex. Retain that precise occurrence with its complete packet and
  -- owners; never reconstruct it by searching for an equal carrier or JSON.
  if !staged then
    if let .construction .. := wire.payload then
      let apex := wire.value
      unless apex.hasMVar || apex.hasLevelMVar || apex.hasFVar || apex.hasLooseBVars do
        h.results.modify (·.insert apex wire)
  if closed && !staged then
    if wire.liftExecution.isSome then
      h.results.modify (·.insert e wire)
    else
      match wire.payload with
      | .ordinary .. => pure ()
      | .computed .. | .construction .. => h.results.modify (·.insert e wire)
  return wire

/-- Prepare a candidate's public recipe without selecting its own registration.
Operation equivalence checks every retained candidate before a single dispatch.
Already returned data retain their exact owning session and observed status. -/
partial def realizeUnobserved (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire := do
  let e ← instantiateMVars e
  if ← stagedLiftNode trace e then
    if let some wire ← preparedLiftReference? h trace e then return wire
    return ← realizeFresh h trace what e
  if !e.hasMVar && !e.hasLevelMVar && !e.hasFVar && !e.hasLooseBVars then
    if let some wire := (← h.results.get)[e]? then return wire
  realizeFresh h trace what e

/-- Supply an initial producer's already fixed parameter reader to the common
node evaluator. Recursive producers keep their own ordinary preparation boundary. -/
partial def realizeFreshWithParameters
    (reader : Harness → Trace → Array Expr → TermElabM (Array ActionDataTemplate))
    (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire :=
  realizeFreshWith elementFragment realizedParameterData realizedEdgeData capturedEdgeData
    reader
    (fun h trace parameters overrides => capturedCallableParameters h trace parameters overrides)
    (fun h trace wire address application parameters descriptor invocationParameters context endpoints inverse =>
      captureSelectedCallable h trace wire address application parameters descriptor
        invocationParameters context endpoints inverse)
    captureRoutedInvocation actionMapEndpoint realizeObjectObservation
    (fun h trace wire => realizeArrowObservation h trace wire)
    computationalOperationReceiver extentFragment?
    (fun h trace what value recoverAction recoverNamed =>
      realizeEndpoint h trace what value recoverAction recoverNamed)
    (fun h trace wire value source context =>
      realizeCallableEndpoint h trace wire value source context)
    (fun h trace source target wire context pointAsMap =>
      frameMorphismTemplate h trace source target wire context pointAsMap)
    (fun h trace input context endpoints publicFrame =>
      captureCompleteCallable h trace input context endpoints publicFrame)
    callableObjectPlan? (fun h trace input context => capturedMapEndpoints h trace input context)
    pointAtAdmissionDomain wholeCallablePoint realizeObjectPresentation
    contextualAction captureMapRoute captureConstructionMap contextualComposition
    structuredProjection captureConstructionLeg retainedLiftExecution
    composedLiftExecution captureDirectLiftInvocation captureLiftField captureLiftFactor realize realizeUnobserved
    realizeFresh h trace what e

/-- Supply the same recursive operations to the separately compiled node evaluator. -/
partial def realizeFresh (h : Harness) (trace : Trace) (what : String) (e : Expr) :
    TermElabM Wire :=
  realizeFreshWithParameters capturedParameterData h trace what e

/-- An accepted operation's actual owner is the declaration argument preceding
its numeral parameters. Its set-valued source and result do not select that owner. -/
partial def realizedOperationOwner (h : Harness) (trace : Trace) (entry : OperationEntry)
    (application : Expr) (actual : Option Wire := none) : TermElabM Wire := do
  let state ← registryState
  let arguments := (operationApplicationBody application).getAppArgs
  let some receiver := arguments[arguments.size - 1 - entry.numerals]?
    | throwError "the complete operation lost its declared owner parameter"
  let some category := state.categories.find? (·.id == entry.category)
    | throwError "the complete operation lost its accepted owner category"
  let receiverContext ← CategoryContext.ofNamed category receiver
  let wire ← match actual with
    | some actual => pure actual
    | none => try
        realizeEndpoint h trace "the operation's exact declared owner" receiver
      catch error =>
        unless Exception.stratum? error == some .noImplementation do throw error
        let (data, dependencies) ← realizedParameterData h trace #[receiver]
        let #[data] := data | throwError "the operation's declared owner lost its parameter data"
        let retained : Wire := {
          form := .diagrams category
          payload := (← combinedRecipePayload receiver data dependencies)
          categoryContext := some receiverContext }
        pure retained
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType wire.value) (← inferType receiver) <&&>
        isDefEq wire.value receiver) do
    throwError "the operation's actual owner changed its complete declaration argument"
  discard <| framingContext (some receiverContext) wire.categoryContext
  unless state.accepts (.operation entry) wire.form do
    throwError "the complete operation's owner representation changed its declared category"
  return wire

/-- Bind the owner's data at its declaration-relative parameter occurrence.
Administrative wrappers need not be the same cache key. No equal carrier or
equal packet selects an occurrence, and all other parameters keep their own
retained data and suppliers. -/
partial def realizedOperationParameterData (h : Harness) (trace : Trace)
    (entry : OperationEntry) (application : Expr) (parameters : Array Expr)
    (owner : Wire) (retained : Option (Array OperationParameterOccurrence) := none)
    (reader : Option CallablePreparationReader := none) :
    TermElabM (Array DataOwnership.Data × Array Wire × Array OperationParameterOccurrence) := do
  let reader := reader.getD {
    observe := fun context wire => capturePointCallable h trace wire context
    observeData := observeActionDataWire h trace }
  let application := operationApplicationBody application
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun arguments _ =>
    arguments.mapM (·.fvarId!.getBinderInfo)
  unless application.getAppNumArgs == infos.size && infos.size > entry.numerals do
    throwError "the operation parameters lost their complete declaration telescope"
  let ownerSlot := infos.size - 1 - entry.numerals
  let ownerParameter := if infos[ownerSlot]!.isExplicit then
      some (((infos.extract 0 ownerSlot).filter (·.isExplicit)).size)
    else none
  unless parameters.size == (infos.filter (·.isExplicit)).size do
    throwError "the operation changed its ordered explicit parameters"
  if let some retained := retained then
    unless retained.size == parameters.size do
      throwError "the operation lost its retained ordered parameter occurrences"
  let mut data := #[]
  let mut dependencies := #[]
  let mut occurrences := #[]
  for index in [:parameters.size] do
    let parameter := parameters[index]!
    let expectedType ← instantiateMVars (← inferType parameter)
    let templates ← if some index == ownerParameter then do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType owner.value) expectedType <&&>
            isDefEq parameter owner.value) do
        throwError "the operation parameter changed its complete selected owner"
      let selected ← forwardRetainedValue owner parameter
      pure #[ActionDataTemplate.wire .retained selected]
    else if let some retained := retained then do
      let some previous := retained[index]?
        | throwError "the operation lost an original declared parameter occurrence"
      unless previous.formal == parameter &&
          (← withoutModifyingState (withTransparency .all <|
            isDefEq previous.expectedType expectedType)) do
        throwError "the operation changed an original nonowner parameter's complete declaration slot"
      let original ← previous.templates.mapM renderCapturedActionData
      unless original.map Prod.fst == previous.data do
        throwStratum .unavailable "the operation lost an original parameter-field producer"
      pure previous.templates
    else do
      let #[selected] ← capturedCallableParameters h trace #[parameter]
        | throwError "the operation lost its complete single declaration parameter"
      pure selected.templates
    let templates ← templates.mapM (mapActionTemplateWires reader.readData)
    let rendered ← templates.mapM renderCapturedActionData
    let occurrence : OperationParameterOccurrence := {
      formal := parameter, expectedType, templates, data := rendered.map Prod.fst,
      dependencies := rendered.foldl (fun inputs item => inputs ++ item.2) #[] }
    data := data ++ occurrence.data
    dependencies := dependencies ++ occurrence.dependencies
    occurrences := occurrences.push occurrence
  return (data, dependencies, occurrences)

/-- The element producer retains its exact owner and expression inputs. Neither
an equal formal cache key nor a later trace replay can replace those occurrences. -/
partial def operationPointRecipeInputs (_h : Harness) (_trace : Trace) (point : Wire) :
    TermElabM (Array Wire) := do
  if point.completedData || point.callableObserved then
    throwError "a completed point cannot select an unobserved operation recipe interface"
  if let some origin ← retainedPointOrigin? point then
    if let .element owner dependencies := origin.recipe then
      return #[owner] ++ dependencies
    return #[]
  if (point.json.getObjValAs? String "ctor").toOption == some "element" then
    throwStratum .noImplementation "the original element has no retained producer occurrence"
  return #[]

/-- Read input presentation occurrences through their retained point roles.
A product is decomposed only through its producer's exact ordered children and
encoding positions. No trace replay or expression lookup selects those inputs. -/
partial def operationPointPresentations (h : Harness) (trace : Trace)
    (context : CategoryContext) (role : OperationEndpointRole) (point : Wire)
    (domain target : Expr) (domainWire : Wire) (data : DataOwnership.Data)
    (bindings : Array OperationPointPresentation := #[]) :
    TermElabM (Array OperationPointPresentation × Bool × Array Wire) := do
  CategoryContext.checkMorphism context point.value domain target
  discard <| framingContext (some context) point.categoryContext
  discard <| checkedFragment data.validate
  match role with
  | .field path =>
    if point.completedData || point.callableObserved then return (bindings, false, #[])
    let some (pointDomain, pointTarget) := Language.homEnds? (← inferType point.value)
      | throwError "the original operation point lost its complete declared endpoints"
    let .ok unwrapped := ComputationalData.valuePayload data.json
      | throwError "the retained operation point has an incomplete value envelope"
    -- A generalized mediator retains its raw child occurrence. A closed product
    -- may already contain the ordinary typed-map framing of that same child.
    -- Both are reproduced before any normalized presentation is introduced.
    let endpoints ← match ← retainedPointOrigin? point with
      | some origin => pure (some (origin.source, origin.target))
      | none => do
        let source ← retainedCallableEndpoint? point pointDomain true (some context)
        let target ← retainedCallableEndpoint? point pointTarget false (some context)
        pure (source.bind fun source => target.map fun target => (source, target))
    let some (sourceWire, targetWire) := endpoints | return (bindings, false, #[])
    let sourceWire ← forwardRetainedValue sourceWire pointDomain
    let targetWire ← forwardRetainedValue targetWire pointTarget
    if data != point.fragment then
      let (framed, _) ← frameRetainedPoint context point sourceWire targetWire
      unless framed == data do
        throwStratum .unavailable "the operation point changed its retained computational occurrence"
    if (unwrapped.getObjValAs? String "ctor").toOption == some "typedMap" then
      let sourceData ← checkedFragment (← ComputationalData.interfaceEndpointData
        #[] point.value data true false)
      let targetData ← checkedFragment (← ComputationalData.interfaceEndpointData
        #[] point.value data false false)
      unless sourceWire.fragment == sourceData && targetWire.fragment == targetData do
        throwStratum .noImplementation
          "the operation point has no retained complete endpoint presentation"
    checkOperationPointPresentation sourceWire
    checkOperationPointPresentation domainWire
    unless sameOperationPointPresentation sourceWire domainWire do
      throwStratum .noImplementation
        "the operation point has a distinct complete generalized-domain presentation"
    if sourceWire.json == targetWire.json &&
        !sameOperationPointPresentation sourceWire targetWire then
      throwStratum .ambiguousRealization
        "the operation point repeats endpoint bytes in different complete contexts"
    let recipeInputs ← operationPointRecipeInputs h trace point
    let mut inputs : Array Wire := #[]
    for input in #[sourceWire, targetWire] ++ recipeInputs do
      checkOperationPointPresentation input
      for previous in inputs do
        if previous.json == input.json && !sameOperationPointPresentation previous input then
          throwStratum .ambiguousRealization
            "the point recipe repeats a descriptor in distinct complete input contexts"
      inputs := inputs.push input
    let bindings ← bindOperationPointPresentation bindings path targetWire
    return (bindings, true, #[point] ++ inputs)
  | .product leftRole rightRole =>
    let some origin ← retainedPointOrigin? point | return (bindings, false, #[])
    let .product _ retainedDomain first second firstPath secondPath := origin.recipe
      | return (bindings, false, #[])
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType retainedDomain) (← inferType domain) <&&>
          isDefEq retainedDomain domain) do
      throwError "the original product point changed its complete domain"
    if data != point.fragment then
      let (framed, _) ← frameRetainedPoint context point origin.source origin.target
      unless framed == data do
        throwStratum .unavailable "the product point changed its retained computational occurrence"
    let componentPaths := #[firstPath, secondPath]
    let product ← withTransparency .all <| whnf target
    unless product.isAppOfArity ``Prod 2 do
      throwError "the original product point changed its declared target"
    let coordinates := product.getAppArgs
    let firstData ← checkedFragment (origin.fragment.project componentPaths[0]!)
    let secondData ← checkedFragment (origin.fragment.project componentPaths[1]!)
    let (bindings, leftComplete, firstEndpoints) ← operationPointPresentations h trace context
      leftRole first domain coordinates[0]! domainWire firstData bindings
    let (bindings, rightComplete, secondEndpoints) ← operationPointPresentations h trace context
      rightRole second domain coordinates[1]! domainWire secondData bindings
    return (bindings, leftComplete && rightComplete, firstEndpoints ++ secondEndpoints)

/-- Reconstruct only the declared product of the already bound endpoint data.
This does not inspect values to infer a product or choose a field presentation. -/
partial def operationPresentationData (role : OperationEndpointRole)
    (bindings : Array OperationPointPresentation) : TermElabM DataOwnership.Data := do
  match role with
  | .field path =>
    let some binding := bindings.find? fun binding => sameOperationFieldPath binding.path path
      | throwError "the complete operation source omitted a declared presentation role"
    return binding.endpoint.fragment
  | .product left right =>
    scopedNode "objectProduct" #[← operationPresentationData left bindings,
      ← operationPresentationData right bindings]

/-- Supply the exact realizer operations to the separately compiled argument
builder. The callbacks retain this same harness and trace; no alternate
selection, decoding rule or execution policy is introduced. -/
partial def prepareOperationPointArgument (h : Harness) (trace : Trace)
    (context : CategoryContext) (point originalDomain originalTarget domain target : Wire)
    (data : DataOwnership.Data) (parameters : Array Wire)
    (reader : Option CallablePreparationReader := none) :
    TermElabM PreparedOperationArgument := do
  let reader := reader.getD {
    observe := fun context wire => capturePointCallable h trace wire context }
  prepareOperationPointArgumentWith
    (fun point => operationPointRecipeInputs h trace point) reader
    h context point originalDomain originalTarget domain target data parameters

/-- A pending operation uses one presentation for every occurrence of a
declared field role. The full actual owner stays in the operation parameters.
Already returned callables and unrelated map-action endpoints never enter here. -/
partial def operationPointEndpoints? (h : Harness) (trace : Trace) (context : CategoryContext)
    (entry : OperationEntry) (application : Expr) (receiver point : Wire)
    (domain source target : Expr) (domainWire : Wire) (data : DataOwnership.Data)
    (parameters : Array Wire) (reader : CallablePreparationReader) :
    TermElabM (Option PreparedOperationPoints) := do
  let some (sourceRole, targetPath) ← operationPointRoles? entry application receiver | return none
  -- Metadata inspection may reuse completed inputs, but it cannot start a new
  -- implementation merely to recover an endpoint presentation.
  let inspect := { h with
    admitted := #[]
    backends := #[]
    deferred := none
    derivation := none
    dispatches := none
    demandObjectActions := false }
  let (bindings, complete, dependencies) ← operationPointPresentations inspect trace context
    sourceRole point domain source domainWire data
  if bindings.isEmpty then return none
  unless complete do
    throwStratum .noImplementation
      "the original operation points do not retain one complete presentation for every source role"
  let some sourceWire ← retainedCallableEndpoint? point source false (some context)
    | throwStratum .noImplementation
        "the operation argument has no retained complete source endpoint occurrence"
  checkOperationPointPresentation sourceWire
  let sourceData ← operationPresentationData sourceRole bindings
  unless sourceWire.fragment == sourceData do
    throwStratum .noImplementation
      "the operation source differs from its original complete point presentations"
  match sourceRole with
  | .field path =>
    let some selected := bindings.find? fun binding => sameOperationFieldPath binding.path path
      | throwError "the complete operation source lost its retained endpoint presentation"
    unless sameOperationPointPresentation sourceWire selected.endpoint do
      throwStratum .noImplementation
        "the operation source changed its complete retained point context"
  | .product .. =>
    unless (← checkOperationProductContext context sourceRole sourceWire bindings) == bindings.size do
      throwError "the operation product changed its complete ordered role inventory"
  let mut targetWire := none
  if let some selected := bindings.find? fun binding => sameOperationFieldPath binding.path targetPath then
    let endpoint := selected.endpoint
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType endpoint.value) (← inferType target) <&&>
          isDefEq endpoint.value target) do
      throwError "the declared result field changed its independently selected complete endpoint"
    CategoryContext.checkObject context target
    discard <| framingContext (some context) endpoint.categoryContext
    targetWire := some { endpoint with payload := forwardPayload endpoint target endpoint.json }
  -- Fix the actual domain and source before constructing the argument packet.
  -- The same normalization applies to every exact retained occurrence, rather
  -- than adding comparison metadata only after an invocation has been framed.
  let (parameters, _) ← normalizeOperationProducts h context parameters #[] (← reader.objects)
  let targetInputs := (targetWire.map fun wire => #[wire]).getD #[]
  let (normalized, _) ← normalizeOperationProducts h context
    (#[domainWire, sourceWire] ++ targetInputs ++ dependencies) parameters (← reader.objects)
  let some actualDomain := normalized[0]?
    | throwError "the operation point lost its complete normalized domain"
  let some actualSource := normalized[1]?
    | throwError "the operation point lost its complete normalized source"
  let actualTarget := if targetWire.isSome then normalized[2]? else none
  let argument ← prepareOperationPointArgument h trace context point domainWire sourceWire
    actualDomain actualSource data parameters (some reader)
  return some {
    domain := actualDomain, source := actualSource, target := actualTarget
    argument := argument.data, argumentTemplate := argument.template
    dependencies := normalized.extract (2 + targetInputs.size) normalized.size ++
      argument.dependencies }

/-- Prepare an operation's actual complete request without dispatching it. This
also covers nullary and staged operations, using their original typed argument. -/
partial def prepareOperationObservation (h : Harness) (trace : Trace) (wire : Wire)
    (id : OperationId) (parameters : Array Expr) (actualOwner : Option Wire := none)
    (retained : Option OperationObservation := none)
    (objects : ComputationalData.InterfaceObjects := #[])
    (initialParameters : Option (Array OperationParameterOccurrence) := none)
    (reader : Option CallablePreparationReader := none)
    (phase : String := "capture") :
    TermElabM OperationObservation := do
  let h := { h with demandObjectActions := false }
  let reader := reader.getD {
    observe := fun context wire => capturePointCallable h trace wire context
    objects := pure objects }
  let objects ← reader.interfaceObjects objects
  if let some actual := operationRecipeId? wire then
    unless actual == id.raw do
      throwError "the retained operation recipe changed its accepted operation"
  let state ← registryState
  let some entry := state.operations.find? (·.id == id)
    | throwError "the retained operation is no longer registered"
  let formal := wire.value
  if let some retained := retained then
    unless retained.original.value == formal && retained.operation == id &&
        retained.parameters == parameters do
      throwError "the operation rebuild changed its original selected request"
  let namedRecipe ← match ← trace.node? formal with
    | some (.namedCallable address _ _) => pure (address == id.raw &&
        (wire.json.getObjValAs? String "ctor").toOption == some address)
    | _ => pure false
  let (arguments, operation) := operationApplicationSpine formal
  let application := operationApplicationBody operation
  unless application.getAppFn.constName? == some entry.declaration do
    throwError "the complete operation recipe changed its accepted declaration"
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun arguments _ =>
    arguments.mapM (·.fvarId!.getBinderInfo)
  unless application.getAppNumArgs == infos.size do
    throwError "the complete operation recipe lost its full declaration application"
  let actualParameters := (application.getAppArgs.zip infos).filterMap fun (value, info) =>
    if info.isExplicit then some value else none
  unless actualParameters.size == parameters.size do
    throwError "the complete operation recipe changed its ordered declaration parameters"
  for (actual, retained) in actualParameters.zip parameters do
    unless ← withTransparency .all <| isDefEq actual retained do
      throwError "the complete operation recipe changed a selected declaration parameter"
  let some (source, target) := Language.homEnds? (← inferType operation)
    | throwError "the accepted operation lost its complete callable signature"
  let some dataCategory := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the point invocation's declared data category is absent"
  let dataContext ← CategoryContext.ofNamed dataCategory source
  CategoryContext.checkMorphism dataContext operation source target
  let argument ← match arguments[0]? with
    | none => do
      let identity ← identityAtContext dataContext source
      Trace.recordProduced (some trace) identity (.contextualIdentity dataContext source)
    | some first => do
      let mut argument := first
      for next in arguments.extract 1 arguments.size do
        let some (domain, middle) := Language.homEnds? (← inferType argument)
          | throwError "the operation's staged argument lost its complete source"
        let some (nextSource, target) := Language.homEnds? (← inferType next)
          | throwError "the operation's staged argument lost its complete target"
        unless ← withTransparency .all <| isDefEq middle nextSource do
          throwError "the operation's staged argument changed a selected intermediate endpoint"
        let composite ← mkAppM ``CategoryTheory.CategoryStruct.comp #[argument, next]
        CategoryContext.checkMorphism dataContext composite domain target
        let composite ← Trace.recordProduced (some trace) composite
          (.contextualComposition dataContext argument next domain middle target)
        argument := composite
      pure argument
  let some (domain, originalSource) := Language.homEnds? (← inferType argument)
    | throwError "the retained operation argument lost its original generalized domain"
  let some (resultDomain, resultTarget) := Language.homEnds? (← inferType formal)
    | throwError "the complete operation result lost its original typed endpoints"
  unless ← withTransparency .all <| isDefEq originalSource source <&&>
      isDefEq resultDomain domain <&&> isDefEq resultTarget target do
    throwError "the complete operation recipe changed its original composition endpoints"
  unless ← withTransparency .all <|
      isDefEq formal (← mkAppM ``CategoryTheory.CategoryStruct.comp #[argument, operation]) do
    throwError "the complete operation recipe changed its original typed composition"
  let receiverWire ← realizedOperationOwner h trace entry application actualOwner
  let (recordSource, recordTarget) ← operationRecordEndpointData entry application receiverWire objects
  let (parameterData, parameterWires, parameterOccurrences) ←
    realizedOperationParameterData h trace entry application parameters receiverWire
      ((retained.map (·.parameterOccurrences)).orElse fun _ => initialParameters) (some reader)
  let descriptorTemplate : ActionDataTemplate := .logical
    (.ctor id.raw (parameterOccurrences.flatMap (·.templates)))
  let callable : Wire := {
    form := wire.form
    payload := (← combinedRecipePayload operation
      (← scopedNode id.raw parameterData) parameterWires)
    categoryContext := some dataContext }
  let callable ← retainIntrinsicAssembly callable .map dataContext descriptorTemplate
  let argumentWire ← match retained with
    | some retained => pure retained.argument
    | none => realize h trace "the operation's original generalized argument" argument
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType argumentWire.value) (← inferType argument) <&&>
        isDefEq argumentWire.value argument) do
    throwError "the operation changed its retained generalized argument occurrence"
  -- The original complete result retains the reader's selected endpoint presentations.
  -- The stripped declaration supplies the internal callable signature checked above.
  let argumentDomain ← match retained with
    | some retained => pure retained.argumentDomain
    | none => realizeCallableEndpoint h trace argumentWire resultDomain true
  let domainWire := argumentDomain
  let pointEndpoints ← if !wire.callableObserved && !wire.completedData &&
      operationRecipe wire id && recordSource.isSome && recordTarget.isSome then
    operationPointEndpoints? h trace dataContext entry application receiverWire argumentWire
      resultDomain originalSource resultTarget domainWire argumentWire.fragment parameterWires reader
  else pure none
  let (argumentData, argumentTemplate, endpoints, argumentChanged) ← match pointEndpoints with
    | some prepared => pure (prepared.argument, prepared.argumentTemplate, prepared.dependencies, false)
    | none => do
      let template ← match retained with
        | some retained => do
          let (original, _) ← renderCapturedActionData retained.argumentTemplate
          unless original == retained.argumentData do
            throwStratum .unavailable "the operation lost its exact original argument-field producer"
          pure retained.argumentTemplate
        | none => frameMorphismTemplate h trace resultDomain originalSource argumentWire (some dataContext)
      let originalTemplate := template
      let template ← mapActionTemplateWires reader.readData template
      let (data, dependencies) ← renderCapturedActionData template
      pure (data, template, dependencies, !sameActionTemplate originalTemplate template)
  -- Retain the canonical argumentDomain for replay, but prepare ordinary
  -- consumer endpoints with the same reader as the argument. A prepared point
  -- already owns its coupled endpoint/comparison frame and retains that frame.
  let domainWire ← match pointEndpoints with
    | some prepared => pure prepared.domain
    | none => reader.readData .object argumentDomain
  -- The argument's actual target supplies the selected input presentation. The
  -- declaration may expose only a reduced carrier with several accepted names;
  -- its complete equality with this original endpoint was checked above.
  let sourceWire ← match pointEndpoints with
    | some prepared => pure prepared.source
    | none => match recordSource with
      | some data => pure {
          form := .diagrams dataCategory
          payload := (← scopedPayload originalSource data receiverWire.completedData)
          categoryContext := some dataContext }
      | none => match retained with
        | some retained => pure retained.sourceWire
        | none => realizeCallableEndpoint h trace argumentWire originalSource false
  let sourceWire ← if pointEndpoints.isSome then pure sourceWire
    else reader.readData .object sourceWire
  let targetEndpoint : CallableEndpointData ← match pointEndpoints.bind (·.target) with
    | some target => pure { wire := target, origin := .retained }
    | none => match recordTarget with
      | some data => pure { origin := .retained, wire := {
          form := .diagrams dataCategory
          payload := (← scopedPayload resultTarget data receiverWire.completedData)
          categoryContext := some dataContext } }
      | none => match retained with
        | some retained =>
          if retained.targetOrigin == .reference then do
            let context ← framingContext (some dataContext) retained.targetWire.categoryContext
            pure {
              origin := .reference
              wire := ← callableEndpointReference callable resultTarget false context }
          else pure { wire := retained.targetWire, origin := .retained }
        | none =>
          realizeCallableEndpointWithOrigin h trace callable resultTarget false
            (some dataContext)
  let targetWire ← if (pointEndpoints.bind (·.target)).isSome then pure targetEndpoint.wire
    else reader.readData .object targetEndpoint.wire
  for (endpoint, expected) in #[(domainWire, resultDomain), (sourceWire, originalSource),
      (targetWire, resultTarget)] do
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType endpoint.value) (← inferType expected) <&&>
          isDefEq endpoint.value expected) do
      throwError "the operation changed a retained complete endpoint occurrence"
  if pointEndpoints.isNone then
    try
      let complete ← checkCapturedArgumentEndpoints dataContext argumentTemplate domainWire sourceWire
      if argumentChanged && !complete then
        throwStratum .noImplementation
          "the observed operation argument omitted its complete public endpoint interface"
    catch error =>
      match error with
      | .error ref message =>
          let details := Json.mkObj [
            ("phase", toJson phase), ("operation", toJson id.raw),
            ("result", operationEndpointDiagnosticSummary wire),
            ("owner", operationEndpointDiagnosticSummary receiverWire),
            ("originalArgument", operationEndpointDiagnosticSummary argumentWire),
            ("operationTarget", operationEndpointDiagnosticSummary targetWire),
            ("argumentChanged", toJson argumentChanged)]
          -- Keep the original syntax reference and complete MessageData tree,
          -- including its stratum tags. Internal exceptions are not rewritten.
          throw (.error ref (message ++ m!"\noperation preparation: {details.compress}"))
      | _ => throw error
  let callable ← retainCallableEndpoints callable sourceWire targetWire dataContext
  let frameCallable := pointEndpoints.isSome || sourceWire.endpointPresentation.isSome ||
    targetWire.endpointPresentation.isSome
  let (callable, callableDependencies) ← if frameCallable then do
      let dataParameters ← DirectConstruction.dataArguments parameters
      unless dataParameters.size == parameterData.size do
        throwError "the operation presentation lost a complete parameter occurrence"
      let localInputs ← IO.mkRef #[sourceWire, targetWire]
      let scope ← callableTemplateValidationScope dataContext operation callable.fragment
        descriptorTemplate (some localInputs) .logical
      let residual ← operationPresentationObjects parameterWires #[] (← localInputs.get)
      let declaredObjects ← reader.interfaceObjects
        (← mergeCallableInterfaceObjects residual objects)
      if let .error message ← ComputationalData.validateCallableAt declaredObjects
          (← inferType operation) callable.json (some scope) then
        throwStratum .malformed m!"the retained operation has incompatible complete parameters: {message}"
      let framed ← prepareMorphismFrameWith reader dataContext callable sourceWire targetWire
      let framed ← publicMorphismFrame dataContext sourceWire targetWire framed
      let scope ← callableTemplateValidationScope dataContext framed.actual
        framed.wire.fragment framed.template (some localInputs)
      let residual ← operationPresentationObjects
        (parameterWires ++ #[sourceWire, targetWire] ++ framed.dependencies) #[] (← localInputs.get)
      let actualObjects ← reader.interfaceObjects
        (← mergeCallableInterfaceObjects residual objects)
      validateOperationPresentationMap framed.actual framed.source.fragment framed.target.fragment
        framed.wire.fragment actualObjects (some scope)
      pure (framed.wire, framed.dependencies)
    else pure (callable, #[])
  let invocation ← pointInvocationData id.raw parameterData callable.fragment
    domainWire.fragment sourceWire.fragment targetWire.fragment argumentData
  let operands := #[wire, receiverWire, callable, argumentWire, domainWire, sourceWire, targetWire] ++
    parameterWires ++ endpoints ++ callableDependencies
  let handles ← if frameCallable then do
      let (_, handles) ← normalizeOperationProducts h dataContext operands parameterWires (← reader.objects)
      pure handles
    else retainServiceOperands h operands
  let input : Wire := {
    form := receiverWire.form
    payload := (← combinedRecipePayload formal invocation operands)
    serviceHandles := handles }
  return {
    original := wire
    operation := id
    trace, parameters, parameterOccurrences, owner := receiverWire
    argument := argumentWire, argumentDomain, argumentData, argumentTemplate,
    argumentDependencies := endpoints
    domainWire, sourceWire, targetWire, targetOrigin := targetEndpoint.origin
    input
    domain := resultDomain
    target := resultTarget
    targetData := targetWire.json
    materialized := wire.actualData || wire.callableObserved ||
      (!namedRecipe && !operationRecipe wire id) }

/-- Inspect one owner through current typed producers. The inspection harness
cannot dispatch, derive, or mutate live caches; only its resulting supplier
constraints will be used by ordinary registration admission. -/
partial def prepareProspectiveReader (h inspect : Harness) (trace : Trace)
    (owner : Wire) (inputs : Array Wire := #[]) : TermElabM ProspectiveReader := do
  let receipts ← h.actions.get
  let reserved := prospectiveReservedWire owner ++ inputs.flatMap prospectiveReservedWire ++
    (← h.serviceOperands.get).flatMap prospectiveReservedWire ++
    (← h.results.get).toArray.flatMap (fun (_, wire) => prospectiveReservedWire wire) ++
    receipts.flatMap (fun receipt => #[Json.arr receipt.parameters] ++
      (#[receipt.input, receipt.result] ++ receipt.parameterInputs ++ receipt.imageEndpoints).flatMap
        prospectiveReservedWire)
  let reserved := reserved ++ (← h.invocations.get).flatMap fun record =>
    prospectiveReservedWire record.input ++ prospectiveReservedInvocation record.captured.interface ++
      record.result.toArray.flatMap prospectiveReservedWire ++
      record.recordFields.toArray.flatMap (fun fields => fields.values.flatMap prospectiveReservedWire)
  let mut declaredLiterals : Array Json := #[]
  for record in ← h.invocations.get do
    if let .routed selected := record.captured.interface then
      declaredLiterals := declaredLiterals ++ (← routedReservedProjectionData selected)
  let reserved := reserved ++ declaredLiterals
  let state ← IO.mkRef ({ reserved } : ProspectiveData)
  let reader : ProspectiveReader := {
    live := h, inspect, trace, state
    objectTemplate := fun recipe original descriptor dependencies => do
      match recipe.owner with
      | .edge selected =>
          let encoder : ScopedActionEncoder := fun edge action => do
            unless edge == selected && (← withoutModifyingState (withTransparency .all <|
                isDefEq (← inferType action) (← inferType recipe.application) <&&>
                  isDefEq action recipe.application)) do
              throwError "the prospective descriptor changed its complete selected action"
            return (descriptor, dependencies)
          let (template, _, _) ← objectActionTemplate inspect trace selected
            recipe.application original (some encoder)
          pure template
      | .construction id _ =>
          capturedConstructionObjectTemplate id recipe.application recipe.target descriptor dependencies original
    invocation := fun owner descriptor morphism => do
      match owner with
      | .edge edge => edgeActionDataInvocation (← registryState) edge descriptor morphism
      | .construction id _ =>
          let some entry := (← registryState).constructions.find? (·.id == id)
            | throwError "the prospective construction lost its accepted operation"
          return (if morphism then entry.mapAddress else id.raw,
            ← capturedConstructionParameters id descriptor)
    endpoints := fun wire context => capturedMapEndpoints inspect trace wire context true }
  return reader

/-- Actual method execution uses one inert prospective reader for both complete
candidate envelopes. Only the selected boundary and registration leave this
scope; its private references never become service operands or actual results. -/
partial def routedInvocationRegistrations (h : Harness) (trace : Trace) (wire : Wire)
    (selected : SelectedRoutedInvocation) :
    TermElabM (SelectedRoutedBoundary × Option Registration) := do
  let privateTrace ← IO.mkRef (← trace.get)
  let inspect ← Harness.empty
  inspect.connections.set (← h.connections.get)
  inspect.serviceOperands.set (← h.serviceOperands.get)
  inspect.results.set (← h.results.get)
  let reader ← prepareProspectiveReader h inspect privateTrace wire
    (#[selected.original] ++ selected.boundaries.map (·.receiver))
  let literals ← routedReservedProjectionData selected
  reader.state.modify fun state => { state with
    reserved := state.reserved ++ prospectiveReservedInvocation (.routed selected) ++ literals,
    activeInvocations := h.invocationStack }
  let (boundary, registration, _) ← prospectiveRoutedSelectionWith reader selected
  return (boundary, registration)

/-- Read an owner inside one private prospective scope. Framing consumers that
need further outputs retain this reader until their whole request is validated. -/
partial def prospectiveOwnerData (h inspect : Harness) (trace : Trace) (owner : Wire)
    (inputs : Array Wire := #[]) (projectApex : Bool := false) :
    TermElabM (Wire × ComputationalData.InterfaceObjects) := do
  let reader ← prepareProspectiveReader h inspect trace owner inputs
  let owner ← prospectiveWireWith reader .object owner
  let owner ← if projectApex then
      prospectiveApexReceiver reader owner
    else pure owner
  return (owner, (← reader.state.get).objects)

/-- Admission projects only unfinished action output slots. Nested intrinsic
records retain every actual sibling and its suppliers. Future references are
bound solely in an isolated metadata harness; no projected Wire, cache entry,
service handle, receipt, or invocation escapes this check. -/
partial def operationObservationRegistrations (h : Harness) (request : OperationObservation) :
    TermElabM (Array Admitted) := do
  let privateTrace ← IO.mkRef (← request.trace.get)
  let inspect ← Harness.empty
  inspect.connections.set (← h.connections.get)
  inspect.serviceOperands.set (← h.serviceOperands.get)
  inspect.results.set (← h.results.get)
  let reader ← prepareProspectiveReader h inspect privateTrace request.owner #[request.input]
  let owner ← prospectiveWireWith reader .object request.owner
  let callableReader : CallablePreparationReader := {
    observe := fun context wire => do
      let projected ← prospectiveWireWith reader .map wire
      capturePointCallableWith reader.endpoints projected context
    observeData := prospectiveWireWith reader
    objects := do return (← reader.state.get).objects }
  -- Even an actual or unchanged owner can retain unfinished comparison maps.
  -- Their future slots and all known siblings belong to this same private scope.
  let projected ← prepareOperationObservation inspect privateTrace request.original request.operation
    request.parameters (some owner) (some request) (← reader.state.get).objects none
    (some callableReader) (phase := "prospective admission")
  unless projected.input.form.id == request.input.form.id &&
      (← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType projected.input.value) (← inferType request.input.value) <&&>
          isDefEq projected.input.value request.input.value)) do
    throwError "prospective admission changed the complete operation or input address: \
      operation {request.operation.raw}, original input {request.input.form.id}, \
      projected input {projected.input.form.id}"
  checkDataOwners h projected.input.fragment
  admittedRegistrations h request.operation.raw projected.input true

/-- Candidate preparation retains recipes. Only a selected direct target
registration demands its exact owner image, then rebuilds the complete request
with that actual data. Missing direct implementations keep the existing proved
derivation path; neither a primitive failure nor changed ownership selects a
different direct registration after this boundary. -/
partial def executeOperationObservation (h : Harness) (request : OperationObservation)
    (selected : Option Registration := none) :
    TermElabM Wire := do
  if request.materialized then return request.original
  let registrations ← if selected.isNone then operationObservationRegistrations h request
    else pure #[]
  if selected.isNone && registrations.isEmpty then
    return ← dispatchOperationObservation h request
  let selected ← match selected with
    | some selected => pure selected
    | none => do
      match registrations with
      | #[selected] => pure selected.registration
      | _ =>
        let choices := registrations.map fun row =>
          (row.registration.operation, row.registration.input, row.registration.backend)
        throwStratum .ambiguousRealization
          m!"several admitted registrations compute the selected operation: {choices}"
  let owner ← realizeObjectObservation { h with demandObjectActions := true }
    request.trace request.owner
  -- Registration selection precedes every new comparison computation. The
  -- exact original operands are rebuilt even when their owner packet is unchanged.
  let reader : CallablePreparationReader := {
    observe := fun context wire => do
      let actual ← realizeArrowObservation { h with demandObjectActions := true } request.trace wire
      capturePointCallable h request.trace actual context
    observeData := observeActionDataWire { h with demandObjectActions := true } request.trace }
  let actual ← prepareOperationObservation h request.trace request.original request.operation
    request.parameters (some owner) (some request) #[] none (some reader)
    (phase := "selected execution")
  dispatchOperationObservation h actual (some selected)

/-- Observe the canonical preparation selected by an encapsulated owner reference.
The reference carries its immutable original input and interface together; no
second caller-supplied body participates in execution or completion. -/
partial def observePreparedInvocation (h : Harness) (trace : Trace)
    (prepared : PreparedInvocation) : TermElabM Wire := do
  let records ← h.invocations.get
  let selected := (records.zipIdx).filter fun (record, _) =>
    record.prepared.same prepared
  let #[(record, position)] := selected
    | throwStratum .unavailable "the invocation's unique owning preparation scope has expired"
  let captured := record.captured
  if record.input.completedData then
    throwStratum .unavailable "actual received data cannot be replayed as a prepared invocation"
  if captured.interface.staged then
    throwError "a staged selected invocation requires its demand/resume owner"
  if let some result := record.result then
    checkCapturedResultInterface result record.captured.interface.result
    checkDataOwners h result.fragment
    return ← forwardRetainedValue result record.input.value
  if h.invocationStack.contains captured.occurrence then
    throwStratum .unavailable "the captured computation has cyclic operand dependencies"
  let active := { h with invocationStack := h.invocationStack.push captured.occurrence }
  let (result, recordFields) : Wire × Option RetainedResultFields ← match record.captured.interface with
    | .intrinsic _ => do
        let active := { active with demandObjectActions := true }
        let result ← observeCurrentIntrinsicAssemblyWith
          (fun role input => match role with
            | .map => realizeArrowObservation active trace input
            | _ => observeActionDataWire active trace role input)
          (fun input context => capturedMapEndpoints active trace input context true)
          active record.input
        pure (result, none)
    | .callable selected => do
      pure (← observeSelectedCallable active trace record.input selected, none)
    | .structured selected => do
      let result ← observeStructuredInvocationWith
        realizeObjectObservation (fun h trace wire => realizeArrowObservation h trace wire)
        (fun h trace wire context endpoints publicFrame =>
          captureCompleteCallable h trace wire context endpoints publicFrame)
        active trace selected
      pure (result, none)
    | .projection selected => do
      pure (← observeStructuredProjection active trace record.input selected, none)
    | .recordProjection selected => do
      pure (← observeRecordProjection active trace selected
        (actualRoutedKnownField active trace), none)
    | .routed selected => observeRoutedInvocation active trace record.input selected
    | .prescribed selected => pure (← observePrescribedInvocation active trace selected
        (actualPrescribedRouteInputs active trace), none)
    | .directLift _ | .liftField _ | .liftFactor _ =>
        throwError "a staged selected invocation escaped its demand/resume owner"
  let result ← completeCapturedInvocation h position record result recordFields
  forwardRetainedValue result record.input.value

/-- Authenticate a separately supplied Wire before entering its canonical owner.
A copied alias or invocation ID cannot install a different producer body. -/
partial def observeCapturedInvocation (h : Harness) (trace : Trace) (wire : Wire)
    (captured : CapturedInvocation) : TermElabM Wire := do
  if captured.interface.staged then
    return ← demandCapturedInvocation h trace wire captured
  let some current ← retainedCapturedInvocation? wire
    | throwStratum .unavailable "the invocation has no current complete producer occurrence"
  unless current.occurrence == captured.occurrence do
    throwError "the invocation observer changed its retained occurrence identity"
  let records ← h.invocations.get
  let selected := records.filter (·.captured.occurrence == captured.occurrence)
  let #[record] := selected
    | throwStratum .unavailable "the invocation's unique owning preparation scope has expired"
  let original ← forwardRetainedValue record.input wire.value
  unless sameCompleteWireContext original { wire with capturedInvocation := none } do
    throwStratum .unavailable "the invocation changed its original complete typed input occurrence"
  let result ← observePreparedInvocation h trace record.prepared
  forwardRetainedValue result wire.value

/-- The only invocation-completion write. Both original protocols and staged
requests validate their complete result against the immutable canonical input. -/
partial def completeCapturedInvocation (h : Harness) (position : Nat)
    (record : InvocationExecution) (result : Wire)
    (recordFields : Option RetainedResultFields := none) : TermElabM Wire := do
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType result.value) (← inferType record.input.value) <&&>
        isDefEq result.value record.input.value) do
    throwError "the completed invocation changed its independently selected result"
  let result ← forwardRetainedValue result record.input.value
  checkCapturedResultInterface result record.captured.interface.result
  let retainedProducer := record.captured.interface.retainsResultOccurrence ||
    (match record.captured.interface with | .routed _ => recordFields.isNone | _ => false)
  let result := if retainedProducer then result
    else { result with capturedInvocation := some record.captured }
  checkDataOwners h result.fragment
  let some current := (← h.invocations.get)[position]?
    | throwStratum .unavailable "the invocation's original completion scope has expired"
  unless current.prepared.same record.prepared do
    throwStratum .unavailable "the invocation changed its canonical prepared input before completion"
  unless current.result.isNone do
    throwError "an invocation cannot independently install a second completion"
  h.invocations.modify fun records => records.modify position fun item =>
    { item with result := some result, recordFields }
  return result

/-- Authenticate the pending reference at entry; the stored interface is the
only request executed. A copied occurrence ID cannot substitute another body. -/
partial def capturedInvocationFrame (h : Harness) (wire : Wire)
    (captured : CapturedInvocation) : TermElabM InvocationFrame := do
  let some current ← retainedCapturedInvocation? wire
    | throwStratum .unavailable "the invocation lost its current complete preparation reference"
  unless current.occurrence == captured.occurrence do
    throwError "the demand changed its original invocation occurrence"
  let records ← h.invocations.get
  let positions := (records.zipIdx).filter (fun (record, _) =>
    record.captured.occurrence == captured.occurrence)
  let #[(record, position)] := positions
    | throwStratum .unavailable "the invocation lost its unique original preparation scope"
  let original ← forwardRetainedValue record.input wire.value
  unless sameCompleteWireContext original { wire with capturedInvocation := none } do
    throwStratum .unavailable "the invocation changed its original complete typed input"
  let operands ← match record.captured.interface with
    | .directLift selected => pure selected.operands
    | .liftField selected => pure #[← invocationOperand .object selected.parent]
    | .liftFactor selected => pure selected.operands
    | _ => pure #[]
  return { position, record, operands }

/-- Resume a fixed selected plan after all of its exact operand positions
returned. This function has no expression reader or dependency observation. -/
partial def resumeCapturedInvocation (h : Harness) (trace : Trace)
    (frame : InvocationFrame) : TermElabM Wire := do
  unless frame.returned.size == frame.operands.size do
    throwError "a selected invocation resumed before all required operands returned"
  match frame.record.captured.interface with
  | .directLift selected =>
      let prepared ← directLiftInputs h selected frame.returned
      let result ← LiftStageExecution.fold Wire.fragment prepared.input
        (fun _ => pure none)
        (observeLiftStageFieldWithInputs h prepared.input selected.formal prepared.form
          prepared.dependencies (some prepared.staticInputPaths))
        liftStageEndpoints
      directLiftResult h selected prepared result
  | .liftField selected =>
      let some parent := frame.returned[0]?
        | throwError "the selected field resumed without its parent construction"
      let some execution := parent.liftExecution
        | throwError "the selected field's parent omitted its complete lift data"
      unless execution.selections.size == selected.plans.size do
        throwError "the selected field changed its original construction stage count"
      for (expected, actual) in selected.plans.zip execution.selections do
        checkRetainedLiftPlan expected actual
      let some output := (← captureLiftFields h execution)[selected.index]?
        | throwError "the selected field lost its fixed output position"
      let output ← forwardRetainedValue output selected.formal
      checkCapturedResultInterface output selected.result
      return { output with
        form := frame.record.input.form,
        liftExecution := if selected.index == 0 then some execution else none
        serviceHandles := parent.serviceHandles ++ execution.stageHandles.flatMap (·.all) ++
          output.serviceHandles }
  | .liftFactor selected =>
      let #[parent, base, cone] := frame.returned
        | throwError "the selected factor lost an exact operand position"
      let some execution := parent.liftExecution
        | throwError "the selected factor's parent omitted its complete construction"
      let output ← completeRetainedLiftFactor h trace selected parent base cone execution
      return { output with form := frame.record.input.form }
  | _ => throwError "an unstaged protocol cannot resume as a selected lift"

/-- Enter, suspend and return through the existing invocation table. Adapted
from PolyFun/PFunctor/Free/HandlerMachine.lean, Phase/runPrefix/result at
b13c074410a955407886cb3fe27e59130aeac090 (Apache-2.0; Devon Tuma).
The selected plan is suspended at its exact next operand position. A dependency
return fills that position only after type, context and owner validation. Field
requests keep this caller frame until their prepared reply validators return;
neither a reply nor an alternate result cache can manufacture completion. -/
partial def demandCapturedInvocation (h : Harness) (trace : Trace) (wire : Wire)
    (captured : CapturedInvocation) : TermElabM Wire := do
  let first ← capturedInvocationFrame h wire captured
  if let some result := first.record.result then
    checkCapturedResultInterface result first.record.captured.interface.result
    checkDataOwners h result.fragment
    return ← forwardRetainedValue result wire.value
  if h.invocationStack.contains captured.occurrence then
    throwStratum .unavailable "the captured computation has cyclic operand dependencies"
  let mut callers := #[first]
  while !callers.isEmpty do
    let some frame := callers.back?
      | throwError "the invocation driver lost its suspended caller"
    let stack := h.invocationStack ++ callers.map (·.record.captured.occurrence)
    let active := { h with invocationStack := stack, demandObjectActions := true }
    if let some operand := frame.operands[frame.returned.size]? then
      let mut returned : Option Wire := none
      if operand.role == .retained then returned := some operand.wire
      else if let some dependency ← retainedCapturedInvocation? operand.wire then
        if dependency.interface.staged then
          if stack.contains dependency.occurrence then
            throwStratum .unavailable "the selected computation has cyclic operand dependencies"
          let child ← capturedInvocationFrame h operand.wire dependency
          if let some result := child.record.result then
            checkCapturedResultInterface result child.record.captured.interface.result
            checkDataOwners h result.fragment
            returned := some (← forwardRetainedValue result operand.formal)
          else callers := callers.push child
        else returned := some (← observeActionDataWire active trace operand.role operand.wire)
      else returned := some (← observeActionDataWire active trace operand.role operand.wire)
      let some dependencyResult := returned | continue
      let dependencyResult ← checkInvocationOperand operand dependencyResult
      checkDataOwners h dependencyResult.fragment
      callers := callers.set! (callers.size - 1)
        { frame with returned := frame.returned.push dependencyResult }
    else
      let result ← resumeCapturedInvocation active trace frame
      let result ← completeCapturedInvocation h frame.position frame.record result
      callers := callers.pop
      if callers.isEmpty then return ← forwardRetainedValue result wire.value
      let some parent := callers.back?
        | throwError "the invocation return lost its suspended parent"
      let some operand := parent.operands[parent.returned.size]?
        | throwError "the invocation return has no selected parent operand position"
      let result ← checkInvocationOperand operand result
      checkDataOwners h result.fragment
      callers := callers.set! (callers.size - 1)
        { parent with returned := parent.returned.push result }
  throwError "the invocation driver exited without a validated result"

/-- Observe the original typed inputs of one selected registered invocation.
No trace expression or cache entry can replace a captured parameter, receiver,
base map, or endpoint. Actual replies retain their distinct completed origin. -/
partial def observeSelectedCallable (h : Harness) (trace : Trace) (wire : Wire)
    (selected : SelectedCallableInvocation) : TermElabM Wire := do
  checkSelectedCallableInvocation wire selected
  let state ← registryState
  let some operation := state.operation? selected.address
    | throwError "the captured callable operation is no longer registered"
  match selected.operationRequest, operation with
  | some request, .operation entry =>
      unless entry.id == request.operation && request.parameters ==
          selected.declarationParameters.map (·.formal) do
        throwError "the captured callable changed its existing operation-owner request"
      let actual ← executeOperationObservation h request
      let actual ← forwardRetainedValue actual wire.value
      if actual.pointDataInterface.isSome then
        return ← captureCompleteCallable h trace actual selected.context
      return actual
  | some _, _ | none, .operation _ =>
      throwError "the captured callable changed its independently selected dispatch owner"
  | none, _ => pure ()
  let h := { h with demandObjectActions := true }
  let observed ← IO.mkRef (#[] : Array (ActionDataRole × Wire × Wire))
  let observe := fun (role : ActionDataRole) (original : Wire) => do
    if let some (_, _, actual) := (← observed.get).find? (fun (selected, input, _) =>
        selected == role && sameCompleteWireContext input original) then return actual
    let actual ← observeActionDataWire h trace role original
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType actual.value) (← inferType original.value) <&&>
          isDefEq actual.value original.value) do
      throwError "the callable input changed its complete independently selected value"
    let actual ← forwardRetainedValue actual original.value
    observed.modify (·.push (role, original, actual))
    return actual
  -- Both templates share the same exact operand occurrences. Memoization is
  -- by complete typed selection, never by equal bytes or formal cache keys.
  let (descriptor, descriptorInputs) ← renderActionDataWith observe selected.descriptor
  let parameters ← selected.parameters.mapM (renderActionDataWith observe)
  let raw : Wire := { wire with
    payload := (← combinedRecipePayload wire.value descriptor descriptorInputs)
    categoryContext := some selected.context
    capturedInvocation := none, callableEndpoints := none
    intrinsicAssembly := none, actionRecipe := none
    morphismFramed := false, morphismFraming := none }
  let endpoint := fun (original : Wire) (origin : CallableEndpointOrigin) (source : Bool) => do
    match origin with
    | .retained => observe .object original
    | .reference => callableEndpointReference raw original.value source (some selected.context)
  let source ← endpoint selected.source selected.sourceOrigin true
  let target ← endpoint selected.target selected.targetOrigin false
  CategoryContext.checkMorphism selected.context wire.value source.value target.value
  let framed ← presentMorphism raw source target (some selected.context)
  let dependencies := descriptorInputs ++
    parameters.foldl (fun inputs item => inputs ++ item.2) #[] ++
    (← observed.get).map (·.2.2)
  dispatchSelectedCallable h wire selected (parameters.map Prod.fst) framed
    source target dependencies

/-- Compatibility entry point for callers that already hold the producer's
complete selected invocation. Supplied metadata checks that same record; it
cannot reconstruct a missing producer from trace expressions or a cache. -/
partial def realizeCallableObservation (h : Harness) (trace : Trace) (wire : Wire)
    (address : String) (parameters : Array DataOwnership.Data) (_dependencies : Array Wire := #[])
    (inverse : Option Bool := none) : TermElabM Wire := do
  if wire.callableObserved || wire.actualData then return wire
  let some captured ← retainedCapturedInvocation? wire
    | throwStratum .noImplementation "the pending callable has no retained typed invocation"
  let some selected ← retainedSelectedCallableInvocation? wire
    | throwStratum .noImplementation "the pending callable has no retained typed invocation"
  let original ← selected.parameters.mapM renderCapturedActionData
  unless address == selected.address && inverse == selected.inverse &&
      parameters == original.map Prod.fst do
    throwError "the callable observation changed its original selected invocation metadata"
  observeCapturedInvocation h trace wire captured

/-- Demand the computational value of an entire arrow. Merely forming a named arrow,
including one used inside a later point invocation, retains its public descriptor.
Only this observation demand dispatches that descriptor. Structural composites are
rebuilt from the observed children through the ordinary checked realization paths,
retaining their exact endpoint frames, declared actions and session dependencies. -/
partial def realizeArrowObservation (h : Harness) (trace : Trace) (wire : Wire)
    (registeredOnly : Bool := false) :
    TermElabM Wire := do
  if let some framing := wire.morphismFraming then
    let reader : CallablePreparationReader := {
      observe := fun context input => do
        let actual ← realizeArrowObservation h trace input registeredOnly
        capturePointCallable h trace actual context
      observeData := observeActionDataWire { h with demandObjectActions := true } trace }
    let prepared ← observeRetainedMorphismFrameWith reader wire framing
    let result := prepared.wire
    return { result with
      serviceHandles := result.serviceHandles ++ (← retainServiceOperands h prepared.dependencies) }
  if wire.callableObserved || wire.actualData then return wire
  if (← retainedIntrinsicAssembly? wire .map).isSome then
    return ← observeCurrentIntrinsicAssembly h trace wire registeredOnly
  if let some recipe := wire.actionRecipe then
    unless recipe.morphism do
      throwError "a map observation cannot consume a retained object-action role"
    return ← observeActionRecipe h trace wire recipe
  if let some captured ← retainedCapturedInvocation? wire then
    unless captured.interface.result.role == .map do
      throwError "a map observation cannot consume another declared result role"
    return ← observeCapturedInvocation h trace wire captured
  let formal := wire.value
  let some node ← (trace.node? formal : IO _) | return wire
  let rebuild (children : Array Expr) : TermElabM Wire := do
    for child in children do
      let input ← realize h trace "the observed arrow's constituent" child
      let actual ← realizeArrowObservation h trace input registeredOnly
      -- The recursive observation caches actual returned data. Ordinary descriptors
      -- remain ordinary inputs and are not promoted to computed values by this demand.
      match actual.payload with
      | .ordinary .. => pure ()
      | _ =>
          if !child.hasMVar && !child.hasLevelMVar && !child.hasFVar && !child.hasLooseBVars then
            h.results.modify (·.insert child actual)
    realizeFresh h trace "the observed complete arrow" formal
  let tag := (wire.json.getObjValAs? String "ctor").toOption
  let actual ← match node with
    | .operationEquivalence representative chosen candidates comparisons => do
        checkOperationEquivalence formal representative chosen candidates comparisons
        -- Use the incoming actual payload at the verified original trace. In particular,
        -- a returned whole callable does not become its formal recipe when only the
        -- transparent wrapper is present in the result cache.
        let input := { wire with payload := forwardPayload wire representative wire.json }
        let some representativeNode ← trace.node? representative
          | throwError "the checked operation class lost its selected trace"
        let operationId ← match representativeNode with
          | .operationApply id .. | .operationPoint id .. => pure id
          | _ => throwError "the checked operation class has no complete operation trace"
        if let some actual := operationRecipeId? input then
          unless actual == operationId.raw do
            throwError "the operation class's representative has a different retained recipe"
        unless operationRecipe input operationId do return wire
        if registeredOnly && !h.admitted.any (fun admitted =>
            candidates.any (·.operation.raw == admitted.registration.operation)) then
          unless ← candidates.anyM (fun candidate => hasGroundedDerivation h candidate.operation.raw) do
            return wire
        let mut applicable : Array (OperationObservation × Registration) := #[]
        let mut requests : Array OperationObservation := #[]
        for candidate in candidates do
          let candidateWire ← if candidate.result == representative then pure input
            else realizeUnobserved h trace "a checked equivalent operation's complete result" candidate.result
          let some candidateNode ← trace.node? candidate.result
            | throwError "a checked equivalent operation lost its retained trace"
          let (id, parameters) ← match candidateNode with
            | .operationApply id parameters .. | .operationPoint id parameters .. =>
                pure (id, parameters)
            | _ => throwError "a checked equivalent operation lost its exact callable address"
          unless id == candidate.operation do
            throwError "a checked equivalent operation changed its accepted address"
          let request ← prepareOperationObservation h trace candidateWire id parameters
          requests := requests.push request
          let registrations ← operationObservationRegistrations h request
          applicable := applicable ++ registrations.map (fun admitted => (request, admitted.registration))
        let mut selected : Option (OperationObservation × Wire) := none
        let mut gaps : Array String := #[]
        match applicable with
          | #[(request, registration)] =>
              selected := some (request, ← executeOperationObservation h request (some registration))
          | #[] =>
              -- The whole-family operation agreement was checked above. A
              -- proved plan computes one of these fixed meanings; it cannot
              -- create another route or hide an ambiguous direct registration.
              for request in requests.qsort (fun left right => left.operation.raw < right.operation.raw) do
                unless ← hasGroundedDerivation h request.operation.raw do continue
                let failures ← h.portFailures.get
                try
                  selected := some (request, ← executeOperationObservation h request)
                  break
                catch error =>
                  unless !Exception.hasConflictingStrata error &&
                      Exception.stratum? error == some .noImplementation &&
                      (← h.portFailures.get) == failures do throw error
                  gaps := gaps.push (← error.toMessageData.toString)
          | _ => do
              let choices := applicable.map fun (_, registration) =>
                (registration.operation, registration.input, registration.backend)
              throwStratum .ambiguousRealization m!"several admitted registered requests compute the checked operation class: {choices}"
        let some (request, actual) := selected
          | if registeredOnly then return wire else
            throwStratum .noImplementation m!"no admitted registration or applicable proved plan computes the checked operation class {candidates.map (·.operation.raw)}; {gaps}"
        match actual.payload with
        | .ordinary .. => pure ()
        | _ => h.results.modify (·.insert request.original.value actual)
        let framed ← forwardOperationEquivalent formal representative actual
        -- The canonical formal interface is unchanged; only the checked candidate's
        -- actual returned data and owning session cross the equality substitution.
        let result := { wire with
          payload := framed.payload, callableObserved := framed.callableObserved
          pointDataInterface := framed.pointDataInterface
          morphismFramed := framed.morphismFramed, morphismFraming := framed.morphismFraming
          actionRecipe := framed.actionRecipe, intrinsicAssembly := framed.intrinsicAssembly
          callableEndpoints := framed.callableEndpoints }
        match result.payload with
        | .ordinary .. => pure ()
        | _ =>
          let retained ← forwardRetainedValue result representative
          h.results.modify (·.insert representative retained)
        pure result
    | .namedMorphism id _ => do
        unless tag == some id.raw do return wire
        throwStratum .noImplementation "the pending named map has no retained typed invocation"
    | .namedCallable address _ _ => do
        unless tag == some address do return wire
        throwStratum .noImplementation "the pending named callable has no retained typed invocation"
    | .presentation _ _ _ => do
        unless tag == some "presentation" do return wire
        throwStratum .noImplementation "the pending presentation has no retained typed invocation"
    | .cellComponent .. => do
        unless tag == some "cellComponent" || tag == some "constructedCellComponent" do return wire
        throwStratum .noImplementation "the pending component has no retained typed invocation"
    | .cartesian _ _ _ _ "hom" => do
        unless tag == some "cartesianMap" do return wire
        throwStratum .noImplementation "the pending cartesian map has no retained typed invocation"
    | .constructionMap .. =>
        throwStratum .noImplementation
          "the pending construction map has no retained typed producer occurrence"
    | .operationApply id parameters _ _ _ | .operationPoint id parameters .. => do
        unless operationRecipe wire id do return wire
        let derived ← hasGroundedDerivation h id.raw
        if registeredOnly && !derived &&
            !h.admitted.any (·.registration.operation == id.raw) then return wire
        let request ← prepareOperationObservation h trace wire id parameters
        let direct ← operationObservationRegistrations h request
        if registeredOnly && !derived && direct.isEmpty then
          return wire
        let failures ← h.portFailures.get
        try executeOperationObservation h request
        catch error =>
          if registeredOnly && direct.isEmpty && !Exception.hasConflictingStrata error &&
              Exception.stratum? error == some .noImplementation &&
              (← h.portFailures.get) == failures then return wire
          throw error
    | .admittedPoint .. | .constrainedPoint .. | .elementValue .. =>
        throwStratum .noImplementation
          "the intrinsic point or value has no current retained typed child occurrences"
    | .morphismComposition .. | .contextualComposition .. | .callableRecipe .. |
        .contextualIdentity .. =>
        throwStratum .noImplementation
          "the intrinsic callable has no current retained typed child occurrences"
    | .morphismTransport _ _ route _ | .contextualRoute _ _ route _ _ true =>
        if route.isEmpty then return wire
        throwStratum .noImplementation
          "the pending map action has no retained typed producer occurrence"
    | _ => pure wire
  if !formal.hasMVar && !formal.hasLevelMVar && !formal.hasFVar && !formal.hasLooseBVars then
    match actual.payload with
    | .ordinary .. => pure ()
    | _ => h.results.modify (·.insert formal actual)
  return actual

end

/-- Materialize a retained generalized operation through its complete public port. -/
partial def realizeOperationObservation (h : Harness) (trace : Trace) (wire : Wire)
    (id : OperationId) (parameters : Array Expr) : TermElabM Wire := do
  if let some actual := operationRecipeId? wire then
    unless actual == id.raw do
      throwError "the retained operation recipe changed its accepted operation"
  unless operationRecipe wire id do return wire
  executeOperationObservation h (← prepareOperationObservation h trace wire id parameters)


-- Legacy prescribed lift adapter
/-- Recover raw inspection arguments from their independently fixed formal
roles and explicit retained dependencies. The private cache never chooses
between distinct occurrences with the same formal key and never starts a port. -/
def legacyLiftRecovery (h : Harness) (dependencies : Array Wire) : TermElabM Harness := do
  let mut supplied : Array Wire := #[]
  for dependency in dependencies do
    discard <| checkedFragment dependency.fragment.validate
    if let some previous := supplied.find? (·.value == dependency.value) then
      unless sameActionOperand previous dependency do
        throwStratum .unavailable "the raw lift arguments have distinct retained occurrences of one formal dependency"
    else supplied := supplied.push dependency
  let results ← IO.mkRef (← h.results.get)
  for dependency in supplied do
    results.modify (·.insert dependency.value dependency)
  return { h with
    results := results
    admitted := #[]
    backends := #[]
    deferred := none
    derivation := none
    dispatches := none }

/-- Raw inspection compatibility only. The scoped legacy adapter is
`executePrescribedLiftData`; production retains actual route images through
`executePrescribedRetainedWith`.
The old result can retain at most one supplying session, so a multi-supplier
result must use the scoped interface rather than discard occurrence ownership. -/
def executePrescribedLift (h : Harness) (trace : Trace) (plan : LiftedSubobjectData.Plan)
    (source base : Wire) (parameters : Array (Array Json × Array Wire))
    (encoder? : Option ActionEncoder := none) :
    TermElabM (Json × Option (String × Nat)) := do
  unless parameters.size == plan.components.size do
    throwError "the prescribed lift lost its complete selected evidence parameters"
  let state ← registryState
  let mut edges : Array EdgeRef := #[]
  let mut rawActions : Array (Option (Json × Array Wire)) := #[]
  for component in plan.components do
    let some row := state.lifts.find? (·.id == component.lift)
      | throwError "the fixed lift plan lost its registered row"
    let .constructMap _ inner := row.edge
      | throwError "the fixed lift plan lost its selected inner action"
    edges := edges.push inner
    rawActions := rawActions.push (← match encoder? with
      | some encoder => some <$> encoder inner component.action
      | none => pure none)
  let mut scopedParameters : Array (Array DataOwnership.Data × Array Wire) := #[]
  let mut scopedActions : Array (EdgeRef × Expr × DataOwnership.Data × Array Wire) := #[]
  for (component, index) in plan.components.zipIdx do
    let actionDependencies := (rawActions[index]!.map Prod.snd).getD #[]
    let recovery ← legacyLiftRecovery h (parameters[index]!.2 ++ actionDependencies)
    let fixed ← DirectConstruction.dataArguments component.selection.parameters
    let (actualParameters, parameterDependencies) ← realizedParameterData recovery trace fixed
    unless actualParameters.map (·.json) == parameters[index]!.1 &&
        sameActionOperands parameterDependencies parameters[index]!.2 do
      throwStratum .unavailable "the raw lift parameters differ from their exact independently retained data or dependencies"
    let (actualAction, actualDependencies) ← realizedEdgeData recovery trace edges[index]! component.action
    if let some (rawAction, dependencies) := rawActions[index]! then
      unless rawAction == actualAction.json && sameActionOperands dependencies actualDependencies do
        throwStratum .unavailable "the raw lift action differs from its exact independently retained descriptor or dependencies"
    scopedParameters := scopedParameters.push (actualParameters, parameterDependencies)
    scopedActions := scopedActions.push (edges[index]!, component.action, actualAction, actualDependencies)
  let position ← IO.mkRef (0 : Nat)
  let encoder : ScopedActionEncoder := fun edge action => do
    let index ← position.modifyGet fun index => (index, index + 1)
    let some (expectedEdge, expectedAction, descriptor, dependencies) := scopedActions[index]?
      | throwError "the scoped lift encoder requested an unretained stage"
    unless edge == expectedEdge && action == expectedAction do
      throwError "the scoped lift encoder changed its independently selected stage"
    return (descriptor, dependencies)
  let data ← executePrescribedLiftData h trace plan source base scopedParameters (some encoder)
  unless (← position.get) == scopedActions.size do
    throwError "the scoped lift encoder omitted a selected stage"
  let owner ← match DataOwnership.owners data.ownership with
    | #[] => pure none
    | #[owner] => pure (some owner)
    | _ =>
      throwStratum .noImplementation
        "the legacy raw lift interface cannot retain multiple supplying sessions; use the scoped interface"
  return (data.json, owner)
-- End legacy prescribed lift adapter

/-- Raw inspection interfaces preserve the existing engineering consumers.
Production assembly uses the fragment-returning owners above. -/
def realizedParameters (h : Harness) (trace : Trace) (parameters : Array Expr) :
    TermElabM (Array Json × Array Wire) := do
  let (data, dependencies) ← realizedParameterData h trace parameters
  return (data.map (·.json), dependencies)

def realizedEdgeDescriptor (h : Harness) (trace : Trace) (edge : EdgeRef) (actual : Expr) :
    TermElabM (Json × Array Wire) := do
  let (data, dependencies) ← realizedEdgeData h trace edge actual
  return (data.json, dependencies)

def elementExpression (h : Harness) (trace : Trace) (value : Expr) :
    TermElabM (Json × Array Wire) := do
  let (data, dependencies) ← elementFragment h trace value
  return (data.json, dependencies)

def frameMorphismData (h : Harness) (trace : Trace) (source target : Expr)
    (wire : Wire) (context : Option CategoryContext := none) :
    TermElabM (Json × Array Wire) := do
  let (data, dependencies) ← frameMorphismFragment h trace source target wire context
  return (data.json, dependencies)

/-- Select the equality observation by its declared syntax and complete signature.
The registered power object supplies the truth-value object. Every candidate is
checked on fresh arguments against equality, so another predicate with the same
spelling cannot observe the fixed question. No stable row identifier or row order
selects its mathematical meaning. The returned parameters are the actual closed
explicit data parameters of the accepted declaration. -/
def equalityObservation (state : RegistryState) (target : Expr) :
    TermElabM (MorphismEntry × Expr × Array Expr × Expr × Expr) := do
  let power ← Language.powerObjectIn state CategoryId.sets
  let truth ← instantiateFresh power.truth
  let some (_, omega) := Language.homEnds? (← inferType truth)
    | throwError "the registered truth map has no complete target"
  let source ← mkAppM ``Prod #[target, target]
  let mut candidates := #[]
  for entry in state.morphisms do
    unless entry.name == "=" && entry.category == CategoryId.sets do continue
    let candidate ← withoutModifyingState do
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType declaration)
      let some (input, output) := Language.homEnds? type | return none
      unless (← withTransparency .all <| isDefEq input source) &&
          (← withTransparency .all <| isDefEq output omega) do return none
      let .ok arrow ← completeArrow declaration parameters | return none
      let function ← Language.functionOf arrow
      let identifies ← withLocalDeclD `x target fun x =>
        withLocalDeclD `y target fun y => do
          let pair ← mkAppM ``Prod.mk #[x, y]
          withTransparency .all <| isDefEq (mkApp function pair) (← mkEq x y)
      unless identifies do return none
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      let mut data := #[]
      for (parameter, info) in parameters.zip infos do
        let parameter ← instantiateMVars parameter
        if info.isExplicit && !(← isProp (← inferType parameter)) then
          data := data.push parameter
      return some (entry, arrow, data, ← instantiateMVars input, ← instantiateMVars output)
    if let some candidate := candidate then candidates := candidates.push candidate
  match candidates with
  | #[candidate] => return candidate
  | #[] =>
    throwStratum .noImplementation
      "the selected carrier has no registered equality observation with the complete declared meaning"
  | _ =>
    throwStratum .ambiguousRealization
      "the selected carrier has several registered equality observations"

/-- Observe the actual data of two points through the uniquely registered equality
characteristic map. The response is computational data and supplies no proof. -/
def observeEquality (h : Harness) (trace : Trace) (first second : Wire) (domain target : Expr) :
    TermElabM Bool := do
  let state ← registryState
  let (equality, arrow, parameterValues, _, truth) ← equalityObservation state target
  for object in #[domain, target, truth] do
    discard <| Semantic.recordNamedObject object (some trace)
  let domainWire ← realize h trace "the computational equality's point domain" domain
  let valueWire ← realize h trace "the computational equality's selected carrier" target
  let sourceData ← scopedNode "objectProduct" #[valueWire.fragment, valueWire.fragment]
  let truthWire ← realize h trace "the computational equality's truth-value carrier" truth
  let (parameters, parameterWires) ← realizedParameterData h trace parameterValues
  let invocation ← pointInvocationData equality.id.raw parameters
    (← scopedNode equality.id.raw parameters) domainWire.fragment sourceData truthWire.fragment
    (DataOwnership.Data.array #[first.fragment, second.fragment])
  let payload ← combinedRecipePayload arrow invocation
    (#[first, second, domainWire, valueWire, truthWire] ++ parameterWires)
  let request : Wire := {
    form := .namedMorphism equality, payload
    serviceHandles := (← retainLiftOperands h
      (#[first, second, domainWire, valueWire, truthWire] ++ parameterWires)) }
  let reply ← sendData h equality.id.raw request (completeRequest := true)
  let answer := reply.data.json
  let backend := reply.backend
  match Backend.ComputationalValue.decode answer with
  | .ok (.inline (.bool truth)) => return truth
  | .ok _ => malformed backend equality.id.raw answer "the declared truth observation requires inline Boolean data"
  | .error message => malformed backend equality.id.raw answer message

/-- Evaluate the recorded decision `p` to a three-valued answer (`Option Bool`), through the
admitted registration of its property on the form of its receiver, sent along the resolved
route. -/
partial def realizeDecision (h : Harness) (trace : Trace) (what : String) (p : Expr) :
    TermElabM (Expr × Json) := do
  let p ← instantiateMVars p
  let some (.property id route receiver recordedComparisons) ← (trace.node? p : IO _)
    | do
      -- `¬ q` (`x ∉ A`) is the negated decision of `q`.
      if let some q := p.not? then
        let (answer, json) ← realizeDecision h trace what q
        return (← mkAppM ``Option.map #[mkConst ``not, answer], json)
      -- A truth value compared with `⊤` (`x ∈ A`) is an equation between two points
      -- `1 ⟶ Ω`: it is observed through the registered equality of `Ω`.
      if let some (_, a, b) := p.eq? then
        if (← (trace.node? a : IO _)).isSome && (← (trace.node? b : IO _)).isSome then
          if let some (domain, target) := Language.homEnds? (← inferType a) then
            let first ← realize h trace s!"the left side of {what}" a
            let second ← realize h trace s!"the right side of {what}" b
            let truth ← observeEquality h trace first second domain target
            return (toExpr (some truth), toJson truth)
      throwStratum .noImplementation m!"nothing decides {what}: it is not a registered \
        property of a value the realized reading evaluates"
  let original ← realize h trace s!"the receiver of {id.raw} in {what}" receiver
  let (request, input) ← operationReceiver trace original route (some (realizedEdgeData h trace)) (some (capturedEdgeData h trace))
  let state ← registryState
  let some property := state.properties.find? (·.id == id)
    | throwError "the recorded property is not registered"
  let some receiverExpression := state.formExpression? original.form
    | throwError "the property receiver lost its accepted category expression"
  let resolution ← match state.resolveProperty receiverExpression property.name with
    | .ok resolution => pure resolution
    | .error error => throwResolutionError state error
  unless resolution.route.refs == route do
    throwError "the recorded property changed its full registered route"
  let comparisonTerms ← Semantic.validatePropertyResolutionComparisons state resolution (some receiver)
  Semantic.checkRecordedRouteComparisons resolution.comparisonWitnesses
    comparisonTerms recordedComparisons
  let some classifier := state.classifier? property.classifier
    | throwError "the recorded property's classifier is not registered"
  -- Check the full selected domain without requiring an encoding of every intermediate image.
  let classifier ← classifierInstance classifier
  discard <| elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax input))) none
  let request ← computationalOperationReceiver h trace id.raw original route request
  let request ← computationalApexReceiver trace (← realizeObjectObservation h trace request)
  call h id.raw request
    (mkApp (mkConst ``Option [0]) (mkConst ``Bool)) resolution.comparisons

/-- A deferred program resolves references by exact occurrence, independently of
expression-keyed execution caches. `known` contains only operands of its parent
request; it is not a registry of alternate meanings for arbitrary JSON. -/
structure ServiceScope where
  harness : Harness
  trace : Trace
  references : Array Wire
  known : Array Wire
  /-- Exact public request positions supplied by the original producer. -/
  inputReferences : Array (DataOwnership.Path × Wire) := #[]
  positionedInputs : Bool := false
  operands : IO.Ref (Array Wire)
  backend : String
  /-- A formal derivation gives each original runtime operand its own transparent
  expression key before building dependent applications. Ordinary service calls
  keep their existing keys. Equal formal values never merge actual suppliers. -/
  operandBinding : Option String := none

partial def serviceContainsRef (data : Json) : Bool :=
  if #["resultRef", "inputRef"].contains
      ((data.getObjValAs? String "ctor").toOption.getD "") then true
  else match data with
    | .arr values => values.any serviceContainsRef
    | .obj fields => fields.any fun _ value => serviceContainsRef value
    | _ => false

def checkServiceOwner (h : Harness) (wire : Wire) : TermElabM Unit := do
  checkDataOwners h wire.fragment

/-- A compiler key denotes one retained operand occurrence. The actual Wire is
kept unchanged, including structured packets and their authoritative fields. -/
def serviceOperandValue (scope : ServiceScope) (handle : Nat) (value : Expr) :
    TermElabM Expr := do
  match scope.operandBinding with
  | none => return value
  | some binding =>
    return ← mkAppM ``Trace.operationResult #[toExpr s!"{binding}:operand:{handle}", value]

def serviceRegister (scope : ServiceScope) (wire : Wire) : TermElabM ServiceRequest.Operand := do
  checkServiceOwner scope.harness wire
  let handle ← scope.operands.modifyGet fun values => (values.size, values.push wire)
  let value ← serviceOperandValue scope handle wire.value
  if value != wire.value then Trace.alias (some scope.trace) wire.value value
  return {
    value := value, data := wire.json, handle
    ownership := wire.ownership
    form := some wire.form, context := wire.categoryContext }

def serviceWire (scope : ServiceScope) (operand : ServiceRequest.Operand) : TermElabM Wire := do
  let some wire := (← scope.operands.get)[operand.handle]?
    | throwError "a typed service operand lost its retained occurrence handle"
  unless (← serviceOperandValue scope operand.handle wire.value) == operand.value &&
      wire.json == operand.data &&
      wire.ownership == operand.ownership do
    throwError "a typed service operand changed its retained occurrence"
  checkServiceOwner scope.harness wire
  return wire

/-- Copied bytes cannot choose between different complete formal selections.
This deliberately uses expression identity, including the full selected dictionary,
instead of conversion of mathematical values. Explicit references remain occurrence based. -/
def sameServiceSelection (left right : Wire) : Bool :=
  sameActionOperand left right && left.form.id == right.form.id &&
    left.presentationIsos == right.presentationIsos &&
    left.categoryContext.map (·.bundle) == right.categoryContext.map (·.bundle) &&
    (match left.categoryContext, right.categoryContext with
      | none, none => true
      | some left, some right => left.expression.syntacticEq right.expression
      | _, _ => false) &&
    left.constructionInputs == right.constructionInputs &&
    left.constructionInputOwnership == right.constructionInputOwnership

/-- Two actions can produce the very same formal value and packet. Their action
receipts still distinguish the selected computation, so copied bytes are ambiguous;
a result reference supplies the required occurrence without consulting this lookup. -/
def distinctServiceActionOrigins (scope : ServiceScope) (wire : Wire) : IO Bool := do
  let origins := (← scope.harness.actions.get).filter fun record =>
    sameServiceSelection record.result wire
  return origins.any fun left => origins.any fun right =>
    left.operation != right.operation || left.action != right.action ||
      !sameServiceSelection left.input right.input || left.parameters != right.parameters ||
      left.parameterOwnership != right.parameterOwnership ||
      !sameActionOperands left.parameterInputs right.parameterInputs ||
      !sameActionOperands left.imageEndpoints right.imageEndpoints

/-- A reference has an already fixed formal value. A copied original packet is
accepted only from the exact parent scope, with ambiguity retained. -/
def serviceRetained (scope : ServiceScope) (data : Json) (expected : Option Expr := none) :
    TermElabM (Option Wire) := do
  let inputPath ← match Backend.inputRefPath? data with
    | .ok path => pure path
    | .error message => throwStratum .malformed message
  if let some inputPath := inputPath then
    let path := inputPath.map fun step => match step with
      | .field name => DataOwnership.Step.field name
      | .index position => DataOwnership.Step.index position
    let matchingInputs := scope.inputReferences.filter (·.1 == path)
    let #[(_, wire)] := matchingInputs
      | throwStratum .malformed "an input reference is not an exact retained request position"
    checkServiceOwner scope.harness wire
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType wire.value) expected do
        throwStratum .malformed "an input reference has a different complete declared type"
    return some wire
  let index ← match Backend.resultRefIndex? data with
    | .ok index => pure index
    | .error message => throwStratum .malformed message
  if let some index := index then
    let some wire := scope.references[index]?
      | throwStratum .malformed "a service reference is outside its completed local scope"
    checkServiceOwner scope.harness wire
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType wire.value) expected do
        throwStratum .malformed "a service reference has a different complete declared type"
    return some wire
  if scope.positionedInputs then return none
  let mut candidates : Array Wire := #[]
  for wire in scope.known do
    unless wire.json == data do continue
    if let some expected := expected then
      unless ← withoutModifyingState <| withTransparency .all <|
          isDefEq (← inferType wire.value) expected do continue
    checkServiceOwner scope.harness wire
    let repeated := candidates.any (sameServiceSelection · wire)
    unless repeated do candidates := candidates.push wire
  match candidates with
  | #[] => return none
  | #[wire] =>
    if ← distinctServiceActionOrigins scope wire then
      throwStratum .ambiguousRealization
        "the parent packet has distinct retained complete action occurrences"
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType wire.value) expected do
        throwError "the retained service input lost its selected full type"
    return some wire
  | _ => do
    throwStratum .ambiguousRealization
      "the parent request has distinct typed occurrences of the same computational packet"

def serviceLiteralWire (scope : ServiceScope) (formal : Expr) (data : Json)
    (dependencies : Array ServiceRequest.Operand := #[]) (form : Option Form := none)
    (context : Option CategoryContext := none) (ownership : DataOwnership.Table := #[])
    (productComponents : Array Wire := #[]) (completed : Bool := true) :
    TermElabM ServiceRequest.Operand := do
  let formal ← SimpleServiceRequest.checkClosed formal
  let wires ← dependencies.mapM (serviceWire scope)
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the published data category is absent"
  let form := form.getD (context.map (ServiceRequest.formFor state · (.diagrams sets))
    |>.getD (.diagrams sets))
  let completed := completed && wires.all (fun wire => match wire.payload with
    | .computed _ (.recipe _) => wire.completedData
    | _ => true)
  let payload ← if completed then scopedPayload formal { json := data, ownership }
    else recipePayload formal { json := data, ownership }
  let wire : Wire := {
    form, payload, categoryContext := context
    objectObserved := completed, callableObserved := completed, productComponents,
    serviceHandles := (← retainServiceOperands scope.harness wires) ++
      wires.flatMap (·.serviceHandles) }
  serviceRegister scope wire

/-- An existing action descriptor selects only its already published projection
addresses. Availability never changes this mathematical selection. -/
def serviceActionInvocation (selected : SimpleServiceRequest.SelectedAction) (morphismAction : Bool) :
    TermElabM (String × Array Json) := do
  let state ← registryState
  let .ok (tag, _) := ComputationalData.envelope selected.descriptor
    | throwError "the selected service action lost its complete descriptor"
  if let some entry := state.functors.find? (·.id.raw == tag) then
    return (if morphismAction then entry.mapAddress else entry.id.raw, selected.parameters)
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    return (if morphismAction then entry.mapAddress else entry.id.raw, selected.parameters)
  let identity ← SimpleServiceRequest.actionIdentity selected.descriptor
  let some edge := state.actionIdentityEdge? identity
    | throwStratum .malformed "the service action has no accepted complete projection identity"
  edgeActionInvocation state edge selected.descriptor morphismAction

/-- A nested public action is a computational demand, not a target data codec.
It crosses the same complete image boundary before a downstream operation runs. -/
def serviceObjectImage (scope : ServiceScope) (selected : SimpleServiceRequest.SelectedAction)
    (target : CategoryContext) (original : Wire) (dependencies : Array Wire) :
    TermElabM Wire := do
  let formal ← Semantic.objOf selected.value original.value
  let (operation, parameters) ← serviceActionInvocation selected false
  let requestInputPaths ← if scope.positionedInputs then do
      let invocation : Backend.ConstructionInvocation := {
        construction := operation, parameters, receiver := original.json }
      let request ← placedData invocation.encode #[
        (#[.field "args"], { json := Json.arr parameters, ownership := selected.parameterOwnership }),
        (#[.field "receiver"], original.fragment)]
      let positions ← (ServiceRequest.prefixInputPaths #[.field "args"]
        selected.parameterInputPaths).mapM fun (path, operand) => do
          pure (path, ← serviceWire scope operand)
      pure (some (← retainServiceInputPaths scope.harness request
        (positions.push (#[.field "receiver"], original))))
    else pure none
  let template : Wire := {
    form := ServiceRequest.formFor (← registryState) target original.form
    payload := (← combinedRecipePayload formal (← scopedNode "functorAction"
      #[{ json := selected.descriptor, ownership := selected.descriptorOwnership }, original.fragment])
      (dependencies.push original))
    categoryContext := some target }
  executeObjectAction scope.harness scope.trace operation selected.value original
    template parameters dependencies selected.parameterOwnership requestInputPaths

mutual

/-- Instantiate the existing public dependent telescope, retaining every actual
explicit data operand. Formal proof/class obligations are closed separately. -/
partial def serviceDeclaration (scope : ServiceScope) (name : Name) (data : Array Json) :
    TermElabM ServiceRequest.Declaration := do
  let constant ← mkConstWithFreshMVarLevels name
  let (fields, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let mut operands : Array ServiceRequest.Operand := #[]
  let mut explicit := #[]
  let mut position := 0
  for (field, info) in fields.zip infos do
    if info.isExplicit then explicit := explicit.push field
    let type ← instantiateMVars (← inferType field)
    unless info.isExplicit && !(← isProp type) do continue
    let some datum := data[position]?
      | throwStratum .malformed "the service declaration omitted an ordered data parameter"
    let operand ← serviceArgument scope type datum
    unless ← withTransparency .all <| isDefEq field operand.value do
      throwStratum .malformed "a service parameter changes its complete dependent interface"
    operands := operands.push operand
    position := position + 1
  unless position == data.size do
    throwStratum .malformed "the service declaration supplied an extra parameter or proof"
  return {
    application := { value := mkAppN constant fields, arguments := fields, explicit }
    operands }

partial def serviceNamed (scope : ServiceScope) (data : Json) (expected : Option Expr := none) :
    TermElabM (Option ServiceRequest.Operand) := do
  let .ok (tag, arguments) := ComputationalData.envelope data | return none
  let state ← registryState
  let selected := (state.objects.find? (·.id.raw == tag)).map
      (fun row => (row.declaration, some (Form.object row), some row.category)) <|>
    (state.callable? tag).map (fun (name, category) => (name, state.form? tag, some category))
  if let some (name, form, category) := selected then
    let declaration ← serviceDeclaration scope name arguments
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType declaration.application.value) expected do
        throwStratum .malformed "a named service operand changes its complete declared type"
    let application ← DirectConstruction.close declaration.application
    let formal ← SimpleServiceRequest.checkClosed application.value
    let context ← match category.bind (fun id => state.categories.find? (·.id == id)) with
      | none => pure none
      | some category =>
        let object := (Language.homEnds? (← inferType formal)).map Prod.fst |>.getD formal
        pure (some (← CategoryContext.ofNamed category object))
    return some (← serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag (declaration.operands.map (·.data)))
      declaration.operands form context
      (DataOwnership.prefix #[.field "args"]
        (ServiceRequest.operandArrayOwnership declaration.operands))
      (completed := (state.objects.find? (·.id.raw == tag)).isSome))
  if #["category", "constructedCategory", "functor"].contains tag then
    let #[.str id, .arr parameters] := arguments
      | throwStratum .malformed "a service dictionary requires its full ordered parameters"
    let declaration := if tag == "category" then
      (state.categories.find? (·.id.raw == id)).map (·.declaration)
    else if tag == "constructedCategory" then
      (state.constructors.find? (·.id.raw == id)).map (·.semantics)
    else (state.functors.find? (·.id.raw == id)).map (·.declaration)
    let some declaration := declaration
      | throwStratum .malformed "the service dictionary is not mathematically published"
    let selected ← serviceDeclaration scope declaration parameters
    if let some expected := expected then
      let formal ← if tag == "functor" then Semantic.asFunctor selected.application.value
        else pure selected.application.value
      unless ← withTransparency .all <| isDefEq (← inferType formal) expected do
        throwStratum .malformed "a service dictionary changes its complete declared parameter type"
    let application ← DirectConstruction.close selected.application
    let formal ← if tag == "functor" then Semantic.asFunctor application.value
      else pure application.value
    return some (← serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag #[toJson id, Json.arr (selected.operands.map (·.data))])
      selected.operands none none
      (ServiceRequest.argsOwnership #[#[], ServiceRequest.operandArrayOwnership selected.operands]))
  return none

partial def serviceObject (scope : ServiceScope) (data : Json) :
    TermElabM ServiceRequest.Operand := do
  if let some wire ← serviceRetained scope data then return ← serviceRegister scope wire
  if let some projected ← serviceProjection? scope data then return projected
  if let some selected ← serviceNamed scope data then return selected
  let .ok (tag, arguments) := ComputationalData.envelope data
    | throwStratum .malformed "a service object requires its complete declared interface"
  match tag, arguments with
  | "valueData", #[child] => serviceObject scope child
  | "objectProduct", #[left, right] =>
    let left ← serviceObject scope left
    let right ← serviceObject scope right
    let formal ← mkAppM ``Prod #[left.value, right.value]
    serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag #[left.data, right.data]) #[left, right] none none
      (ServiceRequest.argsOwnership #[left.ownership, right.ownership])
      #[← serviceWire scope left, ← serviceWire scope right]
  | "arrow", #[source, target, hom] =>
    let source ← serviceObject scope source
    let target ← serviceObject scope target
    let hom ← serviceArgument scope (← mkAppM ``Quiver.Hom #[source.value, target.value]) hom
    let formal ← mkAppM ``CategoryTheory.Arrow.mk #[hom.value]
    let context ← match source.context with
      | some context => do
        let state ← registryState
        let #[constructor] := state.constructors.filter
            (·.semantics == `CasCatalogue.Constructors.arrow)
          | throwError "the public Arrow category constructor is absent or ambiguous"
        pure (some (← CategoryContext.construct context constructor.id))
      | none => pure none
    serviceLiteralWire scope formal
      (SimpleServiceRequest.node tag #[source.data, target.data, hom.data])
      #[source, target, hom] none context
      (ServiceRequest.argsOwnership #[source.ownership, target.ownership, hom.ownership])
  | "coreObject", #[original] =>
    let original ← serviceObject scope original
    let formal ← mkAppM ``CategoryTheory.Core.mk #[original.value]
    let context ← match original.context with
      | some context => do
        let state ← registryState
        let #[constructor] := state.constructors.filter
            (·.semantics == `CasCatalogue.Constructors.core)
          | throwError "the public Core category constructor is absent or ambiguous"
        pure (some (← CategoryContext.construct context constructor.id))
      | none => pure none
    serviceLiteralWire scope formal (SimpleServiceRequest.node tag #[original.data])
      #[original] none context (ServiceRequest.argsOwnership #[original.ownership])
  | "functorAction", #[descriptor, original] =>
    let selected ← SimpleServiceRequest.action (← serviceDecoder scope) descriptor
    let (source, _) ← functorCategoryBundles selected.value
    let original ← serviceArgument scope (← mkAppM ``CategoryTheory.Bundled.α #[source]) original
    let formal ← Semantic.objOf selected.value original.value
    let selected ← SimpleServiceRequest.closeAction selected
    let (_, target) ← functorCategoryBundles selected.value
    let context : CategoryContext := { expression := selected.target, bundle := target }
    let formal ← SimpleServiceRequest.checkClosed formal
    let actual ← serviceObjectImage scope selected context (← serviceWire scope original)
      (← selected.dependencies.mapM (serviceWire scope))
    SimpleServiceRequest.sameValue actual.value formal "nested object action"
    serviceRegister scope actual
  | _, _ =>
    if serviceContainsRef data then
      throwStratum .noImplementation
        "unfinished kernel service preparation: this public object form has unresolved typed reference roles"
    let state ← registryState
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the published data category is absent"
    let .ok formal ← decodeObjectData scope.trace sets data
      | throwStratum .malformed "the service object has no independently recoverable complete interface"
    serviceLiteralWire scope formal data

partial def serviceArrow (scope : ServiceScope) (data : Json) (expected : Option Expr := none) :
    TermElabM ServiceRequest.Operand := do
  if let some wire ← serviceRetained scope data expected then
    unless (Language.homEnds? (← inferType wire.value)).isSome do
      throwStratum .malformed "a service callable reference is not a categorical morphism"
    return ← serviceRegister scope wire
  if let some projected ← serviceProjection? scope data then
    unless (Language.homEnds? (← inferType projected.value)).isSome do
      throwStratum .malformed "the service projection does not select a complete callable"
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq (← inferType projected.value) expected do
        throwStratum .malformed "the service projection changes its complete selected Hom"
    return projected
  if let some selected ← serviceNamed scope data expected then
    unless (Language.homEnds? (← inferType selected.value)).isSome do
      throwStratum .malformed "the service callable descriptor names an object"
    return selected
  let result ← match ComputationalData.envelope data with
  | .ok ("valueData", #[child]) => serviceArrow scope child expected
  | .ok ("typedMap", #[source, target, callable]) =>
    let source ← serviceObject scope source
    let target ← serviceObject scope target
    let type ← match source.context with
      | some context => CategoryContext.hom context source.value target.value
      | none => mkAppM ``Quiver.Hom #[source.value, target.value]
    if let some expected := expected then
      unless ← withTransparency .all <| isDefEq type expected do
        throwStratum .malformed "the service typed map changes its complete declared endpoints"
    let callable ← serviceArgument scope type callable
    let result ← serviceLiteralWire scope callable.value
      (Backend.TypedMap.encode { source := source.data, target := target.data, callable := callable.data })
      #[source, target, callable] callable.form source.context
      (ServiceRequest.argsOwnership #[source.ownership, target.ownership, callable.ownership])
    if let some context := source.context then
      let wire ← retainCallableEndpoints (← serviceWire scope result)
        (← serviceWire scope source) (← serviceWire scope target) context
      serviceRegister scope wire
    else pure result
  | .ok ("identity", #[source, target]) =>
    let source ← serviceObject scope source
    let target ← serviceObject scope target
    SimpleServiceRequest.sameValue target.value source.value "identity endpoint"
    discard <| framingContext source.context target.context
    let formal ← match source.context with
      | some context => identityAtContext context source.value
      | none => mkAppM ``CategoryTheory.CategoryStruct.id #[source.value]
    let result ← serviceLiteralWire scope formal
      (SimpleServiceRequest.node "identity" #[source.data, target.data])
      #[source, target] none source.context
      (ServiceRequest.argsOwnership #[source.ownership, target.ownership])
    if let some context := source.context then
      let wire ← retainCallableEndpoints (← serviceWire scope result)
        (← serviceWire scope source) (← serviceWire scope target) context
      serviceRegister scope wire
    else pure result
  | .ok ("compose", #[first, second]) =>
    let first ← serviceArrow scope first
    let second ← serviceArrow scope second
    let some (domain, middle) := Language.homEnds? (← inferType first.value)
      | throwStratum .malformed "the first service composite operand has no complete Hom"
    let some (middle', target) := Language.homEnds? (← inferType second.value)
      | throwStratum .malformed "the second service composite operand has no complete Hom"
    SimpleServiceRequest.sameValue middle middle' "composite middle object"
    let formal ← match first.context with
      | some context => ServiceRequest.compose context domain middle target first.value second.value
      | none => mkAppM ``CategoryTheory.CategoryStruct.comp #[first.value, second.value]
    let result ← serviceLiteralWire scope formal
      (SimpleServiceRequest.node "compose" #[first.data, second.data])
      #[first, second] none first.context
      (ServiceRequest.argsOwnership #[first.ownership, second.ownership])
    if let some context := first.context then
      let source ← serviceEndpoint scope first true
      let target ← serviceEndpoint scope second false
      let wire ← retainCallableEndpoints (← serviceWire scope result)
        (← serviceWire scope source) (← serviceWire scope target) context
      serviceRegister scope wire
    else pure result
  | .ok ("map", #[descriptor, original]) =>
    let selected ← SimpleServiceRequest.action (← serviceDecoder scope) descriptor
    let original ← serviceArrow scope original
    let formal ← Semantic.mapOf selected.value original.value
    let selected ← SimpleServiceRequest.closeAction selected
    let (_, target) ← functorCategoryBundles selected.value
    let context : CategoryContext := { expression := selected.target, bundle := target }
    let formal ← SimpleServiceRequest.checkClosed formal
    let (sourceBundle, _) ← functorCategoryBundles selected.value
    let some sourceExpression := selected.source <|> original.context.map (·.expression) <|>
        (original.form.bind (← registryState).formExpression?)
      | throwStratum .malformed "the nested map lost its complete original category context"
    let sourceContext : CategoryContext := { expression := sourceExpression, bundle := sourceBundle }
    let original ← serviceWire scope original
    let dependencies ← selected.dependencies.mapM (serviceWire scope)
    let (operation, parameters) ← serviceActionInvocation selected true
    let requestInputPaths ← if scope.positionedInputs then do
        let descriptorPositions ← selected.descriptorInputPaths.mapM fun (path, operand) => do
          pure (path, ← serviceWire scope operand)
        let parameterPositions ← selected.parameterInputPaths.mapM fun (path, operand) => do
          pure (path, ← serviceWire scope operand)
        let descriptorPaths ← retainServiceInputPaths scope.harness
          { json := selected.descriptor, ownership := selected.descriptorOwnership } descriptorPositions
        let parameterPaths ← retainServiceInputPaths scope.harness
          { json := Json.arr parameters, ownership := selected.parameterOwnership } parameterPositions
        pure (some (
          descriptorPaths.map (fun (path, handle) =>
            (#[.field "args", .index 2, .field "args", .index 0] ++ path, handle)) ++
          parameterPaths.map (fun (path, handle) => (#[.field "args", .index 1] ++ path, handle))))
      else pure none
    let template : Wire := {
      form := ServiceRequest.formFor (← registryState) context original.form true
      payload := (← combinedRecipePayload formal (← scopedNode "map"
        #[{ json := selected.descriptor, ownership := selected.descriptorOwnership }, original.fragment])
        (dependencies.push original))
      categoryContext := some context }
    let actual ← executeMapAction scope.harness scope.trace operation selected.value
      sourceContext context original template selected.descriptor parameters dependencies
      (fun source => serviceObjectImage scope selected context source dependencies)
      selected.descriptorOwnership selected.parameterOwnership
      (requestInputPaths := requestInputPaths)
    serviceRegister scope actual
  | _ =>
    if serviceContainsRef data then
      throwStratum .noImplementation
        "unfinished kernel service preparation: this public callable form has unresolved typed reference roles"
    let state ← registryState
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the published data category is absent"
    let decoded ← match expected with
      | some expected => decodeValue scope.trace sets expected data
      | none => pure ((← decodeArrowData scope.trace sets data).map (·, none))
    let .ok (formal, form) := decoded
      | throwStratum .malformed "the service callable has no independently recoverable full signature"
    serviceLiteralWire scope formal data #[] form
  if let some expected := expected then
    unless ← withTransparency .all <| isDefEq (← inferType result.value) expected do
      throwStratum .malformed "the service callable differs from its complete selected Hom type"
  return result

partial def serviceArgument (scope : ServiceScope) (expected : Expr) (data : Json) :
    TermElabM ServiceRequest.Operand := do
  let expected ← instantiateMVars expected
  if ← isProp expected then
    throwStratum .malformed "a proof is not a service data argument"
  if let .ok ("valueData", #[child]) := ComputationalData.envelope data then
    return ← serviceArgument scope expected child
  if let some wire ← serviceRetained scope data (some expected) then
    return ← serviceRegister scope wire
  let result ← if (Language.homEnds? expected).isSome then serviceArrow scope data (some expected)
  else if let some projected ← serviceProjection? scope data then pure projected
  else if let some selected ← serviceNamed scope data (some expected) then pure selected
  else if let .ok (tag, _) := ComputationalData.envelope data then
    if #["objectProduct", "arrow", "coreObject", "functorAction"].contains tag then
      serviceObject scope data
    else servicePlainArgument scope expected data
  else servicePlainArgument scope expected data
  unless ← withTransparency .all <| isDefEq (← inferType result.value) expected do
    throwStratum .malformed "the service operand differs from its complete declared parameter type"
  return result

partial def servicePlainArgument (scope : ServiceScope) (expected : Expr) (data : Json) :
    TermElabM ServiceRequest.Operand := do
  let type ← withTransparency .all <| whnf expected
  if let .arr values := data then
    if type.isAppOfArity ``Prod 2 && values.size == 2 then
      let first ← serviceArgument scope type.getAppArgs[0]! values[0]!
      let second ← serviceArgument scope type.getAppArgs[1]! values[1]!
      let formal ← mkAppM ``Prod.mk #[first.value, second.value]
      return ← serviceLiteralWire scope formal (Json.arr #[first.data, second.data]) #[first, second]
        none none (ServiceRequest.arrayOwnership #[first.ownership, second.ownership])
    if type.isAppOfArity ``List 1 || type.isAppOfArity ``Array 1 then
      let values ← values.mapM (serviceArgument scope type.getAppArgs[0]!)
      let formal ← if type.isAppOf ``List then mkListLit type.getAppArgs[0]! (values.map (·.value)).toList
        else mkArrayLit type.getAppArgs[0]! (values.map (·.value)).toList
      return ← serviceLiteralWire scope formal (Json.arr (values.map (·.data))) values
        none none (ServiceRequest.operandArrayOwnership values)
  if serviceContainsRef data then
    throwStratum .noImplementation
      "unfinished kernel service preparation: this data form has unresolved typed reference roles"
  if containsOpaqueData data then
    throwStratum .unavailable "the service cannot infer a new opaque value's mathematical interface"
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the published data category is absent"
  let .ok (formal, form) ← decodeValue scope.trace sets expected data
    | throwStratum .malformed "the service argument does not decode at its full published type"
  serviceLiteralWire scope formal data #[] form

partial def serviceDecoder (scope : ServiceScope) : TermElabM ServiceRequest.Decoder := pure {
  argument := serviceArgument scope
  object := serviceObject scope
  arrow := fun data => serviceArrow scope data
  endpoint := serviceEndpoint scope
  project := serviceProject scope
  condition := serviceCondition scope
  declaration := serviceDeclaration scope }

partial def serviceEndpoint (scope : ServiceScope) (operand : ServiceRequest.Operand)
    (source : Bool) : TermElabM ServiceRequest.Operand := do
  let wire ← serviceWire scope operand
  let some (left, right) := Language.homEnds? (← inferType wire.value)
    | throwStratum .malformed "the service endpoint requires the original whole callable"
  let formal := if source then left else right
  if let some endpoint ← retainedCallableEndpoint? wire formal source wire.categoryContext then
    return ← serviceRegister scope endpoint
  if let some endpoint ← retainedActionEndpoint? wire wire.categoryContext formal source then
    let endpoint := { endpoint with
      serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
    return ← serviceRegister scope endpoint
  let state ← registryState
  let form := wire.categoryContext.map (ServiceRequest.formFor state · wire.form) |>.getD wire.form
  let .ok projection ← ComputationalData.interfaceEndpointDataWithOrigin #[] wire.value
      wire.fragment source false
    | throwStratum .malformed "the service endpoint lost its original complete callable data"
  if projection.origin == .action then
    unless wire.completedData do
      throwStratum .noImplementation
        "the service endpoint has no retained typed action producer"
    let endpoint := { (← callableEndpointReference wire formal source wire.categoryContext) with
      objectObserved := true
      serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
    return ← serviceRegister scope endpoint
  let completed := wire.completedData && projection.origin == .projection
  let endpoint : Wire := {
    form, payload := (← scopedPayload formal projection.data completed)
    categoryContext := wire.categoryContext, objectObserved := completed
    serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
  serviceRegister scope endpoint

partial def serviceProject (scope : ServiceScope) (operand : ServiceRequest.Operand)
    (field : String) (index : Option Nat) : TermElabM ServiceRequest.Operand := do
  let wire ← serviceWire scope operand
  let state ← registryState
  let context ← match wire.categoryContext with
    | some context => pure context
    | none => do
      let some category := state.categories.find? (·.id == wire.form.category)
        | throwStratum .malformed "the service record lost its complete declared category"
      CategoryContext.ofNamed category wire.value
  let (formal, targetContext, morphism) ← match index with
    | some index =>
      let some plan ← StructuredProjection.construction? wire.value context (some scope.trace)
        | throwStratum .malformed "the service record has no selected universal data ports"
      let port ← plan.selectPort (some index)
      pure (port.formalField, context, (Language.homEnds? port.expectedType).isSome)
    | none =>
      let some plan ← StructuredProjection.arrow? wire.value context
        | throwStratum .malformed "the service record is not a complete Arrow or subobject"
      plan.field field
  if index.isNone then
    let projected ← captureStructuredRecordField scope.harness scope.trace formal wire context field
    let projected ← if morphism then
        realizeArrowObservation { scope.harness with demandObjectActions := true } scope.trace projected
      else realizeObjectObservation { scope.harness with demandObjectActions := true } scope.trace projected
    return ← serviceRegister scope projected
  let literal ← match index with
    | some index =>
      let .construction result _ := wire.payload
        | throwStratum .malformed "the selected data field lost its retained universal packet"
      match result.packet with
      | .created .. => pure none
      | .direct answer =>
        let .ok (_, fields) := ComputationalData.envelope answer
          | throwError "a retained universal packet lost its checked data constructor"
        let some _ := fields[index]?
          | throwError "a retained universal packet lost its checked field"
        pure (some (← checkedFragment <| wire.fragment.project
          #[.field "args", .index 2, .field "args", .index index]))
    | none =>
      if wire.objectIso.isSome || wire.endpointPresentation.isSome ||
          !wire.presentationIsos.isEmpty then pure none
      else if let some fields := subobjectFragments? wire.fragment then
        match field with
        | "source" | "obj" => pure fields[0]?
        | "target" => pure fields[1]?
        | "hom" =>
          let #[source, target, callable] := fields | unreachable!
          if let .ok framed := Backend.TypedMap.decode callable.json then
            unless framed.source == source.json && framed.target == target.json &&
                DataOwnership.project #[.field "args", .index 0] callable.ownership ==
                  source.ownership &&
                DataOwnership.project #[.field "args", .index 1] callable.ownership ==
                  target.ownership do
              throwStratum .malformed "a retained Arrow field changes its actual complete endpoints"
            pure (some callable)
          else pure (some (← scopedNode "typedMap" #[source, target, callable]))
        | "inclusion" => pure (some (← scopedNode "arrow" fields))
        | _ => pure none
      else pure none
  if let some data := literal then
    let completed := wire.completedData
    let projected : Wire := {
      form := ServiceRequest.formFor state targetContext wire.form morphism
      payload := (← scopedPayload formal data completed)
      categoryContext := some targetContext
      objectObserved := completed && !morphism, callableObserved := completed && morphism
      serviceHandles := (← retainServiceOperands scope.harness #[wire]) }
    return ← serviceRegister scope projected
  let results ← IO.mkRef (({} : Std.HashMap Expr Wire).insert wire.value wire)
  let localHarness := { scope.harness with results }
  let projected ← structuredProjection localHarness scope.trace formal wire.value field index
  serviceRegister scope { projected with
    serviceHandles := (← retainServiceOperands scope.harness #[wire]) }

/-- A returned universal packet is resolved through its retained authoritative
Result, never by interpreting the packet as a proof-bearing cone. The repeated
row and diagram are checked against that exact original occurrence. -/
partial def serviceConstructionRecord (scope : ServiceScope) (id : String)
    (diagram packet : Json) : TermElabM ServiceRequest.Operand := do
  let state ← registryState
  let some row := state.limits.find? (·.id.raw == id)
    | throwStratum .malformed "the construction projection has no published owner"
  let original ← if let some wire ← serviceRetained scope packet then pure wire else do
    if scope.positionedInputs then
      throwStratum .malformed "a construction projection requires its exact input or result reference"
    let candidates := scope.known.filter fun wire => match wire.payload with
      | .construction result _ => result.json == packet
      | _ => false
    let mut unique := #[]
    for wire in candidates do
      unless unique.any (sameServiceSelection · wire) do unique := unique.push wire
    let #[wire] := unique
      | if unique.isEmpty then
          throwStratum .noImplementation
            "unfinished kernel service preparation: the construction packet has no retained universal context"
        else
          throwStratum .ambiguousRealization
            "the construction packet has distinct retained universal occurrences"
    checkServiceOwner scope.harness wire
    pure wire
  let .construction result _ := original.payload
    | throwStratum .malformed "a construction packet reference is not a retained universal result"
  unless original.form.id == id && result.colimit == row.colimit do
    throwStratum .malformed "the construction projection changed its exact registered owner"
  if let some retained ← serviceRetained scope diagram then
    SimpleServiceRequest.sameValue retained.value result.diagram "construction diagram"
    unless retained.json == result.diagramJson && retained.ownership ==
        DataOwnership.project #[.field "args", .index 1] original.ownership do
      throwStratum .malformed "the construction projection changed its actual retained diagram"
  else if diagram != result.diagramJson then
    let some category := state.categories.find? (·.id == row.category)
      | throwError "the retained universal row lost its declared category"
    let prepared ← UniversalServiceRequest.limit (← serviceDecoder scope) row (.diagrams category) diagram
    SimpleServiceRequest.sameValue prepared.requestValue result.diagram "construction diagram"
    unless prepared.request == result.diagramJson && prepared.requestOwnership ==
        DataOwnership.project #[.field "args", .index 1] original.ownership do
      throwStratum .malformed "the construction projection changed its actual retained diagram"
  serviceRegister scope original

/-- Released projection envelopes select typed fields of the original occurrence.
The selector is literal; only declared operand/data roles can contain references. -/
partial def serviceProjection? (scope : ServiceScope) (data : Json) :
    TermElabM (Option ServiceRequest.Operand) := do
  let .ok (tag, arguments) := ComputationalData.envelope data | return none
  match tag, arguments with
  | "morphismEndpoint", #[callable, .str side] =>
    unless side == "source" || side == "target" do
      throwStratum .malformed "the endpoint projection has no declared side"
    return some (← serviceEndpoint scope (← serviceArrow scope callable) (side == "source"))
  | "arrowHom", #[receiver] | "subobjectApex", #[receiver] |
      "subobjectInclusion", #[receiver] =>
    let original ← serviceObject scope receiver
    let wire ← serviceWire scope original
    let some context := wire.categoryContext
      | throwStratum .malformed "the structured projection lost its full selected category"
    let some plan ← StructuredProjection.arrow? wire.value context
      | throwStratum .malformed "the structured projection requires its complete declared Arrow interface"
    unless plan.subobject == (tag != "arrowHom") do
      throwStratum .malformed "the structured projection changed its accepted refinement interface"
    return some (← serviceProject scope original
      (if tag == "subobjectApex" then "source" else "hom") none)
  | "constructionApex", #[.str id, diagram, packet] =>
    return some (← serviceConstructionRecord scope id diagram packet)
  | "constructionField", #[.str id, diagram, packet, index] =>
    let .ok index := index.getNat?
      | throwStratum .malformed "the construction field requires its literal data-port index"
    return some (← serviceProject scope
      (← serviceConstructionRecord scope id diagram packet) "field" (some index))
  | "constructionLeg", #[.str id, diagram, packet, index] =>
    let original ← serviceConstructionRecord scope id diagram packet
    let wire ← serviceWire scope original
    let .construction result _ := wire.payload | unreachable!
    let type ← whnfR (← inferType result.diagram)
    unless type.isAppOfArity ``CategoryTheory.Functor 4 do
      throwError "the retained construction lost its complete diagram type"
    let index ← serviceArgument scope type.getAppArgs[0]! index
    let formal ← SimpleServiceRequest.checkClosed (← result.leg index.value)
    let state ← registryState
    let some row := state.limits.find? (·.id.raw == id) | unreachable!
    let inputs ← constructionInputFragments wire
    let diagramData ← checkedFragment (wire.fragment.project #[.field "args", .index 1])
    let packetData ← checkedFragment (wire.fragment.project #[.field "args", .index 2])
    let projection : ProjectedObjectFragment ← match result.packet with
      | .created .. =>
        pure (.deferredAction (← scopedNode "constructionLeg"
          #[{ json := toJson id }, diagramData, packetData, index.fragment]))
      | .direct answer =>
        let encodeInput := fun value => do
          match selectedConstructionInput inputs value with
          | .error message => return .error message
          | .ok (some data) => return .ok (.structural data)
          | .ok none =>
            return ((← Codec.encode value).bind DataOwnership.Data.portable).map
              ProjectedObjectFragment.structural
        let encodeAction := fun action => do
          let mut descriptors := #[]
          for entry in state.functors do
            let descriptor ← withoutModifyingState do
              let declared ← Semantic.asFunctor (← instantiateFresh entry.declaration)
              unless ← withTransparency .all <| isDefEq declared action do return none
              return some (← realizedEdgeData scope.harness scope.trace (.functor entry.id) action).1
            if let some descriptor := descriptor then descriptors := descriptors.push descriptor
          let #[descriptor] := descriptors
            | return .error "the defining map has no unique complete registered action"
          return .ok (ProjectedObjectFragment.structural descriptor)
        match ← StructuredResult.projectDataWith row result.diagram answer index.value
            (fun field _ => pure ((packetData.project #[.field "args", .index field]).map
              ProjectedObjectFragment.structural))
            encodeInput encodeAction (fun tag fields => do
              let data ← DataOwnership.Data.ctor tag (fields.map (·.data))
              return if tag != "map" && fields.all (·.isStructural) then .structural data
                else .deferredAction data) with
        | .ok data => pure data
        | .error message => throwStratum .noImplementation message
    let projected : Wire := {
      form := wire.categoryContext.map (ServiceRequest.formFor state · wire.form true) |>.getD wire.form
      payload := (← scopedPayload formal projection.data projection.isStructural)
      categoryContext := wire.categoryContext, callableObserved := projection.isStructural }
    return some (← serviceRegister scope projected)
  | _, _ => return none

partial def serviceCondition (scope : ServiceScope) (proposition : Expr) : TermElabM Expr := do
  let proposition ← instantiateMVars proposition
  unless ← isProp proposition do throwError "a formal service condition is not a proposition"
  let mut candidates := #[]
  for (_, node) in (← scope.trace.get).toArray do
    if let .liftFactor _ _ _ proof := node then candidates := candidates.push proof
  if let some proof ← Codec.conditionProof proposition then candidates := candidates.push proof
  for proof in candidates do
    unless proof.hasSorry do
      if ← Decide.kernelAccepts proposition proof then return proof
  throwStratum .noImplementation
    "the service request lacks its independently established formal condition"

end

/-- Request preparation is exhaustive over the existing admitted operation
families. It derives meaning before inspecting availability or asking a backend. -/
def prepareServiceRequest (scope : ServiceScope) (operation : String) (input : Form)
    (template : Json) : TermElabM ServiceRequest.Prepared := do
  let state ← registryState
  let some selected := state.operation? operation
    | throwStratum .malformed "a deferred call names an unpublished operation"
  unless state.accepts selected input do
    throwStratum .malformed "a deferred call uses an incompatible published input form"
  let decoder ← serviceDecoder scope
  if let some prepared ← SimpleServiceRequest.prepare? decoder selected input template then
    return prepared
  if let some prepared ← StructuredServiceRequest.prepare? decoder selected input template then
    return prepared
  if let some prepared ← UniversalServiceRequest.prepare? decoder selected input template then
    return prepared
  throwStratum .noImplementation
    "unfinished kernel service preparation: this published operation family has no typed preparer"

/-- Only explicitly retained operands of this request are available as copied
input packets. A global cache entry or earlier action receipt with equal bytes
does not establish that its occurrence was placed in this request. -/
def serviceKnownInputs (h : Harness) (input : Wire) : TermElabM (Array Wire) := do
  let retained ← h.serviceOperands.get
  let mut known := #[input]
  for handle in input.serviceHandles do
    let some wire := retained[handle]?
      | throwError "a service request lost an exact operand occurrence"
    known := known.push wire
  return known

def publicServiceInputPath (path : DataOwnership.Path) : Array Backend.InputPathStep :=
  path.map fun step => match step with
    | .field name => .field name
    | .index position => .index position

/-- A prepared request selects exact retained inputs before a service program
is read. Its option distinguishes a complete empty table from legacy recovery. -/
def serviceRequestInputs (h : Harness) (input : Wire) :
    TermElabM (Bool × Array Wire × Array (DataOwnership.Path × Wire)) := do
  let some paths := input.serviceInputPaths
    | return (false, ← serviceKnownInputs h input, #[])
  let retained ← h.serviceOperands.get
  let mut inputs := #[]
  for (path, handle) in paths do
    let some wire := retained[handle]?
      | throwError "a positioned service input lost its original occurrence"
    unless (← checkedFragment (input.fragment.project path)) == wire.fragment do
      throwError "a positioned service input changed its original data or suppliers"
    if inputs.any (·.1 == path) then
      throwError "a service input position has more than one retained occurrence"
    checkServiceOwner h wire
    inputs := inputs.push (path, wire)
  return (true, #[], inputs)

/-- Cycle detection follows the same exact public positions through their retained
operands. Reallocating an administrative handle or reordering the position table
cannot make the same complete request new. Distinct selected occurrences still
use the existing full selection comparison; no packet lookup supplies an input. -/
partial def sameServiceRequestForCycle (h : Harness) (left right : Wire)
    (active : Array (Nat × Nat) := #[]) : TermElabM Bool := do
  match left.serviceInputPaths, right.serviceInputPaths with
  | none, none => return sameServiceSelection left right
  | some leftPaths, some rightPaths =>
    unless sameServiceSelection { left with serviceInputPaths := none }
        { right with serviceInputPaths := none } do
      return false
    let (_, _, leftInputs) ← serviceRequestInputs h left
    let (_, _, rightInputs) ← serviceRequestInputs h right
    unless leftInputs.size == rightInputs.size do return false
    for ((path, leftHandle), (_, leftInput)) in leftPaths.zip leftInputs do
      let some (_, rightInput) := rightInputs.find? (·.1 == path)
        | return false
      let some (_, rightHandle) := rightPaths.find? (·.1 == path)
        | throwError "a validated service input lost its exact public position"
      if active.contains (leftHandle, rightHandle) then
        throwError "a service request has cyclic positioned input metadata"
      unless ← sameServiceRequestForCycle h leftInput rightInput
          (active.push (leftHandle, rightHandle)) do
        return false
    return true
  | _, _ => return false

/-- Only the original request is annotated with its already fixed positions.
Returned service templates choose those positions explicitly with inputRef. -/
partial def serviceInputTemplate (scope : ServiceScope) (data : Json)
    (path : DataOwnership.Path := #[]) : Json :=
  if scope.inputReferences.any (·.1 == path) then
    Backend.inputRef (publicServiceInputPath path)
  else match data with
    | .arr values => .arr (values.mapIdx fun index value =>
        serviceInputTemplate scope value (path.push (.index index)))
    | .obj fields => Json.mkObj (fields.toList.map fun (key, value) =>
        (key, serviceInputTemplate scope value (path.push (.field key))))
    | value => value

/-- A template with references has only public data envelopes. Extra object
fields cannot hide unchecked references from a declared data-port validator. -/
partial def checkServiceTemplateFraming (template : Json) : TermElabM Unit := do
  if !serviceContainsRef template then return
  if let .ok (some _) := Backend.resultRefIndex? template then return
  if let .ok (some _) := Backend.inputRefPath? template then return
  match template with
  | .arr values => for value in values do checkServiceTemplateFraming value
  | .obj fields =>
    let keys := fields.toList.map Prod.fst
    unless keys.length == 2 && keys.contains "ctor" && keys.contains "args" do
      throwStratum .malformed "a result reference occurs outside a complete public data envelope"
    let .ok _ := template.getObjValAs? String "ctor"
      | throwStratum .malformed "a result reference cannot select a data constructor"
    let .ok arguments := (template.getObjVal? "args").bind (·.getArr?)
      | throwStratum .malformed "a referenced data envelope has no ordered data fields"
    for argument in arguments do checkServiceTemplateFraming argument
  | _ => pure ()

/-- Validate every reference at a pre-existing complete formal data port before
substituting actual packets. The referenced value need not equal the caller's
formal result: a well-framed wrong computation stays available for checking. -/
partial def validateServiceResultTemplate (scope : ServiceScope)
    (prepared : ServiceRequest.Prepared) (template : Json) : TermElabM Unit := do
  if !serviceContainsRef template then return
  checkServiceTemplateFraming template
  let interfaces := scope.references.mapIdx fun index wire =>
    (Backend.resultRef index, wire.value)
  let interfaces := interfaces ++ scope.inputReferences.map fun (path, wire) =>
    (Backend.inputRef (publicServiceInputPath path), wire.value)
  let validate : Expr → Json → TermElabM Unit := fun formal data => do
    if !serviceContainsRef data then return
    let expected ← inferType formal
    if let .error message ← withoutModifyingState <|
        ComputationalData.validatePort formal expected data interfaces then
      throwStratum .malformed m!"a deferred result reference changes its complete data role: {message}"
  if prepared.decisionResult then
    let data := match ComputationalData.envelope template with
      | .ok ("valueData", #[data]) => data
      | _ => template
    unless #["inputRef", "resultRef"].contains
        ((data.getObjValAs? String "ctor").toOption.getD "") do
      throwStratum .malformed "a decision reference must occupy the entire decision result"
    let some wire ← serviceRetained scope data
      | throwStratum .malformed "a decision reference must occupy the entire decision result"
    unless ← isProp wire.value do
      throwStratum .malformed "a decision reference does not retain a declared proposition"
    return
  if let some validatePorts := prepared.validateTemplate then
    validatePorts validate template
  else
    validate prepared.result template

/-- Substitute only already checked references. Ownership follows actual opaque
packets; the entire DAG remains retained separately even when this result is portable. -/
partial def assembleServiceResult (scope : ServiceScope) (template : Json) :
    TermElabM DataOwnership.Data := do
  match Backend.inputRefPath? template with
  | .error message => throwStratum .malformed message
  | .ok (some _) =>
    let some wire ← serviceRetained scope template
      | throwStratum .malformed "a final input reference is outside its exact request scope"
    return wire.fragment
  | .ok none => pure ()
  match Backend.resultRefIndex? template with
  | .error message => throwStratum .malformed message
  | .ok (some index) =>
    let some wire := scope.references[index]?
      | throwStratum .malformed "a final result reference is outside its completed local scope"
    checkServiceOwner scope.harness wire
    return wire.fragment
  | .ok none => pure ()
  if (template.getObjValAs? String "ctor").toOption == some "opaqueData" then
    let some (.ok session) := (← scope.harness.connections.get)[scope.backend]?
      | throwStratum .unavailable "a deferred result's supplying session is unavailable"
    return DataOwnership.Data.capture template (scope.backend, session.identity)
  match template with
  | .arr values =>
    return DataOwnership.Data.array (← values.mapM (assembleServiceResult scope))
  | .obj fields =>
    let mut actual := []
    for (key, value) in fields.toList do
      actual := actual ++ [(key, ← assembleServiceResult scope value)]
    checkedFragment (DataOwnership.Data.object actual)
  | _ => return { json := template }

/-- A service node uses the same dispatch, action execution, completion and
semantic method/property paths as an ordinary computation. Its occurrence handles
are kept independently of the expression-indexed ordinary result cache. -/
partial def executeServiceRequest (scope : ServiceScope) (operation : String) (input : Form)
    (prepared : ServiceRequest.Prepared) : TermElabM ServiceNodeExecution := do
  let h := scope.harness
  checkServiceCallableInterface prepared
  let endpointWires ← match prepared.callableEndpointOperands with
    | none => pure none
    | some (source, target) => do
      let some (.endpoints domain codomain _ _) := prepared.callableInterface
        | throwError "the service endpoint occurrences lost their selected result role"
      let source ← forwardRetainedValue (← serviceWire scope source) domain
      let target ← forwardRetainedValue (← serviceWire scope target) codomain
      pure (some (source, target))
  let dependencies ← prepared.dependencies.mapM (serviceWire scope)
  let requestInputPaths ← if scope.positionedInputs then do
      let positions ← prepared.inputPaths.mapM fun (path, operand) => do
        pure (path, ← serviceWire scope operand)
      pure (some (← retainServiceInputPaths h prepared.fragment positions))
    else pure none
  let request : Wire := {
    form := input
    payload := (← combinedRecipePayload prepared.requestValue prepared.fragment dependencies)
    serviceHandles := (← retainServiceOperands h dependencies),
    serviceInputPaths := requestInputPaths }
  let template : Wire := {
    form := prepared.resultForm
    payload := (← combinedRecipePayload prepared.result prepared.fragment dependencies)
    categoryContext := prepared.resultContext
    constructionInputs := prepared.constructionInputs
    constructionInputOwnership := prepared.constructionInputOwnership }
  let result ← match prepared.action with
    | some (.object action original parameters parameterOperands) =>
      executeObjectAction h scope.trace operation action (← serviceWire scope original)
        template parameters (← parameterOperands.mapM (serviceWire scope))
        (DataOwnership.project #[.field "args"] prepared.requestOwnership)
        requestInputPaths
    | some (.wholeMap action source target original descriptor parameters parameterOperands
        imageSource imageTarget) => do
      let images ← #[imageSource, imageTarget].mapM (serviceWire scope)
      let position ← IO.mkRef (0 : Nat)
      let image : Wire → TermElabM Wire := fun original => do
        let index : Nat ← position.modifyGet fun index => (index, index + 1)
        let some actual := images[index]?
          | throwError "the whole service action requested an extra image endpoint"
        let expected ← Semantic.objOf action original.value
        SimpleServiceRequest.sameValue actual.value expected "retained image endpoint"
        checkServiceOwner h actual
        return actual
      executeMapAction h scope.trace operation action source target (← serviceWire scope original)
        template descriptor parameters (← parameterOperands.mapM (serviceWire scope)) image
        (DataOwnership.project #[.field "args", .index 2, .field "args", .index 0]
          prepared.requestOwnership)
        (DataOwnership.project #[.field "args", .index 1] prepared.requestOwnership)
        (requestInputPaths := requestInputPaths)
    | none =>
      if let some method := prepared.method then do
        let trace := prepared.trace.getD scope.trace
        let original ← serviceWire scope method.receiver
        let parameters : Array RoutedParameterInput ← method.parameters.mapM fun parameter => do
          return {
            actionIndex := parameter.actionIndex, dataIndex := parameter.dataIndex
            wire := (← serviceWire scope parameter.operand) }
        let result ← captureRoutedInvocationFrom h trace "the deferred declared method"
          prepared.result method.id method.route method.receiver.value method.comparisons
          method.application method.lifts original (some parameters)
        realizeObjectObservation h trace result
      else if let some trace := prepared.trace then do
        let #[original] := dependencies
          | throwError "the semantic service request lost its unique original receiver"
        let results ← IO.mkRef (({} : Std.HashMap Expr Wire).insert original.value original)
        let h := { h with results }
        if prepared.decisionResult then
          let (_, data) ← realizeDecision h trace "the deferred declared decision" prepared.result
          pure { template with payload := .computed prepared.result (.inline data) }
        else
          throwError "the service method omitted its complete retained invocation"
      else do
        let reply ← sendData h operation request (completeRequest := true)
        let answer := reply.data.json
        let backend := reply.backend
        let completed ← match ← prepared.complete answer with
          | .ok completed => pure completed
          | .error message => malformed backend operation answer message
        match completed with
        | some completed =>
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq (← inferType completed.apex) (← inferType prepared.result) <&&>
                isDefEq completed.apex prepared.result) do
            throwError "a completed service construction changed its independently derived apex"
          let answer ← receiveReplyFragment h operation reply true
          let packet ← match completed.packet with
            | .direct _ => pure answer
            | .created lift _ _ =>
              scopedNode "createdCone" #[{ json := toJson lift }, request.fragment, answer]
          pure { template with payload := (← constructionPayload template.form completed
            request.fragment packet), objectObserved := true }
        | none =>
          let data ← receiveReplyData h operation reply true
          let received : Wire := { template with
            payload := .computed prepared.result data
            objectObserved := prepared.objectResult, callableObserved := prepared.callableResult }
          retainServiceCallableResult prepared received endpointWires
  checkServiceOwner h result
  return { operation, input := input.id, request, dependencies, result }

/-- Execute one untrusted deferred program in a local reference scope. Every node
has an independently derived formal application and an actual retained Wire.
The enclosing ordinary caller still owns its original formal result expression. -/
partial def completeServiceReply (h : Harness) (trace : Trace)
    (stack : Array (String × Wire))
    (operation : String) (input : Wire) (reply : ComputationalReply) :
    TermElabM ComputationalReply := do
  let answer := reply.data.json
  let backend := reply.backend
  unless (answer.getObjValAs? String "ctor").toOption == some "deferredData" do
    return reply
  let .ok program := Backend.DeferredData.decode answer
    | throwStratum .malformed "the deferred service reply has malformed or out-of-scope references"
  for (previous, wire) in stack do
    if previous == operation then
      if ← sameServiceRequestForCycle h wire input then
        throwStratum .unavailable "a deferred computation recursively requests the same complete input"
  let stack := stack.push (operation, input)
  let active := { h with deferred := some (completeServiceReply h trace stack) }
  let (positionedInputs, known, inputReferences) ← serviceRequestInputs h input
  let operands ← IO.mkRef #[]
  let mut scope : ServiceScope := {
    harness := active, trace, references := #[], known, operands, backend,
    positionedInputs, inputReferences }
  let index ← h.services.modifyGet fun records => (records.size, records.push {
    operation, input, backend, original := answer })
  let outer ← prepareServiceRequest scope operation input.form (serviceInputTemplate scope input.json)
  let mut nodes := #[]
  for call in program.calls do
    let state ← registryState
    let some input := state.form? call.input
      | throwStratum .malformed "a deferred call names an unpublished input form"
    let prepared ← prepareServiceRequest scope call.operation input call.arguments
    let node ← executeServiceRequest scope call.operation input prepared
    nodes := nodes.push node
    h.services.modify fun records => records.modify index fun record => { record with nodes }
    scope := { scope with references := scope.references.push node.result }
  validateServiceResultTemplate scope outer program.result
  let result ← assembleServiceResult scope program.result
  checkDataOwners h result
  if let .error message ← outer.complete result.json then
    throwStratum .malformed m!"the completed deferred reply changes its original result interface: {message}"
  let owner := match DataOwnership.owners result.ownership with
    | #[owner] => some owner
    | _ => none
  h.services.modify fun records => records.modify index fun record =>
    { record with
      nodes, result := result.json, owner, ownership := result.ownership
      completed := true }
  return { data := result, backend := owner.map Prod.fst |>.getD backend }

/-- Retain only full category contexts supplied by the original typed operands.
An equal carrier or another registry object's declaration supplies no context. -/
def derivationContexts (wires : Array (Expr × Wire)) :
    TermElabM (Array CategoryContext × Array Language.Value) := do
  let state ← registryState
  let mut contexts : Array CategoryContext := #[]
  let mut objects : Array Language.Value := #[]
  for (key, wire) in wires do
    let some category := state.categories.find? (·.id == wire.form.category) | continue
    let candidate ← withoutModifyingState do
      try
        let context ← match wire.categoryContext with
          | some context => pure context
          | none => CategoryContext.ofNamed category wire.value
        CategoryContext.checkObject context key
        return some context
      catch error =>
        if Exception.interpretationKind error == .invalid then return none else throw error
    if let some context := candidate then
      unless contexts.any (· == context) do contexts := contexts.push context
      if context.expression.syntacticEq category.expression then
        objects := objects.push (.object key category none none none)
  return (contexts, objects)

/-- Execute a checked mathematical derivation using the ordinary typed readers,
actions, operation observations and service executor. The complete input fixes
the family application before the plan is specialized. All result data remain
untrusted; the retained family proof relates formal expressions only.

The finite family support graph rules out ungrounded cycles before expansion.
A revisit can still terminate at a directly applicable primitive, because the
ordinary dispatcher runs before this callback. Otherwise it is an explicit gap,
even when a cyclic plan changes its arguments on every recursive call. -/
partial def executeDerivedRequest (h : Harness) (trace : Trace)
    (stack : Array ComputationRef) (operation : String) (input : Wire)
    (_completeRequest : Bool) : TermElabM ComputationalReply := do
  let state ← registryState
  let some reference := (state.operation? operation).bind ComputationDerivation.reference?
    | throwStratum .noImplementation m!"no admitted registration or published derivation computes {operation} on {input.form.id}"
  if stack.contains reference then
    throwStratum .noImplementation m!"cyclic computational derivation has no applicable primitive at {operation}; family path {stack.map ComputationDerivation.address}"
  let entries ← computationDerivations
  let support ← derivationSupport h entries (stack.push reference)
  let candidates := (entries.filter fun entry => entry.target == reference &&
    entry.prerequisites.all support.contains).qsort fun left right => left.id.raw < right.id.raw
  if candidates.isEmpty then
    let requested := entries.filter (·.target == reference)
    let missing := requested.map fun entry => (entry.id.raw,
      entry.prerequisites.filter (!support.contains ·) |>.map ComputationDerivation.address)
    throwStratum .noImplementation m!"no finite primitive-supported computational derivation computes {operation} on {input.form.id}; missing or cyclic prerequisites {missing}"
  let (positionedInputs, known, inputReferences) ← serviceRequestInputs h input
  let mut gaps : Array String := #[]
  for entry in candidates do
    let failures ← h.portFailures.get
    try
      let privateTrace ← IO.mkRef (← trace.get)
      let operands ← IO.mkRef #[]
      let binding ← mkFreshUserName `_computationalDerivation
      let scope : ServiceScope := {
        harness := h, trace := privateTrace, references := #[], known, operands
        positionedInputs, inputReferences,
        backend := s!"derivation:{entry.id.raw}", operandBinding := some binding.toString }
      let prepared ← prepareServiceRequest scope operation input.form (serviceInputTemplate scope input.json)
      let some application := prepared.familyApplication
        | throwStratum .noImplementation "the published request preparer does not retain a whole family application"
      let checked ← validateComputationDerivation state.toSemanticState entry
      let expansion ← ComputationDerivation.instantiate checked
        (← instantiateMVars application) (← instantiateMVars prepared.result)
      let originals ← (← operands.get).mapIdxM fun index wire => do
        return (← serviceOperandValue scope index wire.value, wire)
      let (contexts, knownObjects) ← derivationContexts originals
      let calls ← IO.mkRef #[]
      let compiler : ComputationDerivation.Compiler := {
        trace := privateTrace, slots := expansion.slots
        known := originals.map (·.1), knownObjects, contexts, calls }
      let compiled ← ComputationDerivation.compile compiler expansion.expanded
      ComputationDerivation.same expansion.expanded compiled
      let calls ← calls.get
      let index ← h.derivations.modifyGet fun records => (records.size, records.push {
        derivation := entry.id, target := entry.target, application := expansion.application
        original := expansion.original, identity := expansion.identity, input, prerequisites := calls })
      let results ← IO.mkRef (originals.foldl
        (fun cache (key, wire) => cache.insert key wire) ({} : Std.HashMap Expr Wire))
      let active := { h with
        results := results
        demandObjectActions := true
        derivation := some (executeDerivedRequest h privateTrace (stack.push reference)) }
      let active := { active with deferred := some (completeServiceReply active privateTrace #[]) }
      for call in calls do
        let actual ← realize active privateTrace "the formal derivation's published prerequisite" call.result
        let actual ← match call.reference with
          | .operation _ | .morphism _ => realizeArrowObservation active privateTrace actual
          | _ =>
            if (Language.homEnds? (← inferType call.result)).isSome then
              realizeArrowObservation active privateTrace actual
            else realizeObjectObservation active privateTrace actual
        checkServiceOwner active actual
        results.modify (·.insert call.result actual)
        h.derivations.modify fun records => records.modify index fun record =>
          { record with steps := record.steps.push actual }
      let result ← realize active privateTrace "the complete proved derivation" compiled
      let result ← if prepared.callableResult then
          realizeArrowObservation active privateTrace result
        else if prepared.objectResult then realizeObjectObservation active privateTrace result
        else pure result
      checkServiceOwner active result
      if let .error message ← prepared.complete result.json then
        throwStratum .malformed m!"the completed derivation changes its original result interface: {message}"
      let retained := { result with
        payload := forwardPayload result expansion.original result.json
        categoryContext := prepared.resultContext.orElse fun _ => result.categoryContext }
      h.derivations.modify fun records => records.modify index fun record =>
        { record with result := some retained }
      let owner := match DataOwnership.owners result.ownership with
        | #[owner] => some owner
        | _ => none
      return { data := result.fragment, backend := owner.map Prod.fst |>.getD scope.backend }
    catch error =>
      unless !Exception.hasConflictingStrata error &&
          Exception.stratum? error == some .noImplementation &&
          (← h.portFailures.get) == failures do throw error
      gaps := gaps.push s!"{entry.id.raw}: {← error.toMessageData.toString}"
  throwStratum .noImplementation m!"no applicable proved computational derivation computes {operation} on {input.form.id}; {gaps}"

/-- Install the same typed service and derivation boundary for production claims
and direct public Harness clients. No new mathematical selector is installed. -/
def enableService (h : Harness) (trace : Trace) : Harness :=
  let active := { h with derivation := some (executeDerivedRequest h trace #[]) }
  { active with deferred := some (completeServiceReply active trace #[]) }


/-- Whether two closed values of a type with decidable equality are equal: the kernel accepts
the proof by decision of `a = b`, or of `a ≠ b`. The literal forms are registered with decidable
equality; a decision is an `Option Bool`. -/
def evaluatedEq (a b : Expr) : MetaM Bool := do
  if ← isDefEq a b then return true
  if (← Codec.conditionProof (← mkEq a b)).isSome then return true
  match ← decideProp (← mkEq a b) with
  | some equal => return equal
  | none => throwStratum .noImplementation m!"the fixed typed values have no executable equality comparison"

/-- The registered evaluations that apply to the proposition `p`: the `evaluation` of each
registered literal form (a literal row's, a subset-literal row's) whose denotation occurs in `p`.
Each is a `meta` procedure of `lean-categories`, validated there with its row, which rewrites the
images of literals of its form under the catalogue's operations to literals, by the theorems of
its domain, and never closes a goal. -/
def evaluationsOf (state : RegistryState) (p : Expr) : Array Name :=
  let occurs (denotation : Name) : Bool := (p.find? (·.isConstOf denotation)).isSome
  (state.literals.filterMap fun form => if occurs form.denotation then form.evaluation else none)
    ++ (state.subsetLiterals.filterMap fun form =>
      if occurs form.denotation then form.evaluation else none)

/-- Select domain-owned point evaluators only from actual retained complete comparisons. -/
def presentationEvaluationsOf (trace : Trace) (p : Expr) : TermElabM (Array Name) := do
  let state ← registryState
  let some (carrier, _, _) := (← whnfR p).eq? | return #[]
  let pointDomain (type : Expr) : TermElabM (Option Expr) := do
    let type ← withTransparency .all <| whnf type
    if let .forallE _ domain _ _ := type then return some domain
    if type.getAppFn.constName? == some ``TypeCat.Hom && type.getAppNumArgs == 2 then
      return some type.getAppArgs[0]!
    return none
  let some domain ← pointDomain carrier | return #[]
  let mut evaluations := #[]
  for (point, node) in (← trace.get).toArray do
    let .presentationApply id params inverse source target argument := node | continue
    let some entry := state.presentations.find? (·.id == id) | continue
    let some evaluation := entry.evaluation | continue
    let terms := params ++ #[point, source, target, argument]
    if terms.any (fun term => term.hasMVar || term.hasLevelMVar || term.hasFVar ||
        term.hasLooseBVars) then continue
    let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
      xs.mapM (·.fvarId!.getBinderInfo)
    let some application := p.find? fun term =>
        term.getAppFn.constName? == some entry.declaration &&
        term.getAppNumArgs == infos.size | continue
    let actualParams := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
      if info.isExplicit then some arg else none
    unless actualParams.size == params.size do continue
    let same ← (actualParams.zip params).allM fun (actual, expected) =>
      withTransparency .all <| isDefEq actual expected
    unless same do continue
    let some argumentDomain ← pointDomain (← inferType argument) | continue
    unless ← withTransparency .all <| isDefEq argumentDomain domain do continue
    let arrow ← Semantic.presentationArrow entry application inverse
    unless ← withTransparency .all <| isDefEq (← inferType arrow)
        (← mkAppM ``Quiver.Hom #[source, target]) do continue
    let some actualDomain ← pointDomain (← inferType point) | continue
    unless ← withTransparency .all <| isDefEq actualDomain domain do continue
    unless evaluations.contains evaluation do evaluations := evaluations.push evaluation
  return evaluations

/-- Whether Lean's kernel accepts a proof of the closed proposition `p` by the registered
evaluations `evaluations` and decision: the goal `p` is given to each evaluation in turn, through
the one sanctioned runner (`Language.runProcedure`, LC-18). A closed remainder uses the existing
structural decision (`Codec.conditionProof`), retaining its complete declared types while
normalizing their presentation. Kernel-owned trace markers are removed only in this proof
presentation, so they cannot obstruct a registered literal's decision instance; the original
question and its operation records retain them. Ordinary `mkDecideProof` remains available for
a residue with local hypotheses. The assembled proof is checked against the original `p` by Lean's kernel,
synchronously within `decideBudget`. Failure to construct or check a proof decides nothing. -/
def evaluatedDecides (evaluations : Array Name) (p : Expr) : TermElabM Bool := do
  let attempt : TermElabM Bool := do
    let goal ← mkFreshExprMVar p .syntheticOpaque
    let mut remaining := [goal.mvarId!]
    for evaluation in evaluations do
      let [current] := remaining | return false
      match ← Language.runProcedure evaluation current with
      | .ok goals => remaining := goals
      -- not a reading fallback: an evaluation that fails decides nothing, and the claim is then
      -- realized, unchanged
      | .error _ => return false
    match remaining with
    | [] => pure ()
    | [residue] => residue.withContext do
        let condition ← instantiateMVars (← residue.getDecl).type
        let condition ← Core.transform condition (post := fun term => do
          let unanchored := Trace.unanchor term
          if unanchored != term then return .visit unanchored
          let args := term.getAppArgs
          if term.isAppOf ``Trace.operationResult && args.size >= 3 then
            -- The marker's arguments are its binding, complete type, and value.
            -- A wrapped callable may have further arguments on the same spine.
            return .visit (mkAppN args[2]! (args.extract 3 args.size))
          return .done term)
        let structural ← if condition.hasFVar || condition.hasMVar || condition.hasLevelMVar then
          pure none else Codec.conditionProof condition
        let proof ← match structural with
          | some proof => pure proof
          | none => mkDecideProof condition
        residue.assign proof
    | _ => return false
    let proof ← instantiateMVars goal
    if proof.hasMVar || proof.hasLevelMVar || proof.hasSorry then return false
    kernelAccepts p proof
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|
      -- not a reading fallback: a proposition the evaluations and decision do not settle is not
      -- decided by Lean; the claim is then realized, unchanged
      tryCatchRuntimeEx attempt fun _ => pure false

/-- The proposition `p` decided in Lean, generically: `some true` when the kernel accepts its
proof by the registered evaluations that apply to it (`evaluationsOf`) and decision
(`evaluatedDecides`), `some false` when it accepts one of `¬p`, `none` otherwise. -/
def decideEvaluated (p : Expr) (trace? : Option Trace := none) : TermElabM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  let pointEvaluations ← match trace? with
    | some trace => presentationEvaluationsOf trace p
    | none => pure #[]
  let evaluations := pointEvaluations ++ evaluationsOf (← registryState) p
  if ← evaluatedDecides evaluations p then return some true
  if ← evaluatedDecides evaluations (mkNot p) then return some false
  return none

/-- Outcomes available to computation after interpretation. An execution path cannot
construct an authoritative semantic-invalidity or semantic-ambiguity judgement. -/
inductive ExecutionOutcome
  | holds
  | wrong (message : String)
  | gap (reason : String)
  | unavailable (reason : String)
  | malformed (reason : String)
  | internal (reason : String)
  deriving Inhabited, Repr

/-- The runner bridge preserves each computational stratum when reporting it. -/
def ExecutionOutcome.toOutcome : ExecutionOutcome → Outcome
  | .holds => .holds
  | .wrong reason => .wrong reason
  | .gap reason => .gap reason
  | .unavailable reason => .unavailable reason
  | .malformed reason => .malformed reason
  | .internal reason => .internal reason

/-- Discharge `claim` in Lean, generically (`decideEvaluated`): holds when its proposition is
decided true; wrong when it is decided false; `none` when Lean does not
decide it. -/
def discharge (claim : Claim) (trace? : Option Trace := none) :
    TermElabM (Option ExecutionOutcome) := do
  let refuted (what : String) : TermElabM (Option ExecutionOutcome) :=
    return some (.wrong s!"{what} is refuted: Lean decides it false")
  match claim with
  | .binding => return some (.internal "a binding entered execution")
  | .implemented _ => return none
  | .literal _ _ _ _ prop left right =>
      match ← decideEvaluated prop trace? with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .homs _ _ _ prop left right =>
      match ← decideEvaluated prop trace? with
      | some true => return some .holds
      | some false => refuted s!"{left} = {right}"
      | none => return none
  | .decision prop expected shown | .judged _ prop expected shown =>
      let some expected := expected | return none
      match ← decideEvaluated prop trace? with
      | some decided => if decided == expected then return some .holds else refuted shown
      | none => return none

/-- Compare the actual reconstructed points using their retained registered evaluator. -/
def evaluatedPointEq (trace : Trace) (a b : Expr) : TermElabM Bool := do
  let condition ← mkEq a b
  let evaluations ← presentationEvaluationsOf trace condition
  unless evaluations.isEmpty do
    if ← evaluatedDecides evaluations condition then return true
    if ← evaluatedDecides evaluations (mkNot condition) then return false
  evaluatedEq a b

/-- Interpret the port's finite function graphs under categorical composition.
This is execution data, not a proposition: the final graph is independently
decoded at the fixed formal morphism type before an equality is observed. -/
partial def composedFiniteGraph (json : Json) : Except String Json := do
  if json.getArr?.isOk then return json
  if (json.getObjValAs? String "ctor").toOption == some "typedMap" then
    let framed ← Backend.TypedMap.decode json
    return ← composedFiniteGraph framed.callable
  -- `finiteGraph`: an explicit domain inventory and a graph with exactly those keys, once each.
  if (json.getObjValAs? String "ctor").toOption == some "finiteGraph" then
    let #[inventory, graph] ← (json.getObjVal? "args").bind (·.getArr?)
      | throw "a finite graph has exactly an inventory and a graph"
    let inventory ← inventory.getArr?
    let entries ← graph.getArr?
    let keys ← entries.mapM fun entry => do
      let #[key, _] ← entry.getArr? | throw "a finite graph entry is not a pair"
      pure key
    unless keys.size == inventory.size && inventory.all (fun point => keys.contains point) &&
        keys.all (fun key => inventory.contains key) do
      throw "the finite graph's keys are not exactly its inventory"
    return graph
  unless (json.getObjValAs? String "ctor").toOption == some "compose" do
    throw "the computed finite map is neither a graph nor a composite of graphs"
  let #[first, second] ← (json.getObjVal? "args").bind (·.getArr?)
    | throw "the computed composition must have exactly two arrows"
  let first ← (← composedFiniteGraph first).getArr?
  let second ← (← composedFiniteGraph second).getArr?
  let mut result := #[]
  for entry in first do
    let #[input, middle] ← entry.getArr?
      | throw "the first finite map has a malformed graph entry"
    let mut outputs := #[]
    for entry' in second do
      let #[key, output] ← entry'.getArr?
        | throw "the second finite map has a malformed graph entry"
      if key == middle then outputs := outputs.push output
    let #[output] := outputs
      | throw "the second finite map is not uniquely defined on an intermediate point"
    result := result.push (Json.arr #[input, output])
  return Json.arr result

/-- Observe actual computational points through the published equality characteristic map.
The truth datum is never elaborated as a proposition or used as proof evidence. -/
def observeComputedPoints (h : Harness) (trace : Trace) (first second : Wire)
    (formal : Expr) : TermElabM Bool := do
  let state ← registryState
  let pointType ← inferType formal
  let some (domain, target) := Language.homEnds? pointType
    | throwStratum .noImplementation "the computational observation has no retained categorical point endpoints"
  let closedPoint ← withTransparency .all <| isDefEq domain (← closedElementDomain state)
  unless closedPoint do
    -- Decode a whole-arrow graph at the fixed Hom type. An ordinary named
    -- descriptor is not its computed value, even when Lean can evaluate its body.
    -- Explicit identity is structural input; all other values come from data.
    let finiteGraphValue (wire : Wire) : TermElabM (Option Expr) := do
      if let .ordinary value json := wire.payload then
        if let some (.morphismIdentity _ _) ← (trace.node? value : IO _) then
          if (json.getObjValAs? String "ctor").toOption == some "identity" then
            return some value
      let data? := match wire.payload with
        | .ordinary _ json => some json
        | .computed _ (.inline data) => some data
        | _ => none
      let some data := data? | return none
      match composedFiniteGraph data with
      | .ok graph =>
        match ← Codec.decode pointType graph with
        | .ok value => return some value
        | .error message => throwStratum .malformed m!"the computed finite graph is invalid: {message}"
      | .error _ => return none
    if let some actualFirst ← finiteGraphValue first then
      if let some actualSecond ← finiteGraphValue second then
        return ← evaluatedPointEq trace actualFirst actualSecond
    let retained ← framingContext first.categoryContext second.categoryContext
    let context ← match retained with
      | some context => pure context
      | none =>
        let some category := state.categories.find? (·.id == first.form.category)
          | throwError "the whole-callable observation lost its selected category"
        CategoryContext.ofNamed category domain
    CategoryContext.checkMorphism context formal domain target
    CategoryContext.checkMorphism context first.value domain target
    CategoryContext.checkMorphism context second.value domain target
    let owner ← wholeCallableObject formal domain target context
    let one ← closedElementDomain state
    let first ← wholeCallablePoint h trace first domain target one context owner
    let second ← wholeCallablePoint h trace second domain target one context owner
    return ← observeEquality h trace first second one owner.application.value
  -- Closed-point data belongs to the target. In particular a vector element
  -- can itself be a graph and is not the graph of the outer map `1 ⟶ target`.
  if ← ComputationalData.plainType (← withTransparency .all <| whnf target) then
    let observe (wire : Wire) : TermElabM (Option Expr) := do
      match wire.payload with
      | .computed _ (.inline data) =>
        match ← Codec.decode target data with
        | .ok value => return some value
        | .error _ => return none
      | .ordinary value json =>
        let actual? ← match ← (trace.node? value : IO _) with
          | some (.elementNumeral ..) => pure (some value)
          | some (.morphismIdentity ..) => pure (some value)
          | _ => do
            let some category := state.categories.find? (·.id == CategoryId.sets)
              | return none
            -- An ordinary input may be a literal point followed by a declared
            -- inclusion. Decode its actual public descriptor at the fixed point
            -- type; never substitute the retained formal expression for data.
            pure ((← decodeValue trace category pointType json).toOption.map Prod.fst)
        let some actual := actual? | return none
        return some (← withTransparency .all <| whnf (← pointResultValue state actual))
      | _ => return none
    if let some a ← observe first then
      if let some b ← observe second then
        let equation ← mkEq a b
        if let some answer ← Decide.decideProp equation then return answer
        -- The existing structural codec decides the same equation through
        -- declared aliases and inclusions, with independent kernel checking.
        if (← Codec.conditionProof equation).isSome then return true
        if (← Codec.conditionProof (mkNot equation)).isSome then return false
  observeEquality h trace first second domain target

def realizeClaim (h : Harness) (trace : Trace) (claim : Claim) : TermElabM ExecutionOutcome := do
  let h := enableService { h with demandObjectActions := true } trace
  match claim with
  | .binding => return .internal "a binding entered execution"
  | .implemented value =>
      -- A decision is realized as one; anything else as a value.
      if ← isProp value then discard <| realizeDecision h trace "the decision" value
      else
        let wire ← realize h trace "the value" value
        if (Language.homEnds? (← inferType value)).isSome then
          discard <| realizeArrowObservation h trace wire
      return .holds
  | .literal X _ form L _ left right =>
      let w ← realize h trace left X
      match w.form with
      | .literal form' =>
        unless form'.id == form.id do
          throwStratum .malformed m!"{left} is computed in a different declared literal form"
      | _ =>
        unless w.form.category == form.category do
          throwStratum .malformed m!"{left} changed the fixed literal observation category"
      let literalType ← mkConstWithFreshMVarLevels form.type
      unless ← ComputationalData.plainType literalType do
        throwStratum .noImplementation "the literal observation requires a proof-free declared data representation"
      let literal ← match ← Codec.decode literalType w.json with
        | .ok literal => pure literal
        | .error message => throwStratum .malformed m!"the realized literal no longer decodes: {message}"
      return if ← evaluatedEq literal L then .holds
        else .wrong s!"{left} is not {right}: the registration answered {w.json.compress}"
  | .homs f g _ _ left right =>
      let mut a ← realize h trace left f
      let mut b ← realize h trace right g
      unless (← isDefEq (← inferType a.value) (← inferType f)) &&
          (← isDefEq (← inferType b.value) (← inferType g)) do
        throwStratum .malformed m!"the computed arrows changed the fixed comparison endpoints"
      let some (domain, target) := Language.homEnds? (← inferType f)
        | throwStratum .noImplementation "the compared arrows have no retained categorical endpoints"
      unless ← withTransparency .all <| isDefEq domain (← closedElementDomain (← registryState)) do
        a ← realizeArrowObservation h trace a
        b ← realizeArrowObservation h trace b
        return if ← observeComputedPoints h trace a b f then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      if (match a.payload with | .computed .. => true | _ => false) ||
          (match b.payload with | .computed .. => true | _ => false) then
        return if ← observeComputedPoints h trace a b f then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      -- Only literal data on both sides is a value the kernel compares itself. Any other
      -- uncomputed side (an element expression, a power-object map, a composite) is a request
      -- that only a registered computation evaluates.
      unless (match a.form, b.form with | .literal _, .literal _ => true | _, _ => false) do
        return if ← observeEquality h trace a b domain target then .holds
          else .wrong s!"{left} is not {right}: the computational equality observation is false"
      -- The retained formal maps fix the question; only the actual computational answer
      -- data is compared here. Using Wire.value would hide a well-formed wrong answer.
      let observe (wire : Wire) (formal : Expr) : TermElabM Expr := do
        let state ← registryState
        let some category := state.categories.find? (·.id == wire.form.category)
          | throwStratum .malformed "the computed map has no declared category"
        match ← decodeValue trace category (← inferType formal) wire.json with
        | .ok (actual, _) => return actual
        | .error message =>
            throwStratum .noImplementation m!"the computational map has no independent observation decoder: {message}"
      let actualLeft ← observe a f
      let actualRight ← observe b g
      return if ← evaluatedPointEq trace actualLeft actualRight then .holds
        else .wrong s!"{left} is not {right}: computed as {a.json.compress} and \
          {b.json.compress}"
  | .decision prop expected shown | .judged _ prop expected shown =>
      let (answer, json) ← realizeDecision h trace shown prop
      return if ← evaluatedEq answer (toExpr expected) then .holds
        else .wrong s!"{shown} is not the answer: the registration answered {json.compress}"

/-- Representation-only normalization: metadata and bound-variable spelling carry no
mathematical identity. Operations, constants, routes, parameters and logical constructors
remain intact; there is no reduction by truth, provability or logical equivalence. -/
partial def canonicalTerm (term : Expr) : Expr :=
  Id.run (MonadStateCacheT.run (visit term))
where
  /-- Share only exact syntax within this traversal. Binder annotations and all
  data remain significant; neither reduction nor proof irrelevance is a cache key. -/
  visit (term : Expr) : MonadStateCacheT ExprStructEq Expr Id Expr :=
    checkCache (ExprStructEq.mk term) fun _ => do
      match term with
      | .mdata _ child => visit child
      | .app fn arg => return .app (← visit fn) (← visit arg)
      | .lam _ type body info => return .lam .anonymous (← visit type) (← visit body) info
      | .forallE _ type body info => return .forallE .anonymous (← visit type) (← visit body) info
      | .letE _ type value body nondep =>
          return .letE .anonymous (← visit type) (← visit value) (← visit body) nondep
      | .proj type index child => return .proj type index (← visit child)
      | term => return term

def questionTerm (term : Expr) : TermElabM Expr := do
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then throwError "question contains unresolved typed terms"
  return canonicalTerm term

/-- Instantiate the complete tree without reducing its relations or logic. -/
partial def instantiateQuestion : Question → TermElabM Question
  | .proposition term => return .proposition (← questionTerm term)
  | .judgement relation terms route declarations _ => do
      let terms ← terms.mapM questionTerm
      let types ← terms.mapM fun term => do questionTerm (← inferType term)
      return .judgement relation terms route declarations types
  | .conjunction left right => return .conjunction (← instantiateQuestion left) (← instantiateQuestion right)
  | .negation question => return .negation (← instantiateQuestion question)

partial def showQuestion : Question → TermElabM String
  | .proposition term => return s!"{← ppExpr term}"
  | .judgement relation terms route declarations _ => do
      let terms ← terms.mapM fun term => return s!"({← ppExpr term} : {← ppExpr (← inferType term)})"
      return s!"{relation} [{String.intercalate ", " terms.toList}] via {route.toList}; declarations {declarations.toList}"
  | .conjunction left right => return s!"({← showQuestion left}) and ({← showQuestion right})"
  | .negation question => return s!"not ({← showQuestion question})"

partial def encodeQuestion (table : TermTable) : Question → TermElabM Json
  | .proposition term => return Json.arr #[toJson "proposition", toJson (← table.encode term)]
  | .judgement relation terms route declarations types => do
      let terms ← terms.mapM table.encode
      let types ← types.mapM table.encode
      return Json.arr #[toJson "judgement", toJson relation, toJson terms,
        toJson (route.map reprStr), toJson (declarations.map reprStr), toJson types]
  | .conjunction left right =>
      return Json.arr #[toJson "and", ← encodeQuestion table left, ← encodeQuestion table right]
  | .negation question => return Json.arr #[toJson "not", ← encodeQuestion table question]

/-- The semantic question a claim asks, as a fingerprint of its elaborated proposition (and, for a
decision, the expected answer): what an admitted assertion means under this kernel, parser and
pin, compared across candidates by `scripts/check_question_permanence.py` (gov-meaning-permanence).
It is never the statement's text, its outcome, or whether it is provable. -/
def claimQuestion : Claim → TermElabM (String × String)
  | .binding => throwError "a binding has no assertion question"
  | .judged question proposition expected _ => do
      let question ← instantiateQuestion question
      let proposition ← questionTerm proposition
      unless ← isProp proposition do
        throwError "the judged claim has no proposition to evaluate"
      let propositionType ← questionTerm (← inferType proposition)
      let table ← TermTable.new
      let questionRoot ← encodeQuestion table question
      let proposition ← table.encode proposition
      let propositionType ← table.encode propositionType
      let roots := Json.mkObj [("question", questionRoot),
        ("proposition", toJson proposition), ("type", toJson propositionType)]
      return (s!"judged:{expected}:{← table.finish roots}",
        s!"judged:{expected}: {← showQuestion question}")
  | .implemented value => fingerprint "implemented" value
  | .literal _ _ _ _ prop .. => fingerprint "literal" prop
  | .homs _ _ _ prop .. => fingerprint "homs" prop
  | .decision prop expected _ => fingerprint s!"decision:{expected}" prop
where
  /-- The fingerprint, and the proposition as the acceptance author reads it to confirm the
  interpretation it records. -/
  fingerprint (kind : String) (e : Expr) : TermElabM (String × String) := do
    let e ← questionTerm e
    let type ← questionTerm (← inferType e)
    let table ← TermTable.new
    let root ← table.encode e
    let type ← table.encode type
    return (s!"{kind}:{← table.finish (Json.arr #[toJson root, toJson type])}",
      s!"{kind}: {← ppExpr e}")

/-- The complete typed request consumed by execution. Its claim and selected operation
records are prepared and validated together, independently of audit serialization. -/
structure PreparedQuestion where
  claim : Claim
  trace : Std.HashMap Expr Node

/-- An explicit audit export of a prepared request. Execution uses the same retained
claim and operation records; the identity and revision label are export data only. -/
structure TypedQuestion where
  claim : Claim
  trace : Std.HashMap Expr Node
  identity : String × String
  mathematicalRevision : String

/-- Recover the retained execution request without re-reading its syntax or its export. -/
def TypedQuestion.prepared (question : TypedQuestion) : PreparedQuestion :=
  { claim := question.claim, trace := question.trace }

/-- The complete existing presentation record, encoded once for both canonical keys
and the final operation snapshot. Ordered routes, parameters and applications are retained. -/
def encodeParameterPresentation (encode : Expr → TermElabM Nat)
    (source : ParameterPresentation) : TermElabM Json := do
  return Json.arr #[toJson source.source.raw, toJson source.sourceCategory.raw,
    toJson source.targetCategory.raw, toJson (← source.params.mapM encode),
    toJson (source.route.map reprStr), toJson (← source.applications.mapM encode),
    toJson (source.carrierRoute.map reprStr),
    toJson (source.identifications.map Name.toString), toJson (← encode source.object),
    toJson (← encode source.image), toJson (← encode source.identity)]

/-- Keep the prior source/route/parameter ordering where it distinguishes records,
and resolve its ties by every retained field. Source enumeration cannot select an order. -/
def orderParameterPresentations (source : TermTable) (presentations : Array ParameterPresentation) :
    TermElabM (Array ParameterPresentation) := do
  let keyed ← presentations.mapM fun presentation => do
    let parameters ← presentation.params.mapM fun term => do
      source.rootIdentity (← source.encode term)
    return (presentation.source.raw ++ reprStr presentation.route ++ reprStr parameters, presentation)
  QuestionIdentity.orderByCompleteKey keyed fun presentation => do
    let target ← TermTable.new
    let remap ← TermRemap.new source target
    let record ← encodeParameterPresentation remap.encodeTerm presentation
    target.finish record

/-- Complete operation source provenance, including each comparison's constructor
and whiskering contexts separately from its checked typed witness. -/
def encodeOperationSource (encode : Expr → TermElabM Nat) (source : OperationSource) :
    TermElabM Json :=
  OperationAgreement.encodeSource encode source

def encodeOperationCandidate (encode : Expr → TermElabM Nat) (candidate : OperationCandidate) :
    TermElabM Json :=
  OperationAgreement.encodeCandidate encode candidate

def encodeOperationFamilyComparison (encode : Expr → TermElabM Nat)
    (comparison : OperationFamilyComparison) : TermElabM Json := do
  return Json.arr #[toJson comparison.left, toJson comparison.right,
    toJson comparison.leftSource, toJson comparison.rightSource,
    toJson (← comparison.parameters.mapM encode), toJson (← encode comparison.leftFamily),
    toJson (← encode comparison.rightFamily), toJson (← encode comparison.leftType),
    toJson (← encode comparison.rightType), toJson (← encode comparison.identity)]

/-- The operation schema has one encoder. Complete tie keys and the final snapshot
both use this same field traversal; typed terms use the unchanged proof-proposition quotient. -/
def encodeSnapshotNode (source : TermTable) (encode : Expr → TermElabM Nat)
    (node : Node) : TermElabM Json := do
  let encodeContext (context : CategoryContext) : TermElabM Json := do
    return Json.arr #[toJson (reprStr context.expression), toJson (← encode context.bundle)]
  let encodeComparisons (comparisons : Array (RouteComparison × Expr)) : TermElabM Json := do
    return Json.arr (← comparisons.mapM fun (context, value) => do
      pure <| Json.arr #[OperationAgreement.encodeRouteComparison context, toJson (← encode value)])
  match node with
  | .object id parameters =>
      pure (Json.arr #[toJson "object", toJson id.raw, toJson (← parameters.mapM encode)])
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      pure (Json.arr #[toJson "parameterTransport", toJson source.raw,
        toJson sourceCategory.raw, toJson targetCategory.raw, toJson (route.map reprStr),
        toJson (← encode receiver)])
  | .structureTransport sourceCategory targetCategory route receiver =>
      pure (Json.arr #[toJson "structureTransport", toJson sourceCategory.raw,
        toJson targetCategory.raw, toJson (route.map reprStr), toJson (← encode receiver)])
  | .proofRefinement classifier sourceCategory targetCategory source action identity =>
      pure (Json.arr #[toJson "proofRefinement", toJson classifier.raw,
        toJson sourceCategory.raw, toJson targetCategory.raw,
        toJson (← encode source), toJson (← encode action), toJson (← encode identity)])
  | .parameterEquivalence expected representative sources => do
      let sources ← orderParameterPresentations source sources
      let data ← sources.mapM (encodeParameterPresentation encode)
      pure (Json.arr #[toJson "parameterEquivalence", toJson (← encode expected),
        toJson (← encode representative), Json.arr data])
  | .operationEquivalence representative chosen candidates comparisons =>
      pure (Json.arr #[toJson "operationEquivalence", toJson (← encode representative),
        toJson chosen, Json.arr (← candidates.mapM (encodeOperationCandidate encode)),
        Json.arr (← comparisons.mapM (encodeOperationFamilyComparison encode))])
  | .retainedRoute source target route applications receiver =>
      pure (Json.arr #[toJson "retainedRoute", toJson source.raw, toJson target.raw,
        toJson (route.map reprStr), toJson (← applications.mapM encode),
        toJson (← encode receiver)])
  | .namedMorphism id params =>
      pure (Json.arr #[toJson "namedMorphism", toJson id.raw, toJson (← params.mapM encode)])
  | .admittedPoint id category params original originalCategory source target =>
      pure (Json.arr #[toJson "admittedPoint", toJson id.raw, toJson category.raw,
        toJson (← params.mapM encode), toJson (← encode original),
        toJson originalCategory.raw, toJson (← encode source), toJson (← encode target)])
  | .constrainedPoint constructor category domain source target original =>
      pure (Json.arr #[toJson "constrainedPoint", toJson constructor.toString,
        toJson category.raw, toJson (← encode domain), toJson (← encode source),
        toJson (← encode target), toJson (← encode original)])
  | .powerObjectMap id field params =>
      pure (Json.arr #[toJson "powerObjectMap", toJson id.raw, toJson field,
        toJson (← params.mapM encode)])
  | .objectField id field category params =>
      pure (Json.arr #[toJson "objectField", toJson id.raw, toJson field, toJson category.raw,
        toJson (← params.mapM encode)])
  | .namedInclusion id category params source target =>
      pure (Json.arr #[toJson "namedInclusion", toJson id.raw, toJson category.raw,
        toJson (← params.mapM encode), toJson (← encode source),
        toJson (← encode target)])
  | .callableRecipe category domain target body =>
      pure (Json.arr #[toJson "callableRecipe", toJson category.raw,
        toJson (← encode domain), toJson (← encode target),
        toJson (← encode body)])
  | .namedCallable address category params =>
      pure (Json.arr #[toJson "namedCallable", toJson address, toJson category.raw,
        toJson (← params.mapM encode)])
  | .presentation id params inverse =>
      pure (Json.arr #[toJson "presentation", toJson id.raw,
        toJson (← params.mapM encode), toJson inverse])
  | .generator id params =>
      pure (Json.arr #[toJson "generator", toJson id.raw, toJson (← params.mapM encode)])
  | .elementNumeral value target selected =>
      pure (Json.arr #[toJson "elementNumeral", toJson value,
        toJson (← encode target), toJson (← encode selected)])
  | .elementValue point target selected =>
      pure (Json.arr #[toJson "elementValue", toJson (← encode point),
        toJson (← encode target), toJson (← encode selected)])
  | .productMediator category presentation domain left right =>
      pure (Json.arr #[toJson "productMediator", toJson category.raw,
        toJson (← encode presentation), toJson (← encode domain),
        toJson (← encode left), toJson (← encode right)])
  | .morphismComposition category first second source middle target =>
      pure (Json.arr #[toJson "morphismComposition", toJson category.raw,
        toJson (← encode first), toJson (← encode second),
        toJson (← encode source), toJson (← encode middle),
        toJson (← encode target)])
  | .morphismIdentity category object =>
      pure (Json.arr #[toJson "morphismIdentity", toJson category.raw,
        toJson (← encode object)])
  | .contextualRoute source target route applications receiver morphism =>
      pure (Json.arr #[toJson "contextualRoute", ← encodeContext source, ← encodeContext target,
        toJson (route.map reprStr), toJson (← applications.mapM encode),
        toJson (← encode receiver), toJson morphism])
  | .contextualComposition context first second source middle target =>
      pure (Json.arr #[toJson "contextualComposition", ← encodeContext context,
        toJson (← encode first), toJson (← encode second), toJson (← encode source),
        toJson (← encode middle), toJson (← encode target)])
  | .contextualIdentity context object =>
      pure (Json.arr #[toJson "contextualIdentity", ← encodeContext context,
        toJson (← encode object)])
  | .contextualArrow context hom source target =>
      pure (Json.arr #[toJson "contextualArrow", ← encodeContext context,
        toJson (← encode hom), toJson (← encode source), toJson (← encode target)])
  | .arrowProjection receiver =>
      pure (Json.arr #[toJson "arrowProjection", toJson (← encode receiver)])
  | .limitProjection receiver index =>
      pure (Json.arr #[toJson "limitProjection", toJson (← encode receiver),
        toJson (← encode index)])
  | .structuredProjection receiver field index =>
      pure (Json.arr #[toJson "structuredProjection", toJson (← encode receiver),
        toJson field, toJson index])
  | .callableEndpoint context receiver source =>
      pure (Json.arr #[toJson "callableEndpoint", ← encodeContext context,
        toJson (← encode receiver), toJson source])
  | .pointView source target route applications argument =>
      pure (Json.arr #[toJson "pointView", toJson (← encode source),
        toJson (← encode target), toJson (route.map reprStr),
        toJson (← applications.mapM encode), toJson (← encode argument)])
  | .operationPoint id params comparison operation target selected =>
      pure (Json.arr #[toJson "operationPoint", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode comparison),
        toJson (← encode operation), toJson (← encode target),
        toJson (← encode selected)])
  | .operationApply id params operands target selected =>
      pure (Json.arr #[toJson "operationApply", toJson id.raw,
        toJson (← params.mapM encode), toJson (← operands.mapM encode),
        toJson (← encode target), toJson (← encode selected)])
  | .presentationApply id params inverse source target argument =>
      pure (Json.arr #[toJson "presentationApply", toJson id.raw,
        toJson (← params.mapM encode), toJson inverse, toJson (← encode source),
        toJson (← encode target), toJson (← encode argument)])
  | .morphismTransport sourceCategory targetCategory route receiver =>
      pure (Json.arr #[toJson "morphismTransport", toJson sourceCategory.raw,
        toJson targetCategory.raw, toJson (route.map reprStr), toJson (← encode receiver)])
  | .functor id params receiver =>
      pure (Json.arr #[toJson "functor", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode receiver)])
  | .categoryParameter id params =>
      pure (Json.arr #[toJson "categoryParameter", toJson id.raw, toJson (← params.mapM encode)])
  | .functorParameter id params =>
      pure (Json.arr #[toJson "functorParameter", toJson id.raw, toJson (← params.mapM encode)])
  | .cartesian id params baseMorphism receiver field =>
      pure (Json.arr #[toJson "cartesian", toJson id.raw, toJson (← params.mapM encode),
        toJson (← encode baseMorphism), toJson (← encode receiver), toJson field])
  | .construction id params receiver =>
      pure (Json.arr #[toJson "construction", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode receiver)])
  | .constructionMap id params source target morphism =>
      pure (Json.arr #[toJson "constructionMap", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode source),
        toJson (← encode target), toJson (← encode morphism)])
  | .coreObject category object =>
      pure (Json.arr #[toJson "coreObject", ← encodeContext category, toJson (← encode object)])
  | .coreIso category source target forward backward =>
      pure (Json.arr #[toJson "coreIso", ← encodeContext category,
        toJson (← encode source), toJson (← encode target),
        toJson (← encode forward), toJson (← encode backward)])
  | .selectedLift id params source inclusion monic =>
      pure (Json.arr #[toJson "selectedLift", toJson id.raw,
        toJson (← params.mapM encode), toJson (← encode source),
        toJson (← encode inclusion), toJson (← encode monic)])
  | .liftProjection receiver field =>
      pure (Json.arr #[toJson "liftProjection", toJson (← encode receiver), toJson field])
  | .liftFactor receiver baseMap cone proof =>
      pure (Json.arr #[toJson "liftFactor", toJson (← encode receiver),
        toJson (← encode baseMap), toJson (← encode cone), toJson (← encode proof)])
  | .cellComponent id params constructors inverse receiver =>
      pure (Json.arr #[toJson "cellComponent", toJson id.raw,
        toJson (← params.mapM encode), toJson (constructors.map (·.raw)),
        toJson inverse, toJson (← encode receiver)])
  | .cellEndpoint id params constructors inverse right receiver =>
      pure (Json.arr #[toJson "cellEndpoint", toJson id.raw,
        toJson (← params.mapM encode), toJson (constructors.map (·.raw)),
        toJson inverse, toJson right, toJson (← encode receiver)])
  | .binder id params domain body admitted =>
      pure (Json.arr #[toJson "binder", toJson id.raw, toJson (← params.mapM encode),
        toJson (← encode domain), toJson (← encode body),
        toJson (← encode admitted)])
  | .arrow category morphism source target =>
      pure (Json.arr #[toJson "arrow", toJson category.raw,
        toJson (← encode morphism), toJson (← encode source),
        toJson (← encode target)])
  | .literal form literal =>
      pure (Json.arr #[toJson "literal", toJson form.raw, toJson (← encode literal)])
  | .method id route receiver recordedComparisons interpreted =>
      pure (Json.arr #[toJson "method", toJson id.raw, toJson (route.map reprStr),
        toJson (← encode receiver), ← encodeComparisons recordedComparisons,
        ← QuestionIdentity.encodeMethodApplication encode interpreted])
  | .methodWithLifts id route lifts receiver recordedComparisons interpreted =>
      pure (Json.arr #[toJson "methodWithLifts", toJson id.raw, toJson (route.map reprStr),
        toJson (lifts.map (·.raw)), toJson (← encode receiver),
        ← encodeComparisons recordedComparisons,
        ← QuestionIdentity.encodeMethodApplication encode interpreted])
  | .property id route receiver recordedComparisons =>
      pure (Json.arr #[toJson "property", toJson id.raw, toJson (route.map reprStr),
        toJson (← encode receiver), ← encodeComparisons recordedComparisons])
  | .limit id diagram lift =>
      pure (Json.arr #[toJson "limit", toJson id.raw, toJson (← encode diagram),
        toJson (lift.map (·.raw))])

/-- Serialize independently of trace enumeration and anonymous producer allocation.
Only exact administrative duplicates are coalesced; distinct legacy raw records
and proof implementations retain their existing multiplicity. Validate original
references before constructing the identity view. -/
def snapshot (nodes : Array (Expr × Node))
    (timings : Option (IO.Ref (Array (String × Nat))) := none)
    (roots : Array Expr := #[]) : TermElabM String := do
  Trace.checkProducedEntries nodes roots
  let nodes := Trace.identityEntries nodes
  let started ← IO.monoMsNow
  let record (stage : String) (before : Nat) : TermElabM Nat := do
    let now ← IO.monoMsNow
    if let some sink := timings then sink.modify (·.push (stage, now - before))
    return now
  let source ← TermTable.new
  let rooted ← nodes.mapM fun (term, node) => do
    return (← source.encode term, node)
  let afterSource ← record "source_encoding" started
  let keyed ← rooted.mapM fun (root, node) => do
    return (← source.rootIdentity root, (root, node))
  let ordered ← QuestionIdentity.orderByCompleteKey keyed fun (_, node) => do
    let target ← TermTable.new
    let remap ← TermRemap.new source target
    target.finish (← encodeSnapshotNode source remap.encodeTerm node)
  let afterKeys ← record "remapped_keys_and_sort" afterSource
  let table ← TermTable.new
  let remap ← TermRemap.new source table
  let operations ← ordered.mapM fun (sourceRoot, node) => do
    let root ← remap.encode sourceRoot
    let operation ← encodeSnapshotNode source remap.encodeTerm node
    return Json.arr #[toJson root, operation]
  let afterFields ← record "operation_fields" afterKeys
  let result ← table.finish (Json.arr operations)
  discard <| record "compression" afterFields
  return result

/-- Prepare the actual request before either execution or export. Closure and producer
validation are execution invariants; they do not depend on constructing an audit identity. -/
def prepare (scope : Scope) (stx : Syntax)
    (timings : Option (IO.Ref (Array (String × Nat))) := none) : TermElabM PreparedQuestion := do
  let started ← IO.monoMsNow
  let record (stage : String) (before : Nat) : TermElabM Nat := do
    let now ← IO.monoMsNow
    if let some sink := timings then sink.modify (·.push (stage, now - before))
    return now
  let trace ← (Trace.new : IO _)
  let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
  let claim ← (Language.claim scope stx).run { trace := some trace, closedTerms := some closedTerms }
  let afterRead ← record "semantic_reading" started
  let complete (field : Expr) : TermElabM Expr := do
    let field ← instantiateMVars field
    let type ← instantiateMVars (← inferType field)
    for term in #[field, type] do
      if term.hasMVar || term.hasLevelMVar || term.hasFVar || term.hasLooseBVars then
        throwError "question contains an incomplete or unclosed typed term"
    return field
  let claim ← claim.mapTermsM complete
  if let .judged _ proposition _ _ := claim then
    unless ← isProp proposition do
      throwError "the judged claim has no proposition to evaluate"
  let nodes ← (← trace.get).toArray.mapM fun (term, node) => do
    return (← complete term, ← node.mapTermsM complete)
  discard <| record "trace_instantiation" afterRead
  Trace.checkProducedEntries nodes claim.terms
  return { claim, trace := Std.HashMap.ofArray nodes }

/-- Export the existing complete request. The full identity construction and diagnostic
dependency label are requested explicitly, never required by ordinary execution. -/
def exportQuestion (question : PreparedQuestion)
    (timings : Option (IO.Ref (Array (String × Nat))) := none) : TermElabM TypedQuestion := do
  let started ← IO.monoMsNow
  let .ok manifest := Json.parse (← IO.FS.readFile "lake-manifest.json")
    | throwError "cannot identify the mathematical dependency revision"
  let .ok packages := (manifest.getObjVal? "packages").bind (·.getArr?)
    | throwError "cannot read the mathematical dependency revision"
  let some package := packages.find? fun package =>
      (package.getObjValAs? String "name").toOption == some "lean_categories"
    | throwError "no mathematical dependency revision"
  let .ok mathematicalRevision := package.getObjValAs? String "rev"
    | throwError "no pinned mathematical dependency revision"
  let (identity, shown) ← claimQuestion question.claim
  if let some sink := timings then
    let elapsed := (← IO.monoMsNow) - started
    sink.modify (·.push ("question_construction", elapsed))
  let tree ← snapshot question.trace.toArray timings question.claim.terms
  return { claim := question.claim
           trace := question.trace
           mathematicalRevision := mathematicalRevision
           identity := (s!"{identity}:operations:{tree}", shown) }

/-- Read once and explicitly export the complete typed question for comparison or audit. -/
def interpret (scope : Scope) (stx : Syntax)
    (timings : Option (IO.Ref (Array (String × Nat))) := none) : TermElabM TypedQuestion := do
  exportQuestion (← prepare scope stx timings) timings

/-- Execute exactly the prepared request without constructing its serialized identity. -/
def evaluatePrepared (h : Harness) (question : PreparedQuestion) : TermElabM ExecutionOutcome := do
  Trace.checkProducedEntries question.trace.toArray question.claim.terms
  let trace ← IO.mkRef question.trace
  unless h.computationOnly do
    let attempt ← discharge question.claim (some trace)
    if let some outcome := attempt then return outcome
  realizeClaim h trace question.claim

/-- Execute the same retained request carried by an explicit question export. -/
def evaluate (h : Harness) (question : TypedQuestion) : TermElabM ExecutionOutcome :=
  evaluatePrepared h question.prepared

/-- Runtime failures cannot assert mathematical invalidity or semantic ambiguity. Those
judgements belong to interpretation; an unexpected semantic exception during evaluation is
an interpreter defect. -/
def executionFailure (e : Exception) : TermElabM ExecutionOutcome := do
  let reason ← e.toMessageData.toString
  if Exception.hasConflictingStrata e then return .internal reason
  return match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization => .gap reason
    | some .unavailable => .unavailable reason
    | some .malformed => .malformed reason
    | _ => .internal reason

/-- Read a definition in its local statement context; its syntax is used again at each use. -/
def readBinding (scope : Scope) (stx : Syntax) (name : Name) (value : Syntax) :
    TermElabM (Outcome × Scope) := do
  let bind : TermElabM (Outcome × Scope) := do
    let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
    discard <| (Language.claim scope stx).run { closedTerms := some closedTerms }
    return (.holds, scope.insert name value)
  tryCatchRuntimeEx bind fun e => return (← Outcome.ofException e, scope.insert name value)

/-- Interpret before execution, retaining the same request through every later outcome.
Bindings are read without being counted as assertions. Incomplete interpretations fail visibly;
no operand list or truth value stands in for their question. -/
def runAsking (h : Harness) (scope : Scope) (stx : Syntax) :
    TermElabM (Outcome × Scope × Option (String × String)) := do
  if let some (x, t) ← letBinding? stx then
    let (outcome, scope) ← readBinding scope stx x t
    return (outcome, scope, none)
  let interpreted ← tryCatchRuntimeEx (Except.ok <$> interpret scope stx)
    fun e => return .error (← Outcome.ofException e)
  match interpreted with
  | .error outcome => return (outcome, scope, none)
  | .ok question =>
      let outcome ← tryCatchRuntimeEx (evaluate h question) executionFailure
      return (outcome.toOutcome, scope, some question.identity)

/-- Prepare and execute the same request. Audit export is an explicit separate operation. -/
def run (h : Harness) (scope : Scope) (stx : Syntax) : TermElabM (Outcome × Scope) := do
  if let some (x, t) ← letBinding? stx then
    return ← readBinding scope stx x t
  let prepared ← tryCatchRuntimeEx (Except.ok <$> prepare scope stx)
    fun e => return .error (← Outcome.ofException e)
  match prepared with
  | .error outcome => return (outcome, scope)
  | .ok question =>
      let outcome ← tryCatchRuntimeEx (evaluatePrepared h question) executionFailure
      return (outcome.toOutcome, scope)

end Realize

end CasCatalogue
