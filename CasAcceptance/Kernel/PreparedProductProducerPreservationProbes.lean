module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- Engineering-only comparison and ownership controls. Every formal comparison
below is an existing Mathlib construction; opaque packets are arbitrary supplied
data. No leaf runs, mathematical answer is asserted, or registration is added. -/
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let harness ← Harness.empty
  -- A live inert process supplies only session liveness for ownership checks.
  -- It receives no request, computes no answer and has no registration.
  let supplier ← IO.Process.spawn {
    cmd := "/bin/cat", stdin := .piped,
    stdout := .piped, stderr := .inherit }
  try
    let connection : Backend.Conn := {
      child := supplier,
      ready := {
        backend := "product-comparison-fixture", backendVersion := "inert ownership fixture",
        capabilities := #[] }, nextId := ← IO.mkRef 0 }
    harness.connections.modify (·.insert "product-comparison-fixture"
      (.ok { identity := 64, connection }))
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the existing complete set category is absent"
    let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
      | throwError "the existing finite-object declaration is absent"
    let X ← Semantic.object finite #[← `(2)] (some trace)
    let Y ← Semantic.object finite #[← `(3)] (some trace)
    let Z ← Semantic.object finite #[← `(4)] (some trace)
    let semantic ← mkAppM ``Prod #[X, Y]
    let actual ← mkAppM ``Prod #[Y, X]
    let context ← CategoryContext.ofNamed sets semantic
    let semanticWire ← realizeEndpoint harness trace "the selected semantic comparison source" semantic
    let actualWire ← realizeEndpoint harness trace "the selected actual comparison target" actual
    let identityChild ← realizeEndpoint harness trace "the independently selected second factor" Z
    let comparison ← mkAppM ``Equiv.toIso #[← mkAppM ``Equiv.prodComm #[X, Y]]
    let owned (opaqueToken : String) : DataOwnership.Data :=
      DataOwnership.Data.capture (Backend.ComputationalValue.encode (.opaque opaqueToken))
        ("product-comparison-fixture", 64)
    let forward ← scopedNode "typedMap" #[semanticWire.fragment, actualWire.fragment,
      owned "unchanged forward comparison"]
    let backward ← scopedNode "typedMap" #[actualWire.fragment, semanticWire.fragment,
      owned "unchanged backward comparison"]
    let first : Wire := {
      form := .diagrams sets
      payload := (← scopedPayload semantic actualWire.fragment)
      categoryContext := some context
      objectIso := some (← mkAppM ``CategoryTheory.Iso.symm #[comparison])
      endpointPresentation := some {
        comparison, forward := forward.json, backward := backward.json,
        forwardOwnership := forward.ownership, backwardOwnership := backward.ownership } }
    let product (left right : Wire) : TermElabM Wire := do
      let value ← mkAppM ``Prod #[left.value, right.value]
      let data ← scopedNode "objectProduct" #[left.fragment, right.fragment]
      return {
        form := .diagrams sets, payload := (← combinedPayload value data #[left, right]),
        categoryContext := some context, productComponents := #[left, right] }
    let original ← product first identityChild
    let (normalized, _) ← normalizeOperationProducts harness context #[original] #[]
    let #[normalized] := normalized | throwError "normalization changed the product occurrence inventory"
    unless normalized.value == original.value && normalized.fragment == original.fragment &&
        sameProductComponents normalized.productComponents original.productComponents do
      throwError "a current product action replaced its selected context, data or original value"
    let some objectComparison := normalized.objectIso
      | throwError "the independent product object comparison is absent"
    let (_, objectTarget) ← operationComparisonEnds context objectComparison
    unless ← withTransparency .all <| isDefEq objectTarget original.value do
      throwError "the product object comparison has the endpoint-presentation orientation"
    let some presentation := normalized.endpointPresentation
      | throwError "the mixed current product action is absent"
    let (source, target) ← operationComparisonEnds context presentation.comparison
    unless ← withTransparency .all <| isDefEq source original.value <&&>
        isDefEq target (← mkAppM ``Prod #[actual, Z]) do
      throwError "the product endpoint comparison changed a complete factor or orientation"
    let .ok forwardMap := Backend.TypedMap.decode presentation.forward
      | throwError "the forward action omitted its full declared endpoints"
    let .ok backwardMap := Backend.TypedMap.decode presentation.backward
      | throwError "the backward action omitted its full declared endpoints"
    let semanticData ← scopedNode "objectProduct" #[semanticWire.fragment, identityChild.fragment]
    let semanticDomain ← product semanticWire identityChild
    unless semanticDomain.fragment == semanticData do
      throwError "the original generalized maps changed their complete semantic domain"
    unless forwardMap.source == semanticData.json && forwardMap.target == original.json &&
        backwardMap.source == original.json && backwardMap.target == semanticData.json do
      throwError "a product direction reused the other direction's endpoint diagram"
    let .ok ("mediator", #[forwardFirst, _]) := ComputationalData.envelope forwardMap.callable
      | throwError "the forward product action is not the complete ordered mediator"
    let .ok ("mediator", #[backwardFirst, _]) := ComputationalData.envelope backwardMap.callable
      | throwError "the backward product action is not the complete ordered mediator"
    let .ok ("compose", #[forwardLeg, retainedForward]) := ComputationalData.envelope forwardFirst
      | throwError "the forward product component omitted its projection or original map"
    let .ok ("compose", #[backwardLeg, retainedBackward]) := ComputationalData.envelope backwardFirst
      | throwError "the backward product component omitted its projection or original map"
    unless retainedForward == forward.json && retainedBackward == backward.json do
      throwError "the product action rewrote an original supplied comparison map"
    let .ok ("limitLeg", #[_, forwardDiagram, _]) := ComputationalData.envelope forwardLeg
      | throwError "the forward action omitted its registered defining projection"
    let .ok ("limitLeg", #[_, backwardDiagram, _]) := ComputationalData.envelope backwardLeg
      | throwError "the backward action omitted its registered defining projection"
    unless forwardDiagram != backwardDiagram do
      throwError "different complete comparison endpoints acquired one projection diagram"
    let forwardPart ← checkedFragment (presentation.forwardFragment.project
      #[.field "args", .index 2, .field "args", .index 0, .field "args", .index 1])
    let backwardPart ← checkedFragment (presentation.backwardFragment.project
      #[.field "args", .index 2, .field "args", .index 0, .field "args", .index 1])
    unless forwardPart == forward && backwardPart == backward do
      throwError "the product action dropped a positioned comparison supplier"
    -- Both source and target may themselves be products. Transport the whole
    -- callable on this unchanged generalized domain, exactly once.
    let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[original.value]
    let point : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload identity (owned "unchanged generalized callable")),
      categoryContext := some context }
    let point ← retainCallableEndpoints point semanticDomain semanticDomain context
    let framed ← presentMorphism point normalized normalized (some context)
    let again ← presentMorphism framed normalized normalized (some context)
    unless framed.value == point.value && framed.fragment == again.fragment do
      throwError "product framing replaced the original generalized callable or applied a comparison twice"
    let (actualPoint, actualDomain, actualTarget) ← operationFramedPoint context point normalized normalized
    CategoryContext.checkMorphism context actualPoint actualDomain actualTarget
    unless ← withTransparency .all <| isDefEq actualDomain target <&&> isDefEq actualTarget target do
      throwError "actual framed validation lost the original generalized-domain comparison"
    -- The actual operation-argument builder must consume a newly aggregated
    -- nonterminal product-domain comparison before the invocation is assembled.
    let semanticLegs ← operationProductLegs context first.value identityChild.value
      semanticWire.fragment identityChild.fragment
    let firstPoint : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload semanticLegs.first (owned "original first generalized point")),
      categoryContext := some context }
    let secondPoint : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload semanticLegs.second (owned "original second generalized point")),
      categoryContext := some context }
    let firstPoint ← retainCallableEndpoints firstPoint semanticDomain semanticWire context
    let secondPoint ← retainCallableEndpoints secondPoint semanticDomain identityChild context
    let (firstNormalized, _) ← normalizeOperationProducts harness context #[first] #[]
    let #[firstNormalized] := firstNormalized | unreachable!
    -- The new mediator owns a semantic endpoint envelope around each exact
    -- original whole map, before its new comparison frame is assembled. This
    -- fresh typed constructor retains the completed raw child; it neither
    -- clears that child's flags nor claims an unobserved comparison completed.
    let semanticInput (point source target : Wire) : TermElabM Wire := do
      let some endpoints ← retainedCallableEndpoints? point context
        | throwError "the new mediator lost an original whole-map interface"
      unless sameCompleteWireContext endpoints.1 source &&
          sameCompleteWireContext endpoints.2 target do
        throwError "the new mediator replaced an original semantic endpoint"
      let template : ActionDataTemplate := .ctor "typedMap"
        #[.wire .retained source, .wire .retained target, .retained (.wire .map point)]
      let (data, inputs) ← renderCapturedActionData template
      let result : Wire := {
        form := point.form, payload := (← combinedRecipePayload point.value data inputs),
        categoryContext := some context }
      let result ← retainIntrinsicAssembly result .map context template
        #[{ context, source, target, callable := point }] #[] (.retained, .retained)
      retainCallableEndpoints result source target context
    let firstSemantic ← semanticInput firstPoint semanticDomain semanticWire
    let secondSemantic ← semanticInput secondPoint semanticDomain identityChild
    let firstInput ← presentMorphism firstSemantic normalized firstNormalized (some context)
    let secondInput ← presentMorphism secondSemantic normalized identityChild (some context)
    unless firstPoint.completedData && secondPoint.completedData &&
        !firstSemantic.completedData && !secondSemantic.completedData &&
        !firstInput.completedData && !secondInput.completedData &&
        firstInput.morphismFraming.any (fun origin =>
          sameCompleteWireContext origin.input firstSemantic) &&
        secondInput.morphismFraming.any (fun origin =>
          sameCompleteWireContext origin.input secondSemantic) do
      throwError "the pending product frames replaced their original completed maps"
    for (semantic, original, source, target) in
        #[(firstSemantic, firstPoint, semanticDomain, semanticWire),
          (secondSemantic, secondPoint, semanticDomain, identityChild)] do
      let some selected ← retainedIntrinsicAssembly? semantic .map
        | throwError "the semantic envelope lost its original typed producer"
      let .ctor "typedMap" #[.wire .retained selectedSource, .wire .retained selectedTarget,
          .retained (.wire .map child)] := selected.template
        | throwError "the semantic envelope changed its exact original child position"
      let some endpoints ← retainedCallableEndpoints? semantic context
        | throwError "the semantic envelope lost its original complete endpoints"
      unless sameCompleteWireContext child original && sameRetainedServiceHandles child original &&
          sameCompleteWireContext selectedSource source && sameCompleteWireContext selectedTarget target &&
          sameCompleteWireContext endpoints.1 source && sameCompleteWireContext endpoints.2 target &&
          selected.endpointRoles == (.retained, .retained) &&
          (← checkedFragment (semantic.fragment.project #[.field "args", .index 2])) == original.fragment do
        throwError "the semantic envelope changed an original map, supplier, or endpoint occurrence"
    let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[firstPoint.value, secondPoint.value]
    let originalMediator ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
      #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[semanticLegs.presentation], fan]
    let check : String → Wire → Wire → Wire → Wire → Wire →
        PreparedOperationArgument → TermElabM Unit :=
      fun label originalPoint domain target firstOriginal secondOriginal prepared => do
      unless prepared.data != originalPoint.fragment do
        throwError "the {label} regression did not reconstruct the product packet"
      let some preparedWire := prepared.dependencies[0]?
        | throwError "the {label} product omitted its retained whole occurrence"
      let some retainedOriginal := prepared.dependencies[1]?
        | throwError "the {label} product omitted its original whole point"
      unless sameCompleteWireContext retainedOriginal originalPoint &&
          sameRetainedServiceHandles retainedOriginal originalPoint &&
          (← retainedPointOrigin? retainedOriginal).isSome &&
          (← retainedCapturedInvocation? retainedOriginal).isSome do
        throwError "the {label} product replaced its original whole-point provenance"
      let (firstTemplate, secondTemplate, firstPath, secondPath) :
          ActionDataTemplate × ActionDataTemplate × DataOwnership.Path × DataOwnership.Path ←
        match prepared.template with
        | .array #[a, b] =>
          pure (a, b, #[.index 0], #[.index 1])
        | .ctor "typedMap" #[.wire .retained _, .wire .retained _,
            .ctor "mediator" #[a, b]] =>
          pure (a, b, #[.field "args", .index 2, .field "args", .index 0],
            #[.field "args", .index 2, .field "args", .index 1])
        | _ => throwError "the {label} product changed its selected packet constructor"
      let some firstPrepared := capturedTemplateWire? firstTemplate
        | throwError "the {label} product lost its first complete prepared child"
      let some secondPrepared := capturedTemplateWire? secondTemplate
        | throwError "the {label} product lost its second complete prepared child"
      for (path, child, originalChild) in
          #[(firstPath, firstPrepared, firstOriginal), (secondPath, secondPrepared, secondOriginal)] do
        unless (← checkedFragment (prepared.data.project path)) == child.fragment do
          throwError "the {label} product changed a positioned child packet or supplier"
        let closure ← operationPresentationOperandClosure (← harness.serviceOperands.get) child
        unless closure.any (fun retained => sameCompleteWireContext retained originalChild &&
            sameRetainedServiceHandles retained originalChild) do
          throwError "the {label} prepared child lost its exact original whole-map producer"
      let argumentPath : DataOwnership.Path := #[.field "argument"]
      let firstInputPath := argumentPath ++ firstPath
      let secondInputPath := argumentPath ++ secondPath
      let scope : ServiceScope := {
        harness, trace, known := prepared.dependencies, references := #[],
        inputReferences := #[(argumentPath, preparedWire),
          (firstInputPath, firstPrepared), (secondInputPath, secondPrepared)],
        positionedInputs := true,
        operands := ← IO.mkRef #[], backend := "product-comparison-fixture" }
      let copiedOperand ← serviceArrow scope (Backend.inputRef (publicServiceInputPath argumentPath))
        (some (← inferType originalPoint.value))
      let copied ← serviceWire scope copiedOperand
      unless sameCompleteWireContext copied preparedWire &&
          sameRetainedServiceHandles copied preparedWire && copied.fragment == prepared.data do
        throwError "the {label} service input changed the prepared product occurrence"
      for (path, expected) in #[(firstInputPath, firstPrepared), (secondInputPath, secondPrepared)] do
        let operand ← serviceArrow scope (Backend.inputRef (publicServiceInputPath path))
          (some (← inferType expected.value))
        let actual ← serviceWire scope operand
        unless sameCompleteWireContext actual expected && sameRetainedServiceHandles actual expected do
          throwError "the {label} service changed a selected prepared child occurrence"
      -- Demand through the same service-retained occurrence, after its local
      -- result references and exact request paths have been established.
      let observed ← realizeArrowObservation harness trace copied
      let some assembly ← currentIntrinsicAssembly? copied
        | throwError "the {label} reconstructed product lost its current typed producer"
      unless sameActionTemplate assembly.template prepared.template &&
          assembly.endpointRoles == (.retained, .retained) do
        throwError "the {label} product producer differs from its validated prepared template"
      for candidate in #[copied, observed] do
        let some _ ← currentIntrinsicAssembly? candidate
          | throwError "the {label} service observation lost its current producer"
        let some endpoints ← retainedCallableEndpoints? candidate context
          | throwError "the {label} product lost its complete normalized endpoint interface"
        unless sameCompleteWireContext endpoints.1 domain &&
            sameCompleteWireContext endpoints.2 target do
          throwError "the {label} product changed a normalized endpoint occurrence"
        checkDataOwners harness candidate.fragment
      unless observed.fragment == prepared.data do
        throwError "the {label} service observation repeated a child comparison or changed a supplier"
      let refused ← try
        discard <| retainPreparedOperationArgument harness context originalPoint
          prepared.data prepared.template prepared.actual prepared.dependencies
        pure false
      catch error => pure (Exception.stratum? error == some .unavailable)
      unless refused do
        throwError "the {label} changed packet was accepted without its complete producer"
      logInfo m!"PASS: {label} prepared product producer and later exact service consumption"

    -- Generalized mediator: both children acquire the normalized domain frame.
    let oldFirstInput ← presentMorphism firstSemantic original first (some context)
    let oldSecondInput ← presentMorphism secondSemantic original identityChild (some context)
    unless !sameCompleteWireContext oldFirstInput firstInput &&
        !sameCompleteWireContext oldSecondInput secondInput do
      throwError "the mediator regression did not exercise changed child frames"
    let oldTemplate : ActionDataTemplate := .ctor "mediator"
      #[.wire .map oldFirstInput, .wire .map oldSecondInput]
    let (oldData, oldInputs) ← renderCapturedActionData oldTemplate
    let oldMediator : Wire := {
      form := .canonicalMorphism sets,
      payload := (← combinedRecipePayload originalMediator oldData oldInputs),
      categoryContext := some context }
    let oldMediator ← retainPointOrigin oldMediator context original original
      (.product semanticLegs.presentation original.value oldFirstInput oldSecondInput
        #[.field "args", .index 0] #[.field "args", .index 1])
    let oldMediator ← retainIntrinsicAssembly oldMediator .map context oldTemplate
      #[{ context, source := original, target := first, callable := oldFirstInput },
        { context, source := original, target := identityChild, callable := oldSecondInput }]
    let some originalAssembly ← currentIntrinsicAssembly? oldMediator
      | throwError "the original mediator lost its selected assembly"
    let oldMediator ← retainCapturedInvocation harness oldMediator (.intrinsic originalAssembly)
    Trace.record (some trace) originalMediator
      (.productMediator sets.id semanticLegs.presentation original.value firstPoint.value secondPoint.value)
    harness.results.modify fun results => results.insert original.value original
      |>.insert first.value first |>.insert identityChild.value identityChild
      |>.insert firstPoint.value firstPoint |>.insert secondPoint.value secondPoint
    let prepared ← prepareOperationPointArgument harness trace context oldMediator original original
      normalized normalized oldMediator.fragment #[]
    check "typedMap mediator" oldMediator normalized normalized firstPoint secondPoint prepared

    -- The released array encoding uses the published closed-point domain.
    -- Existing constant maps supply only formal interfaces; their opaque data
    -- and comparison packets remain the explicitly owned fixture occurrences.
    let closedDomain ← closedElementDomain state
    let closedSource ← realizeEndpoint harness trace "the original closed-point domain" closedDomain
    let firstFunction ← elabTerm (← `(fun (_ : Fin 1) =>
      (((0 : Fin 2), (0 : Fin 3)), (0 : Fin 4)))) none
    let secondFunction ← elabTerm (← `(fun (_ : Fin 1) => (0 : Fin 4))) none
    let firstFormal ← mkAppM ``TypeCat.ofHom #[firstFunction]
    let secondFormal ← mkAppM ``TypeCat.ofHom #[secondFunction]
    CategoryContext.checkMorphism context firstFormal closedDomain original.value
    CategoryContext.checkMorphism context secondFormal closedDomain identityChild.value
    let firstClosed : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload firstFormal (owned "original first closed whole map")),
      categoryContext := some context }
    let secondClosed : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload secondFormal (owned "original second closed whole map")),
      categoryContext := some context }
    let firstClosed ← retainCallableEndpoints firstClosed closedSource semanticDomain context
    let secondClosed ← retainCallableEndpoints secondClosed closedSource identityChild context
    let firstClosedSemantic ← semanticInput firstClosed closedSource semanticDomain
    let secondClosedSemantic ← semanticInput secondClosed closedSource identityChild
    let firstClosedInput ← presentMorphism firstClosedSemantic closedSource original (some context)
    let secondClosedInput ← presentMorphism secondClosedSemantic closedSource identityChild (some context)
    let changedClosedInput ← presentMorphism firstClosedSemantic closedSource normalized (some context)
    unless !sameCompleteWireContext firstClosedInput changedClosedInput do
      throwError "the array regression did not exercise a changed child frame"
    let arrayTarget ← product original identityChild
    let (arrayNormalized, _) ← normalizeOperationProducts harness context #[arrayTarget] #[]
    let #[arrayNormalized] := arrayNormalized
      | throwError "the closed product changed its target occurrence inventory"
    let arrayLegs ← operationProductLegs context original.value identityChild.value
      semanticDomain.fragment identityChild.fragment
    let arrayFan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[firstFormal, secondFormal]
    let arrayFormal ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
      #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[arrayLegs.presentation], arrayFan]
    let arrayTemplate : ActionDataTemplate := .array
      #[.wire .map firstClosedInput, .wire .map secondClosedInput]
    let (arrayData, arrayInputs) ← renderCapturedActionData arrayTemplate
    let arrayPoint : Wire := {
      form := .canonicalMorphism sets,
      payload := (← combinedRecipePayload arrayFormal arrayData arrayInputs),
      categoryContext := some context }
    let arrayPoint ← retainPointOrigin arrayPoint context closedSource arrayTarget
      (.product arrayLegs.presentation closedDomain firstClosedInput secondClosedInput
        #[.index 0] #[.index 1])
    let arrayPoint ← retainIntrinsicAssembly arrayPoint .map context arrayTemplate
      #[{ context, source := closedSource, target := original, callable := firstClosedInput },
        { context, source := closedSource, target := identityChild, callable := secondClosedInput }]
    let some originalArrayAssembly ← currentIntrinsicAssembly? arrayPoint
      | throwError "the original array lost its selected assembly"
    let arrayPoint ← retainCapturedInvocation harness arrayPoint (.intrinsic originalArrayAssembly)
    let arrayPrepared ← prepareOperationPointArgument harness trace context arrayPoint closedSource arrayTarget
      closedSource arrayNormalized arrayPoint.fragment #[]
    check "closed-point array" arrayPoint closedSource arrayNormalized firstClosed secondClosed arrayPrepared
  finally
    Backend.abort supplier
