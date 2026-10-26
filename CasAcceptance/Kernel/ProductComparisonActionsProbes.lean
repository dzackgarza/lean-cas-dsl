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
    let fan ← mkAppM ``CategoryTheory.Limits.BinaryFan.mk #[firstPoint.value, secondPoint.value]
    let originalMediator ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
      #[← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[semanticLegs.presentation], fan]
    let originalData ← scopedNode "mediator" #[firstPoint.fragment, secondPoint.fragment]
    let mediator : Wire := {
      form := .canonicalMorphism sets,
      payload := (← combinedPayload originalMediator originalData #[firstPoint, secondPoint]),
      categoryContext := some context }
    Trace.record (some trace) originalMediator
      (.productMediator sets.id semanticLegs.presentation original.value firstPoint.value secondPoint.value)
    let saved ← harness.results.get
    harness.results.modify fun results => results.insert original.value original
      |>.insert first.value first |>.insert identityChild.value identityChild
      |>.insert firstPoint.value firstPoint |>.insert secondPoint.value secondPoint
    let prepared ← prepareOperationPointArgument harness trace context mediator original original
      normalized normalized mediator.fragment #[]
    let .ok actualArgument := Backend.TypedMap.decode prepared.data.json
      | throwError "the generalized argument omitted its normalized complete endpoints"
    unless actualArgument.source == normalized.json && actualArgument.target == normalized.json do
      throwError "the prepared argument still advertises its former domain or target"
    let .ok ("mediator", #[preparedFirst, preparedSecond]) :=
        ComputationalData.envelope actualArgument.callable
      | throwError "the prepared generalized argument lost its ordered point occurrences"
    let .ok firstMap := Backend.TypedMap.decode preparedFirst
      | throwError "the first generalized component omitted its normalized endpoints"
    let .ok secondMap := Backend.TypedMap.decode preparedSecond
      | throwError "the second generalized component omitted its normalized endpoints"
    unless firstMap.source == normalized.json && firstMap.target == first.json &&
        secondMap.source == normalized.json && secondMap.target == identityChild.json do
      throwError "a generalized component lost the common actual domain or selected target"
    let .ok ("compose", #[firstSource, firstForward]) := ComputationalData.envelope firstMap.callable
      | throwError "the first generalized point omitted its target transport"
    let .ok ("compose", #[firstInverse, firstOriginal]) := ComputationalData.envelope firstSource
      | throwError "the first generalized point omitted its domain transport"
    let .ok ("compose", #[secondInverse, secondOriginal]) := ComputationalData.envelope secondMap.callable
      | throwError "the second generalized point omitted its domain transport"
    let some firstPresentation := first.endpointPresentation | unreachable!
    unless firstInverse == presentation.backward && secondInverse == presentation.backward &&
        firstForward == firstPresentation.forward do
      throwError "a generalized point changed or repeated an independently selected comparison"
    let .ok firstOriginal := Backend.TypedMap.decode firstOriginal
      | throwError "the first original packet lost its semantic endpoint frame"
    let .ok secondOriginal := Backend.TypedMap.decode secondOriginal
      | throwError "the second original packet lost its semantic endpoint frame"
    unless firstOriginal.source == semanticData.json && firstOriginal.target == semanticWire.json &&
        secondOriginal.source == semanticData.json && secondOriginal.target == identityChild.json &&
        firstOriginal.callable == firstPoint.json && secondOriginal.callable == secondPoint.json do
      throwError "generalized framing rewrote an original supplied callable or its declared semantic endpoint"
    let retainedFirst ← checkedFragment (prepared.data.project
      #[.field "args", .index 2, .field "args", .index 0, .field "args", .index 2,
        .field "args", .index 0, .field "args", .index 1, .field "args", .index 2])
    unless retainedFirst == firstPoint.fragment do
      throwError "generalized framing changed the original point supplier"
    let (firstNormalized, _) ← normalizeOperationProducts harness context #[first] #[]
    let #[firstNormalized] := firstNormalized | unreachable!
    let already ← presentMorphism firstPoint normalized firstNormalized (some context)
    harness.results.modify fun results => results.insert original.value normalized
      |>.insert first.value firstNormalized
    let reused ← prepareOperationPointArgument harness trace context already normalized firstNormalized
      normalized firstNormalized already.fragment #[]
    let .ok reusedFrame := Backend.TypedMap.decode reused.data.json
      | throwError "the unchanged existing point frame lost its full endpoint wrapper"
    unless reusedFrame.callable == already.json do
      throwError "the unchanged existing point frame consumed a comparison twice"
    -- A changed direct frame has an exact producer record. Replaying that
    -- record recovers the original supplied packet without guessing from JSON.
    harness.results.modify fun results => results.insert original.value original
      |>.insert first.value first
    let oldFrame ← presentMorphism firstPoint original first (some context)
    let reframed ← prepareOperationPointArgument harness trace context oldFrame original first
      normalized firstNormalized oldFrame.fragment #[]
    let .ok reframedMap := Backend.TypedMap.decode reframed.data.json
      | throwError "the changed direct frame omitted its normalized actual endpoints"
    unless reframedMap.source == normalized.json && reframedMap.target == first.json do
      throwError "the changed direct frame retained a stale actual endpoint"
    let addedHandles ← retainServiceOperands harness #[original, first]
    let augmented := { oldFrame with serviceHandles := oldFrame.serviceHandles ++ addedHandles }
    let replayed ← prepareOperationPointArgument harness trace context augmented original first
      normalized firstNormalized augmented.fragment #[]
    unless replayed.data == reframed.data do
      throwError "later exact dependency augmentation changed an original framing replay"
    let dangling := { augmented with
      serviceHandles := augmented.serviceHandles.push
        ((← harness.serviceOperands.get).size + 1) }
    let refused ← try
      discard <| prepareOperationPointArgument harness trace context dangling original first
        normalized firstNormalized dangling.fragment #[]
      pure false
    catch _ => pure true
    unless refused do throwError "framing replay accepted a dangling exact dependency occurrence"
    let some origin := oldFrame.morphismFraming
      | throwError "ordinary framing omitted its exact producer provenance"
    let snapshot : WireSnapshot := {
      form := oldFrame.form, payload := oldFrame.payload
      presentationIsos := oldFrame.presentationIsos, objectIso := oldFrame.objectIso
      categoryContext := oldFrame.categoryContext
      morphismFramed := oldFrame.morphismFramed, morphismFraming := oldFrame.morphismFraming }
    unless sameCompleteWireContext (retainedSnapshotWire snapshot) oldFrame do
      throwError "snapshot retention changed the complete original framing provenance"
    let wrongOrigin := { oldFrame with
      morphismFraming := some { origin with
        source := { origin.source with presentationIsos := #[comparison] } } }
    let refused ← try
      discard <| prepareOperationPointArgument harness trace context wrongOrigin original first
        normalized firstNormalized wrongOrigin.fragment #[]
      pure false
    catch error => pure (Exception.stratum? error == some .ambiguousRealization)
    unless refused do throwError "a changed source history was accepted as original framing provenance"
    let scope : ServiceScope := {
      harness, trace, known := prepared.dependencies, references := #[],
      operands := ← IO.mkRef #[], backend := "product-comparison-fixture" }
    let copied ← serviceArrow scope prepared.data.json (some (← inferType mediator.value))
    let copied ← serviceWire scope copied
    unless copied.value == mediator.value && copied.fragment == prepared.data do
      throwError "a nested service request reconstructed instead of retaining the complete prepared argument"
    -- An unchanged typed-map packet must not expose a second framed-status alias.
    let plainIdentity ← mkAppM ``CategoryTheory.CategoryStruct.id #[identityChild.value]
    let plainData ← scopedNode "typedMap" #[identityChild.fragment, identityChild.fragment,
      owned "unchanged already typed input"]
    let plain : Wire := {
      form := .canonicalMorphism sets,
      payload := (← scopedPayload plainIdentity plainData), categoryContext := some context }
    let unchanged ← prepareOperationPointArgument harness trace context plain identityChild identityChild
      identityChild identityChild plain.fragment #[]
    let scope : ServiceScope := {
      harness, trace, known := unchanged.dependencies, references := #[],
      operands := ← IO.mkRef #[], backend := "product-comparison-fixture" }
    let some copied ← serviceRetained scope plain.json
      | throwError "the unchanged typed input was not retained"
    unless sameCompleteWireContext copied plain do
      throwError "unchanged framing created an ambiguous provenance-only copied packet"
    harness.results.set saved
    -- Equal descriptor/source context cannot choose between different actual views.
    for views in #[#[(first, first.value), (first, actual)], #[(first, actual), (first, first.value)]] do
      let refused ← try
        discard <| operationPresentationObjects #[] views
        pure false
      catch error => pure (Exception.stratum? error == some .ambiguousRealization)
      unless refused do throwError "actual endpoint view selection depends on occurrence order"
    -- Normalize aliases in both orders, including a metadata-poor old snapshot
    -- retained through an exact handle. Only normalized views may reach lookup.
    let oldHandles ← retainServiceOperands harness #[original]
    let retainedAlias := { normalized with serviceHandles := normalized.serviceHandles ++ oldHandles }
    let mkScope (known : Array Wire) : TermElabM ServiceScope := do
      return { harness, trace, known, references := #[], operands := ← IO.mkRef #[], backend := "" }
    for originals in #[#[original, retainedAlias], #[retainedAlias, original]] do
      let (_, handles) ← normalizeOperationProducts harness context originals #[]
      let table ← harness.serviceOperands.get
      let known ← handles.mapM fun handle => do
        let some wire := table[handle]? | throwError "the normalized exact handle is missing"
        pure wire
      let scope ← mkScope known
      let some copied ← serviceRetained scope original.json
        | throwError "the current product presentation was not available as a copied input"
      unless sameServiceSelection copied normalized do
        throwError "copied input order changed the product's complete current comparison"
      let operand ← serviceRegister scope copied
      let restored ← serviceWire scope operand
      unless sameCompleteWireContext restored normalized do
        throwError "the product comparison changed through the public typed operand round trip"
    let nested ← product original identityChild
    let (nestedResult, _) ← normalizeOperationProducts harness context #[nested] #[]
    let #[nestedResult] := nestedResult | throwError "the nested product occurrence was lost"
    unless nestedResult.endpointPresentation.isSome && nestedResult.objectIso.isSome &&
        sameProductComponents nestedResult.productComponents nested.productComponents do
      throwError "nested current comparison normalization lost a factor context or action"
    let changedFirst := { first with presentationIsos := #[comparison] }
    let changed ← product changedFirst identityChild
    for originals in #[#[original, changed], #[changed, original]] do
      let (_, handles) ← normalizeOperationProducts harness context originals #[]
      let table ← harness.serviceOperands.get
      let known := handles.filterMap fun handle => table[handle]?
      let rejected ← try
        discard <| serviceRetained (← mkScope known) original.json
        pure false
      catch error => pure (Exception.stratum? error == some .ambiguousRealization)
      unless rejected do
        throwError "a current product action hid a distinct original child history"
    let conflicting := { original with endpointPresentation := some {
      comparison := (← mkAppM ``CategoryTheory.Iso.refl #[original.value]),
      forward := forward.json, backward := backward.json,
      forwardOwnership := forward.ownership, backwardOwnership := backward.ownership } }
    let rejected ← try
      discard <| normalizeOperationProducts harness context #[conflicting] #[]
      pure false
    catch error => pure (Exception.stratum? error == some .ambiguousRealization)
    unless rejected do throwError "a conflicting pre-existing whole-product comparison was replaced"
    let wrong := { first with objectIso := some comparison }
    let rejected ← try
      discard <| normalizeOperationProducts harness context #[← product wrong identityChild] #[]
      pure false
    catch _ => pure true
    unless rejected do throwError "an object comparison with reversed full endpoints was accepted"
    logInfo "PASS: nonidentity mixed/nested product actions, full directions, generalized framing, exact suppliers and copied-context boundaries"
  finally
    Backend.abort supplier
