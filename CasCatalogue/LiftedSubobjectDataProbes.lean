module

public meta import CasCatalogue.Realize
public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Catalogue.Semantics.Limits.Lifts
public import Mathlib.Algebra.Algebra.Bilinear

/-! Engineering checks of opaque packet framing and independently fixed callable plans.
Computational claims are never decoded into categorical laws or accepted proofs. -/

open Lean Meta Elab Term CategoryTheory CasCatalogue

run_elab do
  let state ← registryState
  let some sourceCategory := state.categories.find?
      (·.id.raw == "cat.subobjects_bilin_module")
    | throwError "missing accepted formed-module subobject category"
  let X ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ (ℤ × ℤ) ℤ))) none
  let selectedSource ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilinModuleCategory ℤ ℤ)) none
  let selectedCarrier ← mkAppM ``CategoryTheory.Bundled.α #[selectedSource]
  let selectedX ← mkExpectedTypeHint X selectedCarrier
  let L ← elabTermAndSynthesize (← `(
    CasCatalogue.Modules.Bilinear.Valued.Kernels.forgetMonoLift ℤ ℤ)) none
  let liftType ← whnfR (← inferType L)
  let #[_, selectedCategory, _, _, _] := liftType.getAppArgs
    | throwError "the closed accepted lift fixture has no full source category dictionary"
  let sourceArrow ← mkAppOptM ``CategoryTheory.Arrow
    #[some selectedCarrier, some selectedCategory]
  let sourceStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some selectedCarrier, some selectedCategory]
  let identity ← mkAppOptM ``CategoryTheory.CategoryStruct.id
    #[some selectedCarrier, some sourceStruct, some selectedX]
  let receiver ← mkExpectedTypeHint
    (← mkAppOptM ``CategoryTheory.Arrow.mk
      #[some selectedCarrier, some selectedCategory, some selectedX,
        some selectedX, some identity]) sourceArrow
  let base ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ (ℤ × ℤ))); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let some row := state.lifts.find? (·.id.raw == "lift.bilin_module.restrict")
    | throwError "missing accepted formed-module lift"
  let expectedLifted ← Semantic.liftSubobject state row receiver base
  let expectedType ← inferType expectedLifted
  let .ok prepared ← LiftedSubobjectData.plan expectedType sourceCategory receiver #[row.id] base
    | throwError "the existing selected formal lift has no complete public port plan"
  let #[component] := prepared.components
    | throwError "the exact selected route lost its required component"
  unless component.ports.size == 4 do throwError "the public computation lost a field"
  for port in component.ports do
    discard <| StructuredResult.checkReconstruction port
    unless ← isTypeCorrect port do throwError "a full selected computation port is ill-typed"
  let some form := state.form? row.inputAddress
    | throwError "the published lift input form was not admitted"
  for field in LiftField.all do
    let some operation := state.operation? (row.fieldAddress field)
      | throwError "a public computation field has no concrete operation address"
    unless (state.rejects operation form).isNone do
      throwError "a public lift field was rejected on its own complete input"
    unless (state.rejects operation (.subobject sourceCategory)).isSome do
      throwError "a public lift field accepted an unrelated subobject input"
  let wrongSource ← LiftedSubobjectData.plan expectedType sourceCategory X #[row.id] base
  if wrongSource.isOk then throwError "a lift accepted a source without its complete Arrow type"
  let wrongRoute ← LiftedSubobjectData.plan expectedType sourceCategory receiver
    #[⟨"unregistered.lift"⟩] base
  if wrongRoute.isOk then throwError "a lift accepted a route outside the fixed catalogue"
  let wrongBase ← elabTermAndSynthesize (← `((
    ⟨Arrow.mk (CategoryStruct.id (ModuleCat.of ℤ ℤ)), (by
      change Mono (CategoryStruct.id (ModuleCat.of ℤ ℤ)); infer_instance)⟩ :
    ObjectProperty.FullSubcategory (fun a : Arrow (ModuleCat ℤ) => Mono a.hom)))) none
  let wrongParameters ← LiftedSubobjectData.plan expectedType sourceCategory receiver
    #[row.id] wrongBase
  if wrongParameters.isOk then
    throwError "a lift accepted a different fixed full base ambient in the same category"
  let trace ← CasCatalogue.Trace.new
  let .constructMap _ inner := row.edge
    | throwError "the registered lift lost its selected inner action"
  let action ← Realize.edgeDescriptor trace inner component.action
  let data (token : String) := Json.mkObj [("ctor", "opaqueData"),
    ("args", Json.arr #[toJson token])]
  let ambient := data "source object"
  let sourceData := Json.mkObj [("ctor", "arrow"),
    ("args", Json.arr #[ambient, ambient, data "source map"])]
  let image value := Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[action, value])]
  let baseData := Json.mkObj [("ctor", "subobject"),
    ("args", Json.arr #[data "base apex", data "base ambient", data "base inclusion"])]
  let objectData := data "actual returned object"
  let typedMap source target callable := Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[source, target, callable])]
  let outputs := #[objectData, typedMap objectData ambient (data "actual inclusion"),
    typedMap (image objectData) (data "base apex") (data "actual forward callable"),
    typedMap (data "base apex") (image objectData) (data "actual backward callable")]
  -- Inventory enrichment retains each original descriptor. Both comparisons
  -- must then use the same actual mapped and base endpoints, even for opaque maps.
  let finite descriptor (points : Array Json) := Json.mkObj [("ctor", "finiteData"),
    ("args", Json.arr #[descriptor, Json.arr points])]
  let point (x : Int) := Json.arr #[toJson x, toJson (0 : Int)]
  let mappedA := finite (image objectData) #[point 0]
  let mappedB := finite (image objectData) #[point 1]
  let baseA := finite (data "base apex") #[point 0]
  let baseB := finite (data "base apex") #[point 1]
  let enriched := (outputs.set! 2
    (typedMap mappedA baseA (data "actual forward callable"))).set! 3
    (typedMap baseA mappedA (data "actual backward callable"))
  if let .error message ← LiftedSubobjectData.validatePrefix component action sourceData baseData enriched then
    throwError "exact comparison endpoints rejected their actual inventories: {message}"
  for changed in #[
      enriched.set! 3 (typedMap baseA mappedB (data "different image inventory")),
      enriched.set! 3 (typedMap baseB mappedA (data "different base inventory"))] do
    let .error _ ← LiftedSubobjectData.validatePrefix component action sourceData baseData changed
      | throwError "the inverse comparison changed a previously returned endpoint inventory"
  let selectedParameters ← (← DirectConstruction.dataArguments component.selection.parameters).mapM
    (Realize.parameterData trace)
  let stepWith (parameters? : Option Json) fields := Json.mkObj (
    [("ctor", toJson "liftStep"), ("args", Json.arr #[
      toJson row.id.raw, action, sourceData, baseData, Json.arr fields])] ++
    parameters?.toList.map (fun parameters => ("parameters", parameters)))
  let step fields := stepWith (some (Json.arr selectedParameters)) fields
  let envelopeWith step := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
    baseData, sourceData, toJson #[row.id.raw], Json.arr #[step]])]
  let envelope fields := envelopeWith (step fields)
  let validateSource (_ : CategoryExpr) (fixed : Expr) (data : Json) := do
    ComputationalData.validatePort fixed (← inferType fixed) data
  let validateBase (_ : NamedCategoryEntry) (fixed : Expr) (data : Json) objects := do
    ComputationalData.validatePort fixed (← inferType fixed) data objects
  let decodeWith requested json := LiftedSubobjectData.decode expectedType sourceCategory receiver
    #[row.id] base json validateSource validateBase requested
  let decode := decodeWith (some #[selectedParameters])
  let checked ← decode (envelope outputs)
  let packet ← match checked with
    | some (.ok packet) => pure packet
    | some (.error message) => throwError "complete opaque computational claims rejected: {message}"
    | none => throwError "complete lifted data was not recognized"
  unless packet.outputs == #[outputs] && packet.data == envelope outputs do
    throwError "a complete lift discarded or replaced an actual returned field"
  unless ← withTransparency .all <| isDefEq packet.formalResult expectedLifted do
    throwError "computational claims changed the independently fixed formal result"
  -- The published metadata is mandatory even in the formal-reference framing path.
  if let .error message ← ComputationalData.validatePublicData packet.data then
    throwError "a complete public lift packet was rejected: {message}"
  for metadata in #[none, some Json.null, some (Json.arr #[]),
      some (Json.arr (selectedParameters.push (data "extra parameter")))] do
    let invalid := envelopeWith (stepWith metadata outputs)
    let some result ← decodeWith none invalid
      | throwError "malformed parameter metadata was not recognized"
    if result.isOk then throwError "the framing decoder omitted required evidence parameters"
    if (← ComputationalData.validatePublicData invalid).isOk then
      throwError "the public grammar omitted required evidence parameters"
  let illTyped := selectedParameters.set! 0 (toJson true)
  let some checked ← decodeWith none
      (envelopeWith (stepWith (some (Json.arr illTyped)) outputs))
    | throwError "changed selected parameter framing was not recognized"
  if checked.isOk then throwError "selected parameter data lost its independently fixed interface"
  -- Two different actual packets make reordering observable even when the formal
  -- parameters coincide. They remain data; no canonical parameter is substituted.
  unless selectedParameters.size == 2 do
    throwError "the selected evidence fixture changed its complete data arity"
  let wrapped := data "actual second parameter"
  let actualParameters := #[data "actual first parameter",
    Json.mkObj [("ctor", "valueData"), ("args", Json.arr #[wrapped])]]
  let actualPacket := envelopeWith (stepWith (some (Json.arr actualParameters)) outputs)
  let some (.ok actual) ← decodeWith (some #[actualParameters]) actualPacket
    | throwError "retained actual parameter packets were replaced by their formal recipe"
  unless actual.data == actualPacket && actual.outputs == packet.outputs do
    throwError "parameter validation replaced an actual packet or construction output"
  for changed in #[actualParameters.reverse,
      actualParameters.set! 0 (data "changed opaque parameter"),
      actualParameters.set! 1 wrapped] do
    let some result ← decodeWith (some #[actualParameters])
        (envelopeWith (stepWith (some (Json.arr changed)) outputs))
      | throwError "changed actual parameters were not recognized"
    if result.isOk then throwError "a completed step changed its actual ordered request parameters"
  let some omittedRequest ← decodeWith (some #[]) actualPacket
    | throwError "an incomplete retained request vector was not recognized"
  if omittedRequest.isOk then throwError "a component without its retained request data was accepted"
  let .ok next := LiftedSubobjectData.nextBase sourceData outputs
    | throwError "the actual completed fields could not advance the reverse route"
  let .ok fields := LiftedSubobjectData.fields "subobject" 3 next
    | throwError "the next actual base lost its complete subobject context"
  unless fields[0]! == objectData && fields[2]! == data "actual inclusion" && next != baseData do
    throwError "the next step repeated the initial base instead of the actual preceding outputs"
  let actualObject := finite objectData #[point 0]
  let actualAmbient := finite ambient #[point 0]
  let actualInclusion := outputs.set! 1
    (typedMap actualObject actualAmbient (data "actual inclusion"))
  let .ok actualNext := LiftedSubobjectData.nextBase sourceData actualInclusion
    | throwError "actual defining-map endpoints could not advance the route"
  let .ok actualFields := LiftedSubobjectData.fields "subobject" 3 actualNext
    | throwError "the next actual base lost its subobject fields"
  unless actualFields[0]! == actualObject && actualFields[1]! == actualAmbient do
    throwError "the next base discarded actual defining-map endpoint inventories"
  let incomplete := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
    baseData, sourceData, toJson #[row.id.raw]])]
  let wrongEndpoints := outputs.set! 2
    (typedMap (data "unrelated object") (data "base apex") (data "wrong-domain callable"))
  for invalid in #[incomplete, envelope #[], envelope (outputs.extract 0 3),
      envelope wrongEndpoints] do
    let some result ← decode invalid | throwError "malformed completed framing was not recognized"
    if result.isOk then throwError "an incomplete or wrong-domain component was accepted"
  -- Neither returned object nor callable claims are forced to agree with a canonical answer.
  let wrongObject := data "well-framed mathematically wrong object"
  let wrongOutputs := #[wrongObject, typedMap wrongObject ambient (data "wrong inclusion"),
    typedMap (image wrongObject) (data "base apex") (data "wrong forward"),
    typedMap (data "base apex") (image wrongObject) (data "wrong backward")]
  let some (.ok wrong) ← decode (envelope wrongOutputs)
    | throwError "well-framed wrong data was rejected or certified at the computational boundary"
  unless wrong.outputs == #[wrongOutputs] do
    throwError "wrong computational data was replaced with a canonical result"
  unless ← withTransparency .all <| isDefEq wrong.formalResult packet.formalResult do
    throwError "actual computational claims changed the fixed mathematical question"
  -- The preferred complete Arrow spelling is also a subobject representation
  -- at this independently fixed result type, including inside prescribed lifts.
  let .ok baseFields := LiftedSubobjectData.subobjectFields baseData
    | throwError "the original complete subobject lost its defining Arrow"
  let arrowBase := Json.mkObj [("ctor", "arrow"), ("args", Json.arr baseFields)]
  let arrowStep := Json.mkObj [("ctor", "liftStep"),
    ("parameters", Json.arr selectedParameters), ("args", Json.arr #[
    toJson row.id.raw, action, sourceData, arrowBase, Json.arr outputs])]
  let arrowPacket := Json.mkObj [("ctor", "liftedSubobject"), ("args", Json.arr #[
    arrowBase, sourceData, toJson #[row.id.raw], Json.arr #[arrowStep]])]
  let some (.ok alternate) ← decode arrowPacket
    | throwError "the complete Arrow spelling could not feed a prescribed lift"
  unless alternate.baseData == arrowBase && alternate.outputs == packet.outputs do
    throwError "a lift relabelled or replaced the actual complete Arrow data"
  for invalid in #[
      Json.mkObj [("ctor", "arrow"), ("args", Json.arr (baseFields.extract 0 2))],
      Json.mkObj [("ctor", "cone"), ("args", Json.arr baseFields)]] do
    if (LiftedSubobjectData.subobjectFields invalid).isOk then
      throwError "an incomplete or different construction supplied a subobject Arrow"
  -- Valid live inputs still require an admitted implementation of the public fields.
  let operations := LiftField.all.map row.fieldAddress
  let harness ← Realize.Harness.ofManifest ("CasAcceptance" / "Strata") {
    backends := #[{
      name := "lift-probe"
      command := "python3"
      args := #["probe_lift_protocol.py"] ++ operations }]
    registrations := #[] }
  let dispatches ← IO.mkRef (#[] : Array Json)
  let harness := { harness with dispatches := some dispatches }
  unless harness.admitted.isEmpty && harness.rejected.isEmpty do
    throwError "the absent-implementation fixture unexpectedly installed a registration"
  try
    let .ok session ← harness.connection "lift-probe"
      | throwError "the existing protocol-only fixture did not start"
    let owner := some ("lift-probe", session.identity)
    let sourceWire : Realize.Wire := {
      form := .arrow (← Semantic.namedCategoryFor state prepared.sourceCategory)
      payload := Realize.computedPayload receiver sourceData owner }
    let parameters ← prepared.components.mapM fun component => do
      Realize.realizedParameters harness trace
        (← DirectConstruction.dataArguments component.selection.parameters)
    let (actualAction, actionDependencies) ← Realize.realizedEdgeDescriptor harness trace
      inner component.action
    let encoder : Realize.ActionEncoder := fun edge selectedAction => do
      unless edge == inner && selectedAction == component.action do
        throwError "the missing-implementation control changed its fixed selected action"
      return (actualAction, actionDependencies)
    for baseData in #[baseData, arrowBase] do
      let baseWire : Realize.Wire := {
        form := .subobject prepared.baseCategory
        payload := Realize.computedPayload base baseData owner }
      let missing ← try
          discard <| Realize.executePrescribedLift harness trace prepared
            sourceWire baseWire parameters (some encoder)
          pure false
        catch error =>
          unless CasCatalogue.Exception.stratum? error == some .noImplementation do throw error
          -- Attribute the failure to the first public field, not parameter recovery.
          let message ← error.toMessageData.toString
          unless (message.splitOn
              s!"no admitted registration computes {operations[0]!}").length > 1 do throw error
          pure true
      unless missing do
        throwError "the executor claimed a completed lift without registered execution"
      let connections ← harness.connections.get
      let some (.ok retainedSession) := connections["lift-probe"]?
        | throwError "the missing-implementation control discarded its real supplying session"
      unless connections.size == 1 && retainedSession.identity == session.identity &&
          (← dispatches.get).isEmpty && (← harness.replies.get).isEmpty do
        throwError "the missing-implementation control dispatched or changed its process inventory"
  finally
    harness.stop

run_elab do
  let formal ← elabTermAndSynthesize (← `(fun x : Fin 2 => x)) none
  let object (size : Nat) := Json.mkObj [("ctor", "obj.sets.fin"),
    ("args", Json.arr #[toJson size])]
  let graph (inventory pairs : Array Json) := Json.mkObj [("ctor", "finiteGraph"),
    ("args", Json.arr #[Json.arr inventory, Json.arr pairs])]
  let framed source target callable := Json.mkObj [("ctor", "typedMap"),
    ("args", Json.arr #[source, target, callable])]
  let pair (x y : Nat) := Json.arr #[toJson x, toJson y]
  let source := object 2
  let incompleteGraph := graph #[toJson (0 : Nat)] #[pair 0 0]
  let incomplete ← LiftedSubobjectData.validateMap formal source source
    (framed source source incompleteGraph)
  if incomplete.isOk then
    throwError "a lift map accepted a graph inventory smaller than its actual declared domain"
  let wrong := graph #[toJson (0 : Nat), toJson (1 : Nat)]
    #[pair 0 1, pair 1 1]
  let .ok () ← LiftedSubobjectData.validateMap formal source source (framed source source wrong)
    | throwError "a complete well-framed wrong map was rejected or forced to the canonical identity"
