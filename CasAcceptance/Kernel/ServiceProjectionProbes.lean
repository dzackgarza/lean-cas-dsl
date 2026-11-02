module
import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def rejects (fragment : String) (work : TermElabM α) : TermElabM Unit := do
  let failure ← try
    discard <| work
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless failure.any (fun message => (message.splitOn fragment).length > 1) do
    throwError "projection control expected {fragment}, received {reprStr failure}"

private def fixture : TermElabM (Trace × Harness × Wire × Wire × CategoryContext) := do
  let trace ← Trace.new
  let state ← registryState
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the published finite object is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the published set category is absent"
  let source ← Semantic.object finite #[← `(2)] (some trace)
  let target ← Semantic.object finite #[← `(3)] (some trace)
  let empty ← Harness.empty
  let source ← realize empty trace "the selected source" source
  let target ← realize empty trace "the selected target" target
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[{
      name := "projection-owner", command := "python3"
      args := #["probe_deferred_service.py", "child", "opaque"] }]
    registrations := #[{
      operation := "fun.sets.identity", input := "fun.sets.identity#input"
      backend := "projection-owner" }] }
  let harness ← Harness.ofManifest root manifest
  let calls ← IO.mkRef #[]
  let harness := enableService { harness with dispatches := some calls } trace
  let some identity := state.functors.find? (·.id.raw == "fun.sets.identity")
    | throwError "the accepted identity action is absent"
  let action ← Semantic.edgeFunctor state (.functor identity.id)
  let owned ← executeObjectEdge harness trace (.functor identity.id) action source
  let context ← CategoryContext.ofNamed sets source.value
  return (trace, harness, owned, target, context)

private def record (label : String) (harness : Harness) (checks : Array String)
    (wires : Array Wire) (templates : Array Json := #[]) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_DEFERRED_SERVICE_REPORT" then
    let records ← wires.mapM fun wire => do
      return Json.mkObj [("formal", toJson (reprStr wire.value)),
        ("type", toJson (reprStr (← inferType wire.value))), ("data", wire.json),
        ("owner", toJson wire.owner?), ("context", toJson (reprStr wire.categoryContext)),
        ("retainedOperands", toJson wire.serviceHandles)]
    let replies ← (← harness.replies.get).mapM fun reply => do
      return Json.mkObj [("operation", toJson reply.operation), ("input", reply.input.json),
        ("backend", toJson reply.backend), ("session", toJson reply.session),
        ("original", reply.original), ("completed", toJson reply.completed)]
    IO.FS.withFile path .append fun stream => stream.putStrLn
      (Json.mkObj [("case", toJson label), ("checks", toJson checks),
        ("wires", Json.arr records), ("templates", Json.arr templates),
        ("replies", Json.arr replies)]).compress

run_elab do
  let (trace, harness, source, target, context) ← fixture
  try
    let formal ← instantiateMVars (← elabTermAndSynthesize
      (← `(TypeCat.ofHom (fun (_ : $(← exprToSyntax source.value)) =>
        (show $(← exprToSyntax target.value) from (0 : Fin 3))))) none)
    -- This asymmetric Hom has no identity. The projection-only control retains
    -- arbitrary owned callable data and never evaluates its opaque token.
    let data := Backend.TypedMap.encode {
      source := source.json, target := target.json,
      callable := node "opaqueData" #[toJson "projection-probe-callable"] }
    let mapWire : Wire := {
      form := ServiceRequest.formFor (← registryState) context source.form true
      payload := computedPayload formal data source.owner?
      categoryContext := some context, callableObserved := true }
    let some arrow := (← registryState).constructors.find?
        (·.semantics == `CasCatalogue.Constructors.arrow)
      | throwError "the accepted Arrow constructor is absent"
    let arrowContext ← CategoryContext.construct context arrow.id
    let arrowFormal ← mkAppM ``CategoryTheory.Arrow.mk #[formal]
    let arrowData := node "arrow" #[source.json, target.json, data]
    let arrowWire : Wire := {
      form := .contextual arrowContext.expression source.form
      payload := computedPayload arrowFormal arrowData source.owner?
      categoryContext := some arrowContext, objectObserved := true }
    let scope : ServiceScope := {
      harness, trace, references := #[mapWire, arrowWire], known := #[]
      operands := (← IO.mkRef #[]), backend := "projection-owner" }
    let left ← serviceObject scope (node "morphismEndpoint" #[Backend.resultRef 0, toJson "source"])
    let right ← serviceObject scope (node "morphismEndpoint" #[Backend.resultRef 0, toJson "target"])
    unless (← isDefEq left.value source.value) && left.data == source.json &&
        (← isDefEq right.value target.value) && right.data == target.json do
      throwError "the nested endpoint descriptor changed its actual selected side"
    unless (← serviceWire scope left).owner? == source.owner? &&
        (← serviceWire scope right).owner?.isNone do
      throwError "the nested endpoint descriptor changed field ownership"
    let projected ← serviceArrow scope (node "arrowHom" #[Backend.resultRef 1])
    unless (← isDefEq projected.value formal) && projected.data == data &&
        (← serviceWire scope projected).owner? == source.owner? &&
        projected.handle != left.handle do
      throwError "the retained Arrow projection changed its callable, occurrence or owner"
    rejects "accepted refinement interface" <|
      serviceObject scope (node "subobjectApex" #[Backend.resultRef 1])
    rejects "no declared side" <|
      serviceObject scope (node "morphismEndpoint" #[Backend.resultRef 0, toJson "middle"])
    let swapped := { arrowWire with payload := (computedPayload arrowFormal
      (node "arrow" #[target.json, source.json, data]) source.owner?) }
    let swappedScope := { scope with references := #[swapped] }
    rejects "complete endpoint descriptors differ from its selected data roles" <|
      serviceArrow swappedScope (node "arrowHom" #[Backend.resultRef 0])
    record "nested-endpoint-and-arrow-projections" harness
      #["full asymmetric Hom", "exact actual endpoint fields", "opaque child owner",
        "portable other endpoint", "fresh field handle", "refinement mismatch rejected",
        "selector rejected", "swapped actual endpoints rejected"]
      #[mapWire, arrowWire, ← serviceWire scope left, ← serviceWire scope right,
        ← serviceWire scope projected]
      #[node "morphismEndpoint" #[Backend.resultRef 0, toJson "source"],
        node "arrowHom" #[Backend.resultRef 1]]
  finally harness.stop

run_elab do
  let (trace, harness, original, _, _) ← fixture
  try
    let state ← registryState
    let some identity := state.functors.find? (·.id.raw == "fun.sets.identity") | unreachable!
    let action ← Semantic.edgeFunctor state (.functor identity.id)
    discard <| Semantic.objOf action original.value
    let action ← instantiateMVars action
    let otherAction ← mkAppM ``CategoryTheory.Functor.comp #[action, action]
    checkExecutableEdgeAction state (.functor identity.id) action
    checkExecutableEdgeAction state (.functor identity.id) otherAction
    harness.actions.modify (·.push {
      operation := identity.id.raw, action, input := original,
      parameters := #[], parameterInputs := #[], result := original })
    harness.actions.modify (·.push {
      operation := identity.id.raw, action := otherAction, input := original,
      parameters := #[], parameterInputs := #[], result := original })
    let scope : ServiceScope := {
      harness, trace, references := #[original], known := #[original, original]
      operands := (← IO.mkRef #[]), backend := "projection-owner" }
    rejects "distinct retained complete action occurrences" <|
      serviceObject scope original.json
    let reference ← serviceObject scope (Backend.resultRef 0)
    unless reference.data == original.json && reference.value == original.value &&
        (← serviceWire scope reference).owner? == original.owner? do
      throwError "explicit reference did not disambiguate its actual action occurrence"
    let wrapped ← mkAppM ``id #[original.value]
    let second := { original with payload := computedPayload wrapped original.json original.owner? }
    harness.actions.set #[]
    let scope := { scope with known := #[original, second] }
    unless (← isDefEq original.value wrapped) && original.value != wrapped do
      throwError "the copied-packet control lost its distinct definitionally equal expressions"
    rejects "distinct typed occurrences" <| serviceObject scope original.json
    record "copied-packet-selected-occurrence-ambiguity" harness
      #["same bytes and owner", "distinct complete actions", "explicit reference disambiguates",
        "definitionally equal formal expressions remain distinct"]
      #[original, second, ← serviceWire scope reference]
  finally harness.stop

run_elab do
  let (trace, harness, owned, target, context) ← fixture
  try
    let state ← registryState
    let some row := state.limits.find? (·.id.raw == "lim.sets.product")
      | throwError "the published product is absent"
    let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
    let source := { owned with payload := (computedPayload owned.value
      (node "obj.sets.fin" #[toJson (2 : Nat)]) none) }
    let scope : ServiceScope := {
      harness, trace, references := #[source, target], known := #[]
      operands := (← IO.mkRef #[]), backend := "projection-owner" }
    let some constructor ← Semantic.diagramConstructor row | throwError "the diagram schema is absent"
    let diagram := node (Codec.label constructor) #[Backend.resultRef 0, Backend.resultRef 1]
    let prepared ← UniversalServiceRequest.limit (← serviceDecoder scope) row (.diagrams sets) diagram
    let actualApex := node "obj.sets.fin" #[toJson (6 : Nat)]
    let firstMap := Backend.TypedMap.encode {
      source := actualApex, target := source.json, callable := owned.json }
    let secondMap := Backend.TypedMap.encode {
      source := actualApex, target := target.json, callable := owned.json }
    let answer := node "cone" #[actualApex, firstMap, secondMap]
    let completion ← prepared.complete answer
    let result ← match completion with
      | .ok (some result) => pure result
      | .ok none => throwError "the product completion lost its authoritative Result"
      | .error message => throwError "the typed arbitrary product packet did not validate: {message}"
    let some owner := owned.owner? | throwError "the original child owner is absent"
    let complete : Wire := {
      form := .limitApex row, payload := .construction result (.owned owner.1 owner.2)
      categoryContext := some context, constructionInputs := prepared.constructionInputs }
    let scope := { scope with references := #[source, target, complete] }
    let apex ← serviceObject scope (node "constructionField"
      #[toJson row.id.raw, diagram, Backend.resultRef 2, toJson (0 : Nat)])
    let field ← serviceArrow scope (node "constructionField"
      #[toJson row.id.raw, diagram, Backend.resultRef 2, toJson (1 : Nat)])
    unless apex.data == actualApex &&
        (← serviceWire scope apex).owner?.isNone && field.data == firstMap &&
        (← serviceWire scope field).owner? == owned.owner? do
      throwError "a universal field changed its selected packet or inherited unrelated ownership"
    let index ← elabTermAndSynthesize
      (← `(CategoryTheory.Discrete.mk CategoryTheory.Limits.WalkingPair.left)) none
    let .ok indexData ← Codec.encode index | throwError "the published diagram index has no encoding"
    let leg ← serviceArrow scope (node "constructionLeg"
      #[toJson row.id.raw, diagram, Backend.resultRef 2, indexData])
    unless (← isDefEq leg.value (← result.leg index)) && leg.data == firstMap &&
        (← serviceWire scope leg).owner? == owned.owner? do
      throwError "the universal leg did not use its exact retained data port"
    rejects "exact registered owner" <|
      serviceObject scope (node "constructionApex"
        #[toJson "colim.sets.coproduct", diagram, Backend.resultRef 2])
    rejects "complete selected construction diagram" <|
      serviceObject scope (node "constructionApex"
        #[toJson row.id.raw,
          node (Codec.label constructor) #[Backend.resultRef 1, Backend.resultRef 0],
          Backend.resultRef 2])
    record "retained-universal-field-and-leg-projections" harness
      #["exact registered result", "typed original diagram references", "independent universal presentation",
        "portable apex", "opaque leg owner", "exact constructor data port",
        "diagram index differs from port index", "wrong row rejected", "changed diagram rejected"]
      #[complete, ← serviceWire scope apex, ← serviceWire scope field, ← serviceWire scope leg]
      #[node "constructionField" #[toJson row.id.raw, diagram, Backend.resultRef 2, toJson (1 : Nat)],
        node "constructionLeg" #[toJson row.id.raw, diagram, Backend.resultRef 2, indexData]]
  finally harness.stop

end
