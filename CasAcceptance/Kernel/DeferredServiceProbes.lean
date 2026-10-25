module
import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def wireRecord (wire : Wire) : TermElabM Json := do
  return Json.mkObj [("formal", toJson (reprStr wire.value)),
    ("type", toJson (reprStr (← inferType wire.value))), ("data", wire.json),
    ("form", toJson wire.formId), ("owner", toJson wire.owner?)]

private def evidence (label : String) (harness : Harness) (checks : Array String) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_DEFERRED_SERVICE_REPORT" then
    let services ← (← harness.services.get).mapM fun record => do
      let nodes ← record.nodes.mapM fun selected => do
        return Json.mkObj [("operation", toJson selected.operation), ("input", toJson selected.input),
          ("request", ← wireRecord selected.request),
          ("dependencies", Json.arr (← selected.dependencies.mapM wireRecord)),
          ("result", ← wireRecord selected.result)]
      return Json.mkObj [("operation", toJson record.operation),
        ("input", ← wireRecord record.input), ("backend", toJson record.backend),
        ("original", record.original), ("nodes", Json.arr nodes),
        ("result", record.result), ("owner", toJson record.owner), ("completed", toJson record.completed)]
    let replies ← (← harness.replies.get).mapM fun record => do
      return Json.mkObj [("operation", toJson record.operation), ("input", ← wireRecord record.input),
        ("backend", toJson record.backend), ("session", toJson record.session),
        ("original", record.original), ("completed", toJson record.completed)]
    let dispatches ← match harness.dispatches with | some calls => calls.get | none => pure #[]
    let actions ← (← harness.actions.get).mapM fun action => do
      return Json.mkObj [("operation", toJson action.operation),
        ("action", toJson (reprStr action.action)), ("input", ← wireRecord action.input),
        ("parameters", Json.arr action.parameters),
        ("parameterInputs", Json.arr (← action.parameterInputs.mapM wireRecord)),
        ("imageEndpoints", Json.arr (← action.imageEndpoints.mapM wireRecord)),
        ("result", ← wireRecord action.result)]
    let report := Json.mkObj [("case", toJson label), ("checks", toJson checks), ("actions", Json.arr actions),
      ("services", Json.arr services), ("replies", Json.arr replies), ("dispatches", Json.arr dispatches)]
    IO.FS.withFile path .append fun output => output.putStrLn report.compress

private def fixture (mode : String) : TermElabM (Trace × Harness × FunctorEntry × Expr × Wire) := do
  let trace ← Trace.new
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the existing outer action is absent"
  let some objects := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing source object is absent"
  let source ← Semantic.object objects #[← `(2)] (some trace)
  let empty ← Harness.empty
  let original ← realize empty trace "the original service source" source
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  discard <| Semantic.objOf action source
  let action ← instantiateMVars action
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[
      { name := "outer-service", command := "python3", args := #["probe_deferred_service.py", "outer", mode] },
      { name := "child-service", command := "python3", args := #["probe_deferred_service.py", "child", mode] },
      { name := "target-service", command := "python3", args := #["probe_deferred_service.py", "target", mode] }]
    registrations := #[
      { operation := "fun.sets.list", input := "fun.sets.list#input", backend := "outer-service" },
      { operation := "fun.sets.identity", input := "fun.sets.identity#input", backend := "child-service" },
      { operation := "fun.sets.identity#map", input := "fun.sets.identity#input", backend := "child-service" },
      { operation := "meth.cardinality", input := "cat.sets", backend := "target-service" },
      { operation := "mor.sets.fin_rev", input := "mor.sets.fin_rev", backend := "target-service" }] }
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == 5 do
    throwError "the published service fixtures did not admit"
  let calls ← IO.mkRef #[]
  let harness := enableService { harness with dispatches := some calls } trace
  return (trace, harness, entry, action, original)

run_elab do
  let (trace, harness, entry, action, original) ← fixture "occurrences"
  try
    let result ← executeObjectEdge harness trace (.functor entry.id) action original
    let expected ← Semantic.objOf action original.value
    unless ← isDefEq result.value expected do
      throwError "a child replaced the original caller's formal result"
    unless result.json == node "obj.sets.fin" #[toJson (7 : Nat)] && result.owner?.isNone do
      throwError "the final reference did not retain the first actual portable packet"
    let services ← harness.services.get
    let #[service] := services | throwError "the single service scope was not retained"
    let #[firstNode, secondNode, _, _] := service.nodes
      | throwError "the service omitted its completed nodes"
    let first := firstNode.result
    let second := secondNode.result
    unless (← isDefEq first.value second.value) && first.json != second.json do
      throwError "the occurrence control did not keep equal formal values with distinct packets"
    let some calls := harness.dispatches | throwError "the original dispatch ledger is absent"
    let calls ← calls.get
    let consumed := calls.filter fun call =>
      (call.getObjValAs? String "operation").toOption == some "meth.cardinality"
    unless consumed.size == 2 &&
        (consumed[0]!.getObjVal? "request").toOption == some first.json &&
        (consumed[1]!.getObjVal? "request").toOption == some second.json do
      throwError "ordinary method execution selected an equal cached occurrence"
    unless (← harness.replies.get).size == 5 do throwError "the service discarded an original raw reply"
    let replaced ← withoutModifyingState <| isDefEq result.value first.value
    if replaced then throwError "the original and child formal constructions were identified"
    evidence "same-formal-distinct-actual-occurrences" harness
      #["original-formal-result", "exact-result-reference", "method-occurrence-retention",
        "raw-replies-retained", "portable-target-data", "arbitrary-data-not-mathematical-evidence"]
  finally harness.stop

run_elab do
  let (trace, harness, entry, action, original) ← fixture "opaque"
  try
    let result ← executeObjectEdge harness trace (.functor entry.id) action original
    let some owner := result.owner? | throwError "the child opaque result lost its owner"
    unless owner.1 == "child-service" do throwError "the enclosing answer relabeled the child's owner"
    let #[service] ← harness.services.get | throwError "the opaque service program was not retained"
    let #[child] := service.nodes | throwError "the opaque service lost its child"
    unless child.result.owner? == result.owner? do
      throwError "the final reference changed the child session"
    let state ← registryState
    let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
      | throwError "the asymmetric endpoint fixture is absent"
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the selected set category is absent"
    let target ← Semantic.object finite #[← `(3)] (some trace)
    let empty ← Harness.empty
    let targetWire ← realize empty trace "the different target" target
    let formalMap ← instantiateMVars (← elabTermAndSynthesize
      (← `(TypeCat.ofHom (fun (_ : $(← exprToSyntax original.value)) =>
        (0 : $(← exprToSyntax target))))) none)
    let mapData := Backend.TypedMap.encode {
      source := child.result.json, target := targetWire.json
      callable := node "identity" #[child.result.json, targetWire.json] }
    let mapWire : Wire := {
      form := .canonicalMorphism sets
      payload := computedPayload formalMap mapData (some owner)
      categoryContext := some (← CategoryContext.ofNamed sets original.value)
      callableObserved := true }
    let scope : ServiceScope := {
      harness, trace, references := #[mapWire], known := #[]
      operands := (← IO.mkRef #[]), backend := owner.1 }
    let retained ← serviceRegister scope mapWire
    let sourceEndpoint ← serviceEndpoint scope retained true
    let targetEndpoint ← serviceEndpoint scope retained false
    unless (← isDefEq sourceEndpoint.value original.value) &&
        (← isDefEq targetEndpoint.value target) &&
        sourceEndpoint.data == child.result.json && targetEndpoint.data == targetWire.json &&
        sourceEndpoint.handle != targetEndpoint.handle && sourceEndpoint.handle != retained.handle do
      throwError "the runtime endpoint convention changed a retained side or actual packet"
    unless (← serviceWire scope sourceEndpoint).owner? == some owner &&
        (← serviceWire scope targetEndpoint).owner?.isNone do
      throwError "endpoint projection lost an opaque owner or inherited an unrelated owner"
    let (packet, first, second) ← UniversalServiceRequest.mapPacket (← serviceDecoder scope) retained
    unless packet == mapData && first.data == sourceEndpoint.data && second.data == targetEndpoint.data do
      throwError "the universal preparer reversed the runtime endpoint convention"
    let some context := mapWire.categoryContext | throwError "the selected map context is absent"
    let reversed ← CategoryContext.hom context target original.value
    let rejected ← try
      discard <| serviceArgument scope reversed (Backend.resultRef 0)
      pure false
    catch error => pure (Exception.stratum? error == some .malformed)
    unless rejected do throwError "a referenced callable changed its full selected Hom endpoints"
    let bare := { mapWire with payload := computedPayload formalMap child.result.json (some owner) }
    let bareHandle ← serviceRegister scope bare
    let projection ← serviceEndpoint scope bareHandle true
    unless projection.data == Backend.MorphismEndpoint.encode { callable := bare.json, source := true } do
      throwError "an unframed endpoint selected an unrelated equal cached object"
    let connections ← harness.connections.get
    let some (.ok selected) := connections[owner.1]? | throwError "the child process is absent"
    harness.connections.modify (·.insert owner.1 (.ok { selected with identity := selected.identity + 1 }))
    let expired ← try
      checkServiceOwner harness result
      pure false
    catch error => pure (Exception.stratum? error == some .unavailable)
    harness.connections.set connections
    unless expired do throwError "the child result survived an expired process identity"
    evidence "child-owner-retained" harness #["actual-child-owner", "no-owner-relabel", "expired-session-unavailable", "actual-asymmetric-endpoints",
        "shared-universal-endpoint-convention", "full-Hom-rejection", "exact-bare-endpoint-projection"]
  finally harness.stop


run_elab do
  for (mode, expected, fragment) in #[
      ("forward-reference", Stratum.malformed, "malformed or out-of-scope references"),
      ("bad-type", Stratum.malformed, "reference has a different complete declared type"),
      ("extra-reference", Stratum.malformed, "outside a complete public data envelope"),
      ("backend-selector", Stratum.malformed, "malformed or out-of-scope references"),
      ("mixed-owners", Stratum.unavailable, "different owning sessions"),
      ("cycle", Stratum.unavailable, "recursively requests the same complete input"),
      ("wrong-map-endpoint", Stratum.malformed, "complete endpoint descriptors differ")] do
    let (trace, harness, entry, action, original) ← fixture mode
    try
      let actual ← try
        discard <| executeObjectEdge harness trace (.functor entry.id) action original
        pure (none, "unexpected success")
      catch error => pure (Exception.stratum? error, ← error.toMessageData.toString)
      unless actual.1 == some expected && (actual.2.splitOn fragment).length > 1 do
        throwError "service control {mode} has outcome {reprStr actual}, expected {reprStr expected}: {fragment}"
      unless !(← harness.replies.get).isEmpty do throwError "a rejected service discarded its raw reply"
      if mode == "mixed-owners" || mode == "extra-reference" then
        let #[service] ← harness.services.get | throwError "the rejected scope was not retained"
        unless !service.completed && service.nodes.size == 1 do
          throwError "a rejected final template discarded a completed child's actual Wire"
      evidence mode harness #["exact-typed-stratum", fragment, "raw-reply-retained", "no-availability-route-change"]
    finally harness.stop

run_elab do
  for mode in #["nested", "portable-from-owned"] do
    let (trace, harness, entry, action, original) ← fixture mode
    try
      let original ← if mode == "portable-from-owned" then
        executeObjectEdge harness trace (.functor entry.id) action original
      else pure original
      if mode == "portable-from-owned" then
        unless original.owner?.isSome do throwError "the original owned source was not created"
      let result ← executeObjectEdge harness trace (.functor entry.id) action original
      unless result.owner?.isNone && (← isDefEq result.value (← Semantic.objOf action original.value)) do
        throwError "the completed service changed original meaning or portable result ownership"
      let services ← harness.services.get
      unless services.all (·.completed) do throwError "the service has an unfinished nested scope"
      if mode == "nested" then
        unless services.size == 2 do throwError "the nested program did not retain both reference scopes"
      else
        unless (← harness.replies.get).any (fun record => record.input.owner?.isSome) do
          throwError "the portable completion discarded its original owned input"
      evidence mode harness #["original-formal-result", "complete-reference-scopes", "portable-result", "retained-input-provenance"]
    finally harness.stop

run_elab do
  let trace ← Trace.new
  let harness ← Harness.empty
  let scope : ServiceScope := {
    harness, trace, references := #[], known := #[]
    operands := (← IO.mkRef #[]), backend := "no-provider-selected" }
  let groups ← instantiateMVars (← elabTermAndSynthesize
    (← `(LeanCategories.Algebra.Groups.{0})) none)
  let selected ← serviceArgument scope (← inferType groups)
    (node "category" #[toJson "cat.groups", Json.arr #[]])
  unless ← withTransparency .all <| isDefEq selected.value groups do
    throwError "the public category descriptor changed its full selected dictionary"


run_elab do
  let (trace, harness, entry, action, original) ← fixture "whole-map"
  try
    let result ← executeObjectEdge harness trace (.functor entry.id) action original
    let #[service] ← harness.services.get | throwError "the whole-map program was not retained"
    let #[first, second, mapped] := service.nodes
      | throwError "the whole-map service omitted an object image or map"
    unless (← isDefEq first.result.value second.result.value) &&
        first.result.json != second.result.json do
      throwError "the whole-map service did not retain distinct actual images of one formal endpoint"
    let .ok actual := Backend.TypedMap.decode mapped.result.json
      | throwError "the whole-map service discarded its actual typed callable"
    unless actual.source == first.result.json && actual.target == second.result.json &&
        mapped.result.owner?.isSome && result.owner?.isNone do
      throwError "the whole-map service changed a selected image endpoint or actual result owner"
    let .ok invocation := Backend.PointInvocation.decode mapped.request.json
      | throwError "the whole-map service lost its complete admitted request"
    unless invocation.domain == first.result.json &&
        invocation.argument == node "identity" #[first.result.json, first.result.json] do
      throwError "the service map demand sampled or replaced its original whole domain"
    let .ok ("map", #[descriptor, originalMap]) := ComputationalData.envelope invocation.arrow
      | throwError "the service map discarded its selected action"
    let .ok originalMap := Backend.TypedMap.decode originalMap
      | throwError "the service map discarded the original complete endpoints"
    unless descriptor == node "fun.sets.identity" #[] &&
        originalMap.callable == node "mor.sets.fin_rev" #[toJson (2 : Nat)] do
      throwError "the service map replaced the nonidentity original callable or action"
    evidence "whole-nonidentity-map-service" harness
      #["full-selected-action", "nonidentity-original-callable", "actual-image-occurrences",
        "whole-domain-demand", "owned-callable-retained-in-portable-final-DAG"]
  finally harness.stop

run_elab do
  let (trace, harness, entry, _, original) ← fixture "occurrences"
  let harness := { harness with deferred := none }
  let (image, _) ← Semantic.applyRegisteredFunctor entry original.value #[] (some trace)
  try
    let outcome ← realizeClaim harness trace (.implemented image)
    unless outcome matches .holds do
      throwError "the ordinary production claim did not install the shared service boundary"
    let #[service] ← harness.services.get | throwError "production omitted its service receipt"
    unless service.completed && service.nodes.size == 4 do
      throwError "production did not complete the exact nested requests"
    evidence "ordinary-production-claim-installer" harness
      #["ordinary-realizeClaim", "automatic-service-installation", "actual-child-dispatches"]
  finally harness.stop


run_elab do
  for mode in #["nested-object-argument", "nested-map-argument"] do
    let (trace, harness, entry, action, original) ← fixture mode
    try
      let result ← executeObjectEdge harness trace (.functor entry.id) action original
      unless result.json == node "obj.sets.fin" #[toJson (19 : Nat)] && result.owner?.isNone do
        throwError "the nested input action changed its original final result packet"
      let #[service] ← harness.services.get | throwError "the nested input program was not retained"
      let #[child] := service.nodes | throwError "the nested input lost its explicit target call"
      unless service.completed do throwError "the nested input action did not complete"
      let actions ← harness.actions.get
      unless actions.any (·.operation == "fun.sets.identity") do
        throwError "a nested object action bypassed the shared executable image boundary"
      if mode == "nested-map-argument" then
        unless actions.any (·.operation == "fun.sets.identity#map") && child.result.owner?.isSome do
          throwError "a nested map bypassed actual execution or discarded its target supplier"
      evidence mode harness
        #["nested-action-materialized", "full-source-action-retained", "independent-target-consumer",
          "actual-node-and-action-receipts", "portable-final-result"]
    finally harness.stop

end
