module
import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Protocol-only controls of a shared registered action boundary. Processes
return arbitrary objects/callables, never mathematical correctness evidence. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def dataNode (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def wireRecord (wire : Wire) : TermElabM Json := do
  return Json.mkObj [
    ("form", toJson wire.form.id),
    ("formal", toJson (reprStr wire.value)),
    ("type", toJson (reprStr (← inferType wire.value))),
    ("data", wire.json), ("owner", toJson wire.owner?),
    ("objectObserved", toJson wire.objectObserved),
    ("callableObserved", toJson wire.callableObserved),
    ("category", toJson (wire.categoryContext.map fun context => reprStr context.bundle)),
    ("objectIso", toJson (wire.objectIso.map reprStr))]

private def recordEvidence (label : String) (harness : Harness)
    (calls : IO.Ref (Array Json)) (checks : Array String) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_ACTION_EXECUTION_REPORT" then
    let actions ← (← harness.actions.get).mapM fun receipt => do
      return Json.mkObj [
        ("operation", toJson receipt.operation),
        ("action", toJson (reprStr receipt.action)),
        ("actionType", toJson (reprStr (← inferType receipt.action))),
        ("input", ← wireRecord receipt.input),
        ("parameters", Json.arr receipt.parameters),
        ("parameterInputs", Json.arr (← receipt.parameterInputs.mapM wireRecord)),
        ("imageEndpoints", Json.arr (← receipt.imageEndpoints.mapM wireRecord)),
        ("result", ← wireRecord receipt.result)]
    let report := Json.mkObj [
      ("case", toJson label),
      ("purpose", "Engineering action and ownership controls; no mathematical verdict"),
      ("checks", toJson checks),
      ("dispatches", Json.arr (← calls.get)), ("actions", Json.arr actions)]
    IO.FS.withFile path .append fun output => output.putStrLn report.compress

private def fixture : TermElabM (Trace × FunctorEntry × Expr × Wire × Wire × Wire) := do
  let trace ← Trace.new
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the existing action control is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the original complete category is absent"
  let some objects := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the original named source is absent"
  let source ← Semantic.object objects #[← `(2)] (some trace)
  let target ← Semantic.object objects #[← `(3)] (some trace)
  let empty ← Harness.empty
  let sourceWire ← realize empty trace "the original source" source
  let targetWire ← realize empty trace "the original target" target
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  discard <| Semantic.objOf action source
  let action ← instantiateMVars action
  let morphism ← instantiateMVars (← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun (_ : $(← exprToSyntax source)) =>
      (0 : $(← exprToSyntax target))))) none)
  let context ← CategoryContext.ofNamed sets source
  let original : Wire := {
    form := .canonicalMorphism sets
    payload := .ordinary morphism (toJson ([[0, 0], [1, 0]] : List (List Nat)))
    categoryContext := some context }
  return (trace, entry, action, sourceWire, targetWire, original)

private def harnessFor (entry : FunctorEntry) (options : Array String := #[])
    (sourceOperation : Option String := none) :
    TermElabM (Harness × IO.Ref (Array Json)) := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[
      { name := "action-probe", command := "python3",
        args := #["probe_functor_execution.py", "action", entry.id.raw] ++ options ++
          (sourceOperation.toArray.map ("--source-operation=" ++ ·)) },
      { name := "target-probe", command := "python3",
        args := #["probe_functor_execution.py", "target", "meth.cardinality"] }]
    registrations := #[
      { operation := entry.id.raw, input := entry.inputAddress, backend := "action-probe" },
      { operation := entry.mapAddress, input := entry.inputAddress, backend := "action-probe" },
      { operation := "meth.cardinality", input := "cat.sets", backend := "target-probe" }] ++
      (sourceOperation.toArray.map fun address => {
        operation := address, input := address, backend := "action-probe" }) }
  let calls ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == 3 + sourceOperation.toArray.size do
    throwError "the registered action projections or independent target input were not admitted"
  return ({ harness with dispatches := some calls }, calls)

run_elab do
  let (trace, entry, action, source, target, original) ← fixture
  let edge := EdgeRef.functor entry.id
  for hostile in #[false, true] do
    let (harness, calls) ← harnessFor entry
      (if hostile then #["--wrong-endpoint"] else #[])
    try
      let first ← executeObjectEdge harness trace edge action source
      let second ← executeObjectEdge harness trace edge action target
      unless first.objectObserved && second.objectObserved && first.owner?.isNone &&
          second.owner?.isNone && (← calls.get).size == 2 do
        throwError "the object boundary did not retain its two actual portable images"
      let again ← executeObjectEdge harness trace edge action source
      unless again.json == first.json && (← calls.get).size == 2 do
        throwError "the object action recomputed an already retained exact occurrence"
      if hostile then
        let malformed ← try
          discard <| executeMapRoute harness trace original #[edge] #[action]
          pure false
        catch error => pure (Exception.stratum? error == some .malformed)
        unless malformed && (← calls.get).size == 3 do
          throwError "a wrong complete image endpoint escaped the action boundary"
      else
        let mapped ← executeMapRoute harness trace original #[edge] #[action]
        unless mapped.callableObserved && mapped.owner?.isSome && (← calls.get).size == 3 do
          throwError "the map boundary did not retain the actual returned complete callable"
        let sent := (← calls.get)[2]!
        let .ok request := sent.getObjVal? "request" | throwError "the actual map request was lost"
        let .ok invocation := Backend.PointInvocation.decode request
          | throwError "the map boundary did not use the common whole-domain invocation"
        unless invocation.source == first.json && invocation.domain == first.json &&
            invocation.target == second.json &&
            invocation.argument == dataNode "identity" #[first.json, first.json] do
          throwError "the map boundary replaced a computed endpoint or sampled its domain"
        let .ok ("map", #[descriptor, sourceMap]) := ComputationalData.envelope invocation.arrow
          | throwError "the map request discarded its exact selected action"
        let .ok sourceMap := Backend.TypedMap.decode sourceMap
          | throwError "the map request discarded its original complete source endpoints"
        unless descriptor == dataNode entry.id.raw #[] && sourceMap.source == source.json &&
            sourceMap.target == target.json && sourceMap.callable == original.json do
          throwError "the map request changed actual source data or full action parameters"
        let reused ← executeMapRoute harness trace original #[edge] #[action]
        unless reused.json == mapped.json && reused.owner? == mapped.owner? &&
            (← calls.get).size == 3 do
          throwError "the mapped callable replayed its original descriptor"
        discard <| send harness "meth.cardinality" first
        let consumer := (← calls.get)[3]!
        unless (consumer.getObjVal? "request").toOption == some first.json &&
            (consumer.getObjValAs? String "backend").toOption == some "target-probe" do
          throwError "the independent target consumer did not receive the actual portable image"
        -- Same formal source with different actual data is a distinct execution.
        let changed := { source with payload := .computed source.value (.inline target.json) }
        let changedImage ← executeObjectEdge harness trace edge action changed
        unless changedImage.json != first.json && (← calls.get).size == 5 do
          throwError "the action cache selected a definitionally equal source representation"
        -- The whole action, not coincidence at one object, fixes execution.
        let coincident ← Semantic.objOf action source.value
        let constant ← instantiateMVars (← elabTermAndSynthesize
          (← `((CategoryTheory.Functor.const Type).obj $(← exprToSyntax coincident))) none)
        let refused ← try
          discard <| executeObjectEdge harness trace edge constant source
          pure false
        catch _ => pure true
        unless refused && (← calls.get).size == 5 do
          throwError "a different whole action reused a coincident computed image"
        let connections ← harness.connections.get
        let some (.ok session) := connections["action-probe"]?
          | throwError "the returned callable lost its actual process"
        harness.connections.modify (·.insert "action-probe" (.ok { session with
          identity := session.identity + 1 }))
        let expired ← try
          discard <| executeMapRoute harness trace original #[edge] #[action]
          pure false
        catch error => pure (Exception.stratum? error == some .unavailable)
        harness.connections.set connections
        unless expired && (← calls.get).size == 5 do
          throwError "a retained callable was reused through a different session identity"
      recordEvidence (if hostile then "malformed-image-endpoint" else "retained-whole-action")
        harness calls (if hostile then #["malformed", "exact-image-endpoints"] else
          #["portable-object-images", "owned-whole-callable", "exact-source-data",
            "actual-image-reuse", "independent-target-consumer", "changed-packet-separation",
            "different-whole-action-refused", "expired-session-unavailable"])
    finally harness.stop

run_elab do
  let (trace, entry, action, source, _, _) ← fixture
  let edge := EdgeRef.functor entry.id
  let (harness, calls) ← harnessFor entry #["--first-opaque"]
  try
    let first ← executeObjectEdge harness trace edge action source
    let some owner := first.owner? | throwError "the owned source control did not create an actual token"
    let second ← executeObjectEdge harness trace edge action first
    unless second.owner?.isNone && second.objectObserved && (← calls.get).size == 2 do
      throwError "a self-contained returned image inherited an irrelevant source-session restriction"
    let receipts ← harness.actions.get
    let #[_, retained] := receipts | throwError "the two actual actions lost their receipts"
    unless retained.input.owner? == some owner && retained.input.json == first.json &&
        retained.result.json == second.json do
      throwError "portable image export discarded the original source or its live owner receipt"
    discard <| send harness "meth.cardinality" second
    unless (← calls.get).size == 3 do
      throwError "portable target data could not cross the independent consumer boundary"
    let refused ← try
      discard <| send harness "meth.cardinality" first
      pure false
    catch error => pure (Exception.stratum? error == some .noImplementation)
    unless refused && (← calls.get).size == 3 do
      throwError "an opaque source crossed into a foreign target session"
    recordEvidence "portable-export-from-owned-source" harness calls
      #["actual-source-owner-retained-in-receipt", "portable-result-crosses-process",
        "opaque-source-cannot-cross-process"]
  finally harness.stop

-- Production realization forces a structural action on an actual computed
-- source and maps an actual complete callable, without a named refinement.
run_elab do
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.linear_orders.forget")
    | throwError "the existing structural action control is absent"
  unless entry.structural do throwError "the structural control changed its registered role"
  let some row := state.objects.find? (·.id.raw == "obj.linear_orders.naturals")
    | throwError "the original complete structured source is absent"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the original structured category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the target category is absent"
  let trace ← Trace.new
  let source ← Semantic.object row #[] (some trace)
  let context ← CategoryContext.ofNamed category source
  let (image, _) ← Semantic.applyRegisteredFunctor entry source #[] (some trace)
  let actualSource := dataNode "obj.linear_orders.integers" #[]
  let sourceWire : Wire := {
    form := .object row, payload := .computed source (.inline actualSource)
    categoryContext := some context }
  let (harness, calls) ← harnessFor entry
  let harness := { harness with demandObjectActions := true }
  harness.results.modify (·.insert source sourceWire)
  try
    let observed ← realize harness trace "the actual structural image" image
    unless observed.objectObserved && (← calls.get).size == 1 do
      throwError "production realization left a structural object recipe unexecuted"
    let .ok request := (← calls.get)[0]!.getObjVal? "request"
      | throwError "the actual source action request was not retained"
    unless (request.getObjVal? "receiver").toOption == some actualSource do
      throwError "production realization substituted the formal named source for actual returned data"
    let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
    let sourceCallable := Backend.TypedMap.encode {
      source := actualSource, target := actualSource
      callable := dataNode "identity" #[actualSource, actualSource] }
    let original : Wire := {
      form := .canonicalMorphism category, payload := .computed identity (.inline sourceCallable)
      categoryContext := some context, callableObserved := true }
    harness.results.modify (·.insert identity original)
    let action ← Semantic.edgeFunctor state (.functor entry.id)
    let mapped ← Semantic.mapOf action identity
    Trace.record (some trace) mapped
      (.morphismTransport category.id sets.id #[.functor entry.id] identity)
    let observedMap ← realize harness trace "the actual structural map image" mapped
    unless observedMap.callableObserved && observedMap.owner?.isSome && (← calls.get).size == 2 do
      throwError "production realization did not reuse its existing image for the actual source map"
    let .ok request := (← calls.get)[1]!.getObjVal? "request"
      | throwError "the actual mapped request was not retained"
    let .ok invocation := Backend.PointInvocation.decode request
      | throwError "the production map lost its common whole-domain invocation"
    let .ok ("map", #[_, original]) := ComputationalData.envelope invocation.arrow
      | throwError "the production map discarded its original callable"
    unless original == sourceCallable && invocation.source == observed.json &&
        invocation.target == observed.json do
      throwError "production map execution changed an actual source or image endpoint"
    discard <| send harness "meth.cardinality" observed
    unless (← calls.get).size == 3 do
      throwError "the independent target consumer did not receive the actual structural image"
    recordEvidence "production-structural-action" harness calls
      #["computed-source-not-replaced-by-name", "whole-source-callable-retained",
        "image-endpoints-reused", "target-consumer-receives-only-target-data"]
  finally harness.stop

-- An actual source-category callable is itself returned by a separate public
-- operation in the same live process. Mapping it retains that exact token,
-- and portable endpoint fields reuse the already computed object image.
run_elab do
  let (trace, entry, action, source, _, _) ← fixture
  let state ← registryState
  let some cell := state.cells.find? (·.id.raw == "cell.sets.list.reverse")
    | throwError "the existing source-callable control is absent"
  let address := cell.componentAddress
  let (harness, calls) ← harnessFor entry #[] (some address)
  let harness := { harness with demandObjectActions := true }
  try
    let first ← executeObjectEdge harness trace (.functor entry.id) action source
    let selected ← CellAction.select cell #[] #[] false source.value
    let (domain, codomain) ← CellAction.objects selected source.value
    let formal ← CellAction.component selected source.value
    Trace.record (some trace) domain (.cellEndpoint cell.id #[] #[] false false source.value)
    Trace.record (some trace) codomain (.cellEndpoint cell.id #[] #[] false true source.value)
    Trace.record (some trace) formal (.cellComponent cell.id #[] #[] false source.value)
    let descriptor ← realize harness trace "the registered original source callable" formal
    let original ← realizeArrowObservation harness trace descriptor
    let some owner := original.owner? | throwError "the source callable did not retain its actual owner"
    let .ok originalFrame := Backend.TypedMap.decode original.json
      | throwError "the returned source callable omitted its complete endpoints"
    unless originalFrame.source == first.json && originalFrame.target == first.json &&
        (← calls.get).size == 2 do
      throwError "the source callable failed to reuse the actual object image"
    let mapped ← executeMapRoute harness trace original #[.functor entry.id] #[action]
    unless mapped.owner? == some owner && (← calls.get).size == 4 do
      throwError "the mapped opaque source lost its owner or repeated an endpoint image"
    let .ok request := (← calls.get)[3]!.getObjVal? "request"
      | throwError "the actual owned-map request was not retained"
    let .ok invocation := Backend.PointInvocation.decode request
      | throwError "the actual owned map lost its complete common invocation"
    let .ok ("map", #[_, supplied]) := ComputationalData.envelope invocation.arrow
      | throwError "the actual owned map lost its selected action"
    unless supplied == original.json do
      throwError "mapping an owned source replaced its actual returned callable"
    let reused ← executeMapRoute harness trace original #[.functor entry.id] #[action]
    unless reused.json == mapped.json && reused.owner? == mapped.owner? &&
        (← calls.get).size == 4 do
      throwError "mapping the same owned source replayed its computation"
    recordEvidence "actual-owned-source-callable" harness calls
      #["checked-comparison-endpoints-reuse-images", "original-owned-callable-retained",
        "portable-endpoint-fields-reused", "mapped-result-owner-retained", "no-replay"]
  finally harness.stop

-- A parameterized action retains its full selected scalar object in both
-- requests. Opaque image endpoints remain at the same process for the map.
run_elab do
  let state ← registryState
  let some entry := state.functor? FunctorId.modulesFibreInclusion
    | throwError "the parameterized registered action is absent"
  let some ringRow := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the complete scalar object is absent"
  let some moduleRow := state.objects.find? (·.id.raw == "obj.modules.vectors")
    | throwError "the existing parameterized source is absent"
  let some modules := state.categories.find? (·.id == moduleRow.category)
    | throwError "the source family is absent"
  let trace ← Trace.new
  let ring ← Semantic.object ringRow #[] (some trace)
  let source ← Semantic.object moduleRow #[← exprToSyntax ring, ← `(1)] (some trace)
  let action ← ObjectPresentation.applyParameters entry.declaration #[ring]
  discard <| Semantic.objOf action source
  let action ← instantiateMVars action
  let (sourceBundle, _) ← functorCategoryBundles action
  let context : CategoryContext := { expression := entry.source, bundle := sourceBundle }
  let empty ← Harness.empty
  let sourceWire ← realize empty trace "the complete parameterized source" source
  let ringWire ← realize empty trace "the exact scalar parameter" ring
  let formal ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let original : Wire := {
    form := .canonicalMorphism modules
    payload := .ordinary formal (dataNode "identity" #[sourceWire.json, sourceWire.json])
    categoryContext := some context }
  let (harness, calls) ← harnessFor entry #["--opaque-objects", "--bare-maps"]
  try
    let image ← executeObjectEdge harness trace (.functor entry.id) action sourceWire
    let mapped ← executeMapRoute harness trace original #[.functor entry.id] #[action]
    unless image.owner?.isSome && mapped.owner? == image.owner? && (← calls.get).size == 2 do
      throwError "the parameterized map changed its owned image or repeated its object action"
    let .ok objectRequest := (← calls.get)[0]!.getObjVal? "request"
      | throwError "the parameterized object request was not retained"
    unless (objectRequest.getObjVal? "args").toOption == some (Json.arr #[ringWire.json]) &&
        (objectRequest.getObjVal? "receiver").toOption == some sourceWire.json do
      throwError "the object action changed its full scalar parameter or actual source"
    let .ok mapRequest := (← calls.get)[1]!.getObjVal? "request"
      | throwError "the parameterized map request was not retained"
    let .ok invocation := Backend.PointInvocation.decode mapRequest
      | throwError "the parameterized map lost its complete public invocation"
    let .ok ("map", #[descriptor, _]) := ComputationalData.envelope invocation.arrow
      | throwError "the parameterized map lost its complete selected action"
    unless invocation.parameters == #[ringWire.json] &&
        descriptor == dataNode entry.id.raw #[ringWire.json] &&
        invocation.source == image.json && invocation.target == image.json do
      throwError "the map changed its ordered complete parameter or actual image endpoints"
    recordEvidence "parameterized-owned-images" harness calls
      #["complete-ordered-scalar-parameter", "actual-source-retained",
        "opaque-image-endpoints-reused", "same-owner-map-result"]
  finally harness.stop

-- Equal formal endpoints do not identify two actual endpoint packets. A bare
-- returned whole callable keeps both supplied images through the next action.
run_elab do
  let (trace, entry, action, source, target, original) ← fixture
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source.value]
  let original := { original with
    payload := .computed identity (.inline (Backend.TypedMap.encode {
      source := source.json, target := target.json, callable := original.json }))
    callableObserved := true }
  let (harness, calls) ← harnessFor entry #["--bare-maps"]
  try
    let twice ← executeMapRoute harness trace original
      #[.functor entry.id, .functor entry.id] #[action, action]
    let callsValue ← calls.get
    let .ok firstRequest := callsValue[2]!.getObjVal? "request"
      | throwError "the first complete mapped request was not retained"
    let .ok firstInvocation := Backend.PointInvocation.decode firstRequest
      | throwError "the first complete map lost its public frame"
    let .ok secondRequest := callsValue.back!.getObjVal? "request"
      | throwError "the second complete mapped request was not retained"
    let .ok secondInvocation := Backend.PointInvocation.decode secondRequest
      | throwError "the second complete map lost its public frame"
    let .ok ("map", #[_, sourceMap]) := ComputationalData.envelope secondInvocation.arrow
      | throwError "the second map lost its actual original callable"
    let .ok sourceMap := Backend.TypedMap.decode sourceMap
      | throwError "the bare returned callable lost its independently supplied endpoints"
    unless sourceMap.source == firstInvocation.source && sourceMap.target == firstInvocation.target &&
        sourceMap.source != sourceMap.target && callsValue.size == 6 do
      throwError "a chained bare callable replaced distinct actual endpoints by an equal formal cache key"
    let .ok firstResponse := callsValue[2]!.getObjVal? "response"
      | throwError "the first actual callable reply was not retained"
    let .ok ("valueData", #[firstData]) := ComputationalData.envelope firstResponse
      | throwError "the first reply did not use its public data envelope"
    unless sourceMap.callable == firstData && twice.owner?.isSome do
      throwError "endpoint retention changed the original returned callable or its owner"
    recordEvidence "chained-bare-callable-endpoints" harness calls
      #["same-formal-distinct-actual-endpoints", "bare-return-retained-whole",
        "both-images-retained-through-next-action", "original-owner-retained"]
  finally harness.stop

end
