module
import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls of canonical derived action addresses and their common
executor. Arbitrary process data supply no mathematical correctness verdict. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def node (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

private def addresses (state : RegistryState) (edge : EdgeRef) :
    TermElabM (String × String × String) := do
  if let .functor id := edge then
    let some entry := state.functor? id | throwError "the original functor is absent"
    pure (id.raw, entry.mapAddress, entry.inputAddress)
  else pure (edgeActionAddress edge, edgeActionMapAddress edge, edgeActionInputAddress edge)

private def recordEvidence (label : String) (harness : Harness)
    (calls : IO.Ref (Array Json)) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_DERIVED_ACTION_REPORT" then
    let actions ← (← harness.actions.get).mapM fun receipt => do
      return Json.mkObj [
        ("operation", toJson receipt.operation),
        ("action", toJson (reprStr receipt.action)),
        ("actionType", toJson (reprStr (← inferType receipt.action))),
        ("source", receipt.input.json), ("sourceOwner", toJson receipt.input.owner?),
        ("parameters", Json.arr receipt.parameters),
        ("imageEndpoints", toJson (receipt.imageEndpoints.map fun wire => wire.json)),
        ("imageOwners", toJson (receipt.imageEndpoints.map fun wire => wire.owner?)),
        ("result", receipt.result.json), ("resultOwner", toJson receipt.result.owner?)]
    let report := Json.mkObj [
      ("case", toJson label),
      ("purpose", "Engineering framing/ownership control; no mathematical verdict"),
      ("dispatches", Json.arr (← calls.get)), ("actions", Json.arr actions)]
    IO.FS.withFile path .append fun output => output.putStrLn report.compress

private def runCase (label : String) (edge : EdgeRef) (source : Expr)
    (data : Json) (selectedAction : Option Expr := none) : TermElabM Unit := do
  let state ← registryState
  let trace ← Trace.new
  let action ← match selectedAction with
    | some action => pure action
    | none => Semantic.edgeFunctor state edge
  discard <| Semantic.objOf action source
  let action ← instantiateMVars (← Semantic.asFunctor action)
  let (sourceBundle, _) ← functorCategoryBundles action
  let some expression := state.selectedEdgeSource? edge
    | throwError "the control lost its full source schema"
  let context : CategoryContext := { expression, bundle := sourceBundle }
  CategoryContext.checkObject context source
  if let .error message ← ComputationalData.validatePort source (← inferType source) data then
    throwError "{label}: the original complete source fixture is malformed: {message}"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the fallback registration form is absent"
  let original : Wire := {
    form := contextualForm state context (.diagrams sets)
    payload := .computed source (.inline data), objectObserved := true
    categoryContext := some context }
  let (objectAddress, mapAddress, inputAddress) ← addresses state edge
  let manifest : Manifest := {
    backends := #[
      { name := "derived-action-probe", command := "python3",
        args := #["probe_functor_execution.py", "action", objectAddress,
          "--opaque-objects", "--bare-maps"] }]
    registrations := #[
      { operation := objectAddress, input := inputAddress, backend := "derived-action-probe" },
      { operation := mapAddress, input := inputAddress, backend := "derived-action-probe" }] }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let calls ← IO.mkRef #[]
  let initial ← Harness.ofManifest root manifest
  unless initial.rejected.isEmpty && initial.admitted.size == 2 do
    throwError "the complete registered action projections were not admitted"
  let harness := { initial with dispatches := some calls, demandObjectActions := true }
  harness.results.modify (·.insert source original)
  try
    let image ← executeObjectEdge harness trace edge action original
    let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
    let originalMap : Wire := {
      form := contextualForm state context (.canonicalMorphism sets) true
      payload := .computed identity (.inline (Backend.TypedMap.encode {
        source := data, target := data, callable := node "identity" #[data, data] }))
      categoryContext := some context, callableObserved := true }
    let mapped ← executeMapRoute harness trace originalMap #[edge] #[action]
    unless image.objectObserved && image.owner?.isSome && mapped.callableObserved &&
        mapped.owner? == image.owner? && (← calls.get).size == 2 do
      throwError "the derived action failed to retain and reuse its actual owned image"
    let (descriptor, _) ← realizedEdgeDescriptor harness trace edge action
    let parameters ← if let .functor _ := edge then
        match (descriptor.getObjVal? "args").bind (·.getArr?) with
        | .ok parameters => pure parameters
        | .error _ => throwError "the named action lost its complete parameter vector"
      else pure #[descriptor]
    let .ok objectRequest := (← calls.get)[0]!.getObjVal? "request"
      | throwError "the actual object request was not retained"
    unless (objectRequest.getObjVal? "args").toOption == some (Json.arr parameters) &&
        (objectRequest.getObjVal? "receiver").toOption == some data do
      throwError "the object action changed its selected descriptor or actual source"
    let .ok mapRequest := (← calls.get)[1]!.getObjVal? "request"
      | throwError "the actual map request was not retained"
    let .ok invocation := Backend.PointInvocation.decode mapRequest
      | throwError "the derived map changed the common whole-domain frame"
    unless invocation.operation == mapAddress && invocation.parameters == parameters &&
        invocation.arrow == node "map" #[descriptor, originalMap.json] &&
        invocation.source == image.json && invocation.target == image.json &&
        invocation.domain == image.json &&
        invocation.argument == node "identity" #[image.json, image.json] do
      throwError "the map action changed its complete action, source map or actual image endpoints"
    let reused ← executeMapRoute harness trace originalMap #[edge] #[action]
    unless reused.json == mapped.json && reused.owner? == mapped.owner? &&
        (← calls.get).size == 2 do
      throwError "the derived map replayed an already completed exact action"
    recordEvidence label harness calls
  finally harness.stop

run_elab do
  let state ← registryState
  let classifier := EdgeRef.classifierForget ClassifierId.setsFinite
  let arrow := EdgeRef.constructMap ConstructorId.arrow (.functor ⟨"fun.sets.list"⟩)
  let nested := EdgeRef.constructMap ConstructorId.core arrow
  for edge in #[classifier, arrow, nested] do
    unless state.actionEdge? (edgeActionAddress edge) == some edge do
      throwError "the canonical action address lost its complete registered edge"
    let some input := state.edgeActionInputForm? (edgeActionInputAddress edge)
      | throwError "the canonical action input is absent"
    for address in #[edgeActionAddress edge, edgeActionMapAddress edge] do
      let some operation := state.operation? address
        | throwError "a published action projection was not resolved"
      unless state.accepts operation input do
        throwError "a complete derived request was not admitted at its own selected action"
    let noncanonical := "action: " ++ (edgeImageDescriptor edge).compress
    if (state.operation? noncanonical).isSome then
      throwError "an alternate JSON spelling became a second operation address"
  if (state.operation? (edgeActionAddress (.functor ⟨"fun.sets.list"⟩))).isSome then
    throwError "the derived family added an alias to an existing functor identifier"
  let unavailable := EdgeRef.constructMap ConstructorId.slice (.functor ⟨"fun.sets.list"⟩)
  if (state.operation? (edgeActionAddress unavailable)).isSome then
    throwError "a constructor without a published action gained an executable projection"
  let some classifierOperation := state.operation? (edgeActionAddress classifier)
    | throwError "the classifier action is absent"
  let some arrowInput := state.edgeActionInputForm? (edgeActionInputAddress arrow)
    | throwError "the constructor input is absent"
  if state.accepts classifierOperation arrowInput then
    throwError "one derived action admitted another action's complete input"

run_elab do
  let some row := (← registryState).objects.find? (·.id.raw == "obj.finite_sets.fin")
    | throwError "the existing finite source is absent"
  let source ← Semantic.object row #[← `(2)]
  runCase "classifier-forget-object-and-map" (.classifierForget ClassifierId.setsFinite)
    source (node row.id.raw #[toJson (2 : Nat)])

run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the original finite source is absent"
  let source ← Semantic.object row #[← `(2)]
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
  let point := node "obj.sets.fin" #[toJson (2 : Nat)]
  let arrowData := node "arrow" #[point, point, node "identity" #[point, point]]
  let edge := EdgeRef.constructMap ConstructorId.arrow (.functor ⟨"fun.sets.list"⟩)
  runCase "constructor-map-object-and-map" edge arrow arrowData
  let core ← mkAppM ``CategoryTheory.Core.mk #[arrow]
  runCase "nested-constructor-map-object-and-map" (.constructMap ConstructorId.core edge)
    core (node "coreObject" #[arrowData])
  if (← ComputationalData.validatePort source (← inferType source)
      (node "coreObject" #[point])).isOk then
    throwError "a core object packet selected a Core interface at an unrelated expected type"
  for malformed in #[node "coreObject" #[], node "coreObject" #[point],
      node "coreObject" #[node "arrow" #[point, point]]] do
    if (← ComputationalData.validatePort core (← inferType core) malformed).isOk then
      throwError "a nested core packet omitted or changed its independently selected original interface"

-- An ignored earlier declaration application cannot supply the selected
-- action's parameter data, even when both complete formal functors agree.
run_elab do
  let state ← registryState
  let some entry := state.functor? FunctorId.modulesFibreInclusion
    | throwError "the existing parameterized action is absent"
  let some ringRow := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the complete scalar source is absent"
  let some moduleRow := state.objects.find? (·.id.raw == "obj.modules.vectors")
    | throwError "the selected module source is absent"
  let trace ← Trace.new
  let parameter ← Semantic.object ringRow #[] (some trace)
  let ignored ← mkAppM ``id #[parameter]
  let source ← Semantic.object moduleRow #[← exprToSyntax parameter, ← `(1)] (some trace)
  let selected ← ObjectPresentation.applyParameters entry.declaration #[parameter]
  let other ← ObjectPresentation.applyParameters entry.declaration #[ignored]
  discard <| Semantic.objOf selected source
  discard <| Semantic.objOf other source
  let selected ← instantiateMVars selected
  let other ← instantiateMVars other
  let choose := mkLambda `ignored .default (← inferType other)
    (mkLambda `selected .default (← inferType selected) (mkBVar 0))
  let actual := mkApp2 choose other selected
  let harness ← Harness.empty
  let parameterWire ← realize harness trace "the selected scalar parameter" parameter
  let ignoredWire : Wire := { parameterWire with
    payload := .computed ignored (.owned "unused-source" 901
      (node "opaqueData" #["unused parameter token"])) }
  harness.results.modify (·.insert ignored ignoredWire)
  let (descriptor, dependencies) ← realizedEdgeDescriptor
    { harness with demandObjectActions := true } trace (.functor entry.id) actual
  unless descriptor == node entry.id.raw #[parameterWire.json] &&
      dependencies.all (·.owner?.isNone) do
    throwError "an ignored action parameter replaced the selected complete declaration application"
  let original ← realize harness trace "the complete original module source" source
  runCase "whole-selected-parameter-application" (.functor entry.id)
    source original.json (some actual)

end
