module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

/- Engineering controls of registration selection and data provenance. Opaque
fixtures assert no mathematical answer; no external process is started. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt
    "assert |Sym(3) in Groups| = 6"
    | throwError "the inherited request fixture did not parse"
  let question ← interpret {} parsed
  let trace ← IO.mkRef question.trace
  let state ← registryState
  let empty ← Harness.empty
  let mut checked := false
  for (_, node) in question.trace.toArray do
    let .method id route receiver _ := node | continue
    unless !route.isEmpty do throwError "the inherited request fixture lost its route"
    let initial ← realize empty trace "the selected source" receiver
    let some source := state.categories.find? (·.id == initial.form.category)
      | throwError "the selected source category is absent"
    let some target := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the operation owner is absent"
    let packet := Json.mkObj [("ctor", "opaqueData"),
      ("args", Json.arr #[toJson ("actual selected object" : String)])]
    let original : Wire := { initial with
      form := .diagrams source
      payload := .computed initial.value (.owned "dispatch-probe" 17 packet) }
    let (canonical, expected) ← operationReceiver trace original route
    let harness := fun addresses => Harness.ofManifest "." {
      backends := #[{ name := "dispatch-probe", command := "unused" }]
      registrations := addresses.map fun address => {
        operation := id.raw, input := address, backend := "dispatch-probe" } }
    let inherited ← harness #[target.id.raw]
    unless inherited.rejected.isEmpty && inherited.admitted.size == 1 do
      throwError "the operation-owner registration was not admitted"
    let full ← computationalOperationReceiver inherited trace id.raw original route canonical
    unless full.form.category == target.id && full.owner? == original.owner? &&
        (full.json.getObjValAs? String "ctor").toOption == some "functorAction" do
      throwError "inherited dispatch lost the full action, its category or its live owner"
    unless ← withTransparency .all <| isDefEq full.value expected do
      throwError "inherited dispatch changed the complete independently selected receiver"
    let mut actual := full.json
    for _ in [:route.size] do
      let .ok ("functorAction", #[_, input]) := ComputationalData.envelope actual
        | throwError "inherited dispatch dropped an ordered structural action"
      actual := input
    unless actual == packet do
      throwError "inherited dispatch replaced the actual object with its formal recipe"
    let fused ← harness #[source.id.raw]
    unless fused.rejected.isEmpty && fused.admitted.size == 1 do
      throwError "the existing source-composite registration was not admitted"
    let legacy ← computationalOperationReceiver fused trace id.raw original route canonical
    unless legacy.form.id == original.form.id && legacy.json == packet &&
        legacy.owner? == original.owner? do
      throwError "the existing source registration received a different packet"
    let overlapping ← harness #[source.id.raw, target.id.raw]
    let ambiguous ← try
      discard <| computationalOperationReceiver overlapping trace id.raw original route canonical
      pure false
    catch error =>
      if CasCatalogue.Exception.stratum? error == some .ambiguousRealization then
        pure true
      else throw error
    unless ambiguous do
      throwError "overlapping source and target registrations acquired an implicit priority"
    let firstEdge : Option EdgeRef := route[0]?
    let some (EdgeRef.functor edge) := firstEdge
      | throwError "the structural action fixture lost its first declared functor"
    let some row := state.functor? edge
      | throwError "the declared structural action is absent"
    unless row.structural do throwError "the fixture ceased to be structural"
    let action ← Semantic.edgeFunctor state (.functor edge)
    let image ← Semantic.objOf action original.value
    let actionTrace ← Trace.new
    Trace.record (some actionTrace) image (.functor edge #[] original.value)
    let structural ← Harness.empty
    structural.results.modify (·.insert original.value original)
    let result ← realize structural actionTrace "the complete structural action" image
    unless result.owner? == original.owner? &&
        (result.json.getObjValAs? String "ctor").toOption == some "functorAction" &&
        (← structural.connections.get).isEmpty do
      throwError "a structural action demanded a leaf or discarded the actual dependency"
    checked := true
  unless checked do throwError "the fixture did not exercise an inherited operation"
