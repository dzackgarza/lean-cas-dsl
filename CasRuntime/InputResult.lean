module

public import CasRuntime.FixedInput

public section

namespace CasRuntime

open Lean Meta CasCompiler

private inductive InputResultTree where
  | input (path : Array Name) (selected : FixedInput)
  | record (layout : RecordLayout) (children : Array InputResultTree)

/-- Complete source coverage of this exact prepared result, before resolving any lazy input.
The native record tree retains every computational field, including subsingleton data.
Reuse: fixedInputFor, RecordLayout and the original prepared result addresses. -/
structure InputResultPlan (request : PreparedRequest) where
  private mk ::
  private tree : InputResultTree
  private inputs : InputRoleMap

private partial def prepareInputResult (request : PreparedRequest) (graph : ValueGraph)
    (source : SourceLayout) : MetaM (Option InputResultTree) := do
  if let some input ← request.fixedInputFor graph source then
    return some (.input (← request.source.projectionPathTo source) input)
  if source.kind != .record then
    dbg_trace "[input.result.uncovered] path={source.address} kind={repr source.kind} source={source.source.expression}"
    return none
  let layout ← RecordLayout.ofSource source
  let mut children := #[]
  for field in layout.fields do
    if field.field.wireIndex.isNone then continue
    let some child ← prepareInputResult request graph field.layout | return none
    children := children.push child
  return some (.record layout children)

/-- Establish all input routes without executing a field, selecting a provider or staging data.
A fixed whole root takes precedence over reconstructing its individual fields. -/
opaque PreparedRequest.inputResultPlan (request : PreparedRequest) (graph : ValueGraph) :
    MetaM (Option (InputResultPlan request)) := do
  let some tree ← prepareInputResult request graph request.source | return none
  let inputs ← request.admitInputResultInputs graph
  return some ⟨tree, inputs⟩

private partial def InputResultTree.inputs (tree : InputResultTree) :
    Array (Array Name × FixedInput) :=
  match tree with
  | .input path selected => #[(path, selected)]
  | .record _ children => children.flatMap (·.inputs)

/-- Sealed original selections, validated against input-side access history before output
association can add any wrappers. The public reader cannot replace a selected baseline. -/
structure ResolvedInputResult (request : PreparedRequest) where
  private mk ::
  private plan : InputResultPlan request
  private selected : Array FixedResult

def ResolvedInputResult.selections (resolved : ResolvedInputResult request) : Array FixedResult :=
  resolved.selected

/-- Resolve only an already complete plan. A lazy resolver returns its enriched input access;
the graph derives its original baseline at the exact planned parent and native path.
Reuse: storedValue?, projectionBasis and immutable graph visibility. -/
opaque InputResultPlan.resolve (plan : InputResultPlan request) (graphView : MetaM ValueGraph)
    (resolve : Option (FixedInput → MetaM ValueBinding) := none) :
    MetaM (ResolvedInputResult request) := do
  let mut selected := #[]
  for (path, input) in plan.tree.inputs do
    let value ← input.resolveValue graphView resolve
    selected := selected.push ⟨path, input, value⟩
  return ⟨plan, selected⟩

private partial def InputResultTree.check (tree : InputResultTree) (graph : ValueGraph)
    (selected : Array FixedResult) (value : ValueBinding) : Except String Unit := do
  discard <| graph.requiredOwners #[value]
  match tree with
  | .input path _ =>
    let some original := selected.find? (·.path == path)
      | throw "the complete input result lost a validated selection"
    unless value.value == original.value.value &&
        original.value.associationIds.toList.isPrefixOf value.associationIds.toList do
      throw "the input result changed its original selected occurrence"
  | .record layout children =>
    let some node := graph.find value.value
      | throw "the assembled input result is outside its graph"
    let some stored := node.payload.data.storedFields?
      | throw "the assembled input result has no complete stored record"
    let count := stored.size
    let fields := layout.fields.filterMap (·.field.wireIndex)
    unless count == fields.size && children.size == fields.size do
      throw "the assembled input result changed its complete native field arity"
    for child in children, index in fields do
      child.check graph selected (← graph.project value index)

/-- This particular admitted response contains every original input selected by the complete
plan. It authorizes the selected-output owner gate, not arbitrary source-typed responses. -/
structure InputResultCompletion (request : PreparedRequest) where
  private mk ::
  response : PreparedResponse request
  private inputMap : InputRoleMap

def InputResultCompletion.inputs (completed : InputResultCompletion request) : InputRoleMap :=
  completed.inputMap

/-- Check the sealed tree against the assembled response without rediscovering source routes.
Selected roots may remain lazy; reconstructed records must expose all stored data fields. -/
opaque ResolvedInputResult.admit (resolved : ResolvedInputResult request) (graph : ValueGraph)
    (response : PreparedResponse request) : Except String (InputResultCompletion request) := do
  resolved.plan.tree.check graph resolved.selected response.root
  return ⟨response, resolved.plan.inputs⟩

end CasRuntime
