module

public import CasCompiler.Layout
public import CasRuntime.Owner
public import CasContract.Port

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue.Backend

/-- One exact record occurrence's prepared source and runtime association identity. -/
structure RecordAssociation where
  private mk ::
  id : RuntimeId .association
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  layout : RecordLayout

/-- One prepared application's source slots and selected result dependencies.
Actual values remain in the binding below, independently of the original producing node. -/
structure ApplicationAssociation where
  private mk ::
  id : RuntimeId .association
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  layout : ApplicationLayout
  path : Array Name
  dependencies : Array Nat
  contextDependencies : Array Nat

/-- Original consuming field data, with an optional checked descendant dependency view.
The parameter permits the same data to be retained inside a recursive ValueBinding.
Creating this record cannot attach an association to a value; that boundary remains private. -/
structure FieldInstantiationData (binding : Type) where
  id : RuntimeId .association
  association : RecordAssociation
  field : FieldLayout
  preceding : Array (Option binding)
  view : Option FieldDependencyView := none

def FieldInstantiationData.typeFamily (value : FieldInstantiationData binding) : ClosedTerm :=
  (value.view.map (·.typeFamily)).getD value.field.typeFamily

def FieldInstantiationData.precedingDependencies (value : FieldInstantiationData binding) :
    Array Nat :=
  (value.view.map (·.precedingDependencies)).getD value.field.precedingDependencies

def FieldInstantiationData.projectionPath (value : FieldInstantiationData binding) : Array Name :=
  (value.view.map (·.path)).getD #[]

/-- A consuming role retains its underlying binding and actual dependent prefix.
The recursive data keep earlier associations when an existing node fills another role.
Source: the data model's ResultBinding and dependency-ordered DataInterface contract. -/
inductive ValueBinding where
  | private direct (value : RuntimeId .value) (role : SourceLayout)
  | private atRole (binding : ValueBinding) (role : SourceLayout)
  | private inField (id : RuntimeId .association) (binding : ValueBinding) (role : SourceLayout)
      (association : RecordAssociation) (field : FieldLayout)
      (preceding : Array (Option ValueBinding))
  | private inApplication (binding : ValueBinding) (role : SourceLayout)
      (association : ApplicationAssociation)
      (parameters applicationParameters arguments : Array (Option ValueBinding))
      (callable access : Option ValueBinding) (fields : Array ValueBinding)
  | private inProjection (id : RuntimeId .association) (binding : ValueBinding)
      (role : SourceLayout) (parent : ValueBinding) (path : Array Name)
      (basis : ValueBinding) (fields : Array ValueBinding)
      (dependencies : Array (FieldInstantiationData ValueBinding))

def ValueBinding.value : ValueBinding → RuntimeId .value
  | .direct value _ => value
  | .atRole binding _ | .inField _ binding .. | .inApplication binding ..
  | .inProjection _ binding .. => binding.value

def ValueBinding.role : ValueBinding → SourceLayout
  | .direct _ role | .atRole _ role | .inField _ _ role .. | .inApplication _ role ..
  | .inProjection _ _ role .. => role

/-- Retain the actual node and field associations under a prepared consuming source role.
Reuse: ValueBinding.atRole, shared by graph rebinding and native environment capture. -/
opaque ValueBinding.withRole (binding : ValueBinding) (role : SourceLayout) :
    Except String ValueBinding := do
  if role.kind == .proof then throw "a source proof has no computational value binding"
  return match binding with
    | .atRole underlying _ => .atRole underlying role
    | _ => .atRole binding role

abbrev FieldInstantiation := FieldInstantiationData ValueBinding

/-- Source type families are instantiated by these exact references, never decoded Lean terms. -/
def ValueBinding.instantiations : ValueBinding → Array FieldInstantiation
  | .direct .. => #[]
  | .atRole binding _ => binding.instantiations
  | .inField id binding _ association field preceding =>
    binding.instantiations.push ⟨id, association, field, preceding, none⟩
  | .inApplication binding .. => binding.instantiations
  | .inProjection _ binding _ _ _ _ _ dependencies => binding.instantiations ++ dependencies

structure ApplicationInstantiation where
  private mk ::
  association : ApplicationAssociation
  parameters : Array (Option ValueBinding)
  applicationParameters : Array (Option ValueBinding)
  arguments : Array (Option ValueBinding)
  callable : Option ValueBinding
  access : Option ValueBinding

/-- Retain every consuming application in order, including earlier views of an aliased node. -/
def ValueBinding.applications : ValueBinding → Array ApplicationInstantiation
  | .direct .. => #[]
  | .atRole binding _ | .inField _ binding .. | .inProjection _ binding .. =>
    binding.applications
  | .inApplication binding _ association parameters applicationParameters arguments callable access _ =>
    binding.applications.push ⟨association, parameters, applicationParameters, arguments, callable, access⟩

/-- Field and application identities share one ordered role chain on the same actual node. -/
def ValueBinding.associationIds : ValueBinding → Array (RuntimeId .association)
  | .direct .. => #[]
  | .atRole binding _ => binding.associationIds
  | .inField id binding .. => binding.associationIds.push id
  | .inApplication binding _ association .. => binding.associationIds.push association.id
  | .inProjection id binding .. => binding.associationIds.push id

/-- The exact record accesses retained in binding order, through later aliases and projections.
Reuse: the immutable binding chain; no expression or value search selects a parent. -/
def ValueBinding.projectionAccesses : ValueBinding → Array (ValueBinding × Array Name)
  | .direct .. => #[]
  | .atRole binding _ | .inField _ binding .. | .inApplication binding .. =>
    binding.projectionAccesses
  | .inProjection _ binding _ parent path _ _ _ => binding.projectionAccesses.push (parent, path)

/-- The selected binding before this access added consuming associations.
Reuse: the exact projection producer, retained parent identities and native paths. This baseline
lets a later reply retain an already visible captured value without naming fresh access IDs. -/
def ValueBinding.projectionBasis (value parent : ValueBinding) (path : Array Name) :
    Option ValueBinding :=
  match value with
  | .direct .. => none
  | .atRole binding _ | .inField _ binding .. | .inApplication binding .. =>
    binding.projectionBasis parent path
  | .inProjection _ binding _ selected selectedPath basis _ _ =>
    if selected.value == parent.value && selected.associationIds == parent.associationIds &&
        selectedPath == path then some basis
    else binding.projectionBasis parent path

/-- A projection view retains its exact pre-access binding. This relation identifies an
intermediate parent without erasing unrelated field or application associations. -/
private def ValueBinding.projectionParent : ValueBinding → ValueBinding
  | .atRole binding _ => binding.projectionParent
  | .inProjection _ _ _ _ _ basis _ _ => basis.projectionParent
  | binding => binding

private def valueKey : Name := `CasCompiler.lower.value

def markedKey? (data : MData) : Option Nat :=
  match data.find valueKey with
  | some (.ofNat key) => some key
  | _ => none

/-- Associate an actual retained value with one occurrence of its checked source term.
Reuse: Lean MData, preserved by closure and ignored by kernel conversion, as sourceReference. -/
def markValue (marks : IO.Ref (Array ValueBinding)) (value : ValueBinding) (expression : Expr) :
    BaseIO Expr := do
  let key ← marks.modifyGet fun values => (values.size, values.push value)
  return .mdata (KVMap.empty.setNat valueKey key) expression

private def selectedReferences (indices : Array Nat) (values : Array (Option ValueBinding)) :
    Except String (Array ValueBinding) := do
  let mut selected := #[]
  for index in indices do
    let some value := values[index]?
      | throw "a result dependency is outside its complete reference table"
    if let some value := value then selected := selected.push value
  return selected

structure ContainerSlot where
  path : Array InputPathStep
  binding : ValueBinding
  /-- Computational field position, or an independent retained reference. -/
  fieldIndex : Option Nat

/-- Literal packet structure, typed substitution slots and any actual field/callable bindings.
`none` fields denotes a descriptor without native field data; `some #[]` is an actual empty
record. A source record schema alone does not create computational field identities. -/
structure ValueContainer where
  private mk ::
  template : Json
  slots : Array ContainerSlot
  fields : Option (Array ValueBinding)
  callable : Option ValueBinding

/-- Replace only a previously located JSON position.
Reference: Lean.Json array/object operations and CasContract.Port's InputPathStep grammar. -/
private def replacePosition (json : Json) (path : List InputPathStep) (replacement : Json) :
    Except String Json := do
  match path, json with
  | [], _ => return replacement
  | .index index :: rest, .arr values =>
    let some value := values[index]? | throw "the container position is outside its array"
    return .arr (values.set! index (← replacePosition value rest replacement))
  | .field name :: rest, .obj fields =>
    let value ← json.getObjVal? name
    let value ← replacePosition value rest replacement
    return Json.mkObj (fields.toList.map fun (key, entry) =>
      (key, if key == name then value else entry))
  | _, _ => throw "the container position does not follow the retained JSON structure"

/-- A retained literal cannot carry ambient reference or native-token authority.
Reference: CasContract.Port.validateResultRefs and the runtime immediate-control JSON walk. -/
partial def checkLiteral (json : Json) : Except String Unit := do
  if let .ok tag := json.getObjValAs? String "ctor" then
    if #["scopeRef", "inputRef", "resultRef", "opaqueData", "deferredData"].contains tag then
      throw "the container has an unbound reference, native token or deferred control"
  match json with
  | .arr entries => for entry in entries do checkLiteral entry
  | .obj entries => for (_, entry) in entries.toList do checkLiteral entry
  | _ => pure ()

private def makeContainer (template : Json) (slots : Array ContainerSlot)
    (fields : Option (Array ValueBinding)) (callable : Option ValueBinding) :
    Except String ValueContainer := do
  let mut paths : Array (List InputPathStep) := #[]
  let mut template := template
  for slot in slots do
    if let some index := slot.fieldIndex then
      let some stored := fields
        | throw "a descriptor slot cannot claim an unavailable native field"
      let some field := stored[index]?
        | throw "the container slot is outside its source field table"
      unless slot.binding.value == field.value &&
          slot.binding.associationIds == field.associationIds do
        throw "the container slot does not retain its declared source field"
    let path := slot.path.toList
    if paths.any (fun previous => previous.isPrefixOf path || path.isPrefixOf previous) then
      throw "container reference positions overlap"
    template ← replacePosition template path .null
    paths := paths.push path
  checkLiteral template
  if let some binding := callable then
    unless binding.role.kind == .function do
      throw "the container callable has no prepared function interface"
  return ⟨template, slots, fields, callable⟩

/-- Substitute freshly encoded references without rebuilding literal data from a source term. -/
opaque ValueContainer.fill (container : ValueContainer) (replacements : Array Json) :
    Except String Json := do
  unless replacements.size == container.slots.size do
    throw "container substitution does not match its exact reference arity"
  let mut packet := container.template
  for slot in container.slots, replacement in replacements do
    packet ← replacePosition packet slot.path.toList replacement
  return packet

inductive ValueData
  | portable (bytes : ByteArray)
  | product (fields : Array ValueBinding)
  | container (value : ValueContainer)
  | closure (program : RuntimeId .program) (captures : Array ValueBinding)
  | ownedToken (owner : ConnectionGeneration) (token : String) (captures : Array ValueBinding)

/-- The actual stored record table, distinct from a descriptor's native source schema.
Closures and native tokens keep their existing lazy interfaces outside this table. -/
def ValueData.storedFields? : ValueData → Option (Array ValueBinding)
  | .product fields => some fields
  | .container value => value.fields
  | _ => none

/-- Payload construction stamps native exports from the actual supplying connection. -/
structure ValuePayload where
  private mk ::
  data : ValueData

def ValuePayload.portable (bytes : ByteArray) : ValuePayload := ⟨.portable bytes⟩

def ValuePayload.product (fields : Array ValueBinding) : ValuePayload := ⟨.product fields⟩

opaque ValuePayload.container (template : Json) (slots : Array ContainerSlot)
    (fields : Array ValueBinding) (callable : Option ValueBinding) : Except String ValuePayload := do
  return ⟨.container (← makeContainer template slots (some fields) callable)⟩

/-- Retain a named source value and its actual packet inputs without fabricating its fields.
The public packet grammar is unchanged; no native projection or callable export is supplied. -/
opaque ValuePayload.descriptor (template : Json) (slots : Array ContainerSlot) :
    Except String ValuePayload := do
  return ⟨.container (← makeContainer template slots none none)⟩

def ValuePayload.closure (program : RuntimeId .program)
    (captures : Array ValueBinding) : ValuePayload := ⟨.closure program captures⟩

opaque ValuePayload.ownedExport (connection : Connection) (token : String)
    (captures : Array ValueBinding) : ValuePayload :=
  ⟨.ownedToken connection.generation token captures⟩

/-- Actual argument references and this result role's native formal dependency slots. -/
structure ApplicationOrigin where
  private mk ::
  layout : ApplicationLayout
  parameters : Array (Option ValueBinding)
  arguments : Array (Option ValueBinding)
  path : Array Name
  dependencies : Array Nat
  contextDependencies : Array Nat
  callable : Option ValueBinding

/-- Keep all formal slots and actual references; proof slots have no payload.
Reuse: ApplicationLayout's native telescope and existing ValueBinding identities. -/
opaque ApplicationOrigin.ofArguments (layout : ApplicationLayout)
    (parameters arguments : Array (Option ValueBinding)) (callable : Option ValueBinding) :
    Except String ApplicationOrigin := do
  unless parameters.size == layout.result.source.context.entries.size do
    throw "application provenance requires its complete original context table"
  unless arguments.size == layout.arguments.size do
    throw "application provenance requires the complete argument table"
  for argument in arguments, prepared in layout.arguments do
    if prepared.wireIndex.isNone && argument.isSome then
      throw "a formal proof has no application provenance payload"
  return ⟨layout, parameters, arguments, #[], layout.resultDependencies,
    layout.resultContextDependencies, callable⟩

/-- Keep the original arguments while selecting this source field's own dependencies. -/
opaque ApplicationOrigin.forSource (origin : ApplicationOrigin) (parent source : SourceLayout) :
    MetaM ApplicationOrigin := do
  let path := origin.path ++ (← parent.projectionPathTo source)
  let dependencies ← origin.layout.dependenciesAt path
  return { origin with
    path
    dependencies := dependencies.arguments
    contextDependencies := dependencies.context }

/-- Continue the same source application through an actual record's native field.
The stored result identity licenses access through later source bindings; no source replay occurs. -/
opaque ApplicationOrigin.forProjection (origin : ApplicationOrigin) (projection : Name) :
    MetaM ApplicationOrigin := do
  let path := origin.path.push projection
  let dependencies ← origin.layout.dependenciesAt path
  return { origin with
    path
    dependencies := dependencies.arguments
    contextDependencies := dependencies.context }

private def ApplicationInstantiation.origin (value : ApplicationInstantiation) : ApplicationOrigin :=
  ⟨value.association.layout, value.applicationParameters, value.arguments,
    value.association.path, value.association.dependencies, value.association.contextDependencies,
    value.callable⟩

structure ValueOrigin where
  occurrence : RuntimeId .occurrence
  program : RuntimeId .program
  role : SourceLayout
  parameters : Array (Option ValueBinding)
  application : Option ApplicationOrigin := none
  access : Option ValueBinding := none
  accessPath : Array Name := #[]

/-- Visibility keeps the complete context, stored callable and argument reference planes. -/
def ValueOrigin.references (origin : ValueOrigin) : Array ValueBinding :=
  origin.parameters.filterMap id ++
    (match origin.access with | none => #[] | some value => #[value]) ++
    match origin.application with
    | none => #[]
    | some application =>
      application.parameters.filterMap id ++
      (match application.callable with | none => #[] | some callable => #[callable]) ++
        application.arguments.filterMap id

/-- A tentative immutable node; whole-reply admission and receipt publication are separate. -/
structure ValueNode where
  private mk ::
  id : RuntimeId .value
  origin : ValueOrigin
  payload : ValuePayload
  owners : Array ConnectionGeneration

private def ValueData.references : ValueData → Array ValueBinding
  | .portable _ => #[]
  | .product fields => fields
  | .container value => value.slots.map (·.binding) ++ value.fields.getD #[] ++
      match value.callable with | none => #[] | some binding => #[binding]
  | .closure _ captures | .ownedToken _ _ captures => captures

def ValueNode.references (node : ValueNode) : Array ValueBinding :=
  node.origin.references ++ node.payload.data.references

/-- Persistent storage uses Lean's immutable HashMap; the live ledger holds no copy.
Reference: Lean v4.33.0 Std/Data/HashMap/Basic.lean, `HashMap.insert` and `getElem?`. -/
structure ValueGraph where
  private mk ::
  worker : String
  private nodes : Std.HashMap (RuntimeId .value) ValueNode
  private associations : Std.HashSet (RuntimeId .association)
  private projections : Std.HashMap (RuntimeId .value) (Array ValueBinding)
  private projectionViews : Std.HashMap (RuntimeId .value) (Array ValueBinding)
  private revision : Option (RuntimeId .revision)

def ValueGraph.empty (supply : IdentitySupply) : ValueGraph := ⟨supply.worker, {}, {}, {}, {}, none⟩

/-- Every value or association append has a fresh revision.
Reference: IdentitySupply monotone allocation and persistent HashMap/HashSet insertion. -/
def ValueGraph.sameRevision (left right : ValueGraph) : Bool :=
  left.worker == right.worker && left.revision == right.revision

def ValueGraph.find (graph : ValueGraph) (id : RuntimeId .value) : Option ValueNode :=
  graph.nodes[id]?

/-- Visit immutable instantiation identities, retaining distinct roles on aliased nodes.
Reference: Lean v4.33.0 Lean/Util/ForEachExpr.lean, memoized traversal of shared DAGs.
Reuse: Std.HashSet with worker-issued identities in place of expression keys. -/
private partial def ValueGraph.checkBinding (graph : ValueGraph) (binding : ValueBinding)
    (visited : Std.HashSet (RuntimeId .association)) :
    Except String (Std.HashSet (RuntimeId .association)) := do
  match binding with
  | .direct value _ =>
    unless (graph.find value).isSome do throw "the value reference is outside the visible graph"
    return visited
  | .atRole underlying _ => graph.checkBinding underlying visited
  | .inProjection id underlying _ parent path _ fields dependencies =>
    if visited.contains id then return visited
    unless graph.associations.contains id && id.worker == graph.worker && !path.isEmpty do
      throw "the projection association is outside the visible graph"
    let mut visited ← graph.checkBinding underlying (visited.insert id)
    visited ← graph.checkBinding parent visited
    for field in fields do visited ← graph.checkBinding field visited
    for dependency in dependencies do
      unless graph.associations.contains dependency.id && dependency.id.worker == graph.worker &&
          dependency.association.id.worker == graph.worker &&
          dependency.field.sourceIndex == dependency.preceding.size do
        throw "a projected field dependency lost its original association or prefix"
      for previous in dependency.preceding do
        if let some previous := previous then visited ← graph.checkBinding previous visited
    return visited
  | .inField id underlying _ association field preceding =>
    if visited.contains id then return visited
    unless graph.associations.contains id do
      throw "the field association is outside the visible graph"
    unless id.worker == graph.worker && association.id.worker == graph.worker &&
        field.sourceIndex == preceding.size do
      throw "the field association has a foreign worker or incomplete source prefix"
    let mut visited ← graph.checkBinding underlying (visited.insert id)
    for previous in preceding do
      if let some previous := previous then visited ← graph.checkBinding previous visited
    return visited
  | .inApplication underlying _ association parameters applicationParameters arguments callable access fields =>
    if visited.contains association.id then return visited
    unless graph.associations.contains association.id do
      throw "the application association is outside the visible graph"
    unless association.id.worker == graph.worker && association.program.worker == graph.worker &&
        association.occurrence.worker == graph.worker do
      throw "the application association belongs to a different worker"
    let mut visited ← graph.checkBinding underlying (visited.insert association.id)
    let references := parameters.filterMap id ++ applicationParameters.filterMap id ++
      arguments.filterMap id ++
      (match callable with | none => #[] | some value => #[value]) ++
      (match access with | none => #[] | some value => #[value]) ++ fields
    for reference in references do visited ← graph.checkBinding reference visited
    return visited

private def ValueGraph.require (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueNode := do
  discard <| graph.checkBinding binding {}
  let some node := graph.find binding.value
    | throw "the value reference is outside the visible graph"
  return node

/-- Read only a projection relation published in this immutable graph. Later consuming
aliases may extend its exact parent chain; divergent chains cannot select each other's fields.
Intermediate projection views use their recorded basis, never native declarations or values.
The returned baseline keeps its own owner closure; the parent supplies visibility only. -/
opaque ValueGraph.projected? (graph : ValueGraph) (parent : ValueBinding) (path : Array Name) :
    Except String (Option ValueBinding) := do
  discard <| graph.require parent
  let parent := parent.projectionParent
  discard <| graph.require parent
  let mut selected : Option (Nat × ValueBinding) := none
  for retained in graph.projections[parent.value]?.getD #[] do
    let .inProjection _ _ _ original selectedPath basis _ _ := retained
      | throw "the retained projection index has no actual projection relation"
    let original := original.projectionParent
    unless original.value == parent.value && selectedPath == path &&
        original.associationIds.toList.isPrefixOf parent.associationIds.toList do continue
    if let some (length, _) := selected then
      if original.associationIds.size ≤ length then continue
    discard <| graph.require retained
    discard <| graph.require basis
    selected := some (original.associationIds.size, basis)
  return selected.map (·.2)

/-- Read an already published access under its exact original parent and complete association
chain. The original field baseline remains separate: an earlier or sibling consuming parent
cannot supply this view, and role aliases alone do not change its reference identity.
Reuse: bindProjection's sealed native path and immutable association membership. -/
opaque ValueGraph.projectedAccess? (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : Except String (Option ValueBinding) := do
  discard <| graph.require parent
  for retained in graph.projectionViews[parent.value]?.getD #[] do
    let .inProjection _ _ _ original selectedPath _ _ _ := retained
      | throw "the retained access index has no actual projection relation"
    unless original.value == parent.value && original.associationIds == parent.associationIds &&
        selectedPath == path do continue
    discard <| graph.require retained
    return some retained
  return none

/-- Read source application provenance only from the visible binding and its immutable node. -/
opaque ValueGraph.applicationOrigin (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option ApplicationOrigin) := do
  let node ← graph.require binding
  if let some application := binding.applications.back? then return some application.origin
  return node.origin.application

/-- Recover only the baseline recorded by this exact access, including a directly staged reply.
An origin fallback is permitted only for its actual retained parent and native path. -/
partial def ValueGraph.projectionBasis (graph : ValueGraph) (binding parent : ValueBinding)
    (path : Array Name) : Except String (Option ValueBinding) := do
  let node ← graph.require binding
  discard <| graph.require parent
  if let some basis := binding.projectionBasis parent path then return some basis
  for (selected, suffix) in binding.projectionAccesses.reverse do
    if suffix.isEmpty || suffix.size ≥ path.size then continue
    let initialPath := path.extract 0 (path.size - suffix.size)
    unless path.extract initialPath.size path.size == suffix do continue
    if (← graph.projectionBasis selected parent initialPath).isNone then continue
    if let some basis := binding.projectionBasis selected suffix then return some basis
  let some selected := node.origin.access | return none
  let produced := ValueBinding.direct node.id node.origin.role
  if selected.value == parent.value && selected.associationIds == parent.associationIds &&
      node.origin.accessPath == path then return some produced
  let suffix := node.origin.accessPath
  if suffix.isEmpty || suffix.size ≥ path.size then return none
  let initialPath := path.extract 0 (path.size - suffix.size)
  if path.extract initialPath.size path.size == suffix &&
      (← graph.projectionBasis selected parent initialPath).isSome then return some produced
  return none

/-- The latest retained projection before any newer consuming application.
An application begins another source continuation, even when it returns the same actual node. -/
private def ValueBinding.latestProjection : ValueBinding →
    Option (SourceLayout × ValueBinding × Array Name)
  | .atRole binding _ | .inField _ binding .. => binding.latestProjection
  | .inProjection _ _ source parent path _ _ _ => some (source, parent, path)
  | .direct .. | .inApplication .. => none

/-- The latest actual projection retains its immutable source role, parent and native path.
Later role aliases cannot rewrite this source witness; a newer application starts a different
continuation. Reuse: projectionBasis and the immutable node's original access record. -/
opaque ValueGraph.projectionSelection (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option (SourceLayout × ValueBinding × Array Name)) := do
  let node ← graph.require binding
  let selected ← match binding.latestProjection with
    | some selected => pure (some selected)
    | none =>
      if !binding.applications.isEmpty then return none
      pure (node.origin.access.map fun parent =>
        (node.origin.role, parent, node.origin.accessPath))
  let some (source, parent, path) := selected | return none
  if path.isEmpty then throw "a retained projection producer lost its native field path"
  let some _ ← graph.projectionBasis binding parent path
    | throw "a retained projection producer lost its exact parent and field selection"
  return some (source, parent, path)

/-- Resume only the exact recorded projection producer, preserving the existing reader API. -/
opaque ValueGraph.projectionOrigin (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option (ValueBinding × Array Name)) := do
  return (← graph.projectionSelection binding).map fun (_, parent, path) => (parent, path)

private structure BindingOwners where
  instantiations : Std.HashSet (RuntimeId .association) := {}
  values : Std.HashSet (RuntimeId .value) := {}
  generations : Std.HashSet ConnectionGeneration := {}
  owners : Array ConnectionGeneration := #[]

private partial def ValueGraph.bindingOwners (graph : ValueGraph) (binding : ValueBinding)
    (state : BindingOwners) : Except String BindingOwners := do
  match binding with
  | .direct value _ =>
    if state.values.contains value then return state
    let some node := graph.find value
      | throw "the value reference is outside the visible graph"
    let mut state := { state with values := state.values.insert value }
    for owner in node.owners do
      unless state.generations.contains owner do
        state := { state with
          generations := state.generations.insert owner
          owners := state.owners.push owner }
    return state
  | .atRole underlying _ => graph.bindingOwners underlying state
  | .inProjection id underlying _ _ _ _ fields dependencies =>
    if state.instantiations.contains id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert id }
    for field in fields do state ← graph.bindingOwners field state
    for dependency in dependencies do
      let references ← selectedReferences dependency.precedingDependencies dependency.preceding
      for previous in references do
        state ← graph.bindingOwners previous state
    return state
  | .inField id underlying _ _ field preceding =>
    if state.instantiations.contains id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert id }
    for index in field.precedingDependencies do
      let some previous := preceding[index]?
        | throw "the dependent field is missing a preceding source position"
      if let some previous := previous then
        state ← graph.bindingOwners previous state
    return state
  | .inApplication underlying _ association _ applicationParameters arguments _ _ fields =>
    if state.instantiations.contains association.id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert association.id }
    let dependencies := (← selectedReferences association.contextDependencies applicationParameters) ++
      (← selectedReferences association.dependencies arguments) ++ fields
    for dependency in dependencies do state ← graph.bindingOwners dependency state
    return state

/-- Derive dependencies from visible nodes, rather than accepting owner claims from a reply. -/
opaque ValueGraph.requiredOwners (graph : ValueGraph) (bindings : Array ValueBinding) :
    Except String (Array ConnectionGeneration) := do
  let mut visible : Std.HashSet (RuntimeId .association) := {}
  for binding in bindings do
    visible ← graph.checkBinding binding visible
  let mut state : BindingOwners := {}
  for binding in bindings do state ← graph.bindingOwners binding state
  return state.owners

/-- Retain the same node under an already prepared consuming role. -/
opaque ValueGraph.rebind (graph : ValueGraph) (binding : ValueBinding) (role : SourceLayout) :
    Except String ValueBinding := do
  discard <| graph.require binding
  binding.withRole role

private def ValueBinding.applicationFields : ValueBinding → Option (Array ValueBinding)
  | .direct .. => none
  | .atRole binding _ | .inField _ binding .. => binding.applicationFields
  | .inApplication _ _ _ _ _ _ _ _ fields => some fields
  | .inProjection _ _ _ _ _ _ fields _ => some fields

/-- Projection selects the retained field view, independently of unrelated field owners. -/
opaque ValueGraph.project (graph : ValueGraph) (binding : ValueBinding) (index : Nat) :
    Except String ValueBinding := do
  let node ← graph.require binding
  match node.payload.data with
  | .product fields =>
    let fields := binding.applicationFields.getD fields
    let some field := fields[index]?
      | throw "the projection is outside the retained product"
    return field
  | .container value =>
    let some stored := value.fields
      | throw "the descriptor has no stored native fields"
    let fields := binding.applicationFields.getD stored
    let some field := fields[index]?
      | throw "the projection is outside the retained container"
    return field
  | _ => throw "the retained payload has no stored product fields"

/-- One pure traversal supplies both the stored frontier and the exact visited parent bindings.
The temporary parents are used only while preparing descendant dependency views. -/
private def projectionWalk (graph : ValueGraph) (parent : ValueBinding) (path : Array Name) :
    Except String (Option (ValueBinding × Array Name) × Array (ValueBinding × Array Name)) := do
  discard <| graph.requiredOwners #[parent]
  let mut value := parent
  let mut parents := #[]
  for projection in path, offset in [:path.size] do
    let remaining := path.extract offset path.size
    parents := parents.push (value, remaining)
    let some field := value.role.fields.find? (·.projection == projection)
      | throw "a native field path lost its actual record interface"
    let some index := field.wireIndex
      | throw "a computational field path selected a proof field"
    let some node := graph.find value.value
      | throw "the selected value is outside the visible graph"
    if node.payload.data.storedFields?.isNone then
      if let some retained ← graph.projected? value #[projection] then
        value := retained
        continue
    match node.payload.data with
    | .closure .. | .ownedToken .. => return (some (value, remaining), parents)
    | .container container =>
      if container.fields.isNone then return (none, parents)
      value ← graph.project value index
    | .product .. => value ← graph.project value index
    | .portable .. => throw "the selected value has no native record access interface"
  return (some (value, #[]), parents)

/-- Follow an exact native path through stored or already published fields without execution.
The returned baseline and remaining lazy path keep the existing read-only query contract. -/
opaque ValueGraph.projectionFrontier (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : Except String (Option (ValueBinding × Array Name)) := do
  return (← projectionWalk graph parent path).1

/-- Carry only the original field-prefix requirements of this selected descendant.
The source paths and original associations select these views; no payload equality is used. -/
private def projectionFieldDependencies (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) (selected : ValueBinding) : MetaM (Array FieldInstantiation) := do
  let (_, parents) ← IO.ofExcept <| (projectionWalk graph parent path).mapError IO.userError
  let mut dependencies : Array FieldInstantiation := #[]
  for (parent, remaining) in parents do
    for field in parent.instantiations do
      if field.field.precedingDependencies.isEmpty then continue
      let path := field.projectionPath ++ remaining
      if (selected.instantiations ++ dependencies).any (fun previous =>
          previous.id == field.id && previous.projectionPath == path) then continue
      let view ← field.field.dependencyView path
      dependencies := dependencies.push { field with view := some view }
  return dependencies

/-- Follow stored callable slots to actual code/token data, retaining the complete outer value.
The append-only graph supplies existing references; no source expression reconstructs a callable.
Reuse: ValueGraph.require and Lean v4.33.0 Std.HashSet for exact reference traversal. -/
private partial def storedCallable (graph : ValueGraph) (binding : ValueBinding)
    (visited : Std.HashSet (RuntimeId .value)) : Except String ValueBinding := do
  if visited.contains binding.value then throw "the retained callable references form a cycle"
  let node ← graph.require binding
  match node.payload.data with
  | .closure .. | .ownedToken .. => return binding
  | .container value =>
    let some callable := value.callable | throw "the container has no stored callable"
    storedCallable graph callable (visited.insert binding.value)
  | .portable _ | .product _ => throw "the retained payload has no callable code or token"

opaque ValueGraph.callable (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueBinding := storedCallable graph binding {}

/-- Stage one node without modifying the prior graph or creating a completion witness.
References must already be visible; ownership is derived from those exact nodes and the
actual supplying connection. Payload equality never participates in node allocation. -/
opaque ValueGraph.stage (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (payload : ValuePayload) : IO (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throw <| IO.userError "value staging belongs to a different worker"
  if origin.role.kind == .proof then
    throw <| IO.userError "a source proof has no computational payload"
  unless origin.parameters.size == origin.role.source.context.entries.size do
    throw <| IO.userError "value staging requires the complete producing context table"
  discard <| IO.ofExcept <|
    (graph.requiredOwners origin.references).mapError IO.userError
  let mut dependencies := payload.data.references
  let (contextDependencies, contextParameters) := match origin.application with
    | none => (origin.role.contextDependencies, origin.parameters)
    | some application => (application.contextDependencies, application.parameters)
  dependencies := dependencies ++ (← IO.ofExcept <|
    (selectedReferences contextDependencies contextParameters).mapError IO.userError)
  if let some application := origin.application then
    dependencies := dependencies ++ (← IO.ofExcept <|
      (selectedReferences application.dependencies application.arguments).mapError IO.userError)
  let mut owners ← IO.ofExcept <|
    (graph.requiredOwners dependencies).mapError IO.userError
  match payload.data with
  | .ownedToken owner _ _ =>
    unless owner.worker == graph.worker do
      throw <| IO.userError "the supplying connection belongs to a different worker"
    unless owners.contains owner do owners := owners.push owner
  | .closure program _ =>
    unless program.worker == graph.worker do
      throw <| IO.userError "the closure program belongs to a different worker"
  | .portable _ | .product _ | .container _ => pure ()
  let id ← supply.fresh .value
  let node : ValueNode := ⟨id, origin, payload, owners⟩
  let revision ← supply.fresh .revision
  return ({ graph with
    nodes := graph.nodes.insert id node
    revision := some revision }, .direct id origin.role)

/-- Availability reads current liveness without rewriting the immutable payload. -/
def ValueGraph.isAvailable (graph : ValueGraph) (owners : OwnerRegistry)
    (binding : ValueBinding) : BaseIO Bool := do
  if owners.worker != graph.worker then return false
  let .ok dependencies := graph.requiredOwners #[binding] | return false
  owners.allAlive dependencies

/-- A computational candidate indexed by its prepared layout, retaining its actual root. -/
structure CandidateResponse (source : SourceLayout) where
  private mk ::
  root : ValueBinding

/-- Check the retained operational shape and bind the prepared source role.
Source: execution contract v2 §2 and data model §5. Scope, lifecycle and whole-reply admission
are separate boundaries. Native exports retain lazy field access through their actual root. -/
opaque CandidateResponse.ofValue (source : SourceLayout) (graph : ValueGraph)
    (value : ValueBinding) : Except String (CandidateResponse source) := do
  let node ← graph.require value
  match source.kind, node.payload.data with
  | .proof, _ => throw "a source proof has no computational response"
  | .function, .closure _ _ | .function, .ownedToken _ _ _ => pure ()
  | .function, .container _ => discard <| graph.callable value
  | .function, _ => throw "the candidate has no retained callable payload"
  | .record, .product fields =>
    let expected := source.fields.filter (·.wireIndex.isSome)
    unless fields.size == expected.size do
      throw "the candidate record does not match its prepared field arity"
  | .record, .container container =>
    if let some fields := container.fields then
      let expected := source.fields.filter (·.wireIndex.isSome)
      unless fields.size == expected.size do
        throw "the candidate container does not match its prepared field arity"
  | .record, .closure _ _ | .record, .ownedToken _ _ _ => pure ()
  | .record, _ => throw "the candidate has no retained record interface"
  | .data, _ | .typeValue, _ => pure ()
  return ⟨← graph.rebind value source⟩

/-- Associate an existing result with a prepared application without replacing its node.
Stored fields are exact projections with their own prepared consuming associations.
Reuse: CandidateResponse, immutable graph membership and source-derived dependency selection. -/
opaque ValueGraph.bindApplication (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (value : ValueBinding) (fields : Array ValueBinding) :
    IO (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throw <| IO.userError "application binding belongs to a different worker"
  let some application := origin.application
    | throw <| IO.userError "application binding requires a prepared application origin"
  unless origin.parameters.size == origin.role.source.context.entries.size do
    throw <| IO.userError "application binding requires the complete source context table"
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue origin.role graph value).mapError IO.userError
  let some node := graph.find candidate.root.value
    | throw <| IO.userError "the application result is outside the visible graph"
  let stored := if origin.role.kind == .record then
      (node.payload.data.storedFields?.getD #[]).size
    else 0
  unless fields.size == stored do
    throw <| IO.userError "the application result requires its complete stored field views"
  for field in fields, index in [:fields.size] do
    let original ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
    unless original.value == field.value &&
        original.associationIds.toList.isPrefixOf field.associationIds.toList do
      throw <| IO.userError "an application field view changed its original stored reference"
  discard <| IO.ofExcept <|
    (graph.requiredOwners (origin.references ++ fields)).mapError IO.userError
  let association : ApplicationAssociation := ⟨← supply.fresh .association,
    origin.program, origin.occurrence, application.layout, application.path, application.dependencies,
    application.contextDependencies⟩
  let binding := ValueBinding.inApplication candidate.root origin.role association
    origin.parameters application.parameters application.arguments application.callable origin.access fields
  let revision ← supply.fresh .revision
  let graph := { graph with
    associations := graph.associations.insert association.id
    revision := some revision }
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (graph, binding)

/-- Attach an exact prepared projection to an existing node and its stored field views.
The parent is retained for visibility and source selection, not as a whole-record owner demand.
Reuse: bindApplication for original application data, CandidateResponse and immutable associations. -/
opaque ValueGraph.bindProjection (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (value : ValueBinding) (fields : Array ValueBinding) :
    MetaM (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throwError "projection binding belongs to a different worker"
  let some parent := origin.access
    | throwError "projection binding requires its selected parent"
  if origin.accessPath.isEmpty then
    throwError "projection binding requires its exact source path"
  discard <| IO.ofExcept <|
    (graph.requiredOwners origin.references).mapError IO.userError
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue origin.role graph value).mapError IO.userError
  let some node := graph.find candidate.root.value
    | throwError "the projected value is outside the visible graph"
  let prior ← IO.ofExcept <|
    (graph.projected? parent origin.accessPath).mapError IO.userError
  if let some prior := prior then
    unless candidate.root.value == prior.value &&
        prior.associationIds.toList.isPrefixOf candidate.root.associationIds.toList do
      throwError "the projection changed its retained field reference"
  -- New consuming views may enrich the returned value, but an existing source field
  -- keeps its original stored/published baseline. Both sources constrain this candidate.
  let available ← IO.ofExcept <|
    (graph.projectionFrontier parent origin.accessPath).mapError IO.userError
  let baseline : ValueBinding ← match available with
    | some (selected, #[]) => do
      unless selected.value == candidate.root.value &&
          selected.associationIds.toList.isPrefixOf candidate.root.associationIds.toList do
        throwError "the projection changed its retained field reference"
      match prior with
      | none => pure selected
      | some prior =>
        if prior.associationIds.toList.isPrefixOf selected.associationIds.toList then
          pure selected
        else if selected.associationIds.toList.isPrefixOf prior.associationIds.toList then
          pure prior
        else throwError "the projection changed its retained field reference"
    | _ => pure (prior.getD candidate.root)
  let stored := if origin.role.kind == .record then
      (node.payload.data.storedFields?.getD #[]).size
    else 0
  unless fields.size == stored do
    throwError "projection binding requires its complete stored field views"
  for field in fields, index in [:fields.size] do
    let original ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
    unless original.value == field.value &&
        original.associationIds.toList.isPrefixOf field.associationIds.toList do
      throwError "a projection field view changed its original stored reference"
  let dependencies ← projectionFieldDependencies graph parent origin.accessPath candidate.root
  let (graph, value) ← if origin.application.isSome then
      graph.bindApplication supply origin candidate.root fields
    else pure (graph, candidate.root)
  let id ← supply.fresh .association
  let binding := ValueBinding.inProjection id value origin.role parent origin.accessPath
    baseline fields dependencies
  let projections := if prior.isSome then graph.projections else
    let key := parent.projectionParent.value
    graph.projections.insert key ((graph.projections[key]?.getD #[]).push binding)
  -- Preserve a distinct published access for each exact parent chain. The baseline cache
  -- above deliberately keeps its original binding, independently of these consuming views.
  let previousAccess ← IO.ofExcept <|
    (graph.projectedAccess? parent origin.accessPath).mapError IO.userError
  let projectionViews := if previousAccess.isSome then graph.projectionViews else
    graph.projectionViews.insert parent.value
      ((graph.projectionViews[parent.value]?.getD #[]).push binding)
  let graph := { graph with
    associations := graph.associations.insert id
    projections
    projectionViews
    revision := some (← supply.fresh .revision) }
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (graph, binding)

/-- Ordered actual constructor selections; proof positions retain their formal slots.
This is record storage, not a whole-reply admission or correctness witness. -/
structure RecordPrefix where
  private mk ::
  association : RecordAssociation
  private identities : IdentitySupply
  private selections : Array (Option ValueBinding)

private def RecordPrefix.skipProofs (record : RecordPrefix) : RecordPrefix := Id.run do
  let mut selections := record.selections
  while selections.size < record.association.layout.fields.size do
    let some field := record.association.layout.fields[selections.size]? | break
    if field.field.kind != .proof then break
    selections := selections.push none
  return { record with selections }

/-- Allocate a fresh association before recording any actual field selections.
Reuse: the worker IdentitySupply and complete source-prepared RecordLayout. -/
opaque RecordPrefix.begin (supply : IdentitySupply) (program : RuntimeId .program)
    (occurrence : RuntimeId .occurrence) (layout : RecordLayout) : IO RecordPrefix := do
  unless program.worker == supply.worker && occurrence.worker == supply.worker do
    throw <| IO.userError "record preparation belongs to a different worker"
  let association : RecordAssociation := ⟨← supply.fresh .association, program, occurrence, layout⟩
  return RecordPrefix.skipProofs ⟨association, supply, #[]⟩

/-- Bind this same node at the next field and retain every preceding actual selection.
Visibility checks include the whole prefix; owner requirements follow the declared dependencies.
Reuse: CandidateResponse's operational shape check and ValueGraph reference validation. -/
opaque RecordPrefix.bind (record : RecordPrefix) (graph : ValueGraph) (value : ValueBinding) :
    IO (ValueGraph × RecordPrefix × ValueBinding) := do
  let record := record.skipProofs
  let some prepared := record.association.layout.fields[record.selections.size]?
    | throw <| IO.userError "the complete record has no further computational field"
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue prepared.layout graph value).mapError IO.userError
  let id ← record.identities.fresh .association
  let binding := ValueBinding.inField id
    candidate.root prepared.layout record.association prepared.field record.selections
  let revision ← record.identities.fresh .revision
  let graph := { graph with
    associations := graph.associations.insert id
    revision := some revision }
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (graph, ({ record with selections := record.selections.push (some binding) }).skipProofs,
    binding)

/-- Finish only a complete ordered record; no component is installed in a transaction here. -/
opaque RecordPrefix.finish (record : RecordPrefix) : Except String ValuePayload := do
  let record := record.skipProofs
  unless record.selections.size == record.association.layout.fields.size do
    throw "the dependent record is missing a required computational field"
  return .product (record.selections.filterMap id)

end CasRuntime
