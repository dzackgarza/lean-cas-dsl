module

public import CasRuntime.Execute
public import CasRuntime.Transport
public import CasRuntime.Materialize
public import CasRuntime.Encode
public import CasRuntime.Realization
public import CasCompiler.Lower

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- The worker's computational kernel: the frozen manifest and realization profile, the live
negotiated connections and the code of retained closures.
Source: execution contract v2 §1 and §2, lean-cas-dsl#69 comment 6664277464. -/
structure Kernel where
  private mk ::
  ledger : OccurrenceLedger
  root : System.FilePath
  manifest : Manifest
  manifestDigest : String
  profile : RealizationProfile
  timeoutMs : UInt32
  /-- Registrations of the manifest that name no published operation or declared backend. -/
  rejected : Array String
  private connections : IO.Ref (Std.HashMap String FramedConnection)
  codes : IO.Ref (Std.HashMap (RuntimeId .program) ClosureCode)
  marks : IO.Ref (Array ValueBinding)
  /-- The registrations actually dispatched, in order. An observation, not evidence. -/
  dispatches : IO.Ref (Array Registration)

private def referenceId : ComputationRef → String
  | .operation id => id.raw
  | .functor id => id.raw
  | .method id => id.raw
  | .construction id => id.raw
  | .morphism id => id.raw

/-- The published family that an operation address names: the family address itself, or the
address of one of its fields (`<id>#map`). An unknown address creates no operation. -/
private def publishedFamily? (state : SemanticState) (address : String) : Option ComputationRef :=
  let id := (address.splitOn "#").head!
  (state.operations.find? (·.id.raw == id) |>.map (.operation ·.id)) <|>
  (state.methods.find? (·.id.raw == id) |>.map (.method ·.id)) <|>
  (state.functors.find? (·.id.raw == id) |>.map (.functor ·.id)) <|>
  (state.constructions.find? (·.id.raw == id) |>.map (.construction ·.id)) <|>
  (state.morphisms.find? (·.id.raw == id) |>.map (.morphism ·.id))

/-- Read and freeze the manifest and profile before any invocation. No process starts here.
Without a manifest no leaf is installed. A registration is admitted when its operation is the
address of a published family and its backend is declared. Rejections are reported, and a
rejected registration is never selected. -/
opaque Kernel.load (owners : OwnerRegistry) (manifest : Option System.FilePath)
    (profile : Option Json) (timeoutMs : UInt32) : MetaM Kernel := do
  let (root, text) ← match manifest with
    | some path => pure (path.parent.getD ".", ← IO.FS.readFile path)
    | none => pure (".", "{}")
  let parsed ← IO.ofExcept <| (Json.parse text >>= Manifest.parse).mapError IO.userError
  let state ← semanticState
  let mut admitted := #[]
  let mut rejected := #[]
  for registration in parsed.registrations do
    let described :=
      s!"{registration.operation} on {registration.input} by {registration.backend}"
    if (publishedFamily? state registration.operation).isNone then
      rejected := rejected.push s!"{described}: {registration.operation} is not a published operation"
    else if !parsed.backends.any (·.name == registration.backend) then
      rejected := rejected.push
        s!"{described}: the backend {registration.backend} is not declared in the manifest"
    else admitted := admitted.push registration
  let installed := { parsed with registrations := admitted }
  return ⟨← OccurrenceLedger.new owners, root, installed, ← sha256Hex text,
    ← RealizationProfile.prepare installed profile, timeoutMs, rejected, ← IO.mkRef {},
    ← IO.mkRef {}, ← IO.mkRef #[], ← IO.mkRef #[]⟩

/-- Close every started connection. Their generations become invalid for later demands. -/
opaque Kernel.close (kernel : Kernel) : IO Unit := do
  for (_, wire) in (← kernel.connections.get).toList do wire.close
  kernel.connections.set {}

private def portFailure (error : PortError) : MetaM α :=
  throwStratum error.stratum error.render

private def transactionFailure (failure : TransactionFailure) : MetaM α :=
  match failure with
  | .settled => throwStratum .unavailable "cancelled"
  | .staleOwner | .reservation .staleOwner => throwStratum .unavailable "stale_owner"
  | .reservation .consumed => throwStratum .unavailable "reserved_without_receipt"
  | .reservation .wrongConnection => throwStratum .unavailable "stale_owner"
  | failure => throwError "internal: the active transaction rejected a completion: {repr failure}"

/-- The connection of a declared backend, started and negotiated at its first selected use.
A closed connection is not restarted (execution contract v2 §7).
Reuse: the process environment of the released manifest contract, api/manifest.md. -/
private def Kernel.connection (kernel : Kernel) (backend : String) : MetaM FramedConnection := do
  if let some wire := (← kernel.connections.get)[backend]? then return wire
  let some program := kernel.manifest.backends.find? (·.name == backend)
    | portFailure (.unavailable backend "not declared in the manifest")
  let portPython ← IO.FS.realPath ((← packageDir contractPackage) / "python")
  let path := match ← IO.getEnv "PYTHONPATH" with
    | some inherited => s!"{portPython}:{inherited}"
    | none => portPython.toString
  let started ← FramedConnection.start kernel.ledger.owners backend {
    cmd := program.command, args := program.args, cwd := some kernel.root
    env := #[("PYTHONPATH", some path)] } kernel.timeoutMs
  match started with
  | .error error => portFailure error
  | .ok wire =>
    kernel.connections.modify (·.insert backend wire)
    return wire

private def Kernel.connectionOf (kernel : Kernel) (owner : ConnectionGeneration) :
    MetaM FramedConnection := do
  for (_, wire) in (← kernel.connections.get).toList do
    if wire.connection.generation == owner then return wire
  throwStratum .unavailable "stale_owner"

private def kindName : ComputationalKind → String
  | .proof => "proof"
  | .typeValue => "type"
  | .function => "function"
  | .record => "record"
  | .data => "data"

/-- The prepared interface of one role: its kind and its ordered computational fields. -/
private def layoutJson (layout : SourceLayout) : Json :=
  Json.mkObj [("kind", toJson (kindName layout.kind)),
    ("fields", .arr (layout.fields.filterMap fun field => field.wireIndex.map fun _ =>
      Json.mkObj [("name", toJson field.projection.toString), ("kind", toJson (kindName field.kind))]))]

/-- The dependent invocation context of execution contract v2 §4.1, for a published operation
and for a retained native export. Parameters and arguments keep their source order. -/
private def dependentContext (role : String) (parameters arguments : Array Json)
    (argumentLayouts : Array SourceLayout) (result : SourceLayout) : Json :=
  Json.mkObj [("kind", "dependent"), ("prepared_role", toJson role),
    ("parameters", .arr parameters), ("bindings", .arr #[]), ("arguments", .arr arguments),
    ("argument_layouts", .arr (argumentLayouts.map layoutJson)),
    ("result_layout", layoutJson result)]

private def argumentLayouts (request : PreparedRequest) : Array SourceLayout :=
  match request.application with
  | none => #[]
  | some application => application.arguments.filterMap fun argument =>
      argument.wireIndex.map fun _ => argument.source

/-- The public action address of a selected family field.
The first computational field of a record uses the family address. Another field appends its
name, as the published `<functor id>#map` (api/manifest.md, "Matching and overlap"). -/
private def actionAddress (reference : ComputationRef) (path : Array FieldLayout) : String :=
  match path.back? with
  | some field =>
    if field.wireIndex == some 0 then referenceId reference
    else s!"{referenceId reference}#{field.projection.getString!}"
  | none => referenceId reference

/-- Input addresses of this exact invocation: the complete-request form, and the exact form and
category of each argument that is a registered named object. -/
private def inputForms (reference : ComputationRef) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM (Array String) := do
  let state ← semanticState
  let mut forms := #[s!"{referenceId reference}#input"]
  for argument in arguments do
    if let some (id, _) ← sourceObjectReference? (← argument.inContext context) then
      if let some entry := state.objects.find? (·.id == id) then
        forms := forms ++ #[entry.id.raw, entry.category.raw]
  return forms

private inductive Realization
  | registration (selected : Registration)
  | derivation (checked : CheckedComputationDerivation)

/-- Select the realization of one exact demand by the saturated grounded count.
Source: execution contract v2 §5.1 and §5.2. The root alternatives are the eligible
registrations and the profile's checked derivations. A prerequisite is a delayed demand: an
installed registration or a grounded derivation makes it present, and its own realization is
selected when its actual arguments exist. Zero and many dispatch nothing.
Reuse: RealizationGraph.grounded and GroundedRealizations.uniqueAlternative. -/
private def Kernel.select (kernel : Kernel) (reference : ComputationRef) (address : String)
    (forms : Array String) : MetaM Realization := do
  let eligible := kernel.manifest.registrations.filter fun registration =>
    registration.operation == address && forms.contains registration.input &&
      kernel.manifest.backends.any (·.name == registration.backend) &&
      kernel.profile.allowsPrimitive reference registration
  let mut nodes : Array ComputationRef := #[reference]
  let mut derivations : Array (Array CheckedComputationDerivation) := #[]
  let mut next := 0
  while next < nodes.size do
    let some node := nodes[next]? | break
    let checked := (← checkedComputationDerivations node).filter fun derivation =>
      kernel.profile.allowsDerivation derivation.entry
    for derivation in checked do
      for prerequisite in derivation.prerequisites do
        unless nodes.contains prerequisite.reference do nodes := nodes.push prerequisite.reference
    derivations := derivations.push checked
    next := next + 1
  let size := nodes.size
  let present := fun (node : ComputationRef) =>
    kernel.manifest.registrations.any fun registration =>
      (registration.operation == referenceId node ||
        registration.operation.startsWith s!"{referenceId node}#") &&
        kernel.profile.allowsPrimitive node registration
  let rows : Array (Array (Array Nat)) := nodes.mapIdx fun index node =>
    let primitive : Array (Array Nat) :=
      if index == 0 then eligible.map fun _ => #[]
      else if present node then #[#[]] else #[]
    primitive ++ (derivations[index]?.getD #[]).map fun derivation =>
      derivation.prerequisites.filterMap fun prerequisite =>
        nodes.findIdx? (· == prerequisite.reference)
  let graph : RealizationGraph size := ⟨Vector.ofFn fun node =>
    (rows[node.val]?.getD #[]).map fun children =>
      children.filterMap fun child => if bound : child < size then some ⟨child, bound⟩ else none⟩
  let some grounded := graph.grounded
    | throwError "internal: the realization grounding did not stabilize"
  if root : 0 < size then
    match ← IO.ofExcept <| (grounded.uniqueAlternative ⟨0, root⟩).mapError IO.userError with
    | some alternative =>
      if let some registration := eligible[alternative]? then return .registration registration
      let some derivation := (derivations[0]?.getD #[])[alternative - eligible.size]?
        | throwError "internal: the selected realization is outside its alternatives"
      return .derivation derivation
    | none =>
      if grounded.counts[(⟨0, root⟩ : Fin size)] == .zero then
        throwStratum .noImplementation m!"{address} on {forms}"
      throwStratum .ambiguousRealization m!"{address} on {forms}"
  else throwError "internal: the realization graph has no root demand"

private def kernelCompletion (request : PreparedRequest) (transaction : CellTransaction)
    (value : ValueBinding) : MetaM (PreparedResponse request) := do
  let response ← request.admitResult (← transaction.view) value
  match ← transaction.completeKernel request response with
  | .error failure => transactionFailure failure
  | .ok association => request.admitResult (← transaction.view) association.response.root

/-- Send one prepared invocation on its reserved connection, then admit and stage the whole
reply with its completion. Reuse: FramedConnection.invokeBefore and stageCompletion. -/
private def Kernel.invoke (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (wire : FramedConnection) (reservation : DispatchReservation)
    (encoded : EncodedInputs) (arguments : Json) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  let scope ← RequestScope.issue kernel.ledger reservation graph encoded.slots encoded.inputs #[]
  let reply ← match ← wire.invokeBefore kernel.ledger transaction reservation scope arguments
      kernel.timeoutMs with
    | .ok reply => pure reply
    | .error error => portFailure error
  match ← reply.stageCompletion request transaction scope wire.connection with
  | .error failure => transactionFailure failure
  | .ok association => request.admitResult (← transaction.view) association.response.root

/-- Dispatch a published operation on its selected registration.
`parameters` are the retained family parameters; the request supplies the action arguments. -/
private def Kernel.invokeRegistration (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (registration : Registration) (role : String)
    (parameters : Array ValueBinding) : MetaM (PreparedResponse request) := do
  let wire ← kernel.connection registration.backend
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  let arguments ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
  let roots : Array InputPosition :=
    parameters.mapIdx (fun index binding =>
      { path := #[.field "parameters", .index index], binding }) ++
    arguments.mapIdx (fun index binding =>
      { path := #[.field "arguments", .index index], binding })
  let encoded ← IO.ofExcept <|
    (graph.encodeInputs wire.connection.generation roots).mapError IO.userError
  let identity : DispatchIdentity := {
    manifestDigest := kernel.manifestDigest, registration, profileDigest := kernel.profile.sha256 }
  let reservation ← match ← transaction.reserve request.occurrence identity wire.connection
      (parameters ++ arguments) with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.dispatches.modify (·.push registration)
  kernel.invoke request transaction wire reservation encoded <|
    dependentContext role (encoded.values.extract 0 parameters.size)
      (encoded.values.extract parameters.size encoded.values.size) (argumentLayouts request)
      request.source

/-- Invoke a retained native export on its original supplying connection.
Source: execution contract v2 §4.1. No registration is searched for a selected callable. -/
private def Kernel.invokeExport (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (callable : ValueBinding) (role : String) :
    MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  let code ← IO.ofExcept <| (graph.callable callable).mapError IO.userError
  let some node := graph.find code.value
    | throwError "internal: the native callable is outside the active graph"
  let .ownedToken owner _ _ := node.payload.data
    | throwError "internal: the retained callable has no native export"
  let wire ← kernel.connectionOf owner
  let inputs ← request.admitInputs graph
  let arguments ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
  let roots : Array InputPosition := arguments.mapIdx fun index binding =>
    { path := #[.field "arguments", .index index], binding }
  let encoded ← IO.ofExcept <|
    (graph.encodeExportInputs wire.connection.generation callable roots).mapError IO.userError
  let reservation ← match ← transaction.reserveExport request.occurrence callable wire.connection
      arguments with
    | .ok reservation => pure reservation
    | .error failure => transactionFailure failure
  kernel.invoke request transaction wire reservation encoded <|
    dependentContext role #[] encoded.values (argumentLayouts request) request.source

private def withSourceScope (request : PreparedRequest)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → MetaM α) : MetaM α :=
  request.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let mut bound : Std.HashMap BindingId ValueBinding := {}
    for (entry, value) in request.environment.context.entries.zip request.environment.values do
      if let some value := value then bound := bound.insert entry.id value
    action context bound

private def projectTerm (value : Expr) (field : FieldLayout) : MetaM Expr := do
  let some info := (← getEnv).getProjectionFnInfo? field.projection
    | throwError "internal: a prepared field has no native projection"
  return .proj (← getConstInfoCtor info.ctorName).induct info.i value

/-- Retain a published family, or one more selected field of it, as a delayed demand. -/
private def Kernel.delay (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (captures : Array ValueBinding) : MetaM (PreparedResponse request) := do
  let program ← kernel.ledger.owners.identities.fresh .program
  kernel.codes.modify (·.insert program (.family family path))
  let value ← transaction.stage (← request.originFor request.source) (.closure program captures)
  kernelCompletion request transaction value

/-- The lowering environment of one active cell. Each emitted program runs through the
production interpreter and the supplied kernel executor. -/
private def Kernel.lowering (kernel : Kernel)
    (executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature)
    (transaction : CellTransaction) : LowerEnvironment := {
  ledger := kernel.ledger, transaction, codes := kernel.codes, marks := kernel.marks
  run := fun program => Execute.run executor program transaction }

mutual

/-- Evaluate a checked source term for a claimed demand and complete that demand. -/
private partial def Kernel.evaluate (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction)
    (build : OpenContext → MetaM Expr) : MetaM (PreparedResponse request) := do
  let value ← withSourceScope request fun context bound => do
    lowerTerm (kernel.lowering kernel.executor transaction) request.program context bound
      (← build context)
  kernelCompletion request transaction value

/-- Dispatch a delayed family demand whose action has reached its actual arguments.
The selected registration receives the family parameters and the action arguments.
A selected derivation is the checked plan at those same parameters, fields and arguments. -/
private partial def Kernel.reach (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (parameters : Array ValueBinding) (arguments : Array ClosedTerm) :
    MetaM (PreparedResponse request) := do
  let .primitive boundary universes := family.action
    | throwError "internal: a delayed family demand lost its published boundary"
  let reference := boundary.source.reference
  let address := actionAddress reference path
  let forms ← withSourceScope request fun context _ => inputForms reference context arguments
  match ← kernel.select reference address forms with
  | .registration registration =>
    let role := ".".intercalate (path.map (·.projection.toString)).toList
    kernel.invokeRegistration request transaction registration role parameters
  | .derivation checked =>
    kernel.evaluate request transaction fun context => do
      let plan := checked.plan.instantiateLevelParams checked.universeParams universes
      let formal : Array ClosedTerm := match family.application with
        | none => #[]
        | some application => application.arguments.map (·.source.source)
      let mut term := mkAppN plan (← formal.mapM (·.inContext context))
      for field in path do term ← projectTerm term field
      let values := match request.action with
        | .apply _ _ values => values
        | _ => #[]
      let mut actual := #[]
      for argument in arguments, index in [:arguments.size] do
        let source ← argument.inContext context
        actual := actual.push (← match values[index]?.bind id with
          | some value => markValue kernel.marks value source
          | none => pure source)
      return (mkAppN term actual).headBeta

/-- The kernel-owned concrete executor of prepared demands (T013).
A published family whose value is a callable or a record is retained as a delayed demand.
A field of retained code extends that demand or lowers the source field. An application
dispatches the delayed family on its selected realization, evaluates retained source code at
the actual arguments, or invokes the native export on its original connection. -/
partial def Kernel.execute (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  match request.action with
  | .primitive .. =>
    if request.source.kind == .function || request.source.kind == .record then
      return ← kernel.delay request transaction request #[] request.scope
    let arguments : Array ClosedTerm := match request.application with
      | none => #[]
      | some application => application.arguments.map (·.source.source)
    kernel.reach request transaction request #[] #[] arguments
  | .project operand field =>
    let some node := graph.find operand.value
      | throwError "internal: the projected value is outside the active graph"
    match node.payload.data with
    | .closure program captures =>
      match (← kernel.codes.get)[program]? with
      | some (.family family path) =>
        kernel.delay request transaction family (path.push field) captures
      | some (.term source) =>
        kernel.evaluate request transaction fun context => do
          projectTerm (← source.inContext context) field
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. =>
      kernel.invokeExport request transaction operand s!"project:{field.projection}"
    | _ => throwError "internal: a stored field reached the executor"
  | .apply callable arguments values =>
    let code ← IO.ofExcept <| (graph.callable callable).mapError IO.userError
    let some node := graph.find code.value
      | throwError "internal: the applied value is outside the active graph"
    match node.payload.data with
    | .closure program captures =>
      match (← kernel.codes.get)[program]? with
      | some (.family family path) =>
        kernel.reach request transaction family path captures arguments
      | some (.term source) =>
        kernel.evaluate request transaction fun context => do
          let mut actual := #[]
          for argument in arguments, index in [:arguments.size] do
            let term ← argument.inContext context
            actual := actual.push (← match values[index]?.bind id with
              | some value => markValue kernel.marks value term
              | none => pure term)
          return (mkAppN (← source.inContext context) actual).headBeta
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. => kernel.invokeExport request transaction callable "apply"
    | _ => throwError "internal: the applied value has no code or native export"

/-- The production handler of the dependent operational signature. -/
partial def Kernel.executor (kernel : Kernel) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    return (← kernel.execute request transaction, transaction)

end

/-- Lower and execute one checked source term in the active cell, through the production
interpreter and executor. `bound` is the runtime-binding table of `context`. -/
opaque Kernel.run (kernel : Kernel) (transaction : CellTransaction) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr) : MetaM ValueBinding := do
  let program ← kernel.ledger.owners.identities.fresh .program
  lowerTerm (kernel.lowering kernel.executor transaction) program context bound expression

end CasRuntime
