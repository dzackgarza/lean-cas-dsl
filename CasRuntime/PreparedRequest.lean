module

public import CasCompiler.Program
public import CasRuntime.Value
public import CasRuntime.Environment
public import CasRuntime.DeclaredInput
public import CasRuntime.RoleMap
public import CasRuntime.Literal
public import CasRuntime.Observation
public import Cslib.Foundations.Data.PFunctor.Free

@[expose] public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue

/-- Complete source roles and ordered runtime scope, fixed before a computational reply. -/
structure PreparedRequest where
  private mk ::
  program : CasRuntime.RuntimeId .program
  occurrence : CasRuntime.RuntimeId .occurrence
  action : PreparedAction
  source : SourceLayout
  scope : Array CasRuntime.ValueBinding
  outputs : Array SourceLayout
  record : Option RecordLayout
  environment : CasRuntime.RuntimeEnvironment
  origin : CasRuntime.ValueOrigin
  application : Option ApplicationLayout
  roles : RoleTelescope
  observation : ObservationDescriptor
  private actualArguments : Array CasRuntime.RuntimeArgument
  selection : Option Name := none

/-- Carry the exact source construction identity into its prepared field demands. -/
opaque PreparedRequest.withSelection (request : PreparedRequest) (selection : Option Name) :
    PreparedRequest :=
  { request with selection, observation := request.observation.withSelection selection }

/-- Carry the already prepared frontend document without changing the reached native request. -/
opaque PreparedRequest.withSourceSnapshot (request : PreparedRequest)
    (sourceSnapshot : Option Json) : PreparedRequest :=
  { request with observation := request.observation.withSourceSnapshot sourceSnapshot }

/-- A prepared invocation belongs to one complete request scope, including its fresh
preparation identity when the source occurrence is rebuilt. -/
def requestPreparationMismatchTag : Name := `CasRuntime.requestPreparationMismatch

/-- Require the exact independently retained request before materialization or dispatch. -/
opaque PreparedRequest.requirePreparation (request : PreparedRequest) (scope : RoleScope) :
    MetaM Unit := do
  unless request.roles.scope == scope do
    throwError (MessageData.tagged requestPreparationMismatchTag
      m!"the invocation belongs to a different original request preparation")

def PreparedRequest.reference (request : PreparedRequest) : Option ComputationRef :=
  match request.action with
  | .primitive boundary _ => boundary.reference
  | .project .. | .apply .. => none

def PreparedRequest.universeArguments (request : PreparedRequest) : Option (List Level) :=
  match request.action with
  | .primitive _ arguments => some arguments
  | .project .. | .apply .. => none

/-- The exact native path from the retained operand to this prepared field.
Only preparation establishes the source address and matching access provenance. -/
def PreparedRequest.projectionPath (request : PreparedRequest) : Except String (Array Name) := do
  let .project operand field := request.action
    | throw "the prepared action is not a native projection"
  unless operand.role.address.toList.isPrefixOf field.address.toList do
    throw "the prepared field is outside its retained operand"
  let path := field.address.extract operand.role.address.size field.address.size
  unless !path.isEmpty && path.back? == some field.projection &&
      request.origin.accessPath == path do
    throw "the prepared projection lost its exact native field path"
  let some parent := request.origin.access
    | throw "the prepared projection lost its retained operand"
  unless parent.value == operand.value && parent.associationIds == operand.associationIds do
    throw "the prepared projection changed its retained operand"
  return path

/-- Stamp a result or nested field with the same complete actual argument table.
Reuse: native ApplicationLayout projection dependencies and RuntimeEnvironment.origin. -/
opaque PreparedRequest.originFor (request : PreparedRequest) (source : SourceLayout) :
    MetaM CasRuntime.ValueOrigin := do
  let origin ← request.environment.origin request.program request.occurrence source
  let application ← request.origin.application.mapM (·.forSource request.source source)
  let accessPath ← if request.origin.access.isSome then
      pure (request.origin.accessPath ++ (← request.source.projectionPathTo source))
    else pure #[]
  return { origin with application, access := request.origin.access, accessPath }

private def prepareOrigin (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (environment : CasRuntime.RuntimeEnvironment)
    (application : Option ApplicationLayout) (arguments : Array (Option CasRuntime.ValueBinding)) :
    MetaM CasRuntime.ValueOrigin := do
  let origin ← environment.origin program occurrence source
  if let some layout := application then
    let callable := match action with | .apply callable .. => some callable | _ => none
    let .ok application :=
        CasRuntime.ApplicationOrigin.ofArguments layout environment.values arguments callable
      | throwError "the prepared application has an incompatible actual argument table"
    return { origin with application := some application }
  unless arguments.isEmpty do
    throwError "actual arguments require a prepared native application telescope"
  return origin

private def prepareRequest (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (context : OpenContext) (scope : Array CasRuntime.ValueBinding)
    (environment : CasRuntime.RuntimeEnvironment) (application : Option ApplicationLayout)
    (origin : CasRuntime.ValueOrigin)
    (actualArguments : Array CasRuntime.RuntimeArgument := #[]) :
    MetaM PreparedRequest := do
  unless identities.worker == program.worker && program.worker == occurrence.worker do
    throwError "request preparation mixed worker identities"
  for binding in scope do
    unless binding.value.worker == program.worker do
      throwError "a request scope value belongs to a different worker"
    discard <| binding.role.source.inContext context
  if source.kind == .proof then
    throwError "a source proof has no computational response positions"
  let traced := (source.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traced then dbg_trace "[inclusion.stage] request {repr occurrence}: before output layouts"
  let mut outputs : Array SourceLayout := #[]
  let record ← if source.kind == .record then
      pure (some (← RecordLayout.ofSource source))
    else pure none
  if let some record := record then
    for prepared in record.fields do
      if prepared.field.wireIndex.isSome then outputs := outputs.push prepared.layout
  else outputs := #[source]
  if traced then dbg_trace "[inclusion.stage] request {repr occurrence}: before role telescope"
  let roles ← RoleTelescope.ofRequest identities program occurrence context application source
    (scope.map (·.role))
  if traced then dbg_trace "[inclusion.stage] request {repr occurrence}: prepared"
  -- Snapshot only after the exact current invocation and its producer provenance are fixed.
  let observation ← ObservationDescriptor.prepare program occurrence action source scope outputs
    record environment origin application roles actualArguments
  return ⟨program, occurrence, action, source, scope, outputs, record, environment, origin,
    application, roles, observation, actualArguments, none⟩

private def PreparedRequest.inputValues (request : PreparedRequest) :
    Array (Option CasRuntime.ValueBinding) :=
  match request.action with
    | .apply _ _ values => values
    | .primitive .. => match request.origin.application with
      | none => #[]
      | some application => application.arguments
    | .project .. => #[]

/-- Check the complete declared input map before execution or wire encoding.
Preparation may inspect a source telescope before its input producers have supplied values. -/
opaque PreparedRequest.admitInputs (request : PreparedRequest) (graph : CasRuntime.ValueGraph) :
    MetaM CasRuntime.InputRoleMap := do
  CasRuntime.InputRoleMap.admit request.roles request.environment graph request.inputValues request.scope
    request.actualArguments

/-- Input-result admission requires a complete native source-coverage witness whenever a
computational slot is absent. Every supplied value is checked against its original source
role; the complete formal telescope is unchanged. Ordinary effects use admitInputs above.
The sealed InputResultPlan retains this map before resolving any selected lazy field. -/
opaque PreparedRequest.admitInputResultInputs (request : PreparedRequest)
    (graph : CasRuntime.ValueGraph) : MetaM CasRuntime.InputRoleMap := do
  let arguments := request.inputValues
  if request.roles.arguments.size == arguments.size &&
      (request.roles.arguments.zip arguments).all (fun (role, value) =>
        role.wireIndex.isNone || value.isSome) then
    return ← request.admitInputs graph
  let some application := request.application
    | throwError "a fixed input result has no complete formal application"
  let contextInputs := (request.environment.context.entries.zip request.environment.values).filterMap
    fun (entry, value) => if value.isSome then some entry.id else none
  let some coverage ← request.roles.inputResultCoverage application contextInputs
    | throwError "missing computational inputs require complete native source coverage"
  CasRuntime.InputRoleMap.admitInputResult request.roles coverage request.environment graph
    arguments request.scope request.actualArguments

/-- Check indexed actual operands against the complete native source argument sequence.
Reuse: RuntimeEnvironment.checkArgument; primitive and retained applications share this table. -/
private def prepareArguments (environment : CasRuntime.RuntimeEnvironment)
    (arguments : Array ClosedTerm) (actual : Array CasRuntime.RuntimeArgument) :
    MetaM (Array (Option CasRuntime.ValueBinding)) := do
  let mut values := Array.replicate arguments.size none
  for argument in actual do
    let some specified := arguments[argument.index]?
      | throwError "a runtime argument is outside the complete callable argument list"
    if (values[argument.index]?.bind id).isSome then
      throwError "a callable source argument has duplicate runtime bindings"
    let value ← environment.checkArgument specified argument
    values := values.set! argument.index (some value)
  return values

/-- Apply the exact checked source family in the complete current context.
Result positions retain the source's ordered computational fields and dependent roles.
Indexed actual operands use the same checked provenance table as retained callables.
Source application reuses Lean's native checks and the existing closed-context transport. -/
opaque PreparedRequest.forBoundary (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (boundary : ProgramBoundary)
    (universeArguments : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm)
    (actual : Array CasRuntime.RuntimeArgument)
    (scope : Array CasRuntime.ValueBinding) (parameters : Array CasRuntime.RuntimeParameter) :
    MetaM PreparedRequest := do
  if let .property family := boundary then
    unless arguments.size == family.parameterCount + 1 do
      throwError "a property observation requires its complete original source application"
  unless universeArguments.length == boundary.universeParams.length do
    throwError "request universe arguments do not match the checked source family"
  let universeArguments ← universeArguments.mapM instantiateLevelMVars
  if universeArguments.any (·.hasMVar) then
    throwError "request preparation requires resolved universe arguments"
  let traced := (boundary.family.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traced then dbg_trace "[inclusion.stage] primitive {repr occurrence}: before family layout"
  let family ← withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    empty.close (boundary.family.instantiateLevelParams
      boundary.universeParams universeArguments)
  let layout ← SourceLayout.ofTerm family
  let (source, application) ← if arguments.isEmpty then
      pure (← layout.inContext context, (none : Option ApplicationLayout))
    else do
      let (source, application) ← ApplicationLayout.ofSource layout context arguments
      pure (source, some application)
  if traced then dbg_trace "[inclusion.stage] primitive {repr occurrence}: before environment"
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  if traced then dbg_trace "[inclusion.stage] primitive {repr occurrence}: before argument admission"
  let values ← prepareArguments environment arguments actual
  if traced then dbg_trace "[inclusion.stage] primitive {repr occurrence}: arguments admitted"
  let action := PreparedAction.primitive boundary universeArguments
  let origin ← prepareOrigin program occurrence action source environment application values
  prepareRequest identities program occurrence action source context
    (values.filterMap id ++ scope) environment application origin actual

private def checkPresentationInputs (request : PreparedRequest) (graph : ValueGraph)
    (source target : ValueBinding) (marks : Array ValueBinding) : MetaM Unit := do
  let .primitive (.presentation family) _ := request.action
    | throwError "declared endpoint checking requires its original presentation family"
  request.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let applied ← request.source.source.inContext context
    discard <| family.withEndpoints applied (← source.role.source.inContext context)
      (← target.role.source.inContext context)
    let mut arguments := applied.getAppArgs
    let actual := request.origin.application.map (·.arguments) |>.getD #[]
    unless actual.size == arguments.size do
      throwError "the presentation lost its complete original parameter reference table"
    -- This local mark table is used only by the check. No returned source role can carry
    -- one of these temporary marks; the original supplied endpoint bindings stay intact.
    let retained ← IO.mkRef marks
    for value in actual, index in [:actual.size] do
      if let some value := value then
        arguments := arguments.set! index (← markValue retained value arguments[index]!)
    let (expectedSource, expectedTarget) ← family.endpoints (mkAppN applied.getAppFn arguments)
    let marks ← retained.get
    request.environment.checkDeclaredInput context graph marks expectedSource source
    request.environment.checkDeclaredInput context graph marks expectedTarget target

/-- Prepare a named presentation with its two explicitly supplied native endpoints. Both are
ordinary admitted operands in the same complete context; the source reader or named child
reader has already validated their native correspondence to the original Iso. Endpoint values
are retained as captures, separately from the declaration parameters and original point. -/
opaque PreparedRequest.forPresentation (identities : IdentitySupply)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (family : PresentationFamily) (universes : List Level) (context : OpenContext)
    (arguments : Array ClosedTerm) (actual : Array RuntimeArgument)
    (endpoints : Array ClosedTerm) (endpointValues : Array RuntimeArgument)
    (parameters : Array RuntimeParameter) (graph : ValueGraph)
    (marks : Array ValueBinding) : MetaM PreparedRequest := do
  let #[_, _] := endpoints
    | throwError "the presentation request requires both complete original endpoints"
  let environment ← RuntimeEnvironment.capture program.worker context parameters
  let values ← prepareArguments environment endpoints endpointValues
  let #[some source, some target] := values
    | throwError "the presentation request is missing an actual endpoint value"
  let request ← PreparedRequest.forBoundary identities program occurrence (.presentation family)
    universes context arguments actual #[source, target] parameters
  discard <| request.admitInputs graph
  checkPresentationInputs request graph source target marks
  return request

/-- Read the two explicitly retained endpoint positions and recheck their original native
correspondence. Captures are not searched by expression or payload equality. -/
opaque PreparedRequest.presentationEndpoints (request : PreparedRequest)
    (graph : ValueGraph) (marks : Array ValueBinding) : MetaM (ValueBinding × ValueBinding) := do
  let .primitive (.presentation family) _ := request.action
    | throwError "endpoint preparation requires a published presentation boundary"
  let count := match request.origin.application with
    | none => 0
    | some application => (application.arguments.filterMap id).size
  let #[source, target] := request.scope.extract count request.scope.size
    | throwError "the presentation request lost its exact endpoint capture positions"
  discard <| request.environment.checkResult graph source.role source
  discard <| request.environment.checkResult graph target.role target
  checkPresentationInputs request graph source target marks
  return (source, target)

private def prepareProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (path : Array Name)
    (parameters : Array CasRuntime.RuntimeParameter) : MetaM PreparedRequest := do
  let traced := (operand.role.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traced then dbg_trace "[inclusion.stage] projection {repr occurrence} {repr path}: before layout"
  let mut layout := operand.role
  let mut selected : Option FieldLayout := none
  for projection in path do
    let some field := layout.fields.find? (·.projection == projection)
      | throwError "the projection is outside the retained source layout"
    unless field.wireIndex.isSome do
      throwError "a source proof field has no computational projection"
    selected := some field
    layout ← field.toLayout
  let some field := selected | throwError "a projection requires a native field path"
  let source ← layout.inContext context
  if traced then dbg_trace "[inclusion.stage] projection {repr occurrence}: before environment"
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  if traced then dbg_trace "[inclusion.stage] projection {repr occurrence}: before operand admission"
  discard <| environment.checkOperand graph operand.role operand
  if traced then dbg_trace "[inclusion.stage] projection {repr occurrence}: operand admitted"
  let .ok original := graph.applicationOrigin operand
    | throwError "the projected operand is outside the visible graph"
  let mut application := original
  for projection in path do
    application ← application.mapM (·.forProjection projection)
  let action := PreparedAction.project operand field
  let origin ← prepareOrigin program occurrence action source environment none #[]
  let origin := { origin with application, access := some operand, accessPath := path }
  prepareRequest identities program occurrence action source context
    #[operand] environment none origin

/-- Prepare the exact source field of the retained operand in the complete current scope. -/
opaque PreparedRequest.forProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (index : Nat)
    (parameters : Array CasRuntime.RuntimeParameter) : MetaM PreparedRequest := do
  let some field := operand.role.fields[index]?
    | throwError "the projection is outside the retained source layout"
  prepareProjection identities program occurrence context graph operand
    #[field.projection] parameters

/-- Compose a wholly stored native path without completing its intermediate record values.
The graph must already supply every step; a lazy access remains an ordinary single-field demand. -/
opaque PreparedRequest.forStoredProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (path : Array Name)
    (parameters : Array CasRuntime.RuntimeParameter) : MetaM PreparedRequest := do
  let selected ← IO.ofExcept <| (graph.projectionFrontier operand path).mapError IO.userError
  let some (_, remaining) := selected
    | throwError "the native projection path has no stored field interface"
  unless remaining.isEmpty do
    throwError "a composed projection cannot pass a lazy field boundary"
  prepareProjection identities program occurrence context graph operand path parameters

/-- Apply the retained function with complete formal arguments and indexed actual operands.
Source coercions are lowered before this boundary. Preparation retains empty slots for source
inspection; ordinary effect admission requires every computational operand. A sealed complete
input result may omit only source-proven unused slots. Each supplied operand is checked against
that exact argument and retained in source order. -/
opaque PreparedRequest.forApplication (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (callable : CasRuntime.ValueBinding) (arguments : Array ClosedTerm)
    (actual : Array CasRuntime.RuntimeArgument)
    (parameters : Array CasRuntime.RuntimeParameter) :
    MetaM PreparedRequest := do
  unless callable.role.kind == .function do
    throwError "the retained value has no prepared callable interface"
  if arguments.isEmpty then throwError "callable application requires a source argument"
  let traced := (callable.role.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traced then dbg_trace "[inclusion.stage] application {repr occurrence}: before layout"
  let (source, application) ← ApplicationLayout.ofSource callable.role context arguments
  if traced then dbg_trace "[inclusion.stage] application {repr occurrence}: before environment"
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  if traced then dbg_trace "[inclusion.stage] application {repr occurrence}: before argument admission"
  let values ← prepareArguments environment arguments actual
  if traced then dbg_trace "[inclusion.stage] application {repr occurrence}: arguments admitted"
  let action := PreparedAction.apply callable arguments values
  let origin ← prepareOrigin program occurrence action source environment (some application) values
  prepareRequest identities program occurrence action source context
    (#[callable] ++ values.filterMap id) environment (some application) origin actual

/-- A checked returned interface with scoped bindings for subsequent computational demands. -/
structure PreparedResponse (request : PreparedRequest) where
  private mk ::
  roles : CasRuntime.ResultRoleMap

def PreparedResponse.root (response : PreparedResponse request) : CasRuntime.ValueBinding :=
  response.roles.root

/-- Bind actual returned fields to this request's source-declared result roles.
Every admission of a projection result retains the same prepared operand and native field. -/
opaque PreparedRequest.admitResult (request : PreparedRequest) (graph : CasRuntime.ValueGraph)
    (value : CasRuntime.ValueBinding) : MetaM (PreparedResponse request) := do
  if let .primitive (.property _) _ := request.action then
    let malformed : {α : Type} → String → MetaM α := fun reason =>
      throwStratum .malformed m!"property observation: {reason}"
    let packet ← match graph.packet? value with
      | .ok (some packet) => pure packet
      | .ok none => malformed "the answer has no complete Option Bool packet"
      | .error reason => malformed reason
    match PropertyObservation.decode packet with
    | .ok _ => pure ()
    | .error reason => malformed reason
  let projectionContext := match request.action with
    | .project operand field => some (operand, field)
    | .primitive .. | .apply .. => none
  return ⟨← CasRuntime.ResultRoleMap.admit request.roles request.environment graph value
    projectionContext⟩

/-- Responses retain actual roots and their scoped result bindings under source-prepared layouts.
Reference: CSLib 3951377e, Foundations/Data/PFunctor/Free.lean. -/
def OperationalSignature : PFunctor.{0, 0} :=
  ⟨PreparedRequest, PreparedResponse⟩

/-- CSLib retains dependent continuations for later demands and actual returned references. -/
abbrev OperationalProgram := OperationalSignature.FreeM

end CasRuntime
