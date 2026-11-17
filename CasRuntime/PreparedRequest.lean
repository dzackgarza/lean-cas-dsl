module

public import CasCompiler.Program
public import CasRuntime.Value
public import CasRuntime.Environment
public import CasRuntime.RoleMap
public import Cslib.Foundations.Data.PFunctor.Free

@[expose] public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue

inductive PreparedAction
  | primitive (boundary : ProgramBoundary) (universeArguments : List Level)
  | project (operand : CasRuntime.ValueBinding) (field : FieldLayout)
  | apply (callable : CasRuntime.ValueBinding) (arguments : Array ClosedTerm)
      (values : Array (Option CasRuntime.ValueBinding))

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
  selection : Option Name := none

/-- Carry the exact source construction identity into its prepared field demands. -/
opaque PreparedRequest.withSelection (request : PreparedRequest) (selection : Option Name) :
    PreparedRequest := { request with selection }

def PreparedRequest.reference (request : PreparedRequest) : Option ComputationRef :=
  match request.action with
  | .primitive boundary _ => boundary.reference
  | .project .. | .apply .. => none

def PreparedRequest.universeArguments (request : PreparedRequest) : Option (List Level) :=
  match request.action with
  | .primitive _ arguments => some arguments
  | .project .. | .apply .. => none

/-- Stamp a result or nested field with the same complete actual argument table.
Reuse: native ApplicationLayout projection dependencies and RuntimeEnvironment.origin. -/
opaque PreparedRequest.originFor (request : PreparedRequest) (source : SourceLayout) :
    MetaM CasRuntime.ValueOrigin := do
  let origin ← request.environment.origin request.program request.occurrence source
  let application ← request.origin.application.mapM (·.forSource request.source source)
  return { origin with application, access := request.origin.access }

private def prepareRequest (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (context : OpenContext) (scope : Array CasRuntime.ValueBinding)
    (environment : CasRuntime.RuntimeEnvironment) (application : Option ApplicationLayout)
    (arguments : Array (Option CasRuntime.ValueBinding)) :
    MetaM PreparedRequest := do
  unless identities.worker == program.worker && program.worker == occurrence.worker do
    throwError "request preparation mixed worker identities"
  for binding in scope do
    unless binding.value.worker == program.worker do
      throwError "a request scope value belongs to a different worker"
    discard <| binding.role.source.inContext context
  if source.kind == .proof then
    throwError "a source proof has no computational response positions"
  let origin ← environment.origin program occurrence source
  let origin ← if let some layout := application then do
      let callable := match action with | .apply callable .. => some callable | _ => none
      let .ok application := CasRuntime.ApplicationOrigin.ofArguments layout environment.values arguments callable
        | throwError "the prepared application has an incompatible actual argument table"
      pure { origin with application := some application }
    else do
      unless arguments.isEmpty do
        throwError "actual arguments require a prepared native application telescope"
      pure origin
  let mut outputs : Array SourceLayout := #[]
  let record ← if source.kind == .record then
      pure (some (← RecordLayout.ofSource source))
    else pure none
  if let some record := record then
    for prepared in record.fields do
      if prepared.field.wireIndex.isSome then outputs := outputs.push prepared.layout
  else outputs := #[source]
  let roles ← RoleTelescope.ofRequest identities program occurrence context application source
    (scope.map (·.role))
  return ⟨program, occurrence, action, source, scope, outputs, record, environment, origin,
    application, roles, none⟩

/-- Check the complete declared input map before execution or wire encoding.
Preparation may inspect a source telescope before its input producers have supplied values. -/
opaque PreparedRequest.admitInputs (request : PreparedRequest) (graph : CasRuntime.ValueGraph) :
    MetaM CasRuntime.InputRoleMap := do
  let arguments := match request.action with
    | .apply _ _ values => values
    | .primitive .. => match request.origin.application with
      | none => #[]
      | some application => application.arguments
    | .project .. => #[]
  CasRuntime.InputRoleMap.admit request.roles request.environment graph arguments request.scope

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
  unless universeArguments.length == boundary.universeParams.length do
    throwError "request universe arguments do not match the checked source family"
  let universeArguments ← universeArguments.mapM instantiateLevelMVars
  if universeArguments.any (·.hasMVar) then
    throwError "request preparation requires resolved universe arguments"
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
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  let values ← prepareArguments environment arguments actual
  prepareRequest identities program occurrence (.primitive boundary universeArguments) source context
    (values.filterMap id ++ scope) environment application values

/-- Prepare the exact source field of the retained operand in the complete current scope. -/
opaque PreparedRequest.forProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (index : Nat)
    (parameters : Array CasRuntime.RuntimeParameter) : MetaM PreparedRequest := do
  let some field := operand.role.fields[index]?
    | throwError "the projection is outside the retained source layout"
  unless field.wireIndex.isSome do
    throwError "a source proof field has no computational projection"
  let source ← (← field.toLayout).inContext context
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  discard <| environment.checkResult graph operand.role operand
  let .ok original := graph.applicationOrigin operand
    | throwError "the projected operand is outside the visible graph"
  let application ← original.mapM (·.forProjection field.projection)
  let request ← prepareRequest identities program occurrence (.project operand field) source context
    #[operand] environment none #[]
  return { request with
    origin := { request.origin with application, access := some operand }
    application := application.map (·.layout) }

/-- Apply the retained function with complete formal arguments and indexed actual operands.
Source coercions are lowered before this boundary. Preparation retains empty slots for source
inspection; effect admission requires every computational operand. Each supplied operand is
checked against that exact argument and retained in source order. -/
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
  let (source, application) ← ApplicationLayout.ofSource callable.role context arguments
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  let values ← prepareArguments environment arguments actual
  prepareRequest identities program occurrence (.apply callable arguments values) source context
    (#[callable] ++ values.filterMap id) environment (some application) values

/-- A checked returned interface with scoped bindings for subsequent computational demands. -/
structure PreparedResponse (request : PreparedRequest) where
  private mk ::
  roles : CasRuntime.ResultRoleMap

def PreparedResponse.root (response : PreparedResponse request) : CasRuntime.ValueBinding :=
  response.roles.root

/-- Bind actual returned fields to this request's source-declared result roles. -/
opaque PreparedRequest.admitResult (request : PreparedRequest) (graph : CasRuntime.ValueGraph)
    (value : CasRuntime.ValueBinding) : MetaM (PreparedResponse request) := do
  return ⟨← CasRuntime.ResultRoleMap.admit request.roles request.environment graph value⟩

/-- Responses retain actual roots and their scoped result bindings under source-prepared layouts.
Reference: CSLib 3951377e, Foundations/Data/PFunctor/Free.lean. -/
def OperationalSignature : PFunctor.{0, 0} :=
  ⟨PreparedRequest, PreparedResponse⟩

/-- CSLib retains dependent continuations for later demands and actual returned references. -/
abbrev OperationalProgram := OperationalSignature.FreeM

end CasRuntime
