module

public import LeanCategories.Catalogue.Registry.Computation
public import CasCompiler.Layout
public import CasCompiler.Declaration
public import CasRuntime.Value
public import CasRuntime.Environment
public import Cslib.Foundations.Data.PFunctor.Free

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The accepted whole-family source, before specialization or executable selection. -/
structure SourceProgram where
  private mk ::
  source : CheckedComputationDerivation

/-- One formal callable slot. Its ordinal and published reference are independent of its type. -/
structure PrerequisiteSlot where
  index : Nat
  source : CheckedComputationPrerequisite
  expression : Expr

/-- Read every published alternative through the upstream safety and axiom checks.
The upstream checked packet is retained intact, including rigid universes and equality.
Source: LeanCategories/Catalogue/Registry/Computation.lean at
8c35703b104aca1700b9fb40d1af4164ca31a55d. -/
opaque SourceProgram.forTarget (target : ComputationRef) : MetaM (Array SourceProgram) := do
  return (← checkedComputationDerivations target).map fun source => ⟨source⟩

/-- Open only the prerequisite prefix with fresh locals; keep the entire target family.
Lean's telescope and application operations retain dependent binder types and slot order. -/
def SourceProgram.withPrerequisites (program : SourceProgram)
    (action : Array PrerequisiteSlot → Expr → MetaM α) : MetaM α := do
  let source := program.source
  forallBoundedTelescope (← inferType source.template) (some source.prerequisites.size)
      fun locals _ => do
    unless locals.size == source.prerequisites.size do
      throwError "checked source program has an incomplete prerequisite telescope"
    let slots := source.prerequisites.mapIdx fun index prerequisite =>
      { index, source := prerequisite, expression := locals[index]! : PrerequisiteSlot }
    action slots (mkAppN source.template locals).headBeta

/-- A directly registered family, checked before any specialization or provider selection. -/
structure SourceFamily where
  private mk ::
  source : CheckedComputationPrerequisite
  universeParams : List Name

/-- Resolve the exact public address and retain the entire rigid family.
Reuse: ComputationRef.declaration, the release AxiomAudit.permitted budget and native context closure. -/
opaque SourceFamily.forReference (reference : ComputationRef) : MetaM SourceFamily := do
  let declaration ← reference.declaration (← semanticState)
  let info ← checkedDeclaration declaration
  let family ← withLCtx {} #[] do
    let context ← ContextTelescope.capture #[]
    context.close (mkConst declaration (info.levelParams.map Level.param))
  return ⟨{ reference, declaration, family := family.expression, familyType := family.type },
    info.levelParams⟩

/-- Exact registered family, checked derivation target or ordered primitive slot. -/
inductive ProgramBoundary
  | registered (family : SourceFamily)
  | target (program : SourceProgram)
  | prerequisite (program : SourceProgram) (index : Fin program.source.prerequisites.size)

def ProgramBoundary.source : ProgramBoundary → CheckedComputationPrerequisite
  | .registered family => family.source
  | .target program => {
      reference := program.source.entry.target
      declaration := program.source.targetDeclaration
      family := program.source.target
      familyType := program.source.familyType }
  | .prerequisite program index => program.source.prerequisites[index.val]

def ProgramBoundary.universeParams : ProgramBoundary → List Name
  | .registered family => family.universeParams
  | .target program | .prerequisite program _ => program.source.universeParams

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

def PreparedRequest.reference (request : PreparedRequest) : Option ComputationRef :=
  match request.action with
  | .primitive boundary _ => some boundary.source.reference
  | .project .. | .apply .. => none

def PreparedRequest.universeArguments (request : PreparedRequest) : Option (List Level) :=
  match request.action with
  | .primitive _ arguments => some arguments
  | .project .. | .apply .. => none

private def prepareRequest (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (context : OpenContext) (scope : Array CasRuntime.ValueBinding)
    (environment : CasRuntime.RuntimeEnvironment) (application : Option ApplicationLayout) :
    MetaM PreparedRequest := do
  unless program.worker == occurrence.worker do
    throwError "request preparation mixed worker identities"
  for binding in scope do
    unless binding.value.worker == program.worker do
      throwError "a request scope value belongs to a different worker"
    discard <| binding.role.source.inContext context
  if source.kind == .proof then
    throwError "a source proof has no computational response positions"
  let origin ← environment.origin program occurrence source
  let mut outputs : Array SourceLayout := #[]
  let record ← if source.kind == .record then
      pure (some (← RecordLayout.ofSource source))
    else pure none
  if let some record := record then
    for prepared in record.fields do
      if prepared.field.wireIndex.isSome then outputs := outputs.push prepared.layout
  else outputs := #[source]
  return ⟨program, occurrence, action, source, scope, outputs, record, environment, origin,
    application⟩

/-- Apply the exact checked source family in the complete current context.
Result positions retain the source's ordered computational fields and dependent roles.
Source application reuses Lean's native checks and the existing closed-context transport. -/
opaque PreparedRequest.forBoundary (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (boundary : ProgramBoundary)
    (universeArguments : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm)
    (scope : Array CasRuntime.ValueBinding) (parameters : Array CasRuntime.RuntimeParameter) :
    MetaM PreparedRequest := do
  unless universeArguments.length == boundary.universeParams.length do
    throwError "request universe arguments do not match the checked source family"
  let universeArguments ← universeArguments.mapM instantiateLevelMVars
  if universeArguments.any (·.hasMVar) then
    throwError "request preparation requires resolved universe arguments"
  let family ← withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    empty.close (boundary.source.family.instantiateLevelParams
      boundary.universeParams universeArguments)
  let layout ← SourceLayout.ofTerm family
  let (source, application) ← if arguments.isEmpty then do
      return (← layout.inContext context, none)
    else do
      let (source, application) ← ApplicationLayout.ofSource layout context arguments
      return (source, some application)
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  prepareRequest program occurrence (.primitive boundary universeArguments) source context
    scope environment application

/-- Prepare the exact source field of the retained operand in the complete current scope. -/
opaque PreparedRequest.forProjection (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (operand : CasRuntime.ValueBinding) (index : Nat)
    (parameters : Array CasRuntime.RuntimeParameter) : MetaM PreparedRequest := do
  let some field := operand.role.fields[index]?
    | throwError "the projection is outside the retained source layout"
  unless field.wireIndex.isSome do
    throwError "a source proof field has no computational projection"
  let source ← (← field.toLayout).inContext context
  let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
  prepareRequest program occurrence (.project operand field) source context #[operand] environment none

/-- Apply the retained function with complete formal arguments and indexed actual operands.
Source coercions are lowered before this boundary. Source-only positions remain explicit empty
slots; each supplied operand is checked against that exact argument and retained in source order. -/
opaque PreparedRequest.forApplication (program : CasRuntime.RuntimeId .program)
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
  let mut values : Array (Option CasRuntime.ValueBinding) := Array.replicate arguments.size none
  for argument in actual do
    let some specified := arguments[argument.index]?
      | throwError "a runtime argument is outside the complete callable argument list"
    if (values[argument.index]?.bind id).isSome then
      throwError "a callable source argument has duplicate runtime bindings"
    let value ← environment.checkArgument specified argument
    values := values.set! argument.index (some value)
  prepareRequest program occurrence (.apply callable arguments values) source context
    (#[callable] ++ values.filterMap id) environment (some application)

/-- Responses retain actual candidate roots under source-prepared layouts.
Reference: CSLib 3951377e, Foundations/Data/PFunctor/Free.lean. -/
def OperationalSignature : PFunctor.{0, 0} :=
  ⟨PreparedRequest, fun request => CasRuntime.CandidateResponse request.source⟩

/-- CSLib retains dependent continuations for later demands and actual returned references. -/
abbrev OperationalProgram := OperationalSignature.FreeM

end CasCompiler
