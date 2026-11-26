module

public import CasRuntime.KernelState
public import CasRuntime.Transaction
public import CasRuntime.Association

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

abbrev SourceEvaluation := CellTransaction → RuntimeId .program → OpenContext →
  Std.HashMap BindingId ValueBinding → SourceSelectionScope Expr → Expr → MetaM ValueBinding

def RuntimeEnvironment.evaluateSource (environment : RuntimeEnvironment)
    (evaluate : SourceEvaluation) (transaction : CellTransaction) (program : RuntimeId .program)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (selections : SourceSelectionScope Expr := {}) : MetaM ValueBinding := do
  let current ← RuntimeEnvironment.captureBound environment.worker context bound
    (← transaction.view) (some environment) selections
  evaluate transaction program context bound (← current.selections.inContext context) expression

def withBoundValue [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (identities : IdentitySupply) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (source : Expr) (value : ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → Expr → m α)
    (declaredType : Option Expr := none) (binderInfo : BinderInfo := .default) :
    m α := controlAt MetaM fun run => do
  let type ← match declaredType with
    | some type => pure type
    | none => inferType source
  let mut bound := bound
  if let .fvar localId := source then
    let some binding := context.bindings.find? (·.expression.fvarId! == localId)
      | throwError "a runtime occurrence is outside its complete source context"
    if let some original := bound[binding.id]? then
      unless retainsReference original value do
        throwError (MessageData.tagged `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch
          "a runtime occurrence changed its original source binding")
    bound := bound.insert binding.id value
    if ← withoutModifyingState (isDefEq (← inferType source) type) then
      return ← run (action context bound source)
  let allocated ← identities.fresh .sourceBinding
  let id : BindingId := ⟨allocated.worker, allocated.serial⟩
  context.withLocalBinding id .result `runtimeValue type
    (fun context binding => run (action context (bound.insert id value) binding.expression))
    (originalSource := some source) (binderInfo := binderInfo)

def withApplicationInputs [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (identities : IdentitySupply) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (function : Expr) (sources : Array Expr)
    (values : Array (Option ValueBinding))
    (action : OpenContext → Std.HashMap BindingId ValueBinding → Array Expr → m α) :
    m α := controlAt MetaM fun run => do
  unless sources.size == values.size do
    throwError "native application binding lost its complete original argument table"
  context.withOriginalSources #[mkAppN function sources] fun original =>
    check original[0]!
  let rec visit (remaining : List (Expr × Option ValueBinding))
      (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
      (type : Expr) (actual : Array Expr) : MetaM (stM MetaM m α) := do
    match remaining with
    | [] =>
      check (mkAppN function actual)
      run (action context bound actual)
    | (source, value) :: rest =>
      let .forallE name domain body binderInfo ← whnf type
        | throwError "native application binding lost an original formal argument"
      let next := fun context bound argument =>
        visit rest context bound (body.instantiate1 argument) (actual.push argument)
      match value with
      | some value =>
        withBoundValue identities context bound source value next
          (declaredType := some domain) (binderInfo := binderInfo)
      | none =>
        if source.isFVar && (← withoutModifyingState (isDefEq (← inferType source) domain)) then
          return ← next context bound source
        let allocated ← identities.fresh .sourceBinding
        let id : BindingId := ⟨allocated.worker, allocated.serial⟩
        let role := if ← isProp domain then BindingRole.hypothesis else BindingRole.parameter
        context.withLocalBinding id role name domain
          (fun context binding => next context bound binding.expression)
          (originalSource := some source) (binderInfo := binderInfo)
  visit (sources.zip values).toList context bound (← inferType function) #[]

def portFailure (error : PortError) : MetaM α :=
  throwStratum error.stratum error.render

def transactionFailure (failure : TransactionFailure) : MetaM α :=
  match failure with
  | .settled => throwStratum .unavailable "cancelled"
  | .staleOwner | .reservation .staleOwner => throwStratum .unavailable "stale_owner"
  | .reservation .consumed => throwStratum .unavailable "reserved_without_receipt"
  | .reservation .wrongConnection => throwStratum .unavailable "stale_owner"
  | failure => throwError "internal: the active transaction rejected a completion: {repr failure}"

def kernelCompletion (request : PreparedRequest) (transaction : CellTransaction)
    (value : ValueBinding) (resolve : Option (FixedInput → MetaM ValueBinding) := none) :
    MetaM (PreparedResponse request) := do
  let detail := Json.mkObj [
    ("program", Observation.identityJson request.program),
    ("occurrence", Observation.identityJson request.occurrence),
    ("preparation", Observation.identityJson request.roles.scope.preparation),
    ("transaction", Observation.identityJson transaction.id)]
  CasTools.Diagnostics.emit "kernel.completion.resolve.started" detail
  let fixed ← request.resolveFixedResults transaction request.source value resolve
  CasTools.Diagnostics.emit "kernel.completion.resolve.completed" detail
  let draft ← transaction.draft
  CasTools.Diagnostics.emit "kernel.completion.associate.started" detail
  let (draft, value) ← request.associateResult transaction.owners.identities
    request.source draft value fixed (complete := true)
  CasTools.Diagnostics.emit "kernel.completion.associate.completed" detail
  CasTools.Diagnostics.emit "kernel.completion.admit.started" detail
  let response ← request.admitResult draft.view value
  CasTools.Diagnostics.emit "kernel.completion.admit.completed" detail
  match ← transaction.installDraft draft with
  | .error failure => transactionFailure failure
  | .ok () => pure ()
  CasTools.Diagnostics.emit "kernel.completion.complete.started" detail
  match ← transaction.completeKernel request response with
  | .error failure => transactionFailure failure
  | .ok association =>
    CasTools.Diagnostics.emit "kernel.completion.complete.completed" detail
    CasTools.Diagnostics.emit "kernel.completion.readmit.started" detail
    let response ← request.admitResult (← transaction.view) association.response.root
    CasTools.Diagnostics.emit "kernel.completion.readmit.completed" detail
    return response

def PreparedRequest.withArguments [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (request : PreparedRequest) (_identities : IdentitySupply)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding) (count : Nat)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → Array Expr →
      Array (Option ValueBinding) → m α) : m α :=
  controlAt MetaM fun run =>
    request.environment.withContext context bound fun context bound => do
      request.withInputBindings context bound count fun context bound arguments values =>
        run (action context bound arguments values)

def withSourceScope [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (request : PreparedRequest)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → m α) : m α :=
  controlAt MetaM fun run =>
    request.environment.context.withOpenContext fun context =>
      run (action context request.environment.bound)

def withNativeInterface [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (identities : IdentitySupply) (graph : ValueGraph) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (selections : SourceSelectionScope Expr)
    (value : ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Expr → m α) : m α :=
  controlAt MetaM fun run =>
    withBindingContext graph context bound value fun context bound => do
      let selections ← SourceSelectionScope.merge selections
        (← value.role.selections.inContext context)
      let selections ← match value.admittedInterface? with
        | none => pure selections
        | some native => do
          let retained ← native.role.selections.inContext context
          SourceSelectionScope.merge selections retained
      let source ← value.nativeInterface.selectedSource context
      withBoundValue identities context bound source value fun context bound source =>
        run (action context bound selections source)

def projectTerm (value : Expr) (field : FieldLayout) : MetaM Expr := do
  let some info := (← getEnv).getProjectionFnInfo? field.projection
    | throwError "internal: a prepared field has no native projection"
  return .proj (← getConstInfoCtor info.ctorName).induct info.i value

def FixedInput.resolveInContext (input : FixedInput) (identities : IdentitySupply)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (selections : SourceSelectionScope Expr) (graphView : MetaM ValueGraph)
    (evaluate : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Expr → MetaM ValueBinding) : MetaM ValueBinding := do
  let rec visit (path : List Name) (context : OpenContext)
      (bound : Std.HashMap BindingId ValueBinding) (selections : SourceSelectionScope Expr)
      (parent : ValueBinding) : MetaM ValueBinding := do
    match path with
    | [] => pure parent
    | projection :: rest =>
      let graph ← graphView
      withNativeInterface identities graph context bound selections parent
          fun context bound selections parentTerm => do
        let some field := parent.nativeRole.fields.find? (·.projection == projection)
          | throwError "a fixed input lost its prepared native projection"
        let projected ← projectTerm parentTerm field
        let value ← evaluate context bound selections projected
        let graph ← graphView
        let some _ ← IO.ofExcept <|
            (graph.projectionBasis value parent #[projection]).mapError IO.userError
          | throwError "a fixed input demand lost its actual projection association"
        visit rest context bound selections value

  discard <| input.source.inContext context
  visit input.path.toList context bound selections input.parent

def Kernel.resolveFixedInput (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (transaction : CellTransaction) (program : RuntimeId .program) (input : FixedInput) :
    MetaM ValueBinding := do
  input.source.withOpen fun bindings _ => do
    unless input.parameters.size == input.source.context.entries.size do
      throwError "a fixed input lost its original source context table"
    let context ← ContextTelescope.capture bindings
    let mut bound : Std.HashMap BindingId ValueBinding := {}
    for (entry, value) in input.source.context.entries.zip input.parameters do
      if let some value := value then bound := bound.insert entry.id value
    let graph ← transaction.view
    withBindingContext graph context bound input.parent fun context bound => do
      let selections ← input.parent.role.selections.inContext context
      input.resolveInContext kernel.ledger.owners.identities context bound selections
        (liftM (m := IO) transaction.view) fun context bound selections expression => do
          let environment ← RuntimeEnvironment.captureBound kernel.ledger.owners.worker
            context bound (← transaction.view) (selections := selections)
          evaluateSource transaction program context bound
            (← environment.selections.inContext context) expression

end CasRuntime
