module

public import CasRuntime.Invocation
public import CasCompiler.SourceReference
public import CasCompiler.SelectedField
public import CasCompiler.RecordAction

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Input addresses of this exact invocation: the complete-request form, and the exact form and
category of each argument that is a registered named object. -/
def inputForms (family : String) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM (Array String) := do
  let state ← semanticState
  -- Named morphisms publish their own raw complete-declaration request address.
  let own := if state.morphisms.any (·.id.raw == family) then family else s!"{family}#input"
  let mut forms := #[own]
  for argument in arguments do
    if let some (id, _) ← sourceObjectReference? (← argument.inContext context) then
      if let some entry := state.objects.find? (·.id == id) then
        forms := forms ++ #[entry.id.raw, entry.category.raw]
  return forms

/-- Retain a published family, or one more selected field of it, as a delayed demand. -/
def Kernel.delay (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (captures : Array ValueBinding) : MetaM (PreparedResponse request) := do
  let program ← kernel.ledger.owners.identities.fresh .program
  kernel.codes.modify (·.insert program (.family family path))
  let value ← transaction.stage (← request.originFor request.source) (.closure program captures)
  kernelCompletion request transaction value
    (some (kernel.resolveFixedInput evaluateSource transaction request.program))

/-- Evaluate a checked source term for a claimed demand and complete that demand. -/
private def evaluateRequest (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction)
    (build : OpenContext → MetaM Expr) : MetaM (PreparedResponse request) := do
  let value ← withSourceScope request fun context bound => do
    evaluateSource transaction request.program context bound
      (← build context)
  kernelCompletion request transaction value
    (some (kernel.resolveFixedInput evaluateSource transaction request.program))

/-- Prepare record invocation inputs from the exact retained family result. Only the
source compiler determines their native slots and applications. The original completion
is selected by occurrence and preparation identity, never by expression or type. -/
private def Kernel.prepareRecordAction (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (boundary : ProgramBoundary)
    (universes : List Level) (path : Array FieldLayout) (arguments : Array ClosedTerm) :
    MetaM RecordAction := do
  withSourceScope request fun context bound => do
    let _ := bound
    let mut parent ← family.source.source.inContext context
    if !path.isEmpty then
      let some completion ← transaction.completionFor? family.occurrence
        | throwError "the delayed record lost its original completed family"
      family.requirePreparation completion.request.roles.scope
      parent ← markValue kernel.marks completion.response.root parent
    let formal := family.application.map (·.arguments.map (·.source.source)) |>.getD #[]
    let supplied := family.origin.application.map (·.arguments) |>.getD #[]
    unless formal.size == supplied.size do
      throwError "the record family lost its original complete parameter references"
    let mut parameters := #[]
    for parameter in formal, index in [:formal.size] do
      let source ← parameter.inContext context
      parameters := parameters.push (← match supplied[index]?.bind id with
        | some value => markValue kernel.marks value source
        | none => pure source)
    let values := match request.action with
      | .apply _ _ values => values
      | _ => #[]
    let mut actual := #[]
    for argument in arguments, index in [:arguments.size] do
      let source ← argument.inContext context
      actual := actual.push (← match values[index]?.bind id with
        | some value => markValue kernel.marks value source
        | none => pure source)
    RecordAction.prepare boundary universes context family.source parent path parameters actual
      family.selection

/-- Materialize only the source-prepared invocation slots, after realization selection.
The same path handles ordinary records and released record packets. -/
private def Kernel.recordInputs (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (action : RecordAction) :
    MetaM (Array (Nat × ValueBinding)) := do
  let _ := kernel
  withSourceScope request fun context bound => do
    action.inputs.mapM fun input => do
      let source ← input.source.inContext context
      return (input.sourceIndex,
        ← evaluateSource transaction request.program context bound source)

/-- Dispatch a delayed family demand whose action has reached its actual arguments.
The selected registration receives the family parameters and the action arguments.
A selected derivation is the checked plan at those same parameters, fields and arguments. -/
partial def Kernel.reach (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (parameters : Array ValueBinding) (arguments : Array ClosedTerm) :
    MetaM (PreparedResponse request) := do
  let .primitive boundary universes := family.action
    | throwError "internal: a delayed family demand lost its published boundary"
  if let .property _ := boundary then
    unless path.isEmpty && parameters.isEmpty && request.occurrence == family.occurrence do
      throwError "a property observation lost its complete original primitive request"
    let route ← PreparedPropertyRoute.prepare kernel (← transaction.view) request
    let selected ← route.select kernel.profile kernel.manifest
    let invocation ← selected.materialize kernel evaluateSource request transaction
    return ← kernel.invokeProperty evaluateSource request transaction invocation
  if let .routedMethod _ := boundary then
    let route ← PreparedMethodRoute.prepare kernel (← transaction.view)
      request family path parameters
    let selection ← route.select kernel.profile kernel.manifest
    let selected ← selection.materialize kernel evaluateSource request transaction
    return ← match selection.realization with
      | .registration _ => do
        let invocation ← selected.invocation kernel evaluateSource request transaction
        kernel.invokeMethod evaluateSource request transaction invocation
      | .derivation _ =>
        selected.derivation kernel evaluateSource request transaction
  let role := "/".intercalate (path.map (·.projection.toString)).toList
  if let .presentation selected := boundary then
    let invocation ← PreparedPresentationInvocation.prepare request family path (← transaction.view)
      (← kernel.codes.get) (← kernel.marks.get)
    let registration ← selectLift kernel.profile kernel.manifest (.presentation selected.entry.id)
      invocation.operation invocation.forms
    return ← kernel.invokePresentation evaluateSource request transaction registration invocation
  if let .application selected := boundary then
    let .application entry := selected.owner
      | throwError "the delayed object application changed its exact owner kind"
    let some invocation ← PreparedPointInvocation.prepare? kernel evaluateSource request family path transaction
      | throwError "the object application lost its complete original point interface"
    let registration ← selectLift kernel.profile kernel.manifest (.application entry.id)
      invocation.operation invocation.forms
    return ← kernel.invokePoint evaluateSource request transaction registration invocation
  let action ← kernel.prepareRecordAction request transaction family boundary universes path arguments
  let point ← PreparedPointInvocation.prepare? kernel evaluateSource request family path transaction
  let address := point.map (·.operation) |>.getD action.address
  let forms ← match point with
    | some point => pure point.forms
    | none => withSourceScope request fun context _ => do
      return (← inputForms action.familyAddress context arguments)
  let realization : Realization ← match action.owner with
    | .computation reference => kernel.profile.select kernel.manifest reference address forms
    | .lift id => Realization.registration <$>
        selectLift kernel.profile kernel.manifest (.lift id) address forms
  match realization with
  | .registration registration =>
    match point with
    | some point => kernel.invokePoint evaluateSource request transaction registration point
    | none => do
      let inputs ← kernel.recordInputs evaluateSource request transaction action
      kernel.invokeRegistration evaluateSource request transaction registration role parameters inputs
  | .derivation checked =>
    evaluateRequest kernel evaluateSource request transaction fun context => do
      let plan ← checked.instantiate universes
      let formal : Array ClosedTerm := match family.application with
        | none => #[]
        | some application => application.arguments.map (·.source.source)
      let supplied := family.origin.application.map (·.arguments) |>.getD #[]
      unless formal.size == supplied.size do
        throwError "the source derivation lost its original complete parameter references"
      let mut parameters := #[]
      for parameter in formal, index in [:formal.size] do
        let source ← parameter.inContext context
        parameters := parameters.push (← match supplied[index]?.bind id with
          | some value => markValue kernel.marks value source
          | none => pure source)
      let mut term := plan.betaRev parameters.reverse (preserveMData := true)
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
      return term.betaRev actual.reverse (preserveMData := true)

/-- The kernel-owned concrete executor of prepared demands (T013).
A published family whose value is a callable or a record is retained as a delayed demand.
A field of retained code extends that demand or lowers the source field. An application
dispatches the delayed family on its selected realization, evaluates retained source code at
the actual arguments, or invokes the native export on its original connection. -/
partial def Kernel.execute (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  match request.action with
  | .primitive .. =>
    if request.source.kind == .function || request.source.kind == .record then
      return ← kernel.delay evaluateSource request transaction request #[] request.scope
    let arguments : Array ClosedTerm := match request.application with
      | none => #[]
      | some application => application.arguments.map (·.source.source)
    kernel.reach evaluateSource request transaction request #[] #[] arguments
  | .project operand field =>
    let some node := graph.find operand.value
      | throwError "internal: the projected value is outside the active graph"
    match node.payload.data with
    | .closure program captures =>
      match (← kernel.codes.get)[program]? with
      | some (.family family path) =>
        if request.source.kind == .function || request.source.kind == .record then
          kernel.delay evaluateSource request transaction family (path.push field) captures
        else
          kernel.reach evaluateSource request transaction family (path.push field) captures #[]
      | some (.term source) =>
        evaluateRequest kernel evaluateSource request transaction fun context => do
          projectTerm (← source.inContext context) field
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. =>
      kernel.invokeExport evaluateSource request transaction operand s!"project:{field.projection}"
    | .container container =>
      if container.fields.isSome then
        throwError "internal: a stored field reached the executor"
      throwStratum .noImplementation
        m!"the retained descriptor supplies no native data for {field.projection}"
    | _ => throwError "internal: a stored field reached the executor"
  | .apply callable arguments values =>
    let code ← IO.ofExcept <| (graph.callable callable).mapError IO.userError
    let some node := graph.find code.value
      | throwError "internal: the applied value is outside the active graph"
    match node.payload.data with
    | .closure program captures =>
      match (← kernel.codes.get)[program]? with
      | some (.family family path) =>
        kernel.reach evaluateSource request transaction family path captures arguments
      | some (.term source) =>
        evaluateRequest kernel evaluateSource request transaction fun context => do
          let mut actual := #[]
          for argument in arguments, index in [:arguments.size] do
            let term ← argument.inContext context
            actual := actual.push (← match values[index]?.bind id with
              | some value => markValue kernel.marks value term
              | none => pure term)
          return (mkAppN (← source.inContext context) actual).headBeta
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. => kernel.invokeExport evaluateSource request transaction callable "apply"
    | _ => throwError "internal: the applied value has no code or native export"

end CasRuntime
