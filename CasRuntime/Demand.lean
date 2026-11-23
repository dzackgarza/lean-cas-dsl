module

public import CasRuntime.Invocation
public import CasCompiler.SourceReference
public import CasCompiler.SelectedField

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- The public action address of a selected family field.
The first computational field of a record uses the family address. Another field appends its
name, as the published `<functor id>#map` (api/manifest.md, "Matching and overlap"). -/
def actionAddress (reference : ComputationRef) (path : Array FieldLayout) : String :=
  match path.back? with
  | some field =>
    if field.wireIndex == some 0 then referenceId reference
    else s!"{referenceId reference}#{field.projection.getString!}"
  | none => referenceId reference

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

/-- The preceding computational fields of the prepared source record, at its actual inputs.
The ordered record layout supplies the prefix, including proof erasure. Exact source selection
identities reuse completed fields; no mathematical construction name determines dependencies. -/
partial def Kernel.earlierOutputs (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (family : PreparedRequest)
    (field : FieldLayout) (arguments : Array ClosedTerm) : MetaM (Array ValueBinding) := do
  withSourceScope request fun context bound => do
    let values := match request.action with
      | .apply _ _ values => values
      | _ => #[]
    let mut actual := #[]
    for argument in arguments, index in [:arguments.size] do
      let source ← argument.inContext context
      actual := actual.push (← match values[index]?.bind id with
        | some value => markValue kernel.marks value source
        | none => pure source)
    let mut outputs := #[]
    for preceding in family.source.fields.extract 0 field.sourceIndex do
      if preceding.wireIndex.isNone then continue
      let projection ← preceding.source.inContext context
      let term := mkAppN projection actual
      let term := match family.selection with
        | some selection => selectedField selection preceding.projection term
        | none => term
      outputs := outputs.push (← evaluateSource transaction request.program context bound term)
    return outputs

/-- Dispatch a delayed family demand whose action has reached its actual arguments.
The selected registration receives the family parameters and the action arguments.
A selected derivation is the checked plan at those same parameters, fields and arguments. -/
partial def Kernel.reach (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (parameters : Array ValueBinding) (arguments : Array ClosedTerm) :
    MetaM (PreparedResponse request) := do
  let .primitive boundary universes := family.action
    | throwError "internal: a delayed family demand lost its published boundary"
  let role := "/".intercalate (path.map (·.projection.toString)).toList
  if let .presentation _ := boundary then
    let invocation ← PreparedPresentationInvocation.prepare request family path (← transaction.view)
    let registration ← selectLift kernel.manifest invocation.operation invocation.forms
    return ← kernel.invokePresentation evaluateSource request transaction registration invocation
  let some reference := boundary.reference
    | let .lift lift := boundary
        | throwError "internal: a delayed family demand has no public address"
      -- Every lift port names its field (`<lift>#obj`), the first one included.
      let some field := path.back?
        | throwError "internal: a lift computation was applied without a selected field"
      let address := s!"{lift.lift.raw}#{field.projection.getString!}"
      let forms ← withSourceScope request fun context _ => inputForms lift.lift.raw context arguments
      let earlier ← kernel.earlierOutputs evaluateSource request transaction family field arguments
      kernel.invokeRegistration evaluateSource request transaction (← selectLift kernel.manifest address forms) role
        parameters earlier
  let address := actionAddress reference path
  let forms ← withSourceScope request fun context _ =>
    inputForms (referenceId reference) context arguments
  let forms := forms ++ family.sourceForms
  match ← kernel.profile.select kernel.manifest reference address forms with
  | .registration registration =>
    kernel.invokeRegistration evaluateSource request transaction registration role parameters #[]
  | .derivation checked =>
    evaluateRequest kernel evaluateSource request transaction fun context => do
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
        kernel.delay evaluateSource request transaction family (path.push field) captures
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
