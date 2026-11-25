module

public import CasRuntime.ExecutionContext
public import CasCompiler.PublishedSource
public import CasRuntime.Literal
public import CasRuntime.Encode
public import CasRuntime.RoutedMethod
public import CasRuntime.Property
public import CasRuntime.ConstructionSource

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Read only the value marker returned by this request's own operand binding hook.
No matching source expression, carrier, endpoint or provider descriptor can manufacture
that authority. The current graph checks visibility before the value is used again. -/
private def boundSourceValue (kernel : Kernel) (transaction : CellTransaction)
    (source : Expr) : MetaM ValueBinding := do
  let .mdata data _ := source
    | throwError "the prepared source operand lost its actual bound marker"
  let some index := markedKey? data
    | throwError "the prepared source operand lost its actual bound identity"
  let some value := (← kernel.marks.get)[index]?
    | throwError "the prepared source operand names an unavailable bound identity"
  discard <| IO.ofExcept <| ((← transaction.view).requiredOwners #[value]).mapError IO.userError
  return value

/-- Adapt the released service frame to the common compiler source entrance, then run the
ordinary lowerer and executor. This module owns scoped-reference resolution, original value
binding and owner/form admission. The compiler owns the whole typed application, native
premises, selected routes and complete dependent parameters, exactly as for ordinary source.
Source: execution contract v2 sections 4 and 6; api/python-sdk.md of the leaf contract. -/
partial def Kernel.child (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (call : Json) : MetaM ValueBinding := do
  let malformed : {α : Type} → MessageData → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred call {call.compress}: {reason}"
  let retained : Json → MetaM (Option ValueBinding) := fun packet => do
    match ScopedReference.parse? packet with
    | .error reason => malformed reason
    | .ok none => return none
    | .ok (some reference) =>
      let #[binding] ← scope.resolveMany reservation (← transaction.view) scope.wireId #[reference]
        | throwError "internal: one scoped reference resolved to several values"
      return some binding
  withSourceScope request fun context bound => do
    let sourceFor := fun (value : ValueBinding) => do
      markValue kernel.marks value (← value.role.source.inContext context)
    let readRetained := fun packet => do
      (← retained packet).mapM sourceFor
    let source : PublishedSourceContext := {
      scope := context
      retained := readRetained
      literal := ScalarLiteral.readAt
      bind := fun term => do
        let value ← evaluateSource transaction request.program context bound term
        markValue kernel.marks value term
      rebind := fun original selected => do
        let value ← boundSourceValue kernel transaction selected
        markValue kernel.marks value original
      methodParameters := fun family parameters receiver => do
        let receiver ← boundSourceValue kernel transaction receiver
        try
          request.environment.methodParameters context transaction kernel.marks kernel.ledger.allocate
            family parameters receiver
            (evaluateSource transaction request.program context bound) request.observation.sourceSnapshot
        catch error =>
          malformed m!"the original receiver's category inputs disagree: {error.toMessageData}"
      checkInput := fun expected selected => do
        let value ← boundSourceValue kernel transaction selected
        try
          request.environment.checkDeclaredInput context (← transaction.view)
            (← kernel.marks.get) expected value
        catch error => malformed m!"a complete action parameter disagrees: {error.toMessageData}"
      admitMethod := fun family receiver input => do
        unless ← CasRuntime.RoutedMethodFamily.admitsSourceForm family receiver input do
          malformed "the input form is not the original receiver's source boundary"
      admitProperty := fun family receiver input => do
        let some boundary := (← routedSourceBoundaries family.route receiver)[0]?
          | malformed "the property lost its original source boundary"
        unless boundary.forms.contains input do
          malformed "the input form is not the original receiver's source boundary"
      admitPoint := fun family selected => do
        let value ← boundSourceValue kernel transaction selected
        match family.owner with
        | .morphism row =>
          discard <| InputDescriptorView.requireMorphism (← transaction.view)
            (← kernel.codes.get) value row.id
        | .application row =>
          discard <| InputDescriptorView.requireApplication (← transaction.view)
            (← kernel.codes.get) value row.id
      admitCategorical := fun family parameters selected => do
        let value ← boundSourceValue kernel transaction selected
        let graph ← transaction.view
        let view ← InputDescriptorView.requireCategorical graph (← kernel.codes.get) value family
        let some original := view.family
          | malformed "the categorical arrow lost its original source preparation"
        let values := original.origin.application.map (·.arguments) |>.getD #[]
        unless parameters.size == values.size do
          malformed "the categorical arrow changed its complete original parameter telescope"
        for expected in parameters, supplied in values do
          match supplied with
          | some actual =>
            request.environment.checkDeclaredInput context graph (← kernel.marks.get) expected actual
          | none =>
            unless ← isProof expected do
              malformed "the categorical arrow lost an original computational parameter"
      projection := fun packet position => do
        let some value ← retained packet | malformed "the acted value must be a scoped reference"
        let some field := value.role.fields.find? (·.wireIndex == some position)
          | malformed "the field is outside the prepared record interface"
        return (← sourceFor value, field.projection) }
    let source := { source with
      constructionCone := fun packet => do
        kernel.retainedConstructionCone transaction (← transaction.view) context retained packet
      creationOwner := fun packet => do
        kernel.retainedCreationOwner (← transaction.view) context retained packet }
    let term ← Elab.Term.TermElabM.run' do
      Elab.Term.withSynthesize do PublishedSource.prepare source call
    evaluateSource transaction request.program context bound term

end CasRuntime

