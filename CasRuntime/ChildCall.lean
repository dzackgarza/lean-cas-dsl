module

public import CasRuntime.ExecutionContext
public import CasCompiler.Elaborate
public import CasRuntime.Literal

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- An operand of a child call at its declared type. A scoped reference is its retained value; a
structure given as an array is read field by field at the constructor's field types, so a
reference may stand at any position (`[resultRef, 46]` for a pair); anything else is a scalar
literal. Reuse: Lean structure constructors and ScalarLiteral.readAt. -/
private partial def childOperand (marks : IO.Ref (Array ValueBinding)) (context : OpenContext)
    (retained : Json → MetaM (Option ValueBinding)) (domain : Expr) (packet : Json) :
    MetaM Expr := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred operand {packet.compress}: {reason}"
  if let some binding ← retained packet then
    let source ← binding.role.source.inContext context
    unless ← isDefEq (← inferType source) domain do
      malformed "a referenced operand has a different declared type"
    return ← markValue marks binding source
  let domain ← whnfR (← instantiateMVars domain)
  if let (.arr components, .const owner levels) := (packet, domain.getAppFn) then
    if let some info := getStructureInfo? (← getEnv) owner then
      let constructor := getStructureCtor (← getEnv) owner
      unless components.size == info.fieldNames.size do
        malformed "the structure operand has a different number of fields"
      let mut value := mkAppN (.const constructor.name levels) domain.getAppArgs
      for component in components do
        let .forallE _ field _ _ ← whnf (← inferType value)
          | malformed "the structure operand has more fields than its constructor"
        value := mkApp value (← childOperand marks context retained field component)
      return value
  let some literal ← ScalarLiteral.readAt domain packet
    | malformed "an inline operand has no scalar reading at its declared type"
  return literal

/-- Run one call of a deferred group through the production lowerer and executor.
Source: execution contract v2 §4 and §6; api/python-sdk.md of the leaf contract.
A reference is resolved in the call's own scope and keeps its retained value. An inline
operand is read at the declared type of its position. `$cas.project` and `$cas.apply` act on
a retained value. Any other call names a published operation with its dependent context.
Lean checks the complete call before any dispatch. -/
partial def Kernel.child (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (call : Json) : MetaM ValueBinding := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred call {call.compress}: {reason}"
  let graph ← transaction.view
  let retained : Json → MetaM (Option ValueBinding) := fun packet => do
    match ScopedReference.parse? packet with
    | .error reason => malformed reason
    | .ok none => return none
    | .ok (some reference) =>
      let #[binding] ← scope.resolveMany reservation graph scope.wireId #[reference]
        | throwError "internal: one scoped reference resolved to several values"
      return some binding
  let operation ← match call.getObjValAs? String "op" with
    | .ok operation => pure operation
    | .error reason => malformed reason
  let arguments ← match call.getObjVal? "args" with
    | .ok arguments => pure arguments
    | .error reason => malformed reason
  let list : Json → String → MetaM (Array Json) := fun packet key =>
    match (packet.getObjVal? key).bind (·.getArr?) with
    | .ok values => pure values
    | .error reason => malformed reason
  withSourceScope request fun context bound => do
    let reference : Json → MetaM (ValueBinding × Expr) := fun packet => do
      let some binding ← retained packet | malformed "the acted value must be a scoped reference"
      return (binding, ← markValue kernel.marks binding (← binding.role.source.inContext context))
    -- Apply to every wire operand in order. A formal proof premise has no wire position.
    let applied : Expr → Array Json → MetaM Expr := fun function packets => do
      let mut term := function
      for packet in packets do
        let .forallE _ domain _ _ ← whnf (← inferType term)
          | malformed "more operands than the declared interface"
        if ← isProp domain then malformed "the call requires a formal premise that no leaf supplies"
        term := mkApp term (← childOperand kernel.marks context retained domain packet)
      return term
    let term ← if operation == "$cas.project" then do
        let (binding, source) ← reference ((arguments.getObjVal? "value").toOption.getD .null)
        let position ← match arguments.getObjValAs? Nat "field" with
          | .ok position => pure position
          | .error reason => malformed reason
        let some field := binding.role.fields.find? (·.wireIndex == some position)
          | malformed "the field is outside the prepared record interface"
        projectTerm source field
      else if operation == "$cas.apply" then do
        let (_, source) ← reference ((arguments.getObjVal? "value").toOption.getD .null)
        applied source (← list arguments "arguments")
      else do
        let state ← semanticState
        let mut term ← if let some (row, port) := publishedLift? state operation then do
            -- A lift port: the lift's computation at the evidence parameters, sent to the port.
            let family ← LiftFamily.forLift row port
            let (head, _) ← family.instantiate
            pure (family.mark (← applied head (← list arguments "parameters")))
          else do
            let some family := publishedFamily? state operation
              | malformed "the operation is not a published address"
            let declaration ← family.declaration state
            let selected := match family with
              | .method id => sourceReference ``MethodEntry id.raw declaration
              | .construction id => sourceReference ``ConstructionEntry id.raw declaration
              | .functor id => sourceReference ``EdgeRef.functor id.raw declaration
              | .operation _ | .morphism _ => id
            applied (selected (← mkConstWithFreshMVarLevels declaration))
              (← list arguments "parameters")
        let role ← match arguments.getObjValAs? String "prepared_role" with
          | .ok role => pure role
          | .error reason => malformed reason
        for name in (role.splitOn "/").filter (!·.isEmpty) do
          let some info := (← getEnv).getProjectionFnInfo? name.toName
            | malformed s!"{name} is not a field of the published interface"
          term := .proj (← getConstInfoCtor info.ctorName).induct info.i term
        applied term (← list arguments "arguments")
    let term ← instantiateMVars term
    if term.hasMVar || term.hasLevelMVar then malformed "the call leaves a parameter undetermined"
    evaluateSource transaction request.program context bound term

end CasRuntime
