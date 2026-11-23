module

public import CasRuntime.ExecutionContext
public import CasCompiler.SourceReference
public import CasRuntime.Literal

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual

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
  if let .ok address := packet.getObjValAs? String "ctor" then
    if let some row := (← semanticState).objects.find? (·.id.raw == address) then
      match checkServiceFields #["ctor", "args"] packet with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← match (packet.getObjVal? "args").bind (·.getArr?) with
        | .ok fields => pure fields
        | .error reason => malformed reason
      discard <| checkedDeclaration row.declaration
      let head ← mkConstWithFreshMVarLevels row.declaration
      let value ← childExplicit marks context retained head fields (some domain)
      return sourceReference ``ObjectEntry row.id.raw row.declaration value
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

/-- Apply only the explicitly declared computational parameter positions of a named input
family. Native implicit parameters stay in the full telescope and must be determined by the
actual input types. A proof premise is never read from a provider packet. -/
private partial def childExplicit (marks : IO.Ref (Array ValueBinding)) (context : OpenContext)
    (retained : Json → MetaM (Option ValueBinding)) (head : Expr) (packets : Array Json)
    (expected : Option Expr := none) : MetaM Expr := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred named parameters: {reason}"
  let (parameters, binders, result) ← forallMetaTelescopeReducing (← inferType head)
  if let some expected := expected then
    unless ← isDefEq result expected do
      malformed "the named input has a different complete declared type"
  let mut next := 0
  for parameter in parameters, binder in binders do
    let domain ← inferType parameter
    if !binder.isExplicit || (← isProp domain) then continue
    let some packet := packets[next]?
      | malformed "the named input is missing an explicit parameter"
    let value ← childOperand marks context retained domain packet
    unless ← isDefEq parameter value do
      malformed "a named input parameter has a different declared type"
    next := next + 1
  unless next == packets.size do malformed "the named input has extra parameters"
  let value ← instantiateMVars (mkAppN head parameters)
  if value.hasMVar || value.hasLevelMVar then
    malformed "the named input leaves a complete source parameter undetermined"
  return value

end

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
      else if let some row := publishedPresentation? (← semanticState) operation then do
        match checkServiceFields #["ctor", "args"] arguments with
        | .error reason => malformed reason
        | .ok () => pure ()
        let packet ← match PresentationInvocation.decode arguments with
          | .ok packet => pure packet
          | .error reason => malformed reason
        let family ← PresentationFamily.forEntry row
        let (head, _) ← family.instantiate
        let iso ← childExplicit kernel.marks context retained head packet.parameters
        let (first, second) ← family.endpoints iso
        let (source, target) := if packet.inverse then (second, first) else (first, second)
        let source ← childOperand kernel.marks context retained (← inferType source) packet.source
        let target ← childOperand kernel.marks context retained (← inferType target) packet.target
        let (first, second) := if packet.inverse then (target, source) else (source, target)
        let iso ← try family.withEndpoints iso first second
          catch error => malformed s!"the comparison endpoints do not match the selected family: {← error.toMessageData.toString}"
        let function ← family.function iso packet.inverse
        let .forallE _ domain _ _ ← whnf (← inferType function)
          | malformed "the presentation has no native point function"
        let point ← childOperand kernel.marks context retained domain packet.argument
        pure (mkApp function point)
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
