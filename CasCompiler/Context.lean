module

public import Lean.Meta.Basic
public import Lean.Meta.Check
public import Lean.Meta.Coe
public import Lean.Util.CollectLevelParams

@[expose] public section

namespace CasCompiler

open Lean Meta

structure BindingId where
  session : String
  serial : Nat
  deriving BEq, Hashable, Repr, Inhabited

inductive BindingRole
  | parameter | definition | hypothesis | instance | selectedStructure | result
  deriving BEq, Repr, Inhabited

structure LocalBinding where
  id : BindingId
  role : BindingRole
  expression : Expr
  deriving Inhabited

structure ContextEntry where
  id : BindingId
  role : BindingRole
  userName : Name
  binderInfo : BinderInfo
  kind : LocalDeclKind
  type : Expr
  value : Option Expr
  nondep : Bool

structure ContextInstance where
  className : Name
  binding : BindingId

structure ContextTelescope where
  private mk ::
  entries : Array ContextEntry
  instances : Array ContextInstance

structure OpenContext where
  private mk ::
  telescope : ContextTelescope
  bindings : Array LocalBinding

structure ClosedTerm where
  private mk ::
  context : ContextTelescope
  expression : Expr
  type : Expr
  universeParams : Array Name

private def resolve (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasExprMVar || expression.hasLevelMVar || expression.hasLooseBVars then
    throwError "context publication requires a resolved expression in its local scope"
  return expression

private def closeOver (locals : Array Expr) (expression : Expr) : MetaM Expr := do
  let expression := (← resolve expression).abstract locals
  if expression.hasFVar then
    throwError "context publication contains an escaping local variable"
  return expression

/-- Capture every local declaration in order; the caller supplies stable binding identities.
The exact ordered local-instance environment uses those same stable identities.
Uses Lean's abstraction and local-context APIs at v4.33.0, with no expression-based identity.
Source/reuse record: lean-cas-dsl#66, issuecomment-6693525290. -/
opaque ContextTelescope.capture (bindings : Array LocalBinding) : MetaM OpenContext := do
  let declarations := (← getLCtx).foldl (fun result decl => result.push decl) #[]
  unless declarations.size == bindings.size do
    throwError "context capture requires a complete ordered binding map"
  let mut identities : Std.HashSet BindingId := {}
  let mut localIds : Std.HashMap FVarId BindingId := {}
  let mut locals : Array Expr := #[]
  let mut entries : Array ContextEntry := #[]
  for decl in declarations, binding in bindings do
    unless binding.expression.isFVar && binding.expression.fvarId! == decl.fvarId do
      throwError "context capture binding does not denote its ordered local declaration"
    if binding.id.session.isEmpty || identities.contains binding.id then
      throwError "context capture requires distinct session binding identities"
    identities := identities.insert binding.id
    localIds := localIds.insert decl.fvarId binding.id
    let type ← closeOver locals decl.type
    let value ← (decl.value? true).mapM (closeOver locals)
    entries := entries.push {
      id := binding.id, role := binding.role, userName := decl.userName,
      binderInfo := decl.binderInfo, kind := decl.kind, type, value, nondep := decl.isNondep }
    locals := locals.push binding.expression
  let mut instances : Array ContextInstance := #[]
  for selected in ← getLocalInstances do
    unless selected.fvar.isFVar do
      throwError "a selected local instance must denote a source declaration"
    let some binding := localIds[selected.fvar.fvarId!]?
      | throwError "a selected local instance is outside the complete source telescope"
    unless (← isClass? (← inferType selected.fvar)) == some selected.className do
      throwError "a selected local instance has an incompatible source class"
    instances := instances.push ⟨selected.className, binding⟩
  return ⟨⟨entries, instances⟩, bindings⟩

/-- Close a checked term and its full type over the captured ordered telescope. -/
opaque OpenContext.close (context : OpenContext) (expression : Expr) : MetaM ClosedTerm := do
  let expression ← resolve expression
  check expression
  let type ← resolve (← inferType expression)
  let locals := context.bindings.map (·.expression)
  let expression ← closeOver locals expression
  let type ← closeOver locals type
  let mut levels : CollectLevelParams.State := {}
  for entry in context.telescope.entries do
    levels := levels.collect entry.type
    if let some value := entry.value then levels := levels.collect value
  levels := (levels.collect expression).collect type
  return ⟨context.telescope, expression, type, levels.params⟩

/-- Reopen with fresh Lean locals, preserving stable identities, definitions and instances. -/
def ContextTelescope.withOpen [Monad m] [MonadControlT MetaM m] (context : ContextTelescope)
    (action : Array LocalBinding → m α) : m α := do
  let rec visit (entries : List ContextEntry) (bindings : Array LocalBinding) : m α := do
    match entries with
    | [] => mapMetaM (fun action => do
        let mut instances : LocalInstances := #[]
        for selected in context.instances do
          let some binding := bindings.find? (·.id == selected.binding)
            | throwError "the reopened source telescope lost a selected instance"
          instances := instances.push ⟨selected.className, binding.expression⟩
        withLCtx (← getLCtx) instances action) (action bindings)
    | entry :: rest =>
      let locals := bindings.map (·.expression)
      let type := entry.type.instantiateRev locals
      let next := fun expression =>
        visit rest (bindings.push { id := entry.id, role := entry.role, expression })
      match entry.value with
      | some value =>
        withLetDecl entry.userName type (value.instantiateRev locals) next
          (nondep := entry.nondep) (kind := entry.kind)
      | none => withLocalDecl entry.userName entry.binderInfo type next (kind := entry.kind)
  withLCtx {} #[] <| visit context.entries.toList #[]

/-- Open the stored term only within the scope of its freshly reopened context. -/
def ClosedTerm.withOpen (term : ClosedTerm)
    (action : Array LocalBinding → Expr → MetaM α) : MetaM α :=
  term.context.withOpen fun bindings =>
    action bindings (term.expression.instantiateRev (bindings.map (·.expression)))

/-- Transport into an existing scope by stable identity, preserving the ordered telescope.
Lean checks the substituted types and definitions; names and expression matches do not bind locals. -/
opaque ClosedTerm.inContext (term : ClosedTerm) (target : OpenContext) : MetaM Expr := do
  let mut available : Std.HashMap BindingId (Nat × LocalBinding) := {}
  for binding in target.bindings, index in [:target.bindings.size] do
    available := available.insert binding.id (index, binding)
  let mut locals : Array Expr := #[]
  let mut previous : Option Nat := none
  for entry in term.context.entries do
    let some (index, binding) := available[entry.id]?
      | throwError "the target context is missing a captured binding"
    if let some priorIndex := previous then
      if index ≤ priorIndex then throwError "the target context changed captured binding order"
    previous := some index
    let declaration ← getFVarLocalDecl binding.expression
    unless binding.role == entry.role && declaration.binderInfo == entry.binderInfo &&
        declaration.kind == entry.kind && declaration.isNondep == entry.nondep do
      throwError "the target context changed a captured binding role"
    unless ← isDefEq declaration.type (entry.type.instantiateRev locals) do
      throwError "the target context changed a captured binding type"
    match entry.value, declaration.value? true with
    | none, none => pure ()
    | some expected, some actual =>
      unless ← isDefEq actual (expected.instantiateRev locals) do
        throwError "the target context changed a captured definition"
    | _, _ => throwError "the target context changed a captured declaration kind"
    locals := locals.push binding.expression
  let expression ← resolve (term.expression.instantiateRev locals)
  check expression
  unless ← isDefEq (← inferType expression) (term.type.instantiateRev locals) do
    throwError "context transport changed the captured result type"
  return expression

/-- Apply complete source arguments in the current native scope, including callable coercions.
Reuse: ClosedTerm.inContext, Lean.Meta.coerceToFunction? and Lean.mkAppN at v4.33.0.
Callers close the resulting expression through the checked source publication boundary. -/
opaque OpenContext.apply (context : OpenContext) (function : ClosedTerm)
    (arguments : Array ClosedTerm) : MetaM Expr := do
  let expression ← function.inContext context
  let expression ← if (← whnf (← inferType expression)).isForall then
      pure expression
    else do
      let some coerced ← coerceToFunction? expression
        | throwError "source application requires a callable interface"
      pure coerced
  let arguments ← arguments.mapM (·.inContext context)
  return mkAppN expression arguments

end CasCompiler
