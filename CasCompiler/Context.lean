import Lean.Meta.Basic
import Lean.Meta.Check
import Lean.Util.CollectLevelParams

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

structure ContextTelescope where
  private mk ::
  entries : Array ContextEntry

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
Uses Lean's abstraction and local-context APIs at v4.33.0, with no expression-based identity.
Source/reuse record: lean-cas-dsl#66, issuecomment-6693525290. -/
def ContextTelescope.capture (bindings : Array LocalBinding) : MetaM OpenContext := do
  let declarations := (← getLCtx).foldl (fun result decl => result.push decl) #[]
  unless declarations.size == bindings.size do
    throwError "context capture requires a complete ordered binding map"
  let mut identities : Std.HashSet BindingId := {}
  let mut locals : Array Expr := #[]
  let mut entries : Array ContextEntry := #[]
  for decl in declarations, binding in bindings do
    unless binding.expression.isFVar && binding.expression.fvarId! == decl.fvarId do
      throwError "context capture binding does not denote its ordered local declaration"
    if binding.id.session.isEmpty || identities.contains binding.id then
      throwError "context capture requires distinct session binding identities"
    identities := identities.insert binding.id
    let type ← closeOver locals decl.type
    let value ← (decl.value? true).mapM (closeOver locals)
    entries := entries.push {
      id := binding.id, role := binding.role, userName := decl.userName,
      binderInfo := decl.binderInfo, kind := decl.kind, type, value, nondep := decl.isNondep }
    locals := locals.push binding.expression
  return ⟨⟨entries⟩, bindings⟩

/-- Close a checked term and its full type over the captured ordered telescope. -/
def OpenContext.close (context : OpenContext) (expression : Expr) : MetaM ClosedTerm := do
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
def ContextTelescope.withOpen (context : ContextTelescope)
    (action : Array LocalBinding → MetaM α) : MetaM α := do
  let rec visit (entries : List ContextEntry) (bindings : Array LocalBinding) : MetaM α := do
    match entries with
    | [] => action bindings
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

end CasCompiler
