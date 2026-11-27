module

public import CasCompiler.SelectionEquality
public import CasRuntime.Identity

public section

namespace CasCompiler

open Lean Meta


def SourceSelectionScope.close (scope : SourceSelectionScope Expr) (context : OpenContext) :
    MetaM (SourceSelectionScope ClosedTerm) :=
  context.withClosing (fun _ => pure ()) fun close =>
    SourceSelectionScope.mapM close scope

def SourceSelectionScope.inContext (scope : SourceSelectionScope ClosedTerm) (context : OpenContext) :
    MetaM (SourceSelectionScope Expr) := do
  let gather : StateM (Array ClosedTerm) (SourceSelectionScope Nat) :=
    SourceSelectionScope.mapM (fun term => do
      let index := (← get).size
      modify (·.push term)
      return index) scope
  let (indexed, terms) := gather.run #[]
  let expressions ← ClosedTerm.inContextMany terms context
  SourceSelectionScope.mapM (fun index => do
    let some expression := expressions[index]?
      | throwError "a transported source selection lost an original term position"
    return expression) indexed



def SourceSelectionScope.merge (current incoming : SourceSelectionScope Expr) :
    MetaM (SourceSelectionScope Expr) := do
  let mut result := current
  for (binding, selection) in incoming.toList do
    if let some original := result[binding]? then
      unless original.exactlyMatches Expr.equal selection do
        throwError "one source binding has incompatible retained selections"
    else
      result := result.insert binding selection
  return result



def SourceSelectionScope.checkRequired {α : Type} (scope : SourceSelectionScope α)
    (context : ContextTelescope) : MetaM Unit := do
  for entry in context.entries do
    if entry.role == .selectedStructure && !scope.contains entry.id then
      throwError (MessageData.tagged `CasCompiler.SourceReadM.missingSelection
        m!"the source lost its retained typed selection")


def checkSelectedSourceContext (context : OpenContext)
    (selections : SourceSelectionScope Expr) : MetaM Unit := do
  for binding in context.bindings do
    if binding.role != .selectedStructure then continue
    let some selected := selections[binding.id]?
      | throwError (MessageData.tagged `CasCompiler.SourceReadM.missingSelection
          m!"the source lost its retained typed selection")
    let some original := binding.originalSource
      | throwError "a retained source lost a selected local's original value"
    unless !(← binding.expression.fvarId!.getDecl).isLet && original.equal selected.value do
      throwError "a retained source changed a selected local's original value"
  for (identity, _) in selections.toArray do
    unless context.bindings.any (·.id == identity) do
      throwError "a source selection is outside its complete native context"


def SourceSelectionScope.findAt? (scope : SourceSelectionScope Expr) (context : OpenContext)
    (source : Expr) : Option (SourceSelection Expr) := do
  let .fvar localId := source | none
  let binding ← context.bindings.find? (·.expression.fvarId! == localId)
  scope[binding.id]?



def SourceSelectionScope.alias (scope : SourceSelectionScope Expr) (context : OpenContext)
    (original sourceVariable : Expr) : MetaM (SourceSelectionScope Expr) := do
  let some selection := scope.findAt? context original | return scope
  let .fvar originalId := original
    | throwError "a selected source alias lost its original native binder"
  let .fvar variableId := sourceVariable
    | throwError "a selected source alias requires its explicitly introduced native binder"
  if originalId == variableId then return scope
  let some binding := context.bindings.find? (·.expression.fvarId! == variableId)
    | throwError "the selected source alias is outside its complete context"
  scope.merge (({} : SourceSelectionScope Expr).insert binding.id
    { selection with value := original })



def SourceSelectionScope.withBinding [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (identities : CasRuntime.IdentitySupply) (scope : SourceSelectionScope Expr)
    (context : OpenContext) (selection : SourceSelection Expr)
    (action : OpenContext → SourceSelectionScope Expr → Expr → m α)
    (declaredType : Option Expr := none) : m α := do
  let allocated ← liftM (m := MetaM) <| identities.fresh .sourceBinding
  let id : BindingId := ⟨allocated.worker, allocated.serial⟩
  let type ← liftM (m := MetaM) <| match declaredType with
    | some type => pure type
    | none => inferType selection.value
  context.withLocalBinding id .selectedStructure `selectedSource type
    (fun context binding => action context (scope.insert id selection) binding.expression)
    (originalSource := some selection.value) (preserveInstances := true)


def SourceSelection.abstract (selection : SourceSelection Expr)
    (formals : Array LocalBinding) : MetaM (SourceSelection Expr) := do
  unless selection.formalBindings.isEmpty do
    throwError "a source selection has already abstracted its original formals"
  if formals.isEmpty then return selection
  let result ← selection.mapM fun term =>
    mkLambdaFVars (formals.map (·.expression)) term (usedOnly := false) (usedLetOnly := false)
  let mut formalBindings := #[]
  for formal in formals do
    unless (← getFVarLocalDecl formal.expression).isLet do
      formalBindings := formalBindings.push formal.id
  return { result with formalBindings }


def SourceSelection.specialize (selection : SourceSelection Expr)
    (arguments : Array Expr) : MetaM (SourceSelection Expr) := do
  unless selection.formalBindings.size == arguments.size do
    throwError "a source selection lost its complete original formal argument table"
  if arguments.isEmpty then return selection
  let result ← selection.mapM fun term => do
    let applied := mkAppN term arguments
    check applied
    return applied.headBeta
  return { result with formalBindings := #[] }

end CasCompiler
