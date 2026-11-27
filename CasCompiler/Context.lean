module

public import Lean.Meta.Basic
public import Lean.Meta.Check
public import Lean.Meta.Coe
public import Lean.Util.CollectLevelParams
public import CasCompiler.NativeDeclarations
public import CasTools.Diagnostics

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

  originalSource : Option Expr := none
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

  originalSource : Option Expr := none

structure ContextInstance where
  className : Name
  binding : BindingId

structure ContextTelescope where
  private mk ::
  entries : Array ContextEntry
  instances : Array ContextInstance
  nativeDeclarations : NativeDeclarations




private def ContextTelescope.exactlyMatchesReference (left right : ContextTelescope) : Bool := Id.run do
  unless left.entries.size == right.entries.size &&
      left.instances.size == right.instances.size &&
      left.nativeDeclarations.exactlyMatches right.nativeDeclarations do
    return false
  for first in left.entries, second in right.entries do
    unless first.id == second.id && first.role == second.role &&
        first.userName == second.userName && first.binderInfo == second.binderInfo &&
        first.kind == second.kind && first.nondep == second.nondep &&
        first.type.equal second.type do
      return false
    match first.value, second.value with
    | none, none => pure ()
    | some original, some current =>
      unless original.equal current do return false
    | _, _ => return false
    match first.originalSource, second.originalSource with
    | none, none => pure ()
    | some original, some current =>
      unless original.equal current do return false
    | _, _ => return false
  for first in left.instances, second in right.instances do
    unless first.className == second.className && first.binding == second.binding do
      return false
  return true

private unsafe def ContextTelescope.exactlyMatchesUnsafe
    (left right : ContextTelescope) : Bool :=
  if ptrEq left right then true
  else ContextTelescope.exactlyMatchesReference left right



@[implemented_by ContextTelescope.exactlyMatchesUnsafe]
opaque ContextTelescope.exactlyMatches (left right : ContextTelescope) : Bool :=
  ContextTelescope.exactlyMatchesReference left right

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
  nativeDeclarations : NativeDeclarations

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

private def ContextTelescope.withOpenCore [Monad m] [MonadControlT MetaM m]
    (context : ContextTelescope) (interpretSources : Bool)
    (action : Array LocalBinding → m α) : m α := do

  let rec visit (entries : List ContextEntry) (bindings : Array LocalBinding)
      (locals : Array Expr) : m α := do
    match entries with
    | [] => mapMetaM (fun action => do
        let mut instances : LocalInstances := #[]
        for selected in context.instances do
          let some binding := bindings.find? (·.id == selected.binding)
            | throwError "the reopened source telescope lost a selected instance"
          instances := instances.push ⟨selected.className, binding.expression⟩
        withLCtx (← getLCtx) instances action) (action bindings)
    | entry :: rest =>
      let type := entry.type.instantiateRev locals
      let originalSource := entry.originalSource.map (·.instantiateRev locals)
      let next := fun expression =>
        visit rest (bindings.push {
          id := entry.id, role := entry.role, expression,
          originalSource := if interpretSources then none else originalSource }) (locals.push expression)
      if interpretSources then
        if let some source := originalSource then
          return ← mapMetaM (fun action => do
            check source
            unless ← isDefEq (← inferType source) type do
              throwError "an opaque source binding changed its original mathematical type"
            action) <| withLetDecl entry.userName type source next
              (nondep := entry.nondep) (kind := entry.kind)
      match entry.value with
      | some value =>
        withLetDecl entry.userName type (value.instantiateRev locals) next
          (nondep := entry.nondep) (kind := entry.kind)
      | none => withLocalDecl entry.userName entry.binderInfo type next (kind := entry.kind)
  mapMetaM (fun action => do
    context.nativeDeclarations.ensure
    action) <| withLCtx {} #[] <| visit context.entries.toList #[] #[]





opaque ContextTelescope.capture (bindings : Array LocalBinding) : MetaM OpenContext := do
  let phase : String → MetaM Unit := fun event => do
    try
      let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
      let instances ← getLocalInstances
      liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj [
        ("heartbeats", toJson heartbeats),
        ("bindings", toJson bindings.size),
        ("instances", toJson instances.size)])
    catch _ => pure ()
  phase "source.context.capture.started"
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
    let originalSource ← binding.originalSource.mapM (closeOver locals)
    if originalSource.isSome && value.isSome then
      throwError "an original runtime source cannot replace an authored let definition"
    entries := entries.push {
      id := binding.id, role := binding.role, userName := decl.userName,
      binderInfo := decl.binderInfo, kind := decl.kind, type, value, nondep := decl.isNondep,
      originalSource }
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
  phase "source.context.capture.closedPrefix.finished"
  let declarations ← NativeDeclarations.capture <|
    entries.flatMap fun entry => #[entry.type] ++ entry.value.toArray ++ entry.originalSource.toArray
  phase "source.context.capture.nativeDependencies.finished"
  let telescope : ContextTelescope := ⟨entries, instances, declarations⟩
  if entries.any (·.originalSource.isSome) then
    telescope.withOpenCore true fun _ => pure ()
  phase "source.context.capture.originalSources.finished"
  return ⟨telescope, bindings⟩






opaque OpenContext.withLocalBinding [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (context : OpenContext) (id : BindingId) (role : BindingRole) (userName : Name)
    (type : Expr) (action : OpenContext → LocalBinding → m α)
    (originalSource : Option Expr := none) (binderInfo : BinderInfo := .default)
    (preserveInstances : Bool := false) : m α := do
  let type ← liftM (m := MetaM) (resolve type)
  discard <| liftM (m := MetaM) (getLevel type)
  let preserved : Option LocalInstances ← if preserveInstances then do
      let instances ← liftM (m := MetaM) getLocalInstances
      pure (some instances)
    else pure none
  withLocalDecl userName binderInfo type fun expression => do
    let capture : m α := do
      let binding : LocalBinding := { id, role, expression, originalSource }
      let extended ← liftM (m := MetaM) <| ContextTelescope.capture (context.bindings.push binding)
      action extended binding
    match preserved with
    | none => capture
    | some instances =>
      mapMetaM (fun action => do withLCtx (← getLCtx) instances action) capture


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
    if let some original := entry.originalSource then levels := levels.collect original
  levels := (levels.collect expression).collect type
  let declarations ← NativeDeclarations.capture #[expression, type]
  return ⟨context.telescope, expression, type, levels.params, declarations⟩


private def nativeCheckSnapshot : MetaM (Option
    (Environment × MetavarContext × Meta.Context × Core.Context)) := do
  let context ← readThe Meta.Context


  if context.canUnfold?.isSome || context.trackZetaDelta || context.defEqCtx?.isSome ||
      context.inTypeClassResolution || context.synthPendingDepth != 0 ||
      context.univApprox || (← getPostponed).size != 0 then return none
  return some (← getEnv, ← getMCtx, context, ← readThe Core.Context)

private unsafe def sameNativeCheckSnapshot
    (first second : Option (Environment × MetavarContext × Meta.Context × Core.Context)) : Bool :=
  match first, second with
  | some first, some second =>
    let (firstEnv, firstMVars, firstMeta, firstCore) := first
    let (secondEnv, secondMVars, secondMeta, secondCore) := second
    ptrEq firstEnv secondEnv && ptrEq firstMVars secondMVars &&
      ptrEq firstMeta secondMeta && ptrEq firstCore secondCore
  | _, _ => false

private unsafe def OpenContext.withClosingImpl [Monad m] [MonadLiftT MetaM m]
    [MonadControlT MetaM m] (context : OpenContext) (validate : ClosedTerm → MetaM Unit)
    (action : (Expr → MetaM ClosedTerm) → m α) : m α :=
  controlAt MetaM fun run => do


    let memo : IO.Ref (Option
        (Option (Environment × MetavarContext × Meta.Context × Core.Context) ×
          ExprStructMap ClosedTerm)) ← liftM (m := IO) <| IO.mkRef (some (none, {}))


    let alive ← liftM (m := IO) <| IO.mkRef true
    try
      run <| action fun expression => do
        let expression ← resolve expression
        let before ← nativeCheckSnapshot
        let active ← if ← alive.get then memo.get else pure none
        let entries := match active with
          | some (previous, entries) => if sameNativeCheckSnapshot previous before then entries else {}
          | _ => {}
        let key : ExprStructEq := ⟨expression⟩
        let term ← match entries[key]? with
          | some term => pure term
          | none => context.close expression
        let checked ← nativeCheckSnapshot

        validate term
        let after ← nativeCheckSnapshot
        if active.isSome then
          if ← alive.get then
            if sameNativeCheckSnapshot checked after then
              let entries := if sameNativeCheckSnapshot before checked then entries else {}
              memo.set (some (after, entries.insert key term))
            else
              memo.set (some (none, {}))
        return term
    finally
      alive.set false
      memo.set none







@[implemented_by OpenContext.withClosingImpl]
opaque OpenContext.withClosing [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (context : OpenContext) (validate : ClosedTerm → MetaM Unit)
    (action : (Expr → MetaM ClosedTerm) → m α) : m α :=
  action fun expression => do
    let term ← context.close expression
    validate term
    return term



def ContextTelescope.ensureDeclarations (context : ContextTelescope) : MetaM Unit :=
  context.nativeDeclarations.ensure


def ClosedTerm.ensureDeclarations (term : ClosedTerm) : MetaM Unit := do
  term.context.ensureDeclarations
  term.nativeDeclarations.ensure


opaque ContextTelescope.withOpen [Monad m] [MonadControlT MetaM m] (context : ContextTelescope)
    (action : Array LocalBinding → m α) : m α :=
  context.withOpenCore false action






opaque ContextTelescope.withOpenContext [Monad m] [MonadControlT MetaM m]
    (context : ContextTelescope) (action : OpenContext → m α) : m α :=
  controlAt MetaM fun run =>
    context.withOpenCore false fun bindings => do
      for selected in ← getLocalInstances do
        unless (← isClass? (← inferType selected.fvar)) == some selected.className do
          throwError "a selected local instance has an incompatible source class"
      let declarations ← NativeDeclarations.capture <|
        context.entries.flatMap fun entry =>
          #[entry.type] ++ entry.value.toArray ++ entry.originalSource.toArray
      let checked : ContextTelescope := ⟨context.entries, context.instances, declarations⟩
      if checked.entries.any (·.originalSource.isSome) then
        checked.withOpenCore true fun _ => pure ()
      run (action ⟨checked, bindings⟩)




opaque OpenContext.withOriginalSources (context : OpenContext) (expressions : Array Expr)
    (action : Array Expr → MetaM α) : MetaM α := do
  let locals := context.bindings.map (·.expression)
  let expressions ← expressions.mapM (closeOver locals)
  context.telescope.withOpenCore true fun bindings =>
    action (expressions.map (·.instantiateRev (bindings.map (·.expression))))


def ClosedTerm.withOpen (term : ClosedTerm)
    (action : Array LocalBinding → Expr → MetaM α) : MetaM α := do
  term.ensureDeclarations
  term.context.withOpen fun bindings =>
    action bindings (term.expression.instantiateRev (bindings.map (·.expression)))

private def ContextEntry.checkBinding (entry : ContextEntry) (binding : LocalBinding)
    (locals : Array Expr) : MetaM Unit := do
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
  match entry.originalSource, binding.originalSource with
  | none, none => pure ()
  | some expected, some actual =>
    unless actual.equal (expected.instantiateRev locals) do
      throwError "the target context changed an original source correspondence"
  | _, _ => throwError "the target context lost an original source correspondence"




private def ContextTelescope.localsInContext (source : ContextTelescope) (target : OpenContext)
    (available : Std.HashMap BindingId (Nat × LocalBinding)) : MetaM (Array Expr) := do
  let mut locals : Array Expr := #[]
  let mut previous : Option Nat := none
  for entry in source.entries do
    let some (index, binding) := available[entry.id]?
      | do
        let identity := fun (id : BindingId) => Json.mkObj [
          ("session", toJson id.session), ("serial", toJson id.serial)]
        liftM (m := CoreM) <| CasTools.Diagnostics.emit "source.contextMissingBinding"
          (Json.mkObj [
            ("missing", identity entry.id),
            ("source", .arr (source.entries.map (identity ·.id))),
            ("target", .arr (target.bindings.map (identity ·.id)))])
        throwError "the target context is missing a captured binding"
    if let some priorIndex := previous then
      if index ≤ priorIndex then throwError "the target context changed captured binding order"
    previous := some index
    entry.checkBinding binding locals
    locals := locals.push binding.expression
  return locals

private def ClosedTerm.inContextManyReference (terms : Array ClosedTerm) (target : OpenContext) :
    MetaM (Array Expr) := do
  let mut available : Std.HashMap BindingId (Nat × LocalBinding) := {}
  for binding in target.bindings, index in [:target.bindings.size] do
    available := available.insert binding.id (index, binding)
  let mut expressions := #[]
  for term in terms do
    term.ensureDeclarations
    let locals ← term.context.localsInContext target available
    let expression ← resolve (term.expression.instantiateRev locals)
    check expression
    unless ← isDefEq (← inferType expression) (term.type.instantiateRev locals) do
      throwError "context transport changed the captured result type"
    expressions := expressions.push expression
  return expressions

private unsafe def ClosedTerm.inContextManyImpl (terms : Array ClosedTerm) (target : OpenContext) :
    MetaM (Array Expr) := do
  let mut available : Std.HashMap BindingId (Nat × LocalBinding) := {}
  for binding in target.bindings, index in [:target.bindings.size] do
    available := available.insert binding.id (index, binding)
  let mut previous : Option (ContextTelescope × Array Expr ×
      Option (Environment × MetavarContext × Meta.Context × Core.Context)) := none
  let mut expressions := #[]
  for term in terms do
    term.ensureDeclarations
    let before ← nativeCheckSnapshot
    let locals ← match previous with
      | some (source, locals, checked) =>
        if sameNativeCheckSnapshot checked before && term.context.exactlyMatches source then
          pure locals
        else
          term.context.localsInContext target available
      | none => term.context.localsInContext target available


    let checked ← nativeCheckSnapshot
    previous := if sameNativeCheckSnapshot before checked then
        some (term.context, locals, checked)
      else none
    let expression ← resolve (term.expression.instantiateRev locals)
    check expression
    unless ← isDefEq (← inferType expression) (term.type.instantiateRev locals) do
      throwError "context transport changed the captured result type"
    expressions := expressions.push expression
  return expressions





@[implemented_by ClosedTerm.inContextManyImpl]
opaque ClosedTerm.inContextMany (terms : Array ClosedTerm) (target : OpenContext) :
    MetaM (Array Expr) :=
  ClosedTerm.inContextManyReference terms target



opaque ClosedTerm.inContext (term : ClosedTerm) (target : OpenContext) : MetaM Expr := do
  let expressions ← ClosedTerm.inContextMany #[term] target
  return expressions[0]!





opaque ContextTelescope.withInContext (source : ContextTelescope) (current : OpenContext)
    (action : OpenContext → MetaM α) : MetaM α := do
  source.ensureDeclarations
  let rec visit (entries : List ContextEntry) (original : Array Expr)
      (all : Array LocalBinding) (previous : Option Nat) : MetaM α := do
    match entries with
    | [] =>
      let mut selected := current.telescope.instances
      let mut previous : Option Nat := none
      for instanceEntry in source.instances do
        let index ← match selected.findIdx? (fun entry =>
            entry.binding == instanceEntry.binding && entry.className == instanceEntry.className) with
          | some index => pure index
          | none => do
            let index := selected.size
            selected := selected.push instanceEntry
            pure index
        if let some priorIndex := previous then
          unless priorIndex < index do
            throwError "context import changed an original selected-instance order"
        previous := some index
      let instances : LocalInstances ← selected.mapM fun entry => do
        let some binding := all.find? (·.id == entry.binding)
          | throwError "context import lost an original selected instance"
        return ⟨entry.className, binding.expression⟩
      withLCtx (← getLCtx) instances do
        action (← ContextTelescope.capture all)
    | entry :: rest =>
      if let some index := all.findIdx? (·.id == entry.id) then
        if let some previous := previous then
          unless previous < index do
            throwError "context import changed an original native binder order"
        let binding := all[index]!
        entry.checkBinding binding original
        visit rest (original.push binding.expression) all (some index)
      else
        let type := entry.type.instantiateRev original
        let originalSource := entry.originalSource.map (·.instantiateRev original)
        let next := fun expression =>
          visit rest (original.push expression)
            (all.push { id := entry.id, role := entry.role, expression, originalSource })
            (some all.size)
        match entry.value with
        | some value =>
          withLetDecl entry.userName type (value.instantiateRev original) next
            (nondep := entry.nondep) (kind := entry.kind)
        | none => withLocalDecl entry.userName entry.binderInfo type next (kind := entry.kind)
  visit source.entries.toList #[] current.bindings none




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
