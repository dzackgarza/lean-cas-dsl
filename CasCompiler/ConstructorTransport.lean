module

public import CasCompiler.ConstructorPorts

public section

namespace CasCompiler

open Lean Meta




structure ConstructorProjectionTransport where
  private mk ::
  plan : ConstructorPorts
  result : SourceLayout
  path : Array Name
  selected : InputProjection
  binding : BindingId
  source : SourceLayout
  target : SourceLayout

private def nativeLayoutAt (source : SourceLayout) (path : Array Name) :
    MetaM SourceLayout := do
  let mut current := source
  for projection in path do
    let some field := current.fields.find? (·.projection == projection)
      | throwError "a constructor transport selected an undeclared native field"
    if field.wireIndex.isNone then
      throwError "a constructor transport selected a formal proof field"
    current ← field.toLayout
  return current



opaque ConstructorPorts.projectionTransport (plan : ConstructorPorts) (result : SourceLayout)
    (path : Array Name) : MetaM ConstructorProjectionTransport := do
  let some selected ← plan.projectionAt path
    | throwError "the accepted constructor has no source-prescribed port for this result field"
  let (binding, root) ← match selected.target with
    | .argument index =>
      let some port := plan.ports[index]?
        | throwError "the constructor projection selected an undeclared native argument"
      unless port.argument.wireIndex.isSome do
        throwError "a constructor projection selected a formal proof argument"
      pure (port.binding, port.argument.source)
    | .context id =>
      let source ← plan.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let some binding := bindings.find? (·.id == id)
          | throwError "the constructor projection lost its original context binding"
        SourceLayout.ofTerm (← context.close binding.expression)
          (← (← plan.application.result.selections.inContext context).close context)
      pure (id, source)
  let source ← nativeLayoutAt root selected.path
  let target ← nativeLayoutAt result path
  plan.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let produced ← plan.application.result.source.inContext context
    let expected ← result.source.inContext context
    unless ← isDefEq (← inferType produced) (← inferType expected) do
      throwError "the constructor transport changed its complete native result interface"
    let original ← source.source.inContext context
    let consuming ← target.source.inContext context
    unless ← isDefEq (← inferType original) (← inferType consuming) do
      throwError "the selected constructor port has another native result-field interface"
  return ⟨plan, result, path, selected, binding, source, target⟩




opaque ConstructorProjectionTransport.withContext
    (transport : ConstructorProjectionTransport) (current : OpenContext)
    (action : OpenContext → MetaM α) : MetaM α := do
  transport.plan.context.ensureDeclarations
  let rec visit (entries : List ContextEntry) (original : Array Expr)
      (all : Array LocalBinding) (previous : Option Nat) : MetaM α := do
    match entries with
    | [] =>
      let mut instances ← getLocalInstances
      for selected in transport.plan.context.instances do
        let some binding := all.find? (·.id == selected.binding)
          | throwError "constructor transport lost an original selected instance"
        unless instances.any (fun selectedInstance =>
            selectedInstance.className == selected.className &&
            selectedInstance.fvar == binding.expression) do
          instances := instances.push ⟨selected.className, binding.expression⟩
      withLCtx (← getLCtx) instances do
        let context ← ContextTelescope.capture all


        discard <| transport.source.source.inContext context
        action context
    | entry :: rest =>
      if let some index := all.findIdx? (·.id == entry.id) then
        if let some previous := previous then
          unless previous < index do
            throwError "constructor transport changed the original native binder order"
        let binding := all[index]!
        let declaration ← getFVarLocalDecl binding.expression
        unless binding.role == entry.role && declaration.binderInfo == entry.binderInfo &&
            declaration.kind == entry.kind && declaration.isNondep == entry.nondep do
          throwError "constructor transport changed an original native binding role"
        unless ← isDefEq declaration.type (entry.type.instantiateRev original) do
          throwError "constructor transport changed an original native binder type"
        match entry.originalSource, binding.originalSource with
        | none, none => pure ()
        | some expected, some actual =>
          unless actual.equal (expected.instantiateRev original) do
            throwError "constructor transport changed an original source correspondence"
        | _, _ => throwError "constructor transport changed an original source correspondence"
        match entry.value, declaration.value? true with
        | none, none => pure ()
        | some expected, some actual =>
          unless ← isDefEq actual (expected.instantiateRev original) do
            throwError "constructor transport changed an original native definition"
        | _, _ => throwError "constructor transport changed an original declaration kind"
        visit rest (original.push binding.expression) all (some index)
      else
        unless transport.plan.ports.any (·.binding == entry.id) do
          throwError "constructor transport lost an original request context binding"
        let type := entry.type.instantiateRev original
        let next := fun expression =>
          visit rest (original.push expression)
            (all.push {
              id := entry.id
              role := entry.role
              expression := expression
              originalSource := entry.originalSource.map (·.instantiateRev original) }) (some all.size)
        match entry.value with
        | some value =>
          withLetDecl entry.userName type (value.instantiateRev original) next
            (nondep := entry.nondep) (kind := entry.kind)
        | none => withLocalDecl entry.userName entry.binderInfo type next (kind := entry.kind)
  visit transport.plan.context.entries.toList #[] current.bindings none

private partial def sourceBinderPath? (expression : Expr) :
    MetaM (Option (FVarId × Array Name)) := do
  if let .fvar id := expression then return some (id, #[])
  if let .mdata _ body := expression then return ← sourceBinderPath? body
  let some projection ← SourceProjection.ofExpr? expression | return none
  let some (id, path) ← sourceBinderPath? projection.parent | return none
  return some (id, path.push projection.declaration)

private partial def substitutePortSchema (binding : FVarId) (path : Array Name)
    (replacement : Expr) (expression : Expr) : MetaM Expr := do
  if let some (original, selected) ← sourceBinderPath? expression then
    if original == binding && selected == path then return replacement
  match expression with
  | .mdata data body => return .mdata data (← substitutePortSchema binding path replacement body)
  | .app function argument =>
    return .app (← substitutePortSchema binding path replacement function)
      (← substitutePortSchema binding path replacement argument)
  | .lam name type body info =>
    return .lam name (← substitutePortSchema binding path replacement type)
      (← substitutePortSchema binding path replacement body) info
  | .forallE name type body info =>
    return .forallE name (← substitutePortSchema binding path replacement type)
      (← substitutePortSchema binding path replacement body) info
  | .letE name type value body nondep =>
    return .letE name (← substitutePortSchema binding path replacement type)
      (← substitutePortSchema binding path replacement value)
      (← substitutePortSchema binding path replacement body) nondep
  | .proj name index parent =>
    return .proj name index (← substitutePortSchema binding path replacement parent)
  | _ => return expression

private def ConstructorProjectionTransport.schemaView
    (transport : ConstructorProjectionTransport) (context : OpenContext)
    (expression replacement : Expr) : MetaM Expr := do
  let some original := context.bindings.find? (·.id == transport.binding)
    | throwError "constructor type transport lost its exact original native slot"
  let target ← transport.target.source.inContext context
  unless ← context.withOriginalSources #[← inferType replacement, ← inferType target]
      (fun types => isDefEq types[0]! types[1]!) do
    throwError "constructor type transport changed its selected native slot type"
  let result ← substitutePortSchema original.expression.fvarId! transport.selected.path
    replacement expression
  check result
  return result



opaque ConstructorProjectionTransport.instantiateSchema
    (transport : ConstructorProjectionTransport) (context : OpenContext)
    (schema replacement : Expr) : MetaM Expr := do
  forallTelescope (← inferType schema) fun _ result => do
    unless result.isSort do
      throwError "constructor transport is restricted to native type schemas"
  transport.schemaView context schema replacement


opaque ConstructorProjectionTransport.typeInContext
    (transport : ConstructorProjectionTransport) (context : OpenContext)
    (source : ClosedTerm) (replacement : Expr) : MetaM Expr := do
  let original ← source.inContext context
  let type ← inferType original
  transport.schemaView context type replacement



opaque ConstructorProjectionTransport.schemaInContext
    (transport : ConstructorProjectionTransport) (context : OpenContext)
    (source : ClosedTerm) (replacement : Expr) : MetaM Expr := do
  let original ← source.inContext context
  let type ← inferType original
  forallTelescope type fun _ result => do
    unless result.isSort do
      throwError "constructor transport is restricted to native type schemas"
  transport.schemaView context original replacement



opaque ConstructorProjectionTransport.targetAt (transport : ConstructorProjectionTransport)
    (path : Array Name) : MetaM SourceLayout :=
  nativeLayoutAt transport.target path

end CasCompiler
