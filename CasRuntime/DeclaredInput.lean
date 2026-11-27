module

public import CasRuntime.Environment
public import CasCompiler.Surface

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

private partial def containsRetained (environment : RuntimeEnvironment) (context : OpenContext)
    (source : Expr) : MetaM Bool := do
  if ← environment.hasRetainedSource context source then return true
  match source with
  | .mdata _ body => containsRetained environment context body
  | .app function argument =>
    return (← containsRetained environment context function) ||
      (← containsRetained environment context argument)
  | .lam _ type body _ | .forallE _ type body _ =>
    return (← containsRetained environment context type) ||
      (← containsRetained environment context body)
  | .letE _ type value body _ =>
    return (← containsRetained environment context type) ||
      (← containsRetained environment context value) ||
      (← containsRetained environment context body)
  | .proj _ _ parent => containsRetained environment context parent
  | _ => return false





private def declaredProjection? (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : MetaM (Option ValueBinding) := do
  if path.isEmpty then return some parent
  if let some retained ← IO.ofExcept <|
      (graph.projectedAccess? parent path).mapError IO.userError then return some retained
  let mut selected := parent
  for projection in path do
    let some field := selected.nativeRole.fields.find? (·.projection == projection)
      | throwError "a declared parameter selected a field outside its actual source"
    unless field.wireIndex.isSome do return none
    let some retained ← IO.ofExcept <|
        (graph.projectedAccess? selected #[projection]).mapError IO.userError | return none
    selected := retained
  return some selected




private partial def producingReference? (graph : ValueGraph) (context : OpenContext)
    (origin : ValueOrigin) (source : Expr)
    (path : Array Name := #[]) : MetaM (Option ValueBinding) := do
  if let .mdata _ body := source then
    return ← producingReference? graph context origin body path
  if source.isFVar then
    let some binding := context.bindings.find? (·.expression == source)
      | throwError "a declared parameter is outside its source context"
    let some index := origin.role.source.context.entries.findIdx? (·.id == binding.id)
      | return none
    let some value := origin.parameters[index]?.bind id | return none
    return ← declaredProjection? graph value path
  if let some selected ← SourceProjection.ofExpr? source then
    producingReference? graph context origin selected.parent (#[selected.declaration] ++ path)
  else return none

private structure DeclaredSlot where
  source : Expr
  value : ValueBinding

private structure DescriptorDeclaration where
  declaration : Name
  source : Expr
  path : Array Name
  address : String




private def selectedLimitDeclaration? (context : OpenContext)
    (selected : SourceSelection Expr) : MetaM (Option DescriptorDeclaration) := do
  let some (.limit row) := selected.reference | return none
  if selected.leg.isSome || selected.legOrdinal.isSome then return none
  let some construction := selected.limit
    | throwError "the selected limit result lost its complete original construction"
  let original := construction.source
  unless original.row == row.id.raw && original.declaration == row.declaration &&
      original.colimit == row.colimit && !original.construction.isAnonymous do
    throwError "the selected limit result changed its original construction"
  discard <| checkedDeclaration row.declaration
  let some producer ← sourceApplication? row.declaration selected
    | throwError "the selected limit result lost its retained producer application"
  unless original.presentation.consumeMData.equal producer.consumeMData do
    throwError "the selected limit result changed its original producer application"
  let path := if row.colimit then
      #[``CategoryTheory.Limits.ColimitCocone.cocone, ``CategoryTheory.Limits.Cocone.pt]
    else #[``CategoryTheory.Limits.LimitCone.cone, ``CategoryTheory.Limits.Cone.pt]
  let some cone ← SourceProjection.ofExpr? original.cone
    | throwError "the selected limit result lost its native cone projection"
  unless cone.declaration == path[0]! &&
      cone.parent.consumeMData.equal producer.consumeMData do
    throwError "the selected limit result changed its native cone projection"
  let apex ← mkAppM path[1]! #[original.cone]
  context.withOriginalSources #[construction.receiver, selected.value, apex] fun values => do
    unless ← isDefEq values[0]! values[2]! <&&> isDefEq values[1]! values[2]! do
      throwError "the selected limit result changed its original native apex"
  let producer := producer.consumeMData
  let arity ← forallTelescopeReducing (← inferType producer.getAppFn)
    fun parameters _ => pure parameters.size
  unless producer.getAppNumArgs == arity do
    throwError "the selected limit result lost its complete producer telescope"
  return some ⟨row.declaration, producer, path, row.id.raw⟩

private def descriptorDeclaration? (context : OpenContext) (origin : ValueOrigin)
    (packet : ValueContainer) : MetaM (Option DescriptorDeclaration) := do
  if let some selected ← origin.role.selected? context then
    if let some limit ← selectedLimitDeclaration? context selected then
      unless packet.fields.isNone && packet.callable.isNone do return none
      unless (packet.template.getObjValAs? String "ctor").toOption == some limit.address do
        throwStratum .malformed "a selected result descriptor changed its original source address"
      return some limit
    let some (.named (.registered (.inl row) category)) := selected.reference | return none
    unless row.category == category.id do
      throwError "the selected object descriptor changed its complete original category"
    let original := (selected.originalApplication.getD selected.value).consumeMData
    unless original.getAppFn.isConstOf row.declaration do
      throwError "the selected object descriptor lost its original declared application"
    unless (packet.template.getObjValAs? String "ctor").toOption == some row.id.raw do
      return none
    return some ⟨row.declaration, original, #[], row.id.raw⟩
  let source ← origin.role.source.inContext context
  let original ← sourceDomain source


  unless original.getAppFn.isConstOf ``Prod &&
      (packet.template.getObjValAs? String "ctor").toOption == some "objectProduct" &&
      original.getAppNumArgs == 2 && packet.fields.isNone && packet.callable.isNone do
    return none
  return some ⟨``Prod, original, #[], "objectProduct"⟩



private def descriptorSlots? (graph : ValueGraph) (context : OpenContext)
    (origin : ValueOrigin) (payload : ValueData)
    (declaration : Name) (arity : Nat) : MetaM (Option (Array (Option DeclaredSlot))) := do
  let .container packet := payload | return none
  let some selected ← descriptorDeclaration? context origin packet | return none
  let original := selected.source
  unless selected.declaration == declaration && original.getAppNumArgs == arity do return none
  let arguments := original.getAppArgs
  let information ← getFunInfoNArgs original.getAppFn arguments.size
  let mut slots := Array.replicate arity none
  let mut wire := 0
  for source in arguments, index in [:arguments.size] do
    if ← isProof source then continue
    if (information.paramInfo[index]?.map (·.isExplicit)).getD true then
      let path := #[.field "args", .index wire]
      let #[slot] := packet.slots.filter (·.path == path)
        | throwStratum .malformed "a declared descriptor is missing an exact original parameter slot"
      unless slot.fieldIndex.isNone do
        throwStratum .malformed "a declaration parameter cannot be supplied by a fabricated native field"
      slots := slots.set! index (some ⟨source, slot.binding⟩)
      wire := wire + 1
    else if let some value ← producingReference? graph context origin source then
      slots := slots.set! index (some ⟨source, value⟩)
  let .ok fields := (packet.template.getObjVal? "args").bind (·.getArr?)
    | throwStratum .malformed "a declared descriptor lost its complete parameter packet"
  unless fields.size == wire && packet.slots.size == wire do
    throwStratum .malformed "a declared descriptor changed its complete parameter arity"
  return some slots




private def applicationSlots? (graph : ValueGraph) (context : OpenContext) (origin : ValueOrigin)
    (declaration : Name) (arity : Nat) : MetaM (Option (Array (Option DeclaredSlot))) := do
  let some application := origin.application | return none
  unless application.path.isEmpty do return none
  let family ← application.layout.resultTermFamily.inContext context
  lambdaBoundedTelescope family application.arguments.size fun parameters body => do
    let body := body.headBeta.consumeMData
    unless body.getAppFn.isConstOf declaration && body.getAppNumArgs == arity do return none
    let mut computational := #[]
    for parameter in parameters, position in [:parameters.size] do
      unless ← isProof parameter do computational := computational.push (position, parameter)
    let mut slots := Array.replicate arity none
    for argument in body.getAppArgs, index in [:arity] do
      if ← isProof argument then continue
      let some (selected, path) ← sourceInputProjection? argument (computational.map (·.2))
        | continue
      let some (position, _) := computational[selected]?
        | throwError "a declared application lost its original native argument position"
      let some value := application.arguments[position]?.bind id | continue
      let some parameter := application.layout.arguments[position]?
        | throwError "a declared application lost its original native argument position"
      let some retained ← declaredProjection? graph value path | continue
      let mut source ← parameter.source.source.inContext context
      for projection in path do
        let some info := (← getEnv).getProjectionFnInfo? projection
          | throwError "a declared application lost its native projection metadata"
        source := .proj (← getConstInfoCtor info.ctorName).induct info.i source
      slots := slots.set! index (some ⟨source, retained⟩)
    return some slots





partial def RuntimeEnvironment.checkDeclaredInput (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph)
    (expected : Expr) (value : ValueBinding) : MetaM Unit := do
  let .ok argument := RuntimeArgument.ofValue graph 0 value
    | throwStratum .malformed "a declared input is outside its visible graph"
  let direct ← environment.hasRetainedSource context expected
  let nested ← containsRetained environment context expected
  if direct || !nested then
    discard <| environment.checkArgument (← context.close expected) argument
    return



  let layout ← SourceLayout.ofTerm (← context.close expected)
    (← (← environment.selections.inContext context).close context)
  discard <| environment.checkResult graph layout value


  let retainedSource ← (← context.close expected).inputProjectionSource
  if ← environment.hasRetainedSource context (← retainedSource.inContext context) then
    discard <| environment.checkArgument retainedSource argument
    return
  let expected ← sourceDomain expected
  let .const declaration _ := expected.getAppFn
    | throwStratum .malformed "a declared input has no exact native family for its retained parameters"
  let some node := graph.find value.value
    | throwError "the declared input lost its original producing node"
  let slots ← descriptorSlots? graph context node.origin node.payload.data declaration
    expected.getAppNumArgs
  let slots ← match slots with
    | some slots => pure (some slots)
    | none => applicationSlots? graph context node.origin declaration expected.getAppNumArgs
  let some slots := slots
    | throwStratum .malformed "the declared input has no original parameter reference slots"
  for source in expected.getAppArgs, index in [:expected.getAppNumArgs] do
    if ← isProof source then continue
    let required ← containsRetained environment context source
    match slots[index]?.bind id with
    | none =>
      if required then
        throwStratum .malformed "the declared input is missing an original retained parameter"
    | some slot =>
      let .ok argument := RuntimeArgument.ofValue graph index slot.value
        | throwStratum .malformed "a declared parameter is outside its visible graph"
      discard <| environment.checkArgument (← context.close slot.source) argument
      environment.checkDeclaredInput context graph source slot.value




structure DeclaredInputSlot where
  private mk ::
  declaration : Name
  index : Nat
  source : ClosedTerm
  value : ValueBinding




opaque RuntimeEnvironment.declaredInputAt? (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph)
    (declaration : Name) (index : Nat) (value : ValueBinding) :
    MetaM (Option DeclaredInputSlot) := do


  discard <| environment.checkOperand graph value.role value
  let info ← checkedDeclaration declaration
  let arity ← forallTelescopeReducing info.type fun parameters _ => pure parameters.size
  if index >= arity then return none
  let some node := graph.find value.value
    | throwError "the declared input lost its original producing node"
  let slots ← descriptorSlots? graph context node.origin node.payload.data declaration arity
  let slots ← match slots with
    | some slots => pure (some slots)
    | none => applicationSlots? graph context node.origin declaration arity
  let some slots := slots | return none
  let some slot := slots[index]?.bind id | return none
  environment.checkDeclaredInput context graph slot.source slot.value
  return some ⟨declaration, index, ← context.close slot.source, slot.value⟩




structure DeclaredResultSource where
  private mk ::
  declaration : Name
  source : ClosedTerm
  path : Array Name
  position : Nat




opaque RuntimeEnvironment.declaredResultSource? (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (value : ValueBinding) :
    MetaM (Option DeclaredResultSource) := do
  discard <| environment.checkOperand graph value.role value
  let some node := graph.find value.value
    | throwError "the selected result is outside its original graph"
  let .container packet := node.payload.data | return none
  let some selected ← descriptorDeclaration? context node.origin packet | return none
  if selected.path.isEmpty then return none
  let arguments := selected.source.getAppArgs
  let information ← getFunInfoNArgs selected.source.getAppFn arguments.size
  let mut explicit := #[]
  for argument in arguments, index in [:arguments.size] do
    if (information.paramInfo[index]?.map (·.isExplicit)).getD true &&
        !(← isProof argument) then explicit := explicit.push index
  let #[position] := explicit | return none
  return some ⟨selected.declaration, ← context.close selected.source, selected.path, position⟩

end CasRuntime
