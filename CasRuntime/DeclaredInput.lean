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

/-- Select only an already published access for the exact original native path. Prefer the
whole source-selected path before following independently published single steps: choosing an
intermediate access cannot authorize a continuation under a different consuming parent chain.
Descriptor schemas and raw stored baselines do not manufacture an access witness. -/
private def declaredProjection? (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : MetaM (Option ValueBinding) := do
  if path.isEmpty then return some parent
  if let some retained ← IO.ofExcept <|
      (graph.projectedAccess? parent path).mapError IO.userError then return some retained
  let mut selected := parent
  for projection in path do
    let some field := selected.role.fields.find? (·.projection == projection)
      | throwError "a declared parameter selected a field outside its actual source"
    unless field.wireIndex.isSome do return none
    let some retained ← IO.ofExcept <|
        (graph.projectedAccess? selected #[projection]).mapError IO.userError | return none
    selected := retained
  return some selected

/-- Read an original producing parameter or its already published native projection.
Only the producer's exact source table and marks select a reference; no equal value is found
and no missing native field is forced. This covers non-wire implicit declaration positions. -/
private partial def producingReference? (graph : ValueGraph) (context : OpenContext)
    (origin : ValueOrigin) (marks : Array ValueBinding) (source : Expr)
    (path : Array Name := #[]) : MetaM (Option ValueBinding) := do
  if let .mdata data body := source then
    if let some index := markedKey? data then
      let some value := marks[index]?
        | throwError "a declared parameter lost its original retained-value mark"
      discard <| IO.ofExcept <| (graph.requiredOwners #[value]).mapError IO.userError
      return ← declaredProjection? graph value path
    return ← producingReference? graph context origin marks body path
  if source.isFVar then
    let some binding := context.bindings.find? (·.expression == source)
      | throwError "a declared parameter is outside its source context"
    let some index := origin.role.source.context.entries.findIdx? (·.id == binding.id)
      | return none
    let some value := origin.parameters[index]?.bind id | return none
    return ← declaredProjection? graph value path
  if let some selected ← SourceProjection.ofExpr? source then
    producingReference? graph context origin marks selected.parent (#[selected.declaration] ++ path)
  else return none

private structure DeclaredSlot where
  source : Expr
  value : ValueBinding

private structure DescriptorDeclaration where
  declaration : Name
  source : Expr
  path : Array Name
  address : String

/-- Read only the selected native apex spine emitted by SourceLimit. Its source reference
fixes the original row before any projection is inspected; the descriptor's fields do not
supply an interface or a mathematical reconstruction. -/
private partial def selectedLimitDeclaration? (source : Expr) :
    MetaM (Option DescriptorDeclaration) := do
  match ← instantiateMVars source with
  | .mdata data body =>
    if data.getName `CasCompiler.source.kind == ``LimitEntry then
      if data.contains `CasCompiler.source.leg then return none
      let #[row] := (← semanticState).limits.filter
        (·.id.raw == data.getString `CasCompiler.source.id)
        | throwError "the selected result lost its original limit declaration"
      unless row.declaration == data.getName `CasCompiler.source.declaration do
        throwError "the selected result changed its original limit declaration"
      discard <| checkedDeclaration row.declaration
      let path := if row.colimit then
          #[``CategoryTheory.Limits.ColimitCocone.cocone, ``CategoryTheory.Limits.Cocone.pt]
        else #[``CategoryTheory.Limits.LimitCone.cone, ``CategoryTheory.Limits.Cone.pt]
      let mut original := body
      for declaration in path.reverse do
        let some selected ← SourceProjection.ofExpr? original
          | throwError "the selected limit result lost its native apex projection"
        unless selected.declaration == declaration do
          throwError "the selected limit result changed its native apex projection"
        original := selected.parent
      unless original.getAppFn.isConstOf row.declaration do
        throwError "the selected limit result changed its original producer application"
      let arity ← forallTelescopeReducing (← inferType original.getAppFn)
        fun parameters _ => pure parameters.size
      unless original.getAppNumArgs == arity do
        throwError "the selected limit result lost its complete producer telescope"
      return some ⟨row.declaration, original, path, row.id.raw⟩
    if (markedKey? data).isSome || data.contains `CasCompiler.source.kind ||
        data.contains `CasCompiler.selection then return none
    selectedLimitDeclaration? body
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => selectedLimitDeclaration? value
    | none => pure none
  | .letE _ _ value body _ => selectedLimitDeclaration? (body.instantiate1 value)
  | _ => pure none

private def descriptorDeclaration? (context : OpenContext) (origin : ValueOrigin)
    (packet : ValueContainer) : MetaM (Option DescriptorDeclaration) := do
  let source ← origin.role.source.inContext context
  if let some selected ← selectedLimitDeclaration? source then
    unless packet.fields.isNone && packet.callable.isNone do return none
    unless (packet.template.getObjValAs? String "ctor").toOption == some selected.address do
      throwStratum .malformed "a selected result descriptor changed its original source address"
    return some selected
  let original ← sourceDomain source
  let some declaration := original.getAppFn.constName? | return none
  let addresses := ((← semanticState).objects.filter (·.declaration == declaration)).map (·.id.raw)
  let some address := (packet.template.getObjValAs? String "ctor").toOption | return none
  unless addresses.contains address do return none
  return some ⟨declaration, original, #[], address⟩

/-- Actual explicit descriptor slots are indexed by the declared native argument positions.
The object's schema supplies no field data: these are the already stored descriptor inputs. -/
private def descriptorSlots? (graph : ValueGraph) (context : OpenContext)
    (origin : ValueOrigin) (payload : ValueData) (marks : Array ValueBinding)
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
    else if let some value ← producingReference? graph context origin marks source then
      slots := slots.set! index (some ⟨source, value⟩)
  let .ok fields := (packet.template.getObjVal? "args").bind (·.getArr?)
    | throwStratum .malformed "a declared descriptor lost its complete parameter packet"
  unless fields.size == wire && packet.slots.size == wire do
    throwStratum .malformed "a declared descriptor changed its complete parameter arity"
  return some slots

/-- A genuine native application may retain the same declared inputs without a descriptor.
Only the original producer and exact formal argument positions are used. Native projections
read already published fields; an unrecorded field never supplies a reconstructed slot. -/
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

/-- Check complete declared input data against independently retained original source inputs.
An outer input reference is checked by the ordinary argument boundary. Nested references must
be witnessed by exact stored descriptor slots or original native application arguments, with
the same node and association checks recursively. Native equality cannot select these inputs. -/
partial def RuntimeEnvironment.checkDeclaredInput (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (marks : Array ValueBinding)
    (expected : Expr) (value : ValueBinding) : MetaM Unit := do
  let .ok argument := RuntimeArgument.ofValue graph 0 value marks
    | throwStratum .malformed "a declared input is outside its visible graph"
  discard <| environment.checkArgument (← context.close expected) argument
  if ← environment.hasRetainedSource context expected then return
  unless ← containsRetained environment context expected do return
  -- Native instance wrappers can conceal the same original field path. Re-admit that
  -- source-only path before accepting its retained occurrence; equality is insufficient.
  let retainedSource ← (← context.close expected).inputProjectionSource
  if ← environment.hasRetainedSource context (← retainedSource.inContext context) then
    discard <| environment.checkArgument retainedSource argument
    return
  let expected ← sourceDomain expected
  let .const declaration _ := expected.getAppFn
    | throwStratum .malformed "a declared input has no exact native family for its retained parameters"
  let some node := graph.find value.value
    | throwError "the declared input lost its original producing node"
  let slots ← descriptorSlots? graph context node.origin node.payload.data marks declaration
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
      let .ok argument := RuntimeArgument.ofValue graph index slot.value marks
        | throwStratum .malformed "a declared parameter is outside its visible graph"
      discard <| environment.checkArgument (← context.close slot.source) argument
      environment.checkDeclaredInput context graph marks source slot.value

/-- One original producing declaration argument at its exact native position. The source and
binding come from the same admitted descriptor/application slot; consumers cannot construct a
new correspondence from two equal specialized source expressions. -/
structure DeclaredInputSlot where
  private mk ::
  declaration : Name
  index : Nat
  source : ClosedTerm
  value : ValueBinding

/-- Read an original declared argument by a position already established on the full abstract
source telescope. This reuses the same producer and complete-arity gates as declared-input
checking. It cannot search for an equal value, force a missing field, or reconstruct a slot. -/
opaque RuntimeEnvironment.declaredInputAt? (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (marks : Array ValueBinding)
    (declaration : Name) (index : Nat) (value : ValueBinding) :
    MetaM (Option DeclaredInputSlot) := do
  -- This is an actual already selected producer input. Its authenticated native projection
  -- may carry the original dependent prefix; ordinary candidate result admission is separate.
  discard <| environment.checkOperand graph value.role value
  let info ← checkedDeclaration declaration
  let arity ← forallTelescopeReducing info.type fun parameters _ => pure parameters.size
  if index >= arity then return none
  let some node := graph.find value.value
    | throwError "the declared input lost its original producing node"
  let slots ← descriptorSlots? graph context node.origin node.payload.data marks declaration arity
  let slots ← match slots with
    | some slots => pure (some slots)
    | none => applicationSlots? graph context node.origin declaration arity
  let some slots := slots | return none
  let some slot := slots[index]?.bind id | return none
  environment.checkDeclaredInput context graph marks slot.source slot.value
  return some ⟨declaration, index, ← context.close slot.source, slot.value⟩

/-- A selected descriptor result whose whole native family has one explicit computational
input. The source, projection path and original argument position are read together from
the actual producer; consumers cannot construct an unrelated source correspondence. -/
structure DeclaredResultSource where
  private mk ::
  declaration : Name
  source : ClosedTerm
  path : Array Name
  position : Nat

/-- Recover only an already selected descriptor's exact native projection and input position.
The following declaredInputAt? lookup must still supply its actual retained input node.
No category is inferred from the descriptor's result type or its printable packet. -/
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
