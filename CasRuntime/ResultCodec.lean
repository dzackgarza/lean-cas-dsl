module

public import CasRuntime.PreparedRequest
public import CasRuntime.ExecutionContext
public import CasRuntime.CallableView
public import CasRuntime.Transaction
public import CasCompiler.ConstructorPorts
public import CasCompiler.CategoricalPointFamily
public import CasCompiler.MapInterface
public import CasCompiler.PointPath

public section

namespace CasRuntime

open Lean Meta CasCompiler


abbrev PreparedCallableTransport := ValueGraph → SourceLayout → ValueContainer → MetaM ValuePayload




inductive PreparedSymbolicEndpoint where
  | value (binding : ValueBinding)
  | inline (position : Nat)




inductive PreparedSymbolicOperand where
  | value (binding : ValueBinding)
  | objectData (endpoint : PreparedSymbolicEndpoint)
  | mapData (source target : PreparedSymbolicEndpoint)




structure PreparedSymbolicNode where
  source : SourceLayout
  environment : RuntimeEnvironment
  tag : String
  operands : Array PreparedSymbolicOperand
  action : Option ValueContainer
  framed : PreparedSymbolicEndpoint × PreparedSymbolicEndpoint
  inputActions : Array ValueContainer
  fieldPrefix : Option NativeFieldPrefix := none





abbrev PreparedSymbolicCheck := ValueGraph → Array PreparedSymbolicNode → MetaM Unit


structure PreparedMapOperand where
  private mk ::
  binding : ValueBinding
  source : ValueBinding
  target : ValueBinding


structure PreparedMapResult where
  private mk ::
  native : SourceLayout
  environment : RuntimeEnvironment
  source : ValueBinding
  target : ValueBinding
  sourceInventory : Option (Array CallableDatum)
  targetInventory : Option (Array CallableDatum)
  callablePath : Option (Array Name)
  makeCallable : Option PreparedCallableTransport
  symbolic : Option ValueContainer
  operands : Array PreparedMapOperand
  checkSymbolic : Option PreparedSymbolicCheck
  fieldPrefix : Option NativeFieldPrefix := none





abbrev PreparedConstructionTransport :=
  SourceLayout → ValueContainer → Array CasCatalogue.Backend.InputPathStep →
    Array (Option ValueBinding) → CellDraft →
    MetaM (CellDraft × ValueBinding)

structure PreparedConstructionResult where
  private mk ::
  plan : ConstructorPorts
  category : CasCatalogue.CategoryExpr
  bundle : ClosedTerm
  colimit : Bool
  assemble : PreparedConstructionTransport
  checkSymbolic : Option PreparedSymbolicCheck

inductive PreparedResultKind where
  | native (check : PreparedSymbolicCheck)
  | map (prepared : PreparedMapResult)
  | construction (prepared : PreparedConstructionResult)


structure PreparedResultCodec (scope : RoleScope) where
  private mk ::
  kind : PreparedResultKind

private def endpointInventory (graph : ValueGraph) (value : ValueBinding) :
    MetaM (Option (Array CallableDatum)) := do
  let packet ← IO.ofExcept <| (graph.callableDatum value).mapError IO.userError
  IO.ofExcept <| packet.endpointInventory.mapError IO.userError






opaque PreparedMapResult.forSource (environment : RuntimeEnvironment) (native : SourceLayout)
    (graph : ValueGraph)
    (source target : ValueBinding)
    (makeCallable : Option PreparedCallableTransport := none)
    (callablePath : Option (NativePointPath native) := none)
    (symbolic : Option ValueContainer := none)
    (operands : Array (ValueBinding × ValueBinding × ValueBinding) := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM PreparedMapResult := do
  if makeCallable.isSome && callablePath.isNone then
    throwError "a map callable transport requires its checked original native carrier path"
  let environment ← environment.withGraph (some graph)
  if let some symbolic := symbolic then
    unless symbolic.fields.isNone && symbolic.callable.isNone do
      throwError "a source-prepared symbolic map requires its original descriptor view"
    discard <| IO.ofExcept <|
      (graph.requiredOwners (symbolic.slots.map (·.binding))).mapError IO.userError
  let inspect := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
      (expression : Expr) => do
    let environment ← RuntimeEnvironment.captureBound environment.worker context bound graph
      (some environment) (← native.selections.inContext context)
    let checkEndpoint := fun (environment : RuntimeEnvironment) (context : OpenContext)
        (endpoint : Expr) (value : ValueBinding) => do
      let checked ← match fieldPrefix with
        | none => pure false
        | some nativePrefix => nativePrefix.checkEndpoint environment context graph endpoint value
      unless checked do environment.checkDeclaredInput context graph endpoint value
    let (sourceExpression, targetExpression) ← nativeMapEndpoints expression
    checkEndpoint environment context sourceExpression source
    checkEndpoint environment context targetExpression target
    let operands ← operands.mapM fun (binding, source, target) => do
      discard <| environment.checkOperand graph binding.role binding
      withBindingContext graph context bound binding fun context bound => do
        let environment ← RuntimeEnvironment.captureBound environment.worker context bound graph
          (some environment) (← binding.role.selections.inContext context)
        let original ← binding.selectedSource context
        let (sourceExpression, targetExpression) ← nativeMapEndpoints original
        checkEndpoint environment context sourceExpression source
        checkEndpoint environment context targetExpression target
        return (⟨binding, source, target⟩ : PreparedMapOperand)
    return (operands, environment)
  let (operands, environment) ← environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    native.source.context.withInContext context fun context => do
      match fieldPrefix with
      | none => inspect context environment.bound (← native.source.inContext context)
      | some nativePrefix =>
        unless nativePrefix.native.address == native.address &&
            nativePrefix.native.source.context.exactlyMatches native.source.context &&
            nativePrefix.native.source.expression.equal native.source.expression &&
            nativePrefix.native.source.type.equal native.source.type &&
            nativePrefix.native.source.universeParams == native.source.universeParams &&
            nativePrefix.native.source.nativeDeclarations.exactlyMatches native.source.nativeDeclarations &&
            nativePrefix.native.selectionBinding == native.selectionBinding &&
            SourceSelectionScope.exactlyMatches (fun (left right : ClosedTerm) =>
              left.context.exactlyMatches right.context && left.expression.equal right.expression &&
                left.type.equal right.type && left.universeParams == right.universeParams &&
                left.nativeDeclarations.exactlyMatches right.nativeDeclarations)
              nativePrefix.native.selections native.selections do
          throwError "the map codec changed its exact native field prefix"
        nativePrefix.withBoundType context graph environment.bound fun context type bound =>
          withLocalDeclD `nativeMap type fun expression => inspect context bound expression
  for actual in operands do
    for retained in operands do
      if actual.binding.value == retained.binding.value &&
          actual.binding.associationIds == retained.binding.associationIds then
        unless actual.source.value == retained.source.value &&
            actual.source.associationIds == retained.source.associationIds &&
            actual.target.value == retained.target.value &&
            actual.target.associationIds == retained.target.associationIds do
          throwError "one original map operand has conflicting retained endpoint slots"
  return ⟨native, environment, source, target, ← endpointInventory graph source,
    ← endpointInventory graph target, callablePath.map (·.path), makeCallable, symbolic,
    operands, checkSymbolic, fieldPrefix⟩



opaque PreparedResultCodec.forNative (request : PreparedRequest)
    (check : PreparedSymbolicCheck) : MetaM (PreparedResultCodec request.roles.scope) :=
  pure ⟨.native check⟩


opaque PreparedResultCodec.forMap (request : PreparedRequest) (graph : ValueGraph)
    (source target : ValueBinding)
    (makeCallable : Option PreparedCallableTransport := none)
    (callablePath : Option (NativePointPath request.source) := none)
    (symbolic : Option ValueContainer := none)
    (operands : Array (ValueBinding × ValueBinding × ValueBinding) := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none) :
    MetaM (PreparedResultCodec request.roles.scope) := do
  return ⟨.map (← PreparedMapResult.forSource request.environment request.source graph
    source target makeCallable callablePath symbolic operands checkSymbolic)⟩




opaque PreparedResultCodec.forConstruction (request : PreparedRequest) (plan : ConstructorPorts)
    (category : CasCatalogue.CategoryExpr) (bundle : ClosedTerm)
    (colimit : Bool) (assemble : PreparedConstructionTransport)
    (checkSymbolic : Option PreparedSymbolicCheck := none) :
    MetaM (PreparedResultCodec request.roles.scope) := do
  unless plan.originalContext.exactlyMatches request.environment.context do
    throwError "the construction codec changed its original native request context"
  request.source.source.withOpen fun bindings value => do
    let context ← ContextTelescope.capture bindings
    discard <| bundle.inContext context
    let diagram ← plan.interface.diagram.inContext context
    let expected ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone
      else ``CategoryTheory.Limits.Cone) #[diagram]
    unless ← withTransparency .all <| isDefEq (← inferType value) expected do
      throwError "the construction codec changed its original native cone diagram"
  return ⟨.construction ⟨plan, category, bundle, colimit, assemble, checkSymbolic⟩⟩

end CasRuntime
