module

public import CasRuntime.PreparedRequest
public import CasRuntime.CallableView
public import CasRuntime.Transaction
public import CasCompiler.ConstructorPorts
public import CasCompiler.CategoricalPointFamily
public import CasCompiler.MapInterface
public import CasCompiler.PointPath

public section

namespace CasRuntime

open Lean Meta CasCompiler

/-- Prepared transport of an admitted complete callable packet at its native output field. -/
abbrev PreparedCallableTransport := ValueGraph → SourceLayout → ValueContainer → MetaM ValuePayload

/-- Native interface positions of supplied symbolic endpoints. An inline position denotes
only its original packet position during validation; it never becomes a runtime value or
formal answer. Repeated composition boundaries share the same already checked position. -/
inductive PreparedSymbolicEndpoint where
  | value (binding : ValueBinding)
  | inline (position : Nat)

/-- An actual selected operand or an inline map's explicitly retained complete endpoints.
Inline data receive no invented native map value. A source validator may use abstract
arrow locals only while checking its original category interface, then discard them. -/
inductive PreparedSymbolicOperand where
  | value (binding : ValueBinding)
  | objectData (endpoint : PreparedSymbolicEndpoint)
  | mapData (source target : PreparedSymbolicEndpoint)

/-- One node of a complete symbolic callable's interface constraints. Inline endpoint
positions share one namespace across the whole tree; actual original bindings stay explicit.
The action route records exactly the enclosing map descriptors, from outermost to innermost. -/
structure PreparedSymbolicNode where
  source : SourceLayout
  environment : RuntimeEnvironment
  tag : String
  operands : Array PreparedSymbolicOperand
  action : Option ValueContainer
  framed : PreparedSymbolicEndpoint × PreparedSymbolicEndpoint
  inputActions : Array ValueContainer
  fieldPrefix : Option NativeFieldPrefix := none

/-- Validate the whole symbolic tree in one transient native interface scope. Constraints
from original named arrows and nested maps must survive their parent abstractions. The
source producer retains its category/action interface; no answer is compared with the
requested mathematical expression, and no temporary mathematical value enters the graph. -/
abbrev PreparedSymbolicCheck := ValueGraph → Array PreparedSymbolicNode → MetaM Unit

/-- An explicitly supplied native map and its independently retained actual endpoints. -/
structure PreparedMapOperand where
  private mk ::
  binding : ValueBinding
  source : ValueBinding
  target : ValueBinding

/-- Actual complete endpoints and original execution transport of a native map result. -/
structure PreparedMapResult where
  private mk ::
  native : SourceLayout
  environment : RuntimeEnvironment
  marks : Array ValueBinding
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

/-- Attach the complete native cone/cocone to its original packet and admitted constructor
ports. The original constructor path retains every inline envelope. Proof positions stay
explicit empty slots. The callback receives the current isolated draft; it preserves original
port baselines when adding the native record field views. -/
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
  marks : Array ValueBinding

inductive PreparedResultKind where
  | native (check : PreparedSymbolicCheck)
  | map (prepared : PreparedMapResult)
  | construction (prepared : PreparedConstructionResult)

/-- A released structured reply interpretation sealed to its original request preparation. -/
structure PreparedResultCodec (scope : RoleScope) where
  private mk ::
  kind : PreparedResultKind

private def endpointInventory (graph : ValueGraph) (value : ValueBinding) :
    MetaM (Option (Array CallableDatum)) := do
  let packet ← IO.ofExcept <| (graph.callableDatum value).mapError IO.userError
  IO.ofExcept <| packet.endpointInventory.mapError IO.userError

/-- Seal actual endpoints at this already selected native Hom position. Constructor ports
use their original formal binder and exact preceding runtime context; descendant fields use
their own native source. No root map endpoint is substituted for another native map role.
Reuse: categoricalPointEndpoints and RuntimeEnvironment.checkDeclaredInput. These check
original source slots and occurrence identities without decoding or recomputing endpoints. -/
opaque PreparedMapResult.forSource (environment : RuntimeEnvironment) (native : SourceLayout)
    (graph : ValueGraph)
    (source target : ValueBinding) (marks : Array ValueBinding := #[])
    (makeCallable : Option PreparedCallableTransport := none)
    (callablePath : Option (NativePointPath native) := none)
    (symbolic : Option ValueContainer := none)
    (operands : Array (ValueBinding × ValueBinding × ValueBinding) := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM PreparedMapResult := do
  if makeCallable.isSome && callablePath.isNone then
    throwError "a map callable transport requires its checked original native carrier path"
  let available ← IO.ofExcept <|
    (mergeSourceMarks environment.sourceMarks
      (marks.mapIdx fun index value => (index, value))).mapError IO.userError
  let captured ← IO.ofExcept <| (retainedSourceMarks available native.source).mapError IO.userError
  let environment ← environment.withSourceMarks captured (some graph)
  if let some symbolic := symbolic then
    unless symbolic.fields.isNone && symbolic.callable.isNone do
      throwError "a source-prepared symbolic map requires its original descriptor view"
    discard <| IO.ofExcept <|
      (graph.requiredOwners (symbolic.slots.map (·.binding))).mapError IO.userError
  let inspect := fun (context : OpenContext) (expression : Expr)
      (captured : Array (Nat × ValueBinding)) => do
    let environment ← environment.withSourceMarks captured (some graph)
    let checkEndpoint := fun (endpoint : Expr) (value : ValueBinding) => do
      let checked ← match fieldPrefix with
        | none => pure false
        | some nativePrefix => nativePrefix.checkEndpoint environment context graph marks endpoint value
      unless checked do environment.checkDeclaredInput context graph marks endpoint value
    let (sourceExpression, targetExpression) ← nativeMapEndpoints expression
    checkEndpoint sourceExpression source
    checkEndpoint targetExpression target
    operands.mapM fun (binding, source, target) => do
      discard <| environment.checkOperand graph binding.role binding
      let original ← binding.role.source.inContext context
      let (sourceExpression, targetExpression) ← nativeMapEndpoints original
      checkEndpoint sourceExpression source
      checkEndpoint targetExpression target
      return (⟨binding, source, target⟩ : PreparedMapOperand)
  let operands ← match fieldPrefix with
    | none => native.source.withOpen fun bindings expression => do
      inspect (← ContextTelescope.capture bindings) expression environment.sourceMarks
    | some nativePrefix =>
      unless nativePrefix.native.address == native.address &&
          nativePrefix.native.source.context.exactlyMatches native.source.context &&
          nativePrefix.native.source.expression.equal native.source.expression &&
          nativePrefix.native.source.type.equal native.source.type &&
          nativePrefix.native.source.universeParams == native.source.universeParams &&
          nativePrefix.native.source.nativeDeclarations.exactlyMatches native.source.nativeDeclarations do
        throwError "the map codec changed its exact native field prefix"
      nativePrefix.withMarkedType graph environment.sourceMarks (fun context type captured =>
        withLocalDeclD `nativeMap type fun expression => inspect context expression captured)
        (minimumKey := marks.size)
  for actual in operands do
    for retained in operands do
      if actual.binding.value == retained.binding.value &&
          actual.binding.associationIds == retained.binding.associationIds then
        unless actual.source.value == retained.source.value &&
            actual.source.associationIds == retained.source.associationIds &&
            actual.target.value == retained.target.value &&
            actual.target.associationIds == retained.target.associationIds do
          throwError "one original map operand has conflicting retained endpoint slots"
  return ⟨native, environment, marks, source, target, ← endpointInventory graph source,
    ← endpointInventory graph target, callablePath.map (·.path), makeCallable, symbolic,
    operands, checkSymbolic, fieldPrefix⟩

/-- Keep native reply fields on the same source-checked symbolic interface boundary.
Each field still obtains its own original endpoints and preceding-field witnesses. -/
opaque PreparedResultCodec.forNative (request : PreparedRequest)
    (check : PreparedSymbolicCheck) : MetaM (PreparedResultCodec request.roles.scope) :=
  pure ⟨.native check⟩

/-- Seal the root result's codec to the original complete request preparation. -/
opaque PreparedResultCodec.forMap (request : PreparedRequest) (graph : ValueGraph)
    (source target : ValueBinding) (marks : Array ValueBinding := #[])
    (makeCallable : Option PreparedCallableTransport := none)
    (callablePath : Option (NativePointPath request.source) := none)
    (symbolic : Option ValueContainer := none)
    (operands : Array (ValueBinding × ValueBinding × ValueBinding) := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none) :
    MetaM (PreparedResultCodec request.roles.scope) := do
  return ⟨.map (← PreparedMapResult.forSource request.environment request.source graph
    source target marks makeCallable callablePath symbolic operands checkSymbolic)⟩

/-- Seal a complete constructor-port result to the unchanged native cone/cocone request.
The native comparison checks only the selected schema/diagram; actual port suppliers are
subsequently checked by the original constructor context and native dependent interface. -/
opaque PreparedResultCodec.forConstruction (request : PreparedRequest) (plan : ConstructorPorts)
    (category : CasCatalogue.CategoryExpr) (bundle : ClosedTerm)
    (colimit : Bool) (assemble : PreparedConstructionTransport)
    (checkSymbolic : Option PreparedSymbolicCheck := none) (marks : Array ValueBinding := #[]) :
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
  return ⟨.construction ⟨plan, category, bundle, colimit, assemble, checkSymbolic, marks⟩⟩

end CasRuntime
