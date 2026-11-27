module

public import CasRuntime.Point
public import CasRuntime.ConstructorPorts
public import CasCompiler.LimitFamily

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend



structure PreparedLimitInvocation where
  private mk ::
  preparation : RoleScope
  family : LimitFamily
  owner : SelectedLimitOwner ClosedTerm
  plan : ConstructorPorts
  bundle : ClosedTerm
  diagram : ValueContainer
  forms : Array String
  dependencies : Array ValueBinding
  views : Array InputDescriptorView
  private inputs : InputRoleMap



opaque PreparedLimitInvocation.prepare (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) :
    MetaM PreparedLimitInvocation := do
  let .primitive (.limit family owner) _ := request.action
    | throwError "a raw construction requires its original complete limit boundary"
  let inputs ← request.admitInputs (← transaction.view)
  withSourceScope request fun context bound => do
    request.withArguments kernel.ledger.owners.identities context bound family.parameterCount
        fun context bound parameters originals => do
      let selected ← family.ownerAt (← owner.mapM (·.inContext context)) parameters
      family.requireInterface selected.source
      let interface ← selected.source.interface.mapM context.close
      let fresh : MetaM BindingId := do
        let identity ← liftM (m := BaseIO) <| kernel.ledger.owners.identities.fresh .sourceBinding
        return ⟨identity.worker, identity.serial⟩
      let plan ← ConstructorPorts.prepare interface fresh
        (selections := request.environment.selections)
      let (tag, arguments) ← LimitFamily.diagramPorts selected.source.interface.diagram
      let mut values := #[]
      for argument in arguments, index in [:arguments.size] do
        let value ← evaluateSource transaction request.program context bound
          (← request.environment.selections.inContext context) argument
        let graph ← transaction.view
        let actual ← IO.ofExcept <|
          (RuntimeArgument.ofValue graph index value).mapError IO.userError
        let value ← request.environment.checkArgument (← context.close argument) actual
        request.environment.checkDeclaredInput context graph argument value
        values := values.push value
      let payload ← IO.ofExcept <| (ValuePayload.descriptor
        (Json.mkObj [("ctor", toJson tag), ("args", .arr (Array.replicate values.size .null))])
        (values.mapIdx fun index binding =>
          { path := #[.field "args", .index index], binding, fieldIndex := none })).mapError IO.userError
      let .container diagram := payload.data
        | throwError "the original diagram lost its complete native descriptor"
      let graph ← transaction.view
      discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
      let roots := originals.filterMap id ++ values
      let views ← InputDescriptorView.collect graph (← kernel.codes.get) roots
      return ⟨request.roles.scope, family, owner, plan, ← context.close selected.source.bundle,
        diagram, #[family.entry.category.raw],
        request.scope ++ roots ++ views.flatMap (·.dependencies), views, inputs⟩


opaque PreparedLimitInvocation.requireInputs (invocation : PreparedLimitInvocation)
    (request : PreparedRequest) (graph : ValueGraph) : MetaM Unit := do
  request.requirePreparation invocation.preparation
  request.requirePreparation invocation.inputs.telescope.scope
  discard <| IO.ofExcept <| (invocation.inputs.arguments graph).mapError IO.userError
  discard <| IO.ofExcept <| (graph.requiredOwners invocation.dependencies).mapError IO.userError


def PreparedLimitInvocation.encode (invocation : PreparedLimitInvocation)
    (graph : ValueGraph) (receiver : ConnectionGeneration) :
    Except String (EncodedInputs × Json) := do
  let roots := invocation.diagram.slots.map fun slot =>
    ({ path := slot.path, binding := slot.binding } : InputPosition)
  let encoded ← graph.encodeInputs receiver roots invocation.views
  return (encoded, ← invocation.diagram.fill encoded.values)

private def constructionCaptures (invocation : PreparedLimitInvocation)
    (packet : ValueContainer) (ports : Array (Option ValueBinding)) : Array ValueBinding :=
  invocation.dependencies ++ packet.slots.map (·.binding) ++ ports.filterMap id




private def assembleConstruction (invocation : PreparedLimitInvocation) (kernel : Kernel)
    (request : PreparedRequest) (registration : Registration) : PreparedConstructionTransport :=
    fun source packet constructorPath ports draft => do
  request.requirePreparation invocation.preparation
  unless source.address == request.source.address && source.kind == .record do
    throwError "the construction transport changed its original whole native result"
  let family := invocation.family
  let admitted ← ConstructorPortPrefix.ofValues request draft.view invocation.plan ports

  let (draft, apex) ← admitted.transportProjection request #[family.apexProjection] draft
  let layout ← RecordLayout.ofSource source
  let #[apexField, transformationField] := layout.fields.filter (·.field.wireIndex.isSome)
    | throwError "the complete native cone changed its computational field schema"
  unless apexField.field.projection == family.apexProjection &&
      transformationField.field.projection == family.legProjection do
    throwError "the complete native cone changed its original apex/transformation order"
  let transformation ← RecordLayout.ofSource transformationField.layout
  let #[appField] := transformation.fields.filter (·.field.wireIndex.isSome)
    | throwError "the native cone transformation changed its complete data interface"
  unless appField.field.projection == ``CategoryTheory.NatTrans.app &&
      appField.layout.kind == .function do
    throwError "the cone transformation lost its original component function"
  let nativePrefix ← RecordPrefix.prepare kernel.ledger.owners.identities request.program
    request.occurrence layout draft.view request.environment.bound
  let (draft, nativePrefix, apex) ← liftM (m := IO) <| draft.bindField nativePrefix apex
  let transformationPrefix ← nativePrefix.currentField
  let transPrefix ← RecordPrefix.prepare kernel.ledger.owners.identities request.program
    request.occurrence transformation draft.view request.environment.bound
  let appPrefix ← (← transPrefix.currentField).join
    (← transformationPrefix.descend ``CategoryTheory.NatTrans.app)
  let path := #[family.legProjection, ``CategoryTheory.NatTrans.app]
  let captures := constructionCaptures invocation packet ports
  discard <| IO.ofExcept <| (draft.view.requiredOwners captures).mapError IO.userError
  let program ← kernel.ledger.owners.identities.fresh .program
  kernel.codes.modify (·.insert program
    (.constructionLeg request registration invocation.diagram packet ports path captures))
  let (draft, code) ← liftM (m := IO) <| draft.stage
    (← appPrefix.attachOrigin (← request.originFor appField.layout (some draft.view)) draft.view)
    (.closure program captures)
  let wrapped ← IO.ofExcept <| (ValuePayload.retainedCallable packet code).mapError IO.userError
  let (draft, app) ← liftM (m := IO) <| draft.stage
    (← appPrefix.attachOrigin (← request.originFor appField.layout (some draft.view)) draft.view)
    wrapped
  discard <| appPrefix.checkResult request.environment draft.view app
  let (draft, transPrefix, _) ← liftM (m := IO) <| draft.bindField transPrefix app
  let transPayload ← IO.ofExcept <| transPrefix.finish.mapError IO.userError
  let (draft, nativeTransformation) ← liftM (m := IO) <| draft.stage
    (← transformationPrefix.attachOrigin
      (← request.originFor transformationField.layout (some draft.view)) draft.view) transPayload
  discard <| transformationPrefix.checkResult request.environment draft.view nativeTransformation
  let (draft, nativePrefix, nativeTransformation) ← liftM (m := IO) <|
    draft.bindField nativePrefix nativeTransformation
  discard <| IO.ofExcept <| nativePrefix.finish.mapError IO.userError
  let mut slots : Array ContainerSlot := #[]
  for port in invocation.plan.ports, value in ports do
    if let some index := port.argument.wireIndex then
      let some value := value
        | throwError "the complete construction lost an admitted original data port"
      slots := slots.push {
        path := constructorPath ++ #[.field "args", .index index],
        binding := value, fieldIndex := none }
    else if value.isSome then
      throwError "the construction supplied computational data at an original proof position"
  let payload ← IO.ofExcept <|
    (ValuePayload.completeContainer packet slots #[apex, nativeTransformation]).mapError IO.userError
  liftM (m := IO) <| draft.stage (← request.originFor source (some draft.view)) payload



opaque PreparedLimitInvocation.resultCodec (invocation : PreparedLimitInvocation)
    (kernel : Kernel) (request : PreparedRequest) (transaction : CellTransaction)
    (registration : Registration) : MetaM (PreparedResultCodec request.roles.scope) := do
  request.requirePreparation invocation.preparation
  PreparedResultCodec.forConstruction request invocation.plan invocation.family.category.expression
    invocation.bundle invocation.family.entry.colimit
    (assembleConstruction invocation kernel request registration)
    (some (preparedSymbolicCheck kernel request transaction))




opaque Kernel.constructionLeg (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (original : PreparedRequest) (registration : Registration)
    (diagram packet : ValueContainer) (ports : Array (Option ValueBinding)) (path : Array Name)
    (retained captures : Array ValueBinding) : MetaM (PreparedResponse request) := do
  let .primitive (.limit family _) _ := original.action
    | throwError "the stored cone component lost its original complete construction"
  let .apply callable _ _ := request.action
    | throwError "a stored cone component requires its actual native index"
  unless path == #[family.legProjection, ``CategoryTheory.NatTrans.app] do
    throwError "the stored cone component changed its native field path"
  let graph ← transaction.view
  let inputs ← request.admitInputs graph
  let #[index] ← IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
    | throwError "the cone component changed its complete original index telescope"
  unless captures.size == retained.size &&
      (captures.zip retained).all (fun (actual, expected) =>
        actual.value == expected.value && actual.associationIds == expected.associationIds) do
    throwError "the cone component changed its original captures"
  discard <| IO.ofExcept <|
    (graph.requiredOwners (captures ++ ports.filterMap id ++ #[callable, index])).mapError IO.userError
  let some completion ← transaction.completionFor? original.occurrence
    | throwError "the cone component lost its original producing completion"
  original.requirePreparation completion.request.roles.scope
  let .invocation dispatch _ _ := completion.producer
    | throwError "the cone component lost its original supplying invocation"
  let .primitive selected := dispatch.selected
    | throwError "the cone component changed its original supplying dispatch kind"
  unless selected.registration == registration &&
      selected.manifestDigest == kernel.manifestDigest &&
      selected.profileDigest == kernel.profile.sha256 do
    throwError "the cone component changed its originally selected realization"
  let cone := completion.response.root
  let some node := graph.find cone.value
    | throwError "the cone component lost its complete actual parent"
  let .container actual := node.payload.data
    | throwError "the cone component lost its complete returned data packet"
  unless actual.retainsOriginalPacket packet do
    throwError "the cone component changed its original returned packet"
  let some _ ← IO.ofExcept <|
      (graph.projectionBasis callable cone path).mapError IO.userError
    | throwError "the component callable has another cone or original projection ancestry"
  let diagramPrefix := #[InputPathStep.field "args", .index 1]
  let slots := diagram.slots.map (fun slot =>
      { slot with path := diagramPrefix ++ slot.path, fieldIndex := none }) ++
    #[{ path := #[.field "args", .index 2], binding := cone, fieldIndex := none },
      { path := #[.field "args", .index 3], binding := index, fieldIndex := none }]
  let exports := diagram.exports.map (·.prefixed diagramPrefix)
  let symbolic ← IO.ofExcept <| (CallablePacket.symbolic
    (Json.mkObj [("ctor", toJson "constructionLeg"), ("args", .arr #[
      toJson family.operation, diagram.template, .null, .null])])).mapError IO.userError
  let payload ← IO.ofExcept <|
    (ValuePayload.callablePacket symbolic slots none exports).mapError IO.userError
  let value ← transaction.stage (← request.originFor request.source) payload
  kernelCompletion request transaction value

end CasRuntime
