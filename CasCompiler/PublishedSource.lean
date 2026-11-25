module

public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceCarrier
public import CasCompiler.PointFamily
public import CasCompiler.CategoricalPointSource
public import CasCompiler.LimitFamily
public import CasCompiler.ConstructionEndpoint
public import CasCompiler.LimitUniversalFamily
public import CasCompiler.PreparedCreationFamily
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Lean.Meta.AbstractMVars
public import CasCompiler.PresentationFamily
public import CasCompiler.PropertyFamily
public import CasCompiler.LiftFamily
public import CasCompiler.RecordAction
public import CasCompiler.PublishedPorts
public import CasCompiler.SourceCell
public import CasContract.Port
public import CasCatalogue.Admission
public import LeanCategories.Catalogue.Registry.Computation

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue CasCatalogue.Backend

/-- External operands supply data or an original retained native expression. These hooks
carry no operation lookup, dependent application, route selection or mathematical proof.
Runtime ownership and scoped references stay outside the compiler. -/
structure PublishedSourceContext where
  scope : OpenContext
  retained : Json → MetaM (Option Expr)
  literal : Expr → Json → MetaM (Option Expr)
  bind : Expr → MetaM Expr
  rebind : Expr → Expr → MetaM Expr
  methodParameters : RoutedMethodFamily → Array Expr → Expr → MetaM (Array Expr)
  checkInput : Expr → Expr → MetaM Unit
  admitMethod : RoutedMethodFamily → Expr → String → MetaM Unit
  admitProperty : PropertyFamily → Expr → String → MetaM Unit
  admitPoint : PointFamily → Expr → MetaM Unit
  admitCategorical : CategoricalPointFamily → Array Expr → Expr → MetaM Unit :=
    fun _ _ _ => throwError "a retained categorical arrow requires its original runtime owner"
  constructionCone : Json → MetaM (Option (Expr × NativeLimitSelection × Expr)) :=
    fun _ => pure none
  creationOwner : Json → MetaM (Option (NativeLimitSelection × Expr)) :=
    fun _ => pure none
  constructionEndpoint : NativeConstructionLeg → Bool → Expr → MetaM Bool :=
    fun _ _ _ => pure false
  projection : Json → Nat → MetaM (Expr × Name)

namespace PublishedSource

private def malformed {α : Type} (reason : MessageData) : TermElabM α :=
  throwStratum .malformed m!"published source request: {reason}"

private def arrayField (packet : Json) (key : String) : TermElabM (Array Json) := do
  match (packet.getObjVal? key).bind (·.getArr?) with
  | .ok values => pure values
  | .error reason => malformed reason

/-- An external name selects an exact source row; equal native declarations or categories
are not alternative suppliers. Ordinary named syntax calls this same selected-row producer
once its public spelling and qualification have selected the row. -/
def namedApplicable (entry : ObjectEntry ⊕ MorphismEntry) (category : NamedCategoryEntry)
    (apply : Expr → Option Expr → TermElabM (Except MessageData Expr)) :
    TermElabM (Except MessageData (Expr × Expr)) :=
  registeredExpressionsApplicable entry category apply

private def namedSelection? (address : String) :
    MetaM (Option ((ObjectEntry ⊕ MorphismEntry) × NamedCategoryEntry)) := do
  let state ← semanticState
  let entries := (state.objects.filter (·.id.raw == address)).map Sum.inl ++
    (state.morphisms.filter (·.id.raw == address)).map Sum.inr
  if entries.isEmpty then return none
  let #[entry] := entries
    | throwStratum .semanticAmbiguity m!"the published source address {address} has several owners"
  let owner := match entry with | .inl entry => entry.category | .inr entry => entry.category
  let #[category] := state.categories.filter (·.id == owner)
    | throwError "the published source input lost its complete registered category"
  return some (entry, category)

mutual

/-- Read data only at the complete declared source type. Named objects and maps use the
ordinary selected-row producer; native records use their actual constructor telescope.
The shared application elaborator preserves each actual retained operand at its original
position, including repeated equal-valued but independently owned operands. -/
private partial def readOperand (context : PublishedSourceContext) (domain : Expr) (packet : Json) :
    TermElabM Expr := do
  if let some source ← context.retained packet then
    checkRegisteredDomains (← inferType source) domain
    unless ← isDefEq (← inferType source) domain do
      malformed "a retained operand has a different declared type"
    return source
  if let .ok address := packet.getObjValAs? String "ctor" then
    if let some (entry, category) ← namedSelection? address then
      match checkServiceFields #["ctor", "args"] packet with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← arrayField packet "args"
      let formed ← namedApplicable entry category fun head expected => do
        let value ← explicit context head fields expected
        unless ← isDefEq (← inferType value) domain do
          return .error m!"the named input has a different complete declared type"
        return .ok value
      let (_, value) ← match formed with
        | .ok value => pure value
        | .error reason => malformed reason
      return value
  let isArrow := (packet.getObjValAs? String "ctor").toOption == some "arrow"
  let packet ← if isArrow then do
      match checkServiceFields #["ctor", "args"] packet with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← arrayField packet "args"
      unless fields.size == 3 do malformed "an Arrow operand requires both endpoints and its hom"
      pure (.arr fields)
    else pure packet
  let domain ← whnfR (← instantiateMVars domain)
  if let (.arr components, .const owner levels) := (packet, domain.getAppFn) then
    if (getStructureInfo? (← getEnv) owner).isSome then
      let constructor := getStructureCtor (← getEnv) owner
      let head := mkAppN (.const constructor.name levels) domain.getAppArgs
      let computational ← forallTelescopeReducing (← inferType head) fun fields _ => do
        return (← fields.filterM fun field => return !(← isProof field)).size
      unless components.size == computational do
        malformed "the structure operand has a different number of computational fields"
      let value ← complete context head components
      unless ← isDefEq (← inferType value) domain do
        malformed "the structure operand changed its complete declared type"
      if isArrow then
        let hom ← mkAppM ``CategoryTheory.Comma.hom #[value]
        let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[hom]
        unless ← isDefEq (← inferType arrow) domain do
          malformed "the Arrow packet belongs to another complete native record"
      return value
  let some value ← context.literal domain packet
    | malformed "an inline operand has no scalar reading at its declared type"
  return value

/-- Ordinary explicit source arguments and external named parameters share one native
application producer, including the registered source-instance inference view. -/
private partial def explicit (context : PublishedSourceContext) (head : Expr) (packets : Array Json)
    (expected : Option Expr := none) (resolved : Bool := true) : TermElabM Expr := do
  let value ← applySourceDataArguments head packets.size expected fun index domain => do
      let some packet := packets[index]? | malformed "the source input lost an original parameter"
      readOperand context domain packet
  let value ← instantiateMVars value
  if resolved && (value.hasMVar || value.hasLevelMVar) then
    malformed "the source input leaves a complete native parameter undetermined"
  return value

/-- A complete-interface request exposes all computational positions, while formal proof
positions remain source hypotheses. It uses the same native producer as ordinary syntax. -/
private partial def complete (context : PublishedSourceContext) (head : Expr) (packets : Array Json) :
    TermElabM Expr :=
  applySourceArguments head (Array.replicate packets.size Syntax.missing) fun index domain => do
    let some packet := packets[index]? | malformed "the source input lost an original parameter"
    readOperand context domain packet

end

/-- Read one external operand at its complete original native type. The recursive reader
and application machinery remain compiler implementation details. -/
opaque operand (context : PublishedSourceContext) (domain : Expr) (packet : Json) :
    TermElabM Expr := readOperand context domain packet

private partial def actionParameters (edge : EdgeRef) (descriptor : Json) :
    TermElabM (Array Json) := do
  let fields ← arrayField descriptor "args"
  let parameters ← match edge with
    | .functor _ => pure fields
    | .classifierForget _ =>
      let #[_, .arr parameters] := fields
        | malformed "classifier forgetting lost its complete parameter array"
      pure parameters
    | .constructMap _ inner =>
      let #[_, action] := fields
        | malformed "the constructor action lost its complete inner action"
      actionParameters inner action
  unless routedActionDescriptor edge parameters == descriptor do
    malformed "the action descriptor differs from its exact selected edge"
  return parameters

/-- Select and apply a method through the same whole-family producer and C6 agreement
as native source. The released action descriptors retain their explicit route; provider
availability never selects it. Runtime callbacks only bind already typed original inputs. -/
private def method (context : PublishedSourceContext) (entry : MethodEntry)
    (input : String) (arguments : Json) : TermElabM Expr := do
  let state ← semanticState
  let registry : RegistryState := { toSemanticState := state }
  let some form := registry.form? input | malformed "the explicit input form is not published"
  let some category := state.categories.find? (·.id == form.category)
    | malformed "the input form lost its original source category"
  match checkServiceFields #["ctor", "args", "receiver"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match ConstructionInvocation.decodeMethod entry.id.raw entry.functor.raw arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  let identities ← packet.parameters.mapM fun descriptor =>
    match descriptorActionIdentity descriptor with
    | .ok identity => pure identity
    | .error reason => malformed reason
  let families ← RoutedMethodFamily.atSource category.expression entry.name
  let #[family] := families.filter (fun family => family.entry.id == entry.id &&
      (family.route.refs.push (.functor family.functor.id)).map edgeImageDescriptor == identities)
    | malformed "the residual actions are not one complete first-hit method route"
  let mut evidence := #[]
  for declaration in ← getLCtx do
    if ← isProp declaration.type then evidence := evidence.push (mkFVar declaration.fvarId)
  let agreements ← family.agreements evidence
  let (_, levels) ← family.instantiate
  let categoryFamily := family.categoryFamily.instantiateLevelParams family.universeParams levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  let domain ← mkAppM ``CategoryTheory.Bundled.α #[mkAppN categoryFamily parameters]
  let receiverPacket ← if (packet.receiver.getObjValAs? String "ctor").toOption == some "arrow" then do
      let .construct constructor #[.category _] := category.expression
        | malformed "an Arrow receiver requires its published Arrow source category"
      unless (state.constructors.find? (·.id == constructor)).any
          (·.semantics == `CasCatalogue.Constructors.arrow) do
        malformed "the receiver descriptor does not belong to this source constructor"
      match checkServiceFields #["ctor", "args"] packet.receiver with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← arrayField packet.receiver "args"
      unless fields.size == 3 do malformed "the Arrow receiver requires both endpoints and its hom"
      pure (Json.arr fields)
    else pure packet.receiver
  let receiver ← operand context domain receiverPacket
  let receiver ← instantiateMVars receiver
  let parameters ← parameters.mapM instantiateMVars
  let levels ← levels.mapM instantiateLevelMVars
  if receiver.hasMVar || receiver.hasLevelMVar ||
      parameters.any (fun parameter => parameter.hasMVar || parameter.hasLevelMVar) then
    malformed "the receiver leaves the complete method category undetermined"
  context.admitMethod family receiver input
  let receiver ← context.bind receiver
  let edges := family.route.refs.push (.functor family.functor.id)
  let actions ← family.specializeActions levels parameters
  let routes ← family.actionParameterInputs
  let mut selected := parameters
  let mut supplied : Array (Array Expr) := #[]
  let mut selectedSlots : Std.HashSet Nat := {}
  for edge in edges, action in actions, descriptor in packet.parameters, inputs in routes do
    let expected ← routedActionParameters edge action
    let packets ← actionParameters edge descriptor
    unless packets.size == expected.size && inputs.size == expected.size do
      malformed "an action changed its complete native parameter arity"
    let mut values := #[]
    for (_, source) in expected, packet in packets, route in inputs do
      let term ← operand context (← inferType source) packet
      let term ← instantiateMVars term
      if term.hasMVar || term.hasLevelMVar then
        malformed "an action parameter leaves its native type undetermined"
      let value ← context.bind term
      values := values.push value
      if let some index := route then
        unless selectedSlots.contains index do
          let some original := selected[index]?
            | malformed "the action lost its original category parameter position"
          selected := selected.set! index (← context.rebind original value)
          selectedSlots := selectedSlots.insert index
    supplied := supplied.push values
  selected ← context.methodParameters family selected receiver
  let checkedActions ← family.specializeActions levels selected
  let mut retainedInputs := #[]
  for edge in edges, action in checkedActions, values in supplied do
    let expected ← routedActionParameters edge action
    let mut inputs := #[]
    for (_, source) in expected, value in values do
      context.checkInput source value
      inputs := inputs.push value
    retainedInputs := retainedInputs.push inputs
  let (result, _) ← family.applyAt levels selected receiver retainedInputs
  let mut term := result
  for proof in agreements.reverse do
    let mut proof := proof.instantiateLevelParams family.universeParams levels
    for parameter in selected do proof ← mkAppM ``congrFun #[proof, parameter]
    checkWithKernel proof
    term ← withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] term
        (usedLetOnly := false) (generalizeNondepLet := false)
  return term

private def property (context : PublishedSourceContext) (entry : PropertyEntry)
    (input : String) (arguments : Json) : TermElabM Expr := do
  let state ← semanticState
  let registry : RegistryState := { toSemanticState := state }
  let some form := registry.form? input | malformed "the explicit input form is not published"
  if let some reason := registry.rejects (.property entry) form then malformed reason
  let some category := state.categories.find? (·.id == form.category)
    | malformed "the input form lost its original source category"
  let categoryFamily ← nativeCategoryFamily state category.expression fun _ => mkFreshLevelMVar
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  let bundle := mkAppN categoryFamily parameters
  let domain ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let receiver ← operand context domain arguments
  let receiver ← instantiateMVars receiver
  let bundle ← instantiateMVars bundle
  if receiver.hasMVar || receiver.hasLevelMVar || bundle.hasMVar || bundle.hasLevelMVar then
    malformed "the receiver leaves the complete property category undetermined"
  let (family, source) ← PropertyFamily.forReceiver
    ⟨.object, category.expression, bundle, none, none⟩ entry.id receiver
  context.admitProperty family receiver input
  return source

private def namedPoint (context : PublishedSourceContext) (operation : String)
    (arguments : Json) : TermElabM Expr := do
  let state ← semanticState
  let morphisms := state.morphisms.filter (·.id.raw == operation)
  let applications := state.objects.filter fun entry =>
    entry.application.isSome && entry.applicationAddress == operation
  let family ← match morphisms, applications with
    | #[row], #[] => PointFamily.forEntry row
    | #[], #[row] => PointFamily.forApplication row
    | #[], #[] => malformed "the point request does not name a released callable"
    | _, _ => malformed "the point request has several released callable owners"
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match PointInvocation.decode arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  unless packet.operation == operation do malformed "the point packet changed its released operation"
  let head ← mkConstWithFreshMVarLevels family.declaration
  let expectedArrow ← explicit context head packet.parameters
  let (expectedSource, expectedTarget) ← family.endpoints expectedArrow
  let expectedFunction ← family.function expectedArrow
  let .forallE _ pointType _ _ ← whnfR (← inferType expectedFunction)
    | malformed "the named morphism has no complete point-function interface"
  let point ← operand context pointType packet.argument
  let some original ← sourcePointOrigin? point
    | malformed "the operand has no retained original generalized-point domain"
  let domain ← operand context (← inferType original.domain) packet.domain
  let source ← operand context (← inferType expectedSource) packet.source
  let target ← operand context (← inferType expectedTarget) packet.target
  let arrow ← if let some arrow ← context.retained packet.arrow then do
      context.admitPoint family arrow
      pure arrow
    else do
      match checkServiceFields #["ctor", "args"] packet.arrow with
      | .error reason => malformed reason
      | .ok () => pure ()
      unless (packet.arrow.getObjValAs? String "ctor").toOption == some operation do
        malformed "the arrow descriptor belongs to a different released family"
      let value ← explicit context head (← arrayField packet.arrow "args")
      pure (family.mark value)
  let point ← try family.withRequest expectedArrow domain source target point
    catch error => malformed m!"the complete named point inputs disagree: {error.toMessageData}"
  let function ← family.function arrow
  let (result, _) ← elabSourceApplication function #[Syntax.missing] none
    fun _ _ => pure point
  return result

private def presentation (context : PublishedSourceContext) (row : PresentationComparisonEntry)
    (arguments : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match PresentationInvocation.decode arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  let family ← PresentationFamily.forEntry row
  let (head, _) ← family.instantiate
  let iso ← explicit context head packet.parameters
  let (first, second) ← family.endpoints iso
  let (source, target) := if packet.inverse then (second, first) else (first, second)
  let source ← operand context (← inferType source) packet.source
  let target ← operand context (← inferType target) packet.target
  let (first, second) := if packet.inverse then (target, source) else (source, target)
  let iso ← try family.withEndpoints iso first second
    catch error => malformed m!"the comparison endpoints do not match the selected family: {error.toMessageData}"
  let function ← family.function iso packet.inverse
  let (result, _) ← elabSourceApplication function #[Syntax.missing] none fun _ domain =>
    operand context domain packet.argument
  return result

/-- Decode the released complete component packet, then invoke the same native cell producer
as ordinary source syntax. The ordered constructor path acts on the entire selected cell. -/
private def component (context : PublishedSourceContext) (operation : String)
    (entry : CellEntry) (constructors : Array ConstructorId) (arguments : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match if constructors.isEmpty then
      (CellComponent.decode arguments).map (fun cell => (⟨#[], cell⟩ : ConstructedCellComponent))
    else ConstructedCellComponent.decode arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  unless packet.address == operation && packet.component.cell == entry.id.raw &&
      packet.constructors == constructors.map (·.raw) do
    malformed "the component changed its selected cell or complete constructor path"
  let application ← explicit context (← mkConstWithFreshMVarLevels entry.declaration)
    packet.component.parameters (resolved := false)
  let mut cell ← nativeSourceCell entry application packet.component.inverse
  for constructor in constructors.reverse do cell ← cell.construct constructor
  let domain ← mkAppM ``CategoryTheory.Bundled.α #[cell.sourceBundle]
  let receiver ← operand context domain packet.component.receiver
  return (← cell.component ⟨receiver, none⟩).value

/-- Form an explicitly selected action from the actual native declaration inputs. The
recursive constructor interface is the same one used by sourceEdgeFunctor and native cells. -/
private partial def action (context : PublishedSourceContext) (edge : EdgeRef)
    (descriptor : Json) : TermElabM (Expr × CategoryExpr) := do
  let state ← semanticState
  let parameters ← actionParameters edge descriptor
  match edge with
  | .functor id =>
    let some entry := state.functor? id | malformed "the selected action functor is absent"
    let view ← viewExpressions (.inl entry) none fun head =>
      explicit context head parameters (resolved := false)
    return (view.functor, view.target)
  | .classifierForget id =>
    let some entry := state.classifier? id | malformed "the selected action classifier is absent"
    let view ← viewExpressions (.inr entry) none fun head =>
      explicit context head parameters (resolved := false)
    return (view.functor, view.target)
  | .constructMap id inner =>
    let some entry := state.constructor? id | malformed "the selected action constructor is absent"
    let some declaration := entry.functorialAction
      | malformed "the selected constructor has no declared functor action"
    let #[_, descriptor] ← arrayField descriptor "args"
      | malformed "the constructor lost its complete original action"
    let (inner, target) ← action context inner descriptor
    let (sourceBundle, targetBundle) ← functorCategoryBundles inner
    discard <| checkedDeclaration declaration
    let value ← applyConstructorInterface declaration #[sourceBundle, targetBundle] #[inner]
    return (sourceReference ``ConstructorEntry.functorialAction id.raw declaration value,
      .construct id #[.category target])

private def selectedAction (descriptor : Json) : TermElabM EdgeRef := do
  let identity ← match descriptorActionIdentity descriptor with
    | .ok identity => pure identity
    | .error reason => malformed reason
  let state ← semanticState
  if let .ok id := identity.getObjValAs? String "functor" then
    let #[entry] := state.functors.filter (·.id.raw == id)
      | malformed "the action descriptor has no unique original functor"
    return .functor entry.id
  let address ← match actionAddress identity with
    | .ok address => pure address
    | .error reason => malformed reason
  let .ok (some (edge, false)) := PublishedPorts.edge? state address
    | malformed "the action descriptor has no complete published native edge"
  return edge

/-- Form the supplied native action on its actual typed operand without selecting a provider. -/
opaque actionOperand (context : PublishedSourceContext) (descriptor : Json) (arrow : Expr) :
    TermElabM Expr := do
  let edge ← selectedAction descriptor
  let (functor, _) ← action context edge descriptor
  let value ← mkAppM ``CategoryTheory.Functor.map #[functor, arrow]
  check value
  return value

private def nativeHomType (value : Expr) : TermElabM Expr := do
  let type ← inferType value
  let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
  unless type.isAppOfArity ``Quiver.Hom 4 do
    malformed "the symbolic map has no complete original native Hom interface"
  return type

/-- Read the actual parent of this Hom's Quiver projection, without category search. -/
private def nativeHomStructure (type : Expr) : TermElabM Expr := do
  let quiver := type.getAppArgs[1]!.consumeMData
  if quiver.isAppOfArity ``CategoryTheory.CategoryStruct.toQuiver 2 then
    return quiver.getAppArgs[1]!
  if let .proj owner 0 value := quiver then
    if owner == ``CategoryTheory.CategoryStruct then return value
  malformed "the symbolic map lost its original complete category structure"

/-- A retained native object, or one explicitly shared inline endpoint position. -/
inductive NativeSymbolicEndpoint
  | value (expression : Expr)
  | inline (position : Nat)

/-- Existing native values and the explicit endpoint interfaces of inert inline map data. -/
inductive NativeSymbolicOperand
  | value (expression : Expr)
  | objectData (endpoint : NativeSymbolicEndpoint)
  | mapData (source target : NativeSymbolicEndpoint)

/-- One supplied symbolic node in a single complete packet's endpoint namespace. -/
structure NativeSymbolicNode where
  expected : Expr
  tag : String
  operands : Array NativeSymbolicOperand
  descriptor : Option Json
  framed : Option (NativeSymbolicEndpoint × NativeSymbolicEndpoint) := none
  inputActions : Array Json := #[]

/-- Zero is available only from the structure at this Hom's actual complete Category. -/
private def nativeZero (type source target : Expr) : TermElabM Expr := do
  let structureValue ← nativeHomStructure type
  let structureValue := structureValue.consumeMData
  let category ← if structureValue.isAppOfArity
      ``CategoryTheory.Category.toCategoryStruct 2 then
      pure structureValue.getAppArgs[1]!
    else if let .proj owner 0 value := structureValue then
      if owner == ``CategoryTheory.Category then pure value
      else malformed "zero lost its original complete category structure"
    else malformed "zero lost its original complete category structure"
  let carrier := type.getAppArgs[0]!
  let classType ← mkAppOptM ``CategoryTheory.Limits.HasZeroMorphisms
    #[some carrier, some category]
  let some zeros := (← trySynthInstance classType).toOption
    | malformed "the original complete category has no zero-morphism structure"
  let instanceValue ← mkAppOptM ``CategoryTheory.Limits.HasZeroMorphisms.zero
    #[some carrier, some category, some zeros, some source, some target]
  let hom := mkAppN type.getAppFn
    (type.getAppArgs.set! 2 source |>.set! 3 target)
  mkAppOptM ``Zero.zero #[some hom, some instanceValue]

/-- Preserve the particular descriptor occurrence's original construction and typed
index while preparing its native component. The same parser serves direct operands
and the whole symbolic-tree constraint check. -/
private def readConstructionLeg (context : PublishedSourceContext) (packet : Json) :
    TermElabM NativeConstructionLeg := do
  match checkServiceFields #["ctor", "args"] packet with
  | .error reason => malformed reason | .ok () => pure ()
  let #[identity, diagramPacket, conePacket, indexPacket] ← arrayField packet "args"
    | malformed "the construction leg requires its complete diagram, cone and typed index"
  let operation ← match identity.getStr? with
    | .ok value => pure value
    | .error reason => malformed reason
  let some (owner, selected, cone) ← context.constructionCone conePacket
    | malformed "the construction leg lost its original completed native selection"
  unless selected.source.row == operation do
    malformed "the construction leg changed its original registered construction"
  let (nativeTag, fields) ← LimitFamily.diagramPorts selected.source.diagram
  match checkServiceFields #["ctor", "args"] diagramPacket with
  | .error reason => malformed reason | .ok () => pure ()
  unless (diagramPacket.getObjValAs? String "ctor").toOption == some nativeTag do
    malformed "the construction leg changed its original native diagram constructor"
  let packets ← arrayField diagramPacket "args"
  unless packets.size == fields.size do
    malformed "the construction leg changed its complete native diagram arity"
  for expected in fields, packet in packets do
    let actual ← operand context (← inferType expected) packet
    context.checkInput expected (← context.bind actual)
  let transformation ← mkAppM (if selected.source.colimit then
    ``CategoryTheory.Limits.Cocone.ι else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation]
  let .forallE _ domain _ _ ← whnfR (← inferType component)
    | malformed "the selected cone lost its original native diagram-object telescope"
  let index ← operand context domain indexPacket
  NativeConstructionLeg.prepare owner selected cone (← context.bind index)

/-- Named symbolic arrows use their original published declarations and complete parameters. -/
private def descriptorArrow (context : PublishedSourceContext) (tag : String)
    (packet : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] packet with
  | .error reason => malformed reason | .ok () => pure ()
  let state ← semanticState
  if tag == "constructionLeg" then
    return (← readConstructionLeg context packet).value
  if tag == "objectField" then
    let parsed ← match ObjectField.decode packet with
      | .ok parsed => pure parsed | .error reason => malformed reason
    let #[entry] := state.objects.filter (·.id.raw == parsed.object)
      | malformed "the object field has no unique original object declaration"
    let object ← explicit context (← mkConstWithFreshMVarLevels entry.declaration) parsed.parameters
    let field ← match parsed.field with
      | "constants" => pure entry.constants
      | "inclusion" => pure entry.inclusion
      | "presentation" | "inversePresentation" =>
        pure (entry.functorPresentation.map (·.identification))
      | "refinement" | "inverseRefinement" => pure (entry.refines.map (·.identification))
      | _ => pure none
    let some declaration := field
      | malformed "the original object has no selected published map field"
    discard <| checkedDeclaration declaration
    let value ← applyObjectParameters entry.id.raw declaration object.getAppArgs
    if parsed.field == "constants" || parsed.field == "inclusion" then return value
    let inverse := parsed.field == "inversePresentation" || parsed.field == "inverseRefinement"
    return ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[value]
  if tag == "cellComponent" || tag == "constructedCellComponent" then
    let parsed ← match if tag == "cellComponent" then
        (CellComponent.decode packet).map fun value =>
          ({ constructors := #[], component := value } : ConstructedCellComponent)
      else ConstructedCellComponent.decode packet with
      | .ok parsed => pure parsed
      | .error reason => malformed reason
    let .ok (some (entry, constructors)) := PublishedPorts.component? state parsed.address
      | malformed "the symbolic component has no original accepted owner"
    return ← component context parsed.address entry constructors packet
  if tag == "cartesianMap" then
    let parsed ← match CartesianMap.decode packet with
      | .ok parsed => pure parsed
      | .error reason => malformed reason
    let .ok (some entry) := PublishedPorts.cartesian? state parsed.address
      | malformed "the symbolic cartesian map has no original family-reindex owner"
    let family ← CategoricalPointFamily.forOwner (.cartesian entry)
    let application ← explicit context (← mkConstWithFreshMVarLevels family.declaration)
      parsed.parameters (resolved := false)
    let .const _ levels := application.getAppFn.consumeMData
      | malformed "the cartesian descriptor lost its complete declaration spine"
    let head := family.arrowFamily.instantiateLevelParams family.universeParams levels
    let partialArrow := mkAppN head application.getAppArgs
    let .forallE _ domain _ _ ← whnfR (← inferType partialArrow)
      | malformed "the cartesian descriptor lost its native receiver"
    let receiver ← operand context domain parsed.receiver
    return (← family.arrowAt levels (application.getAppArgs.push receiver)).1
  if tag == "presentation" then
    let #[identity, .arr parameters, direction] ← arrayField packet "args"
      | malformed "a presentation arrow requires its original id, parameters and direction"
    let id ← match identity.getStr? with
      | .ok id => pure id | .error reason => malformed reason
    let inverse ← match direction.getBool? with
      | .ok inverse => pure inverse | .error reason => malformed reason
    let #[entry] := state.presentations.filter (·.id.raw == id)
      | malformed "the presentation arrow has no unique accepted comparison"
    discard <| checkedDeclaration entry.declaration
    let iso ← explicit context (← mkConstWithFreshMVarLevels entry.declaration) parameters
    return ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[iso]
  if let some (Sum.inr entry, category) ← namedSelection? tag then
    match checkServiceFields #["ctor", "args"] packet with
    | .error reason => malformed reason | .ok () => pure ()
    let formed ← namedApplicable (.inr entry) category fun head expected => do
      return .ok (← explicit context head (← arrayField packet "args") expected)
    let .ok (_, value) := formed
      | malformed "the named symbolic arrow changed its complete native declaration"
    return value
  if let #[entry] := state.binders.filter (·.id.raw == tag) then
    discard <| checkedDeclaration entry.operation
    return sourceReference ``BinderEntry entry.id.raw entry.operation
      (← explicit context (← mkConstWithFreshMVarLevels entry.operation) (← arrayField packet "args"))
  malformed "the symbolic arrow has no supplied original native declaration"

private def symbolicEndpoint (fresh : Expr → TermElabM Expr)
    (carrier : Expr) (endpoint : NativeSymbolicEndpoint)
    (known : IO.Ref (Array (Nat × Expr))) : TermElabM Expr := do
  match endpoint with
  | .value expression =>
    unless ← isDefEq (← inferType expression) carrier do
      malformed "an actual endpoint belongs to another declared category carrier"
    return expression
  | .inline position =>
    if let some (_, expression) := (← known.get).find? (·.1 == position) then
      unless ← isDefEq (← inferType expression) carrier do
        malformed "one inline endpoint changed its original native category carrier"
      return expression
    let expression ← fresh carrier
    known.modify (·.push (position, expression))
    return expression

private partial def withSymbolicOperands (carrier : Expr)
    (domain : Expr → Expr → TermElabM Expr) (operands : Array NativeSymbolicOperand)
    (index : Nat) (actual : Array Expr) (known : IO.Ref (Array (Nat × Expr)))
    (fresh : Expr → TermElabM Expr)
    (finish : Array Expr → TermElabM Unit) : TermElabM Unit := do
  let some operand := operands[index]? | return ← finish actual
  match operand with
  | .value value =>
    withSymbolicOperands carrier domain operands (index + 1) (actual.push value) known fresh finish
  | .objectData endpoint =>
    let object ← symbolicEndpoint fresh carrier endpoint known
    withSymbolicOperands carrier domain operands (index + 1) (actual.push object) known fresh finish
  | .mapData source target =>
    let source ← symbolicEndpoint fresh carrier source known
    let target ← symbolicEndpoint fresh carrier target known
    let type ← domain source target
    check type
    withLocalDeclD (← mkFreshUserName `inlineMapInterface) type fun arrow =>
      withSymbolicOperands carrier domain operands (index + 1) (actual.push arrow) known fresh finish

/-- Compare the complete native category interface independently of packet endpoint positions. -/
private def checkSymbolicCategory (actual expected : Expr) : TermElabM Unit := do
  let actualArgs := actual.getAppArgs
  let expectedArgs := expected.getAppArgs
  checkRegisteredDomains actualArgs[0]! expectedArgs[0]!
  unless ← isDefEq (mkAppN actual.getAppFn (actualArgs.extract 0 2))
        (mkAppN expected.getAppFn (expectedArgs.extract 0 2)) <&&>
      isDefEq (← nativeHomStructure actual) (← nativeHomStructure expected) do
    malformed "the symbolic operands use another full native category or Hom interface"

/-- A nested map's input category follows only its supplied complete action descriptors. -/
private partial def withSymbolicCategory (context : PublishedSourceContext) (type : Expr)
    (actions : Array Json) (index : Nat) (finish : Expr → TermElabM Unit) : TermElabM Unit := do
  let some descriptor := actions[index]? | return ← finish type
  let edge ← selectedAction descriptor
  let (functor, _) ← action context edge descriptor
  let (source, target) ← functorCategoryBundles functor
  let targetCarrier ← mkAppM ``CategoryTheory.Bundled.α #[target]
  withLocalDeclD (← mkFreshUserName `nestedTargetInterface) targetCarrier fun targetObject => do
    let targetType ← nativeHomType (← categoricalPointIdentity target targetObject)
    checkSymbolicCategory targetType type
    let sourceCarrier ← mkAppM ``CategoryTheory.Bundled.α #[source]
    withLocalDeclD (← mkFreshUserName `nestedSourceInterface) sourceCarrier fun sourceObject => do
      let sourceType ← nativeHomType (← categoricalPointIdentity source sourceObject)
      withSymbolicCategory context sourceType actions (index + 1) finish

/-- Provenance travels with this one endpoint constraint, including across an
inline intermediate. It is never recovered by using an endpoint expression as a key. -/
private structure SymbolicEndpointConstraint where
  source : Expr
  construction : Option (NativeConstructionLeg × Bool) := none

/-- Validate the entire symbolic tree in one transient endpoint constraint context.
Inline positions are interface metavariables only during this check. Every concrete native
endpoint constraint is retained independently, so unification cannot erase original runtime
occurrence marks. The supplied check compares their actual source dependencies afterward. -/
private def validateSymbolicCore (context : PublishedSourceContext)
    (nodes : Array NativeSymbolicNode)
    (checkShared : Expr → Expr → TermElabM Unit) : TermElabM Unit := do
  let stableContext ← getLCtx
  let stableInstances ← getLocalInstances
  let stable := stableContext.foldl (fun values declaration =>
    values.push (mkFVar declaration.fvarId)) (#[] : Array Expr)
  let freshEndpoint : Expr → TermElabM Expr := fun carrier => do
    let carrier ← instantiateMVars carrier
    if (carrier.find? fun term => term.isFVar && !stable.contains term).isSome then
      malformed "an inline endpoint carrier depends on a temporary category interface"
    withLCtx stableContext stableInstances <| mkFreshExprMVar carrier
  let checked ← IO.mkRef (#[] : Array Expr)
  let known ← IO.mkRef (#[] : Array (Nat × Expr))
  let constraints ← IO.mkRef (#[] : Array (Nat × SymbolicEndpointConstraint))
  let comparisons ← IO.mkRef
    (#[] : Array (SymbolicEndpointConstraint × SymbolicEndpointConstraint))
  let compare := fun (first second : SymbolicEndpointConstraint) => do
    let left ← instantiateMVars first.source
    let right ← instantiateMVars second.source
    let handledLeft ← match first.construction with
      | some (original, target) => context.constructionEndpoint original target right
      | none => pure false
    let handledRight ← match second.construction with
      | some (original, target) => context.constructionEndpoint original target left
      | none => pure false
    unless handledLeft || handledRight do checkShared left right
  let constrain := fun (actual : Expr) (endpoint : NativeSymbolicEndpoint)
      (construction : Option NativeConstructionLeg) (target : Bool) => do
    let stated ← symbolicEndpoint freshEndpoint (← inferType actual) endpoint known
    let actual : SymbolicEndpointConstraint :=
      ⟨actual, construction.map fun original => (original, target)⟩
    match endpoint with
    | .value _ => comparisons.modify (·.push (actual, ⟨stated, none⟩))
    | .inline position => constraints.modify (·.push (position, actual))
    unless ← isDefEq actual.source stated do
      malformed "a symbolic map changed its explicitly framed native endpoint"
  let rec visit : List NativeSymbolicNode → TermElabM Unit
    | [] => do
      synthesizeSyntheticMVars (postpone := .no)
      for (first, second) in ← comparisons.get do
        compare first second
      let constraints ← constraints.get
      for (position, expression) in constraints do
        for (otherPosition, other) in constraints do
          if position == otherPosition then
            compare expression other
      let transient := (← getLCtx).foldl (fun values declaration =>
        let value := mkFVar declaration.fvarId
        if stable.contains value then values else values.push value) (#[] : Array Expr)
      for (_, expression) in ← known.get do
        let carrier ← instantiateMVars (← inferType expression)
        if carrier.hasMVar || carrier.hasLevelMVar ||
            (carrier.find? fun term => term.isFVar && !stable.contains term).isSome then
          malformed "an inline endpoint has no complete native carrier in its original scope"
      let allowed ← (← known.get).foldlM (fun result (_, expression) => do
        let unresolved ← getMVars (← instantiateMVars expression)
        return result ++ unresolved) (#[] : Array MVarId)
      for expression in ← checked.get do
        let expression ← mkLambdaFVars transient (← instantiateMVars expression)
          (usedOnly := false) (usedLetOnly := false)
        for unknown in ← getMVars expression do
          unless allowed.contains unknown do
            malformed m!"the symbolic interface leaves a native parameter undetermined: {← inferType (.mvar unknown)}"
          let type ← instantiateMVars (← inferType (.mvar unknown))
          if type.hasMVar || type.hasLevelMVar ||
              (type.find? fun term => term.isFVar && !stable.contains term).isSome then
            malformed "an inline endpoint has no complete native carrier in its original scope"
        let abstracted ← abstractMVars expression (levels := false)
        let closed ← mkLambdaFVars stable abstracted.expr
          (usedOnly := false) (usedLetOnly := false)
        let closed ← instantiateMVars closed
        if closed.hasMVar || closed.hasLevelMVar || closed.hasFVar || closed.hasSorry then
          malformed "the symbolic interface did not close over its exact rigid native scope"
        checkWithKernel closed
    | node :: remaining => do
      let type ← nativeHomType node.expected
      withSymbolicCategory context type node.inputActions 0 fun type => do
        let args := type.getAppArgs
        let functor : Option Expr ← if node.tag == "map" then do
            let some descriptor := node.descriptor
              | malformed "a map action lost its complete descriptor"
            let edge ← selectedAction descriptor
            pure (some (← action context edge descriptor).1)
          else pure none
        let domain := fun source target => do
          if let some functor := functor then
            let map ← mkAppOptM ``CategoryTheory.Functor.map
              #[none, none, none, none, some functor, some source, some target]
            let .forallE _ domain _ _ ← whnfR (← inferType map)
              | malformed "the native action lost its full source-map type"
            return domain
          return mkAppN type.getAppFn (args.set! 2 source |>.set! 3 target)
        let carrier ← if let some functor := functor then do
            let (source, _) ← functorCategoryBundles functor
            mkAppM ``CategoryTheory.Bundled.α #[source]
          else pure args[0]!
        withSymbolicOperands carrier domain node.operands 0 #[] known freshEndpoint fun operands => do
          let mut construction : Option NativeConstructionLeg := none
          let value ← if node.tag == "identity" then do
              let #[object] := operands
                | malformed "an identity requires its actual original object"
              let structureValue ← nativeHomStructure type
              mkAppOptM ``CategoryTheory.CategoryStruct.id
                #[some args[0]!, some structureValue, some object]
            else if node.tag == "zero" then do
              let #[source, target] := operands
                | malformed "zero requires its two original endpoints"
              nativeZero type source target
            else if node.tag == "compose" then do
              let #[first, second] := operands
                | malformed "composition requires its two original maps"
              let firstType ← nativeHomType first
              let secondType ← nativeHomType second
              comparisons.modify (·.push (⟨firstType.getAppArgs[3]!, none⟩,
                ⟨secondType.getAppArgs[2]!, none⟩))
              let structureValue ← nativeHomStructure type
              mkAppOptM ``CategoryTheory.CategoryStruct.comp #[
                some args[0]!, some structureValue, some firstType.getAppArgs[2]!,
                some firstType.getAppArgs[3]!, some secondType.getAppArgs[3]!,
                some first, some second]
            else if let some functor := functor then do
              let #[arrow] := operands
                | malformed "a map action requires its actual original map"
              mkAppM ``CategoryTheory.Functor.map #[functor, arrow]
            else do
              let some descriptor := node.descriptor
                | malformed "the symbolic arrow lost its complete original descriptor"
              if node.tag == "constructionLeg" then
                let original ← readConstructionLeg context descriptor
                construction := some original
                pure original.value
              else descriptorArrow context node.tag descriptor
          let actual ← nativeHomType value
          checkSymbolicCategory actual type
          checked.modify (·.push value)
          if let some (source, target) := node.framed then
            constrain actual.getAppArgs[2]! source construction false
            constrain actual.getAppArgs[3]! target construction true
          visit remaining
  visit nodes.toList

/-- Validate supplied symbolic data in a transient native scope. Authenticated opaque packet
positions are opened as rigid locals at their original declaration binder. Discovering a new
position restarts the complete check; no partial pass or opaque mathematical term escapes.
The optional position resolver is used only here, never by ordinary source preparation. -/
opaque validateSymbolicBatch (context : PublishedSourceContext)
    (nodes : Array NativeSymbolicNode)
    (checkShared : Expr → Expr → TermElabM Unit)
    (parameterCount : Nat := 0)
    (parameterPosition? : Json → MetaM (Option Nat) := fun _ => pure none) :
    TermElabM Unit := do
  let original ← Term.saveState
  try
    withNewMCtxDepth do
      let rec withParameters (fuel : Nat) (parameters : Array (Nat × Expr)) :
          TermElabM Unit := do
        let saved ← Term.saveState
        let current := (← getLCtx).foldl (fun values declaration =>
          values.push (mkFVar declaration.fvarId)) (#[] : Array Expr)
        let pending ← IO.mkRef (none : Option (Nat × Expr × Meta.SavedState))
        let validationContext := { context with
          literal := fun domain packet => do
            let some position ← parameterPosition? packet | return ← context.literal domain packet
            unless position < parameterCount do
              throwError "an opaque symbolic parameter is outside its original packet table"
            if ← isProp domain then
              throwError "opaque symbolic data cannot supply a native proof parameter"
            if let some (_, value) := parameters.find? (·.1 == position) then
              checkRegisteredDomains (← inferType value) domain
              unless ← isDefEq (← inferType value) domain do
                throwError "one opaque packet position changed its native declaration type"
              return some value
            if (← pending.get).isNone then
              pending.set (some (position, ← instantiateMVars domain, ← Meta.saveState))
            throwError "the symbolic parameter requires its exact transient native scope" }
        let outcome ← try
            validateSymbolicCore validationContext nodes checkShared
            for (_, value) in parameters do
              if ← isProof value then
                malformed "opaque symbolic data resolved to a native proof parameter"
            pure (Except.ok ())
          catch error => pure (Except.error error)
        match ← pending.get with
        | none =>
          match outcome with
          | .ok () => pure ()
          | .error error =>
            saved.restore (restoreInfo := true)
            throw error
        | some (position, domain, discovered) =>
          discovered.restore
          let domain ← instantiateMVars domain
          let template ← abstractMVars domain
          if template.expr.hasMVar ||
              (template.expr.find? fun term => term.isFVar && !current.contains term).isSome then
            saved.restore (restoreInfo := true)
            malformed "an opaque parameter depends on a temporary or unresolved source scope"
          saved.restore (restoreInfo := true)
          let (_, _, domain) ← openAbstractMVarsResult template
          match fuel with
          | 0 => malformed "the opaque parameter table changed during native framing"
          | fuel + 1 =>
            check domain
            withLocalDeclD (← mkFreshUserName `opaqueNativeParameter) domain fun value =>
              withParameters fuel (parameters.push (position, value))
      withParameters parameterCount #[]
  finally
    original.restore (restoreInfo := true)

/-- Source-only single-node entrance. Runtime packets use the complete batch above. -/
opaque validateSymbolic (context : PublishedSourceContext) (expected : Expr) (tag : String)
    (operands : Array NativeSymbolicOperand) (descriptor : Option Json)
    (inputActions : Array Json := #[]) : TermElabM Unit :=
  validateSymbolicBatch context #[{ expected, tag, operands, descriptor, inputActions }]
    fun first second => do
      checkRegisteredDomains first second
      unless ← isDefEq first second do
        malformed "the symbolic maps changed their shared original native endpoint"

private def homAt (bundle source target : Expr) : TermElabM Expr := do
  let type ← nativeHomType (← categoricalPointIdentity bundle source)
  return mkAppN type.getAppFn (type.getAppArgs.set! 3 target)

mutual

/-- Read explicit map data through actual native operands and the complete selected category. -/
private partial def mapValue (context : PublishedSourceContext) (bundle : Expr)
    (packet : Json) : TermElabM Expr := do
  if let some value ← context.retained packet then
    let type ← nativeHomType value
    unless ← isDefEq type (← homAt bundle type.getAppArgs[2]! type.getAppArgs[3]!) do
      malformed "a retained map belongs to a different complete selected category"
    return value
  let tag ← match packet.getObjValAs? String "ctor" with
    | .ok tag => pure tag
    | .error reason => malformed reason
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  if tag == "typedMap" then
    let data ← match TypedMap.decode packet with
      | .ok data => pure data
      | .error reason => malformed reason
    let source ← context.bind (← operand context carrier data.source)
    let target ← context.bind (← operand context carrier data.target)
    return ← mapAt context bundle source target data.callable
  if tag == "identity" || tag == "zero" then
    let #[sourcePacket, targetPacket] ← arrayField packet "args"
      | malformed "an identity requires both complete endpoint positions"
    let source ← context.bind (← operand context carrier sourcePacket)
    let target ← if sourcePacket == targetPacket then pure source
      else context.bind (← operand context carrier targetPacket)
    if tag == "identity" then
      context.checkInput source target
      return ← categoricalPointIdentity bundle source
    return ← nativeZero (← homAt bundle source target) source target
  if tag == "compose" then
    let #[first, second] ← arrayField packet "args"
      | malformed "composition requires its two complete actual maps"
    let first ← mapValue context bundle first
    let second ← mapValue context bundle second
    let firstType ← nativeHomType first
    let secondType ← nativeHomType second
    let structureValue ← nativeHomStructure (← nativeHomType
      (← categoricalPointIdentity bundle firstType.getAppArgs[2]!))
    return ← mkAppOptM ``CategoryTheory.CategoryStruct.comp #[
      some carrier, some structureValue, some firstType.getAppArgs[2]!,
      some firstType.getAppArgs[3]!, some secondType.getAppArgs[3]!, some first, some second]
  if tag == "map" then
    let #[descriptor, arrow] ← arrayField packet "args"
      | malformed "a map requires its complete action and original typed source arrow"
    let edge ← selectedAction descriptor
    let (functor, _) ← action context edge descriptor
    let (source, target) ← functorCategoryBundles functor
    unless ← isDefEq target bundle do
      malformed "the map action has another complete selected target category"
    return ← mkAppM ``CategoryTheory.Functor.map #[functor, ← mapValue context source arrow]
  let value ← descriptorArrow context tag packet
  let type ← nativeHomType value
  unless ← isDefEq type (← homAt bundle type.getAppArgs[2]! type.getAppArgs[3]!) do
    malformed "the symbolic arrow has another full native selected category"
  return value

private partial def mapAt (context : PublishedSourceContext) (bundle source target : Expr)
    (packet : Json) : TermElabM Expr := do
  let domain ← homAt bundle source target
  let tag := (packet.getObjValAs? String "ctor").toOption
  let value ← if tag.any (#["typedMap", "identity", "zero", "compose", "map", "cellComponent",
      "constructedCellComponent", "cartesianMap", "presentation", "objectField",
      "constructionLeg"].contains ·) then
      mapValue context bundle packet
    else operand context domain packet
  checkRegisteredDomains (← inferType value) domain
  unless ← isDefEq (← inferType value) domain do
    malformed "the supplied map changed its complete native endpoints or category"
  return value

end

private def pointOwner (state : SemanticState) (operation : String)
    (packet : PointInvocation) :
    TermElabM (CategoricalPointOwner × Array Json × Array Json × Json) := do
  if let .ok (some (entry, constructors)) := PublishedPorts.component? state operation then
    let #[.arr parameters, receiver, direction] := packet.parameters
      | malformed "a component requires its complete declaration parameters, receiver and direction"
    let inverse ← match direction.getBool? with
      | .ok inverse => pure inverse
      | .error reason => malformed reason
    unless !inverse || entry.invertible do malformed "the selected component has no inverse"
    let descriptor : ConstructedCellComponent := {
      constructors := constructors.map (·.raw)
      component := { cell := entry.id.raw, parameters, receiver, inverse } }
    let arrow := if constructors.isEmpty then descriptor.component.encode else descriptor.encode
    return (.component entry constructors inverse, parameters, #[receiver], arrow)
  if let .ok (some entry) := PublishedPorts.cartesian? state operation then
    let #[.arr parameters, receiver] := packet.parameters
      | malformed "a cartesian map requires all original reindex parameters and its receiver"
    return (.cartesian entry, parameters, #[receiver],
      ({ reindex := entry.id.raw, parameters, receiver } : CartesianMap).encode)
  let morphisms := state.morphisms.filter (·.id.raw == operation)
  let applications := state.objects.filter fun entry =>
    entry.application.isSome && entry.applicationAddress == operation
  let binders := state.binders.filter (·.id.raw == operation)
  if let (#[entry], #[], #[]) := (morphisms, applications, binders) then
    return (.named (.morphism entry), packet.parameters, #[],
      Json.mkObj [("ctor", toJson operation), ("args", .arr packet.parameters)])
  if let (#[], #[entry], #[]) := (morphisms, applications, binders) then
    return (.named (.application entry), packet.parameters, #[],
      Json.mkObj [("ctor", toJson operation), ("args", .arr packet.parameters)])
  if let (#[], #[], #[entry]) := (morphisms, applications, binders) then
    return (.binder entry, packet.parameters, #[],
      Json.mkObj [("ctor", toJson operation), ("args", .arr packet.parameters)])
  unless morphisms.isEmpty && applications.isEmpty && binders.isEmpty do
    malformed "the point request has several original published owners"
  let direct := state.functors.filter (fun entry => entry.id.raw ++ "#map" == operation)
  let edge ← match direct with
    | #[entry] => pure (EdgeRef.functor entry.id)
    | #[] =>
      match PublishedPorts.edge? state operation with
      | .ok (some (edge, true)) => pure edge
      | _ => malformed "the point request does not name an actual published categorical arrow"
    | _ => malformed "the map request has several original functor owners"
  let request ← match edge with
    | .functor id =>
      match PointInvocation.decodeFunctorMap id.raw packet.encode with
      | .ok value => pure value
      | .error reason => malformed reason
    | _ =>
      match PointInvocation.decodeActionMap
          ("action:" ++ (edgeImageDescriptor edge).compress) packet.encode with
      | .ok value => pure value
      | .error reason => malformed reason
  let #[descriptor, arrow] ← arrayField request.arrow "args"
    | malformed "the action lost its original map descriptor"
  let parameters ← actionParameters edge descriptor
  let arrow ← match TypedMap.decode arrow with
    | .ok arrow => pure arrow
    | .error reason => malformed reason
  return (.action edge, parameters, #[arrow.source, arrow.target, arrow.callable], request.arrow)

/-- All original native parameters and endpoints come from the released point envelope.
A whole-map demand returns its actual native arrow. Scalar continuation retains the original
carrier field, and generalized application uses the native composition family. -/
private def point (context : PublishedSourceContext) (operation : String)
    (arguments : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match PointInvocation.decode arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  unless packet.operation == operation do malformed "the point packet changed its original operation"
  let state ← semanticState
  let (owner, declarationPackets, extras, descriptor) ← pointOwner state operation packet
  let retainedArgument ← context.retained packet.argument
  let generalized : Bool ← match retainedArgument with
    | some value => do
      let type ← inferType value
      pure (type.isAppOfArity ``Quiver.Hom 4 ||
        (← whnfR type).isAppOfArity ``Quiver.Hom 4)
    | none => do
      let tag := (packet.argument.getObjValAs? String "ctor").toOption.getD ""
      pure (#["typedMap", "identity", "zero", "compose", "map", "cellComponent",
        "constructedCellComponent", "cartesianMap", "presentation", "objectField",
        "constructionLeg"].contains tag || state.morphisms.any (·.id.raw == tag) ||
        state.binders.any (·.id.raw == tag))
  if !generalized then
    if let .named _ := owner then return ← namedPoint context operation arguments
  let family ← CategoricalPointFamily.forOwner owner
  let original ← explicit context (← mkConstWithFreshMVarLevels family.declaration)
    declarationPackets (resolved := false)
  let .const declaration levels := original.getAppFn.consumeMData
    | malformed "the point declaration lost its original application spine"
  unless declaration == family.declaration do malformed "the point changed its original declaration"
  let mut parameters := original.getAppArgs
  unless parameters.size == family.declarationParameterCount do
    malformed "the point lost its complete original declaration telescope"
  let arrowHead := family.arrowFamily.instantiateLevelParams family.universeParams levels
  for packet in extras, index in [:extras.size] do
    let partialArrow := mkAppN arrowHead parameters
    let .forallE _ domain _ _ ← whnfR (← inferType partialArrow)
      | malformed "the point descriptor supplied another native parameter"
    let value ← if let .action edge := owner then
        if index == 2 then do
          let (functor, _) ← categoricalActionValue state edge original
          let (sourceBundle, _) ← functorCategoryBundles functor
          mapAt context sourceBundle parameters[family.declarationParameterCount]!
            parameters[family.declarationParameterCount + 1]! packet
        else operand context domain packet
      else operand context domain packet
    parameters := parameters.push value
  unless parameters.size == family.parameterCount do
    malformed "the point descriptor omitted an original native parameter"
  parameters ← parameters.mapM instantiateMVars
  let levels ← levels.mapM instantiateLevelMVars
  let (expectedArrow, bundle) ← family.arrowAt levels parameters
  let (expectedSource, expectedTarget) ← categoricalPointEndpoints expectedArrow
  let source ← context.bind (← operand context (← inferType expectedSource) packet.source)
  let target ← context.bind (← operand context (← inferType expectedTarget) packet.target)
  context.checkInput expectedSource source
  context.checkInput expectedTarget target
  let retainedArrow ← context.retained packet.arrow
  let arrow ← if let some arrow := retainedArrow then do
      context.admitCategorical family parameters arrow
      pure arrow
    else do
      unless packet.arrow == descriptor do
        malformed "the point arrow differs from its complete original source descriptor"
      pure expectedArrow
  if generalized then
    let whole := (packet.argument.getObjValAs? String "ctor").toOption == some "identity" &&
      packet.domain == packet.source &&
      (packet.argument.getObjVal? "args" >>= Json.getArr?).toOption ==
        some #[packet.source, packet.source]
    let domain ← if whole then pure source
      else context.bind (← operand context (← inferType expectedSource) packet.domain)
    let point ← if whole then categoricalPointIdentity bundle source
      else mapAt context bundle domain source packet.argument
    let family ← if whole then family.asWhole else pure family
    let point ← family.withRequest levels parameters arrow domain source target point
    return ← family.mark levels parameters domain point
  let function ← family.function levels parameters arrow
  let .forallE _ pointType _ _ ← whnfR (← inferType function)
    | malformed "the selected category has no native scalar point interface"
  let point ← operand context pointType packet.argument
  let some originalPoint ← sourcePointOrigin? point
    | malformed "the scalar operand lost its original generalized-point domain"
  let domain ← context.bind (← operand context (← inferType originalPoint.domain) packet.domain)
  context.checkInput originalPoint.domain domain
  let family ← family.asReference
  let arrow ← if retainedArrow.isSome then pure arrow
    else family.mark levels parameters source (← categoricalPointIdentity bundle source)
  let point ← family.withScalarRequest levels parameters arrow domain source target point
  let function ← family.function levels parameters arrow
  let (result, _) ← elabSourceApplication function #[Syntax.missing] none fun _ _ => pure point
  return result

/-- A raw diagram is read at the actual selected presentation's native constructor.
Original declaration metavariables identify parameter positions before any native unification;
the supplied source/type subterms at those exact positions retain their original occurrences. -/
private def rawLimit (context : PublishedSourceContext) (entry : LimitEntry)
    (arguments : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason | .ok () => pure ()
  let family ← LimitFamily.forId entry.id
  let declaration ← mkConstWithFreshMVarLevels family.entry.declaration
  let (parameters, _, result) ← forallMetaTelescopeReducing (← inferType declaration)
  let result ← whnfR result
  unless result.isAppOf (if entry.colimit then ``CategoryTheory.Limits.ColimitCocone
      else ``CategoryTheory.Limits.LimitCone) do
    malformed "the raw limit lost its original universal presentation"
  let some originalDiagram := result.getAppArgs.back?
    | malformed "the raw limit lost its complete native diagram"
  let (nativeTag, fields) ← LimitFamily.diagramPorts originalDiagram
  let tag ← match arguments.getObjValAs? String "ctor" with
    | .ok tag => pure tag | .error reason => malformed reason
  unless tag == nativeTag do malformed "the raw diagram changed its original declared constructor"
  let packets ← arrayField arguments "args"
  unless fields.size == packets.size do
    malformed "the raw diagram changed its complete original explicit field count"
  let (_, bundle) ← functorCategoryBundles originalDiagram
  let mut parameterIds : Std.HashMap MVarId Nat := {}
  for parameter in parameters, index in [:parameters.size] do
    let .mvar identity := parameter
      | malformed "the raw presentation lost an original formal parameter position"
    parameterIds := parameterIds.insert identity index
  let retained ← IO.mkRef (Array.replicate parameters.size (none : Option Expr))
  let remember := fun (identity : MVarId) (actual : Expr) => do
    let some index := parameterIds[identity]? | return
    if ← isProof actual then return
    let actual ← instantiateMVars actual
    if actual.hasMVar || actual.hasLevelMVar then
      malformed "the raw diagram did not supply a complete original parameter"
    if let some previous := (← retained.get)[index]?.bind id then
      -- The already chosen original position is authoritative. A later occurrence
      -- validates against it; equal native expressions never choose another supplier.
      context.checkInput actual previous
    else
      let bound ← context.bind actual
      retained.modify (·.set! index (some bound))
  let rec positions : Expr → Expr → TermElabM Unit
    | .mvar identity, actual => remember identity actual
    | .mdata _ expected, actual => positions expected actual
    | .app expectedFunction expectedArgument, actual => do
      let .app actualFunction actualArgument := actual.consumeMData | return
      positions expectedFunction actualFunction
      positions expectedArgument actualArgument
    | .proj owner index expected, actual => do
      let .proj actualOwner actualIndex actual := actual.consumeMData | return
      unless owner == actualOwner && index == actualIndex do return
      positions expected actual
    | .lam _ domain body _, actual => do
      let .lam _ actualDomain actualBody _ := actual.consumeMData | return
      positions domain actualDomain
      positions body actualBody
    | .forallE _ domain body _, actual => do
      let .forallE _ actualDomain actualBody _ := actual.consumeMData | return
      positions domain actualDomain
      positions body actualBody
    | .letE _ type value body _, actual => do
      let .letE _ actualType actualValue actualBody _ := actual.consumeMData | return
      positions type actualType
      positions value actualValue
      positions body actualBody
    | _, _ => pure ()
  for original in fields, packet in packets do
    let statedType ← inferType original
    let type ← instantiateMVars statedType
    let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
    let actual ← if type.isAppOfArity ``Quiver.Hom 4 then mapValue context bundle packet
      else operand context type packet
    let actualType ← inferType actual
    checkRegisteredDomains actualType statedType
    unless ← isDefEq actual original do
      malformed "the raw diagram changed a fixed native field or original parameter"
    positions original actual
    positions statedType actualType
  let selected ← retained.get
  let mut computational := #[]
  for parameter in parameters, index in [:parameters.size] do
    if ← isProof parameter then continue
    let some actual := selected[index]?.bind id
      | malformed "the raw diagram omitted an original native parameter position"
    computational := computational.push actual
  let declaration ← instantiateMVars declaration
  let applied ← applySourceArguments declaration (Array.replicate computational.size Syntax.missing)
    fun index domain => do
      let some actual := computational[index]?
        | malformed "the raw presentation changed its complete computational telescope"
      unless ← isDefEq (← inferType actual) domain do
        malformed "the raw parameter changed its original native binder type"
      pure actual
  let .const selectedDeclaration levels := applied.getAppFn.consumeMData
    | malformed "the raw limit lost its actual declaration spine"
  unless selectedDeclaration == entry.declaration &&
      applied.getAppNumArgs == family.parameterCount do
    malformed "the raw presentation changed its original complete application"
  family.mark levels applied.getAppArgs

private def actionObject (context : PublishedSourceContext) (operation : String)
    (edge : EdgeRef) (arguments : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args", "receiver"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match edge with
    | .functor _ =>
      match ConstructionInvocation.decode operation arguments with
      | .ok packet => pure packet
      | .error reason => malformed reason
    | _ =>
      match ConstructionInvocation.decodeAction operation arguments with
      | .ok packet => pure packet
      | .error reason => malformed reason
  let declarationPackets ← match edge with
    | .functor _ => pure packet.parameters
    | _ => actionParameters edge packet.parameters[0]!
  let family ← SourceActionFamily.forEdge edge
  unless family.operation == operation do malformed "the object action changed its original edge"
  let original ← explicit context (← mkConstWithFreshMVarLevels family.declaration)
    declarationPackets (resolved := false)
  let .const declaration levels := original.getAppFn.consumeMData
    | malformed "the object action lost its complete native declaration spine"
  unless declaration == family.declaration && original.getAppNumArgs == family.parameterCount do
    malformed "the object action changed its complete native declaration telescope"
  let parameters := original.getAppArgs
  let head := family.family.instantiateLevelParams family.universeParams levels
  let .forallE _ domain _ _ ← whnfR (← inferType (mkAppN head parameters))
    | malformed "the object action lost its original native receiver"
  let receiver ← operand context domain packet.receiver
  let parameters ← parameters.mapM instantiateMVars
  let levels ← levels.mapM instantiateLevelMVars
  family.mark levels parameters (← instantiateMVars receiver)

/-- A universal action consumes the actual earlier cone at its original native slot.
The retained completion supplies the owner; external parameters and prepared_role only
validate that same selected source interface. They cannot select another equal cone. -/
private def universalRequest (context : PublishedSourceContext) (operation input : String)
    (family : LimitUniversalFamily) (arguments : Json) : TermElabM Expr := do
  unless input == family.input do
    malformed "the universal action requires its complete original native input form"
  let role ← match arguments.getObjValAs? String "prepared_role" with
    | .ok role => pure role | .error reason => malformed reason
  let path := ((role.splitOn "/").filter (!·.isEmpty)).toArray.map String.toName
  unless path[0]? == some family.projection do
    malformed "the universal action lost its full original presentation path"
  let bindings ← arrayField arguments "bindings"
  for binding in bindings do
    match checkServiceFields #["slot", "value"] binding with
    | .ok () => pure () | .error reason => malformed reason
  let some coneProjection := (← getEnv).getProjectionFnInfo?
      family.presentation.coneProjection
    | malformed "the universal action lost its original native cone projection"
  let #[coneBinding] := bindings.filter fun binding =>
      binding.getObjValAs? Nat "slot" == .ok coneProjection.i
    | malformed "the universal action requires exactly its original completed cone slot"
  let conePacket ← match coneBinding.getObjVal? "value" with
    | .ok packet => pure packet | .error reason => malformed reason
  let some (owner, selected, cone) ← context.constructionCone conePacket
    | malformed "the universal action requires its original retained complete cone"
  family.presentation.requireInterface selected.source
  let original := selected.source.interface.presentation
  let .const declaration levels := original.consumeMData.getAppFn
    | malformed "the universal cone lost its original declared presentation"
  unless declaration == family.presentation.entry.declaration &&
      original.getAppNumArgs == family.parameterCount do
    malformed "the universal cone belongs to another original native presentation"
  let supplied ← complete context (mkConst declaration levels)
    (← arrayField arguments "parameters")
  let supplied ← instantiateMVars supplied
  unless supplied.consumeMData.getAppFn == original.consumeMData.getAppFn &&
      supplied.getAppNumArgs == family.parameterCount do
    malformed "the universal request changed its complete original parameter telescope"
  for expected in original.getAppArgs, actual in supplied.getAppArgs do
    if ← isProof expected then
      unless ← isDefEq (← inferType expected) (← inferType actual) do
        malformed "the universal request changed an original formal hypothesis"
    else
      context.checkInput expected (← context.bind actual)
  let parent ← SourceLayout.ofTerm (← context.scope.close original)
  let #[universal] := parent.fields.filter (·.projection == family.projection)
    | malformed "the universal action lost its original native record position"
  let predecessors ← parent.actionInputs context.scope original #[universal]
  unless bindings.size == predecessors.size do
    malformed "the universal action changed its complete earlier native field inputs"
  for predecessor in predecessors do
    let #[binding] := bindings.filter fun binding =>
        binding.getObjValAs? Nat "slot" == .ok predecessor.sourceIndex
      | malformed "the universal action changed an original predecessor slot"
    let packet ← match binding.getObjVal? "value" with
      | .ok packet => pure packet | .error reason => malformed reason
    let expected ← predecessor.source.inContext context.scope
    let actual ← if predecessor.projection == family.presentation.coneProjection then
        pure cone
      else context.bind (← operand context (← inferType expected) packet)
    context.checkInput expected actual
  let initial ← family.markAtOwner owner levels original.getAppArgs (some cone)
  let mut layout ← SourceLayout.ofTerm (← context.scope.close initial)
  let mut fields : Array FieldLayout := #[]
  for projection in path.extract 1 path.size do
    let #[field] := layout.fields.filter (·.projection == projection)
      | malformed "the universal action requests another native data field"
    if field.wireIndex.isNone then
      malformed "a universal property's formal law is not a computational field"
    fields := fields.push field
    layout ← field.toLayout
  unless operation == nativeRecordActionAddress family.operation fields do
    malformed "the universal operation differs from its exact native field address"
  complete context (← layout.source.inContext context.scope)
    (← arrayField arguments "arguments")

/-- A creation request starts from its explicit original source owner and unchanged
actual target c/t. All remaining source data are checked at their retained native positions;
the fixed comparison stays inside the already selected contextual family. -/
private def creationRequest (context : PublishedSourceContext) (operation input : String)
    (arguments : Json) : TermElabM Expr := do
  let packets ← arrayField arguments "parameters"
  unless packets.size ≥ 4 do
    malformed "the creation request requires its target cone, universal data, owner and source diagram"
  let some conePacket := packets[0]? | malformed "the creation request lost its target cone"
  let some universalPacket := packets[1]? | malformed "the creation request lost its universal data"
  let some ownerPacket := packets[2]? | malformed "the creation request lost its original source owner"
  let some diagramPacket := packets[3]? | malformed "the creation request lost its source diagram"
  let some (selected, owner) ← context.creationOwner ownerPacket
    | malformed "the creation request requires its explicit retained original construction owner"
  let some prepared ← PreparedCreationFamily.ofSelection context.scope owner
    | malformed "the retained owner has no original accepted creation family"
  unless prepared.operation == operation && input == prepared.input &&
      prepared.construction == selected.source.construction do
    malformed "the creation request changed its original lift, input or selected construction"
  unless (← arrayField arguments "bindings").isEmpty do
    malformed "a complete creation request cannot replace its result's native predecessor fields"
  let some (_, target, cone) ← context.constructionCone conePacket
    | malformed "the creation request requires its original actual completed target cone"
  unless target.source.row == prepared.target.entry.id.raw &&
      target.source.construction == prepared.construction do
    malformed "the creation request changed its original target-cone occurrence"
  prepared.target.requireInterface target.source
  let expectedCone ← prepared.interface.targetCone.inContext context.scope
  context.checkInput expectedCone cone
  let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
  let universal ← context.bind (← operand context universalType universalPacket)
  context.checkInput (← prepared.interface.targetUniversal.inContext context.scope) universal
  match checkServiceFields #["ctor", "args"] diagramPacket with
  | .ok () => pure () | .error reason => malformed reason
  unless diagramPacket.getObjValAs? String "ctor" == .ok prepared.inputs.diagramTag do
    malformed "the creation request changed its original native source diagram constructor"
  let fields ← arrayField diagramPacket "args"
  unless fields.size == prepared.inputs.diagramPorts.size do
    malformed "the creation request changed its complete native source diagram fields"
  for field in prepared.inputs.diagramPorts, packet in fields do
    let expected ← field.source.source.inContext context.scope
    context.checkInput expected
      (← context.bind (← operand context (← inferType expected) packet))
  let captures := prepared.captureSources
  unless packets.size == 4 + captures.size do
    malformed "the creation request changed its full original computational capture table"
  for source in captures, packet in packets.extract 4 packets.size do
    let expected ← source.inContext context.scope
    context.checkInput expected
      (← context.bind (← operand context (← inferType expected) packet))
  let prepared ← prepared.withArguments context.scope cone universal
  let initial ← prepared.mark context.scope
  let role ← match arguments.getObjValAs? String "prepared_role" with
    | .ok role => pure role | .error reason => malformed reason
  let path := ((role.splitOn "/").filter (!·.isEmpty)).toArray.map String.toName
  let mut layout ← SourceLayout.ofTerm (← context.scope.close initial)
  for projection in path do
    let #[field] := layout.fields.filter (·.projection == projection)
      | malformed "the creation continuation changed its original native result path"
    if field.wireIndex.isNone then
      malformed "a creation law is not a computational result field"
    layout ← field.toLayout
  complete context (← layout.source.inContext context.scope)
    (← arrayField arguments "arguments")

/-- The single compiler entrance from a published address and its original typed operands.
Wire scope/owner checks are callbacks, and every mathematical application and selected route
is formed here through the native source producers. The result goes to the ordinary lowerer. -/
opaque prepare (context : PublishedSourceContext) (call : Json) : TermElabM Expr := do
  let operation ← match call.getObjValAs? String "op" with
    | .ok operation => pure operation
    | .error reason => malformed reason
  let arguments ← match call.getObjVal? "args" with
    | .ok arguments => pure arguments
    | .error reason => malformed reason
  let state ← semanticState
  if state.objects.any (fun entry => entry.application.isSome && entry.applicationAddress == operation) &&
      state.entries.any (·.stableId == operation) then
    malformed "the application address also names another registered row"
  let input := do
    match call.getObjValAs? String "input" with
    | .ok input => pure input
    | .error reason => malformed reason
  let term ← if operation == "$cas.project" then do
      let position ← match arguments.getObjValAs? Nat "field" with
        | .ok position => pure position
        | .error reason => malformed reason
      let (source, projection) ← context.projection
        ((arguments.getObjVal? "value").toOption.getD .null) position
      let some info := (← getEnv).getProjectionFnInfo? projection
        | malformed "the retained source field lost its native projection"
      let value := Expr.proj (← getConstInfoCtor info.ctorName).induct info.i source
      check value
      pure value
    else if operation == "$cas.apply" then do
      let some source ← context.retained ((arguments.getObjVal? "value").toOption.getD .null)
        | malformed "the acted value must be a scoped reference"
      complete context source (← arrayField arguments "arguments")
    else if let .ok (some (edge, false)) := PublishedPorts.edge? state operation then
      actionObject context operation edge arguments
    else if (arguments.getObjVal? "receiver").isOk &&
        state.functors.any (·.id.raw == operation) then do
      let #[entry] := state.functors.filter (·.id.raw == operation)
        | malformed "the object action has several original functor owners"
      actionObject context operation (.functor entry.id) arguments
    else if let some entry := state.methods.find? (·.id.raw == operation) then
      method context entry (← input) arguments
    else if let some entry := state.properties.find? (·.id.raw == operation) then
      property context entry (← input) arguments
    else if (arguments.getObjValAs? String "ctor").toOption == some "apply" then
      point context operation arguments
    else if let .ok (some (entry, constructors)) := PublishedPorts.component? state operation then
      component context operation entry constructors arguments
    else if let some row := state.presentations.find? (·.id.raw == operation) then
      presentation context row arguments
    else if (← PublishedPorts.creation? state operation).isSome then
      creationRequest context operation (← input) arguments
    else if let some family ← PublishedPorts.limitUniversal? state operation then
      universalRequest context operation (← input) family arguments
    else if state.limits.any (·.id.raw == operation) then do
      let #[entry] := state.limits.filter (·.id.raw == operation)
        | malformed "the raw limit address has several original native owners"
      rawLimit context entry arguments
    else do
      let (initial, prescribed, reference) ← if let some (_, family, path) ← LiftFamily.forAddress? state operation then do
          let (head, _) ← family.instantiate
          pure (family.mark (← complete context head (← arrayField arguments "parameters")), some path, none)
        else do
          let some family ← PublishedPorts.family? state operation
            | malformed "the operation is not a published address"
          let declaration ← family.declaration state
          discard <| checkedDeclaration declaration
          let selected ← match family with
            | .method _ => malformed "a method requires its complete routed invocation"
            | .construction id => pure (sourceReference ``ConstructionEntry id.raw declaration)
            | .functor id => pure (sourceReference ``EdgeRef.functor id.raw declaration)
            | .operation id => pure (sourceReference ``OperationEntry id.raw declaration)
            | .morphism id => pure (sourceReference ``MorphismEntry id.raw declaration)
          pure (← complete context (selected (← mkConstWithFreshMVarLevels declaration))
            (← arrayField arguments "parameters"), none, some family)
      let role ← match arguments.getObjValAs? String "prepared_role" with
        | .ok role => pure role
        | .error reason => malformed reason
      let path := ((role.splitOn "/").filter (!·.isEmpty)).toArray.map String.toName
      if let some prescribed := prescribed then
        unless path == prescribed do malformed "the requested field differs from its published lift address"
      let mut layout ← SourceLayout.ofTerm (← context.scope.close initial)
      let mut selected : Array FieldLayout := #[]
      for projection in path do
        let #[field] := layout.fields.filter (·.projection == projection)
          | malformed m!"{projection} is not a field of this published interface"
        if field.wireIndex.isNone then malformed "a formal proof is not a published computational field"
        selected := selected.push field
        layout ← field.toLayout
      if let some reference := reference then
        unless operation == recordActionAddress reference selected do
          malformed "the operation address differs from its actual declared computational field"
      let term ← layout.source.inContext context.scope
      complete context term (← arrayField arguments "arguments")
  let term ← instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then malformed "the call leaves a complete native parameter undetermined"
  check term
  return term

end PublishedSource
end CasCompiler
