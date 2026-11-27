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




structure PublishedSourceContext (σ : Type) where
  scope : σ → OpenContext
  identities : σ → CasRuntime.IdentitySupply
  selections : σ → SourceSelectionScope Expr
  select : SourceSelection Expr → Option Expr → StateCpsT σ TermElabM Expr
  retained : σ → Json → MetaM (Option Expr)
  actionSource : Json → StateCpsT σ TermElabM (Option Expr)
  literal : Expr → Json → MetaM (Option Expr)
  bind : Expr → StateCpsT σ TermElabM Expr
  bindAt : Expr → Expr → StateCpsT σ TermElabM Expr
  rebind : Expr → Expr → StateCpsT σ TermElabM Expr
  methodParameters : RoutedMethodFamily → Array Expr → Expr → StateCpsT σ TermElabM (Array Expr)
  checkInput : σ → Expr → Expr → MetaM Unit
  admitMethod : σ → RoutedMethodFamily → Expr → String → MetaM Unit
  admitProperty : σ → PropertyFamily → Expr → String → MetaM Unit
  admitPoint : σ → PointFamily → Expr → MetaM Unit
  admitCategorical : σ → CategoricalPointFamily → Array Expr → Expr → MetaM Unit :=
    fun _ _ _ _ => throwError "a retained categorical arrow requires its original runtime owner"
  constructionCone : Json → StateCpsT σ TermElabM (Option (Expr × NativeLimitSelection × Expr)) :=
    fun _ => pure none
  creationOwner : Json → StateCpsT σ TermElabM (Option (NativeLimitSelection × Expr)) :=
    fun _ => pure none
  constructionEndpoint : σ → NativeConstructionLeg → Bool → Expr → MetaM Bool :=
    fun _ _ _ _ => pure false
  projection : Json → Nat → StateCpsT σ TermElabM (Expr × Name)
  withLocal : Name → Expr → StateCpsT σ TermElabM Expr :=
    fun _ _ => liftM (m := TermElabM) <|
      throwError "this source context cannot introduce a symbolic native parameter"

namespace PublishedSource


private def checkInput (context : PublishedSourceContext σ) (expected actual : Expr) :
    StateCpsT σ TermElabM Unit := do
  context.checkInput (← get) expected actual

private def malformed {m : Type → Type _} [Monad m] [MonadLiftT MetaM m]
    {α : Type} (reason : MessageData) : m α :=
  liftM (m := MetaM) <| throwStratum .malformed m!"published source request: {reason}"


private def selection? (context : PublishedSourceContext σ) (value : Expr) :
    StateCpsT σ TermElabM (Option (SourceSelection Expr)) := do
  let state ← get
  let some selected := (context.selections state).findAt? (context.scope state) value.getAppFn
    | return none
  unless selected.formalBindings.size == value.getAppNumArgs do return none
  return some (← liftM (m := MetaM) <| selected.specialize value.getAppArgs)


private def sourceLayout (context : PublishedSourceContext σ) (value : Expr) :
    StateCpsT σ TermElabM SourceLayout := do
  let state ← get
  let scope := context.scope state
  let selections := context.selections state
  let selectionBinding := match value with
    | .fvar localId => do
      let binding ← scope.bindings.find? (·.expression.fvarId! == localId)
      if selections.contains binding.id then some binding.id else none
    | _ => none
  liftM (m := MetaM) <| SourceLayout.ofTerm (← scope.close value)
    (← SourceSelectionScope.close selections scope) selectionBinding

private def arrayField (packet : Json) (key : String) : TermElabM (Array Json) := do
  match (packet.getObjVal? key).bind (·.getArr?) with
  | .ok values => pure values
  | .error reason => malformed reason




def namedApplicable (entry : ObjectEntry ⊕ MorphismEntry) (category : NamedCategoryEntry)
    (select : SourceSelection Expr → Option Expr → StateCpsT σ TermElabM Expr)
    (apply : Expr → Option Expr → StateCpsT σ TermElabM (Except MessageData Expr)) :
    StateCpsT σ TermElabM (Except MessageData (Expr × Expr)) :=
  registeredExpressionsApplicableScoped entry category select apply

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





private partial def readOperand (context : PublishedSourceContext σ) (domain : Expr) (packet : Json) :
    StateCpsT σ TermElabM Expr := do
  if let some source ← context.retained (← get) packet then
    let type ← inferType source
    checkRegisteredDomains type domain
    if ← isDefEq type domain then return source
    let compatible ← (context.scope (← get)).withOriginalSources #[type, domain] fun original => do
      checkRegisteredDomains original[0]! original[1]!
      isDefEq original[0]! original[1]!
    unless compatible do malformed "a retained operand has a different declared type"
    let source ← context.bindAt source domain
    unless ← isDefEq (← inferType source) domain do
      liftM (m := TermElabM) <|
        throwError "the retained operand binding changed its original dependent native type"
    return source
  if let .ok address := packet.getObjValAs? String "ctor" then
    if let some (entry, category) ← namedSelection? address then
      match checkServiceFields #["ctor", "args"] packet with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← arrayField packet "args"
      let formed ← namedApplicable entry category context.select fun head expected => do
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
  let domain ← whnfR (← liftM (m := MetaM) <| instantiateMVars domain)
  if let (.arr components, .const owner levels) := (packet, domain.getAppFn) then
    if (getStructureInfo? (← liftM (m := MetaM) getEnv) owner).isSome then
      let constructor := getStructureCtor (← liftM (m := MetaM) getEnv) owner
      let head := mkAppN (.const constructor.name levels) domain.getAppArgs
      let computational ← liftM (m := MetaM) <| forallTelescopeReducing (← inferType head) fun fields _ => do
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



private partial def explicit (context : PublishedSourceContext σ) (head : Expr) (packets : Array Json)
    (expected : Option Expr := none) (resolved : Bool := true) : StateCpsT σ TermElabM Expr := do
  let value ← applySourceDataArgumentsScoped head packets.size expected fun index domain => do
      let some packet := packets[index]? | malformed "the source input lost an original parameter"
      readOperand context domain packet
  let value ← liftM (m := MetaM) <| instantiateMVars value
  if resolved && (value.hasMVar || value.hasLevelMVar) then
    malformed "the source input leaves a complete native parameter undetermined"
  return value



private partial def complete (context : PublishedSourceContext σ) (head : Expr) (packets : Array Json) :
    StateCpsT σ TermElabM Expr :=
  applySourceArgumentsScoped head (Array.replicate packets.size Syntax.missing) fun index domain => do
    let some packet := packets[index]? | malformed "the source input lost an original parameter"
    readOperand context domain packet

end



opaque operand (context : PublishedSourceContext σ) (domain : Expr) (packet : Json) :
    StateCpsT σ TermElabM Expr := readOperand context domain packet

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




private def method (context : PublishedSourceContext σ) (entry : MethodEntry)
    (input : String) (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  for declaration in ← liftM (m := MetaM) getLCtx do
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
  let receiver ← liftM (m := MetaM) <| instantiateMVars receiver
  let parameters ← liftM (m := MetaM) <| parameters.mapM instantiateMVars
  let levels ← liftM (m := MetaM) <| levels.mapM instantiateLevelMVars
  if receiver.hasMVar || receiver.hasLevelMVar ||
      parameters.any (fun parameter => parameter.hasMVar || parameter.hasLevelMVar) then
    malformed "the receiver leaves the complete method category undetermined"
  context.admitMethod (← get) family receiver input
  let receiver ← context.bind receiver
  let edges := family.route.refs.push (.functor family.functor.id)
  let actions ← family.specializeActions levels parameters
  let routes ← family.actionParameterInputs
  let mut selected := parameters
  let mut supplied : Array (Array Expr) := #[]
  let mut selectedSlots : Std.HashSet Nat := {}
  unless family.actionFamilies.size == edges.size do
    malformed "the selected method lost its complete original action-family table"
  for edge in edges, actionFamily in family.actionFamilies, action in actions,
      descriptor in packet.parameters, inputs in routes do
    let expected ← routedActionParameters actionFamily action
    let packets ← actionParameters edge descriptor
    unless packets.size == expected.size && inputs.size == expected.size do
      malformed "an action changed its complete native parameter arity"
    let mut values := #[]
    for (_, source) in expected, packet in packets, route in inputs do
      let term ← operand context (← inferType source) packet
      let term ← liftM (m := MetaM) <| instantiateMVars term
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
  for actionFamily in family.actionFamilies, action in checkedActions, values in supplied do
    let expected ← routedActionParameters actionFamily action
    let mut inputs := #[]
    for (_, source) in expected, value in values do
      checkInput context source value
      inputs := inputs.push value
    retainedInputs := retainedInputs.push inputs
  let (result, _) ← family.applyAt levels selected receiver context.select retainedInputs
  let mut term := result
  for proof in agreements.reverse do
    let mut proof := proof.instantiateLevelParams family.universeParams levels
    for parameter in selected do proof ← mkAppM ``congrFun #[proof, parameter]
    checkWithKernel proof
    term ← liftM (m := MetaM) <|
      withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
        fun binding => mkLetFVars #[binding] term
          (usedLetOnly := false) (generalizeNondepLet := false)
  return term

private def property (context : PublishedSourceContext σ) (entry : PropertyEntry)
    (input : String) (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  let receiver ← liftM (m := MetaM) <| instantiateMVars receiver
  let bundle ← liftM (m := MetaM) <| instantiateMVars bundle
  if receiver.hasMVar || receiver.hasLevelMVar || bundle.hasMVar || bundle.hasLevelMVar then
    malformed "the receiver leaves the complete property category undetermined"
  let (family, source) ← PropertyFamily.forReceiver
    ⟨.object, category.expression, bundle, none, none⟩ entry.id receiver
  context.admitProperty (← get) family receiver input
  context.select source none

private def namedPoint (context : PublishedSourceContext σ) (operation : String)
    (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  let some selectedPoint ← selection? context point
    | malformed "the operand has no retained original generalized-point domain"
  let some original := selectedPoint.pointOrigin
    | malformed "the operand has no retained original generalized-point domain"
  let domain ← operand context (← inferType original.domain) packet.domain
  let source ← operand context (← inferType expectedSource) packet.source
  let target ← operand context (← inferType expectedTarget) packet.target
  let arrow ← if let some arrow ← context.retained (← get) packet.arrow then do
      context.admitPoint (← get) family arrow
      pure arrow
    else do
      match checkServiceFields #["ctor", "args"] packet.arrow with
      | .error reason => malformed reason
      | .ok () => pure ()
      unless (packet.arrow.getObjValAs? String "ctor").toOption == some operation do
        malformed "the arrow descriptor belongs to a different released family"
      let value ← explicit context head (← arrayField packet.arrow "args")
      let .const declaration levels := value.getAppFn
        | malformed "the named arrow lost its original declaration spine"
      unless declaration == family.declaration do
        malformed "the named arrow changed its original declaration"
      context.select (← family.selected levels value.getAppArgs value) none
  let scope := context.scope (← get)
  let selectedPoint ← liftM (m := TermElabM) <| do
    try
      family.withRequest arrow domain source target
        { selectedPoint with value := point } (some scope)
    catch error =>
      malformed m!"the complete named point inputs disagree: {error.toMessageData}"
  let function ← family.function arrow
  let (result, _) ← elabSourceApplicationScoped function #[Syntax.missing] none
    fun _ domain => context.select selectedPoint (some domain)
  return result

private def presentation (context : PublishedSourceContext σ) (row : PresentationComparisonEntry)
    (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  let source ← operand context (← inferType source.value) packet.source
  let target ← operand context (← inferType target.value) packet.target
  let (first, second) := if packet.inverse then (target, source) else (source, target)
  let scope := context.scope (← get)
  let selected ← liftM (m := TermElabM) <| do
    try family.withEndpoints iso first second (some scope)
    catch error => malformed m!"the comparison endpoints do not match the selected family: {error.toMessageData}"
  let iso ← context.select selected none
  let function ← family.function iso packet.inverse
  let (result, _) ← elabSourceApplicationScoped function #[Syntax.missing] none fun _ domain =>
    operand context domain packet.argument
  return result



private def component (context : PublishedSourceContext σ) (operation : String)
    (entry : CellEntry) (constructors : Array ConstructorId) (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  context.select (← cell.selectedComponent ⟨receiver, none⟩) none



private partial def action (context : PublishedSourceContext σ) (edge : EdgeRef)
    (descriptor : Json) : StateCpsT σ TermElabM (Expr × CategoryExpr) := do
  let state ← semanticState
  let parameters ← actionParameters edge descriptor
  match edge with
  | .functor id =>
    let some entry := state.functor? id | malformed "the selected action functor is absent"
    let view ← viewExpressionsScoped (.inl entry) none context.select fun head =>
      explicit context head parameters (resolved := false)
    return (view.functor, view.target)
  | .classifierForget id =>
    let some entry := state.classifier? id | malformed "the selected action classifier is absent"
    let view ← viewExpressionsScoped (.inr entry) none context.select fun head =>
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
    let selected ← sourceReferenceAt (.constructorInterface entry .functorialAction) value value
    return (← context.select selected none, .construct id #[.category target])

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


opaque actionOperand (context : PublishedSourceContext σ) (descriptor : Json) (arrow : Expr) :
    StateCpsT σ TermElabM Expr := do
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


private def nativeHomStructure (type : Expr) : TermElabM Expr := do
  let quiver := type.getAppArgs[1]!.consumeMData
  if quiver.isAppOfArity ``CategoryTheory.CategoryStruct.toQuiver 2 then
    return quiver.getAppArgs[1]!
  if let .proj owner 0 value := quiver then
    if owner == ``CategoryTheory.CategoryStruct then return value
  malformed "the symbolic map lost its original complete category structure"


inductive NativeSymbolicEndpoint
  | value (expression : Expr)
  | inline (position : Nat)


inductive NativeSymbolicOperand
  | value (expression : Expr)
  | objectData (endpoint : NativeSymbolicEndpoint)
  | mapData (source target : NativeSymbolicEndpoint)


structure NativeSymbolicNode where
  expected : Expr
  tag : String
  operands : Array NativeSymbolicOperand
  descriptor : Option Json
  framed : Option (NativeSymbolicEndpoint × NativeSymbolicEndpoint) := none
  inputActions : Array Json := #[]


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




private def readConstructionLeg (context : PublishedSourceContext σ) (packet : Json) :
    StateCpsT σ TermElabM NativeConstructionLeg := do
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
    checkInput context expected (← context.bind actual)
  let transformation ← mkAppM (if selected.source.colimit then
    ``CategoryTheory.Limits.Cocone.ι else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation]
  let .forallE _ domain _ _ ← whnfR (← inferType component)
    | malformed "the selected cone lost its original native diagram-object telescope"
  let index ← operand context domain indexPacket
  NativeConstructionLeg.prepare owner selected cone (← context.bind index)


private def descriptorArrow (context : PublishedSourceContext σ) (tag : String)
    (packet : Json) : StateCpsT σ TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] packet with
  | .error reason => malformed reason | .ok () => pure ()
  let state ← semanticState
  if tag == "constructionLeg" then
    return ← context.select (← (← readConstructionLeg context packet).selected) none
  if tag == "objectField" then
    let parsed ← match ObjectField.decode packet with
      | .ok parsed => pure parsed | .error reason => malformed reason
    let #[entry] := state.objects.filter (·.id.raw == parsed.object)
      | malformed "the object field has no unique original object declaration"
    let #[category] := state.categories.filter (·.id == entry.category)
      | malformed "the object field lost its complete original registered category"
    let formed ← namedApplicable (.inl entry) category context.select fun head expected => do
      return .ok (← explicit context head parsed.parameters expected)
    let .ok (_, object) := formed
      | malformed "the object field changed its complete original declared object"
    let some selectedObject ← selection? context object
      | malformed "the object field lost its exact selected object binding"
    let some original ← sourceApplication? entry.declaration selectedObject
      | malformed "the object field lost its original declaration parameter table"
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
    let value ← applyObjectParameters entry.id.raw declaration original.getAppArgs
    let value ← if parsed.field == "constants" || parsed.field == "inclusion" then pure value
      else do
        let inverse := parsed.field == "inversePresentation" || parsed.field == "inverseRefinement"
        mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[value]
    let selected := sourceDerivedReference (.named (.registered (.inl entry) category)) value
    return ← context.select { selected with originalApplication := some original } none
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
    return ← context.select (← family.arrowSelection levels (application.getAppArgs.push receiver)) none
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
    let family ← PresentationFamily.forEntry entry
    let iso ← context.select (← family.selected iso) none
    return ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[iso]
  if let some (Sum.inr entry, category) ← namedSelection? tag then
    match checkServiceFields #["ctor", "args"] packet with
    | .error reason => malformed reason | .ok () => pure ()
    let formed ← namedApplicable (.inr entry) category context.select fun head expected => do
      return .ok (← explicit context head (← arrayField packet "args") expected)
    let .ok (_, value) := formed
      | malformed "the named symbolic arrow changed its complete native declaration"
    return value
  if let #[entry] := state.binders.filter (·.id.raw == tag) then
    discard <| checkedDeclaration entry.operation
    let value ← explicit context (← mkConstWithFreshMVarLevels entry.operation)
      (← arrayField packet "args")
    return ← context.select (← sourceReferenceAt (.binder entry) value value) none
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


private def checkSymbolicCategory (actual expected : Expr) : TermElabM Unit := do
  let actualArgs := actual.getAppArgs
  let expectedArgs := expected.getAppArgs
  checkRegisteredDomains actualArgs[0]! expectedArgs[0]!
  unless ← isDefEq (mkAppN actual.getAppFn (actualArgs.extract 0 2))
        (mkAppN expected.getAppFn (expectedArgs.extract 0 2)) <&&>
      isDefEq (← nativeHomStructure actual) (← nativeHomStructure expected) do
    malformed "the symbolic operands use another full native category or Hom interface"


private partial def withSymbolicCategory (type : Expr)
    (actions : Array Expr) (index : Nat) (finish : Expr → TermElabM Unit) : TermElabM Unit := do
  let some functor := actions[index]? | return ← finish type
  let (source, target) ← functorCategoryBundles functor
  let targetCarrier ← mkAppM ``CategoryTheory.Bundled.α #[target]
  withLocalDeclD (← mkFreshUserName `nestedTargetInterface) targetCarrier fun targetObject => do
    let targetType ← nativeHomType (← categoricalPointIdentity target targetObject)
    checkSymbolicCategory targetType type
    let sourceCarrier ← mkAppM ``CategoryTheory.Bundled.α #[source]
    withLocalDeclD (← mkFreshUserName `nestedSourceInterface) sourceCarrier fun sourceObject => do
      let sourceType ← nativeHomType (← categoricalPointIdentity source sourceObject)
      withSymbolicCategory sourceType actions (index + 1) finish



private structure SymbolicEndpointConstraint where
  source : Expr
  construction : Option (NativeConstructionLeg × Bool) := none





private def validatePreparedSymbolic (context : PublishedSourceContext σ) (state : σ)
    (nodes : Array (NativeSymbolicNode × Array Expr × Option Expr ×
      Option NativeConstructionLeg × Option Expr))
    (checkShared : σ → Expr → Expr → TermElabM Unit) : TermElabM Unit := do
  let stableContext ← liftM (m := MetaM) getLCtx
  let stableInstances ← liftM (m := MetaM) getLocalInstances
  let stable := stableContext.foldl (fun values declaration =>
    values.push (mkFVar declaration.fvarId)) (#[] : Array Expr)
  let freshEndpoint : Expr → TermElabM Expr := fun carrier => do
    let carrier ← liftM (m := MetaM) <| instantiateMVars carrier
    if (carrier.find? fun term => term.isFVar && !stable.contains term).isSome then
      malformed "an inline endpoint carrier depends on a temporary category interface"
    withLCtx stableContext stableInstances <| mkFreshExprMVar carrier
  let checked ← IO.mkRef (#[] : Array Expr)
  let known ← IO.mkRef (#[] : Array (Nat × Expr))
  let constraints ← IO.mkRef (#[] : Array (Nat × SymbolicEndpointConstraint))
  let comparisons ← IO.mkRef
    (#[] : Array (SymbolicEndpointConstraint × SymbolicEndpointConstraint))
  let compare := fun (first second : SymbolicEndpointConstraint) => do
    let left ← liftM (m := MetaM) <| instantiateMVars first.source
    let right ← liftM (m := MetaM) <| instantiateMVars second.source
    let handledLeft ← match first.construction with
      | some (original, target) => context.constructionEndpoint state original target right
      | none => pure false
    let handledRight ← match second.construction with
      | some (original, target) => context.constructionEndpoint state original target left
      | none => pure false
    unless handledLeft || handledRight do checkShared state left right
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
  let rec visit : List (NativeSymbolicNode × Array Expr × Option Expr ×
      Option NativeConstructionLeg × Option Expr) → TermElabM Unit
    | [] => do
      synthesizeSyntheticMVars (postpone := .no)
      for (first, second) in ← comparisons.get do
        compare first second
      let constraints ← constraints.get
      for (position, expression) in constraints do
        for (otherPosition, other) in constraints do
          if position == otherPosition then
            compare expression other
      let transient := (← liftM (m := MetaM) getLCtx).foldl (fun values declaration =>
        let value := mkFVar declaration.fvarId
        if stable.contains value then values else values.push value) (#[] : Array Expr)
      for (_, expression) in ← known.get do
        let carrier ← liftM (m := MetaM) <| instantiateMVars (← inferType expression)
        if carrier.hasMVar || carrier.hasLevelMVar ||
            (carrier.find? fun term => term.isFVar && !stable.contains term).isSome then
          malformed "an inline endpoint has no complete native carrier in its original scope"
      let allowed ← (← known.get).foldlM (fun result (_, expression) => do
        let unresolved ← getMVars (← liftM (m := MetaM) <| instantiateMVars expression)
        return result ++ unresolved) (#[] : Array MVarId)
      for expression in ← checked.get do
        let expression ← mkLambdaFVars transient (← liftM (m := MetaM) <| instantiateMVars expression)
          (usedOnly := false) (usedLetOnly := false)
        for unknown in ← getMVars expression do
          unless allowed.contains unknown do
            malformed m!"the symbolic interface leaves a native parameter undetermined: {← inferType (.mvar unknown)}"
          let type ← liftM (m := MetaM) <| instantiateMVars (← inferType (.mvar unknown))
          if type.hasMVar || type.hasLevelMVar ||
              (type.find? fun term => term.isFVar && !stable.contains term).isSome then
            malformed "an inline endpoint has no complete native carrier in its original scope"
        let abstracted ← abstractMVars expression (levels := false)
        let closed ← mkLambdaFVars stable abstracted.expr
          (usedOnly := false) (usedLetOnly := false)
        let closed ← liftM (m := MetaM) <| instantiateMVars closed
        if closed.hasMVar || closed.hasLevelMVar || closed.hasFVar || closed.hasSorry then
          malformed "the symbolic interface did not close over its exact rigid native scope"
        checkWithKernel closed
    | (node, actions, functor, construction, prepared) :: remaining => do
      let type ← nativeHomType node.expected
      withSymbolicCategory type actions 0 fun type => do
        let args := type.getAppArgs
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
              let some value := prepared
                | throwError "the symbolic arrow lost its prepared original native descriptor"
              pure value
          let actual ← nativeHomType value
          checkSymbolicCategory actual type
          checked.modify (·.push value)
          if let some (source, target) := node.framed then
            constrain actual.getAppArgs[2]! source construction false
            constrain actual.getAppArgs[3]! target construction true
          visit remaining
  visit nodes.toList




private def validateSymbolicCore (context : PublishedSourceContext σ)
    (nodes : Array NativeSymbolicNode)
    (checkShared : σ → Expr → Expr → TermElabM Unit) : StateCpsT σ TermElabM Unit := do
  let prepared ← nodes.mapM fun node => do
    let actions ← node.inputActions.mapM fun descriptor => do
      let edge ← selectedAction descriptor
      return (← action context edge descriptor).1
    let functor ← if node.tag == "map" then do
        let some descriptor := node.descriptor
          | malformed "a map action lost its complete descriptor"
        let edge ← selectedAction descriptor
        pure (some (← action context edge descriptor).1)
      else pure none
    let (construction, value) ← if #["identity", "zero", "compose", "map"].contains node.tag then
        pure (none, none)
      else do
        let some descriptor := node.descriptor
          | malformed "the symbolic arrow lost its complete original descriptor"
        if node.tag == "constructionLeg" then
          let original ← readConstructionLeg context descriptor
          pure (some original, some original.value)
        else
          pure (none, some (← descriptorArrow context node.tag descriptor))
    pure (node, actions, functor, construction, value)
  validatePreparedSymbolic context (← get) prepared checkShared





opaque validateSymbolicBatch (context : PublishedSourceContext σ) (initial : σ)
    (nodes : Array NativeSymbolicNode)
    (checkShared : σ → Expr → Expr → TermElabM Unit)
    (parameterCount : Nat := 0)
    (parameterPosition? : Json → MetaM (Option Nat) := fun _ => pure none) :
    TermElabM Unit := do
  let original ← Term.saveState
  try
    withNewMCtxDepth do
      let rec withParameters (fuel : Nat) (parameters : Array (Nat × Expr)) (state : σ) :
          TermElabM Unit := do
        let saved ← Term.saveState
        let current := (← liftM (m := MetaM) getLCtx).foldl (fun values declaration =>
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
              pending.set (some (position, ← liftM (m := MetaM) <| instantiateMVars domain, ← Meta.saveState))
            throwError "the symbolic parameter requires its exact transient native scope" }
        let outcome ← try
            (validateSymbolicCore validationContext nodes checkShared).runK state fun _ _ => pure ()
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
          let domain ← liftM (m := MetaM) <| instantiateMVars domain
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
            (context.withLocal (← mkFreshUserName `opaqueNativeParameter) domain).runK state fun value state =>
              withParameters fuel (parameters.push (position, value)) state
      withParameters parameterCount #[] initial
  finally
    original.restore (restoreInfo := true)


opaque validateSymbolic (context : PublishedSourceContext σ) (initial : σ) (expected : Expr) (tag : String)
    (operands : Array NativeSymbolicOperand) (descriptor : Option Json)
    (inputActions : Array Json := #[]) : TermElabM Unit :=
  validateSymbolicBatch context initial #[{ expected, tag, operands, descriptor, inputActions }]
    fun _ first second => do
      checkRegisteredDomains first second
      unless ← isDefEq first second do
        malformed "the symbolic maps changed their shared original native endpoint"

private def homAt (bundle source target : Expr) : TermElabM Expr := do
  let type ← nativeHomType (← categoricalPointIdentity bundle source)
  return mkAppN type.getAppFn (type.getAppArgs.set! 3 target)

mutual


private partial def mapValue (context : PublishedSourceContext σ) (bundle : Expr)
    (packet : Json) : StateCpsT σ TermElabM Expr := do
  if let some value ← context.retained (← get) packet then
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
      checkInput context source target
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

private partial def mapAt (context : PublishedSourceContext σ) (bundle source target : Expr)
    (packet : Json) : StateCpsT σ TermElabM Expr := do
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




private def point (context : PublishedSourceContext σ) (operation : String)
    (arguments : Json) : StateCpsT σ TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match PointInvocation.decode arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  unless packet.operation == operation do malformed "the point packet changed its original operation"
  let state ← semanticState
  let (owner, declarationPackets, extras, descriptor) ← pointOwner state operation packet
  let retainedArgument ← context.retained (← get) packet.argument
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
  parameters ← liftM (m := MetaM) <| parameters.mapM instantiateMVars
  let levels ← liftM (m := MetaM) <| levels.mapM instantiateLevelMVars
  let (expectedArrow, bundle) ← family.arrowAt levels parameters
  let (expectedSource, expectedTarget) ← categoricalPointEndpoints expectedArrow
  let source ← context.bind (← operand context (← inferType expectedSource) packet.source)
  let target ← context.bind (← operand context (← inferType expectedTarget) packet.target)
  checkInput context expectedSource source
  checkInput context expectedTarget target
  let retainedArrow ← context.retained (← get) packet.arrow
  let arrow ← if let some arrow := retainedArrow then do
      context.admitCategorical (← get) family parameters arrow
      pure arrow
    else do
      unless packet.arrow == descriptor do
        malformed "the point arrow differs from its complete original source descriptor"
      context.select (← family.arrowSelection levels parameters) none
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
    let selected ← family.withRequest levels parameters arrow domain source target point
      (some (context.scope (← get)))
    let function := mkAppN
      (family.family.instantiateLevelParams family.universeParams levels) parameters
    let .forallE _ pointType _ _ ← whnfR (← inferType (mkApp function domain))
      | malformed "the generalized point lost its original native argument position"
    let point ← context.select selected (some pointType)
    let selected ← family.selected levels parameters domain { selected with value := point }
      (context := some (context.scope (← get)))
    return ← context.select selected none
  let function ← family.function levels parameters arrow
  let .forallE _ pointType _ _ ← whnfR (← inferType function)
    | malformed "the selected category has no native scalar point interface"
  let point ← operand context pointType packet.argument
  let some selectedPoint ← selection? context point
    | malformed "the scalar operand lost its original generalized-point domain"
  let some originalPoint := selectedPoint.pointOrigin
    | malformed "the scalar operand lost its original generalized-point domain"
  let domain ← context.bind (← operand context (← inferType originalPoint.domain) packet.domain)
  checkInput context originalPoint.domain domain
  let family ← family.asReference
  let selectedPoint ← family.withScalarRequest levels parameters arrow domain source target
    { selectedPoint with value := point } (some (context.scope (← get)))
  let function ← family.function levels parameters arrow
  let (result, _) ← elabSourceApplicationScoped function #[Syntax.missing] none
    fun _ domain => context.select selectedPoint (some domain)
  return result




private def rawLimit (context : PublishedSourceContext σ) (entry : LimitEntry)
    (arguments : Json) : StateCpsT σ TermElabM Expr := do
  match checkServiceFields #["ctor", "args"] arguments with
  | .error reason => malformed reason | .ok () => pure ()
  let family ← LimitFamily.forId entry.id
  let declaration ← mkConstWithFreshMVarLevels family.entry.declaration
  let previous ← liftM (m := MetaM) getMCtx
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
  let owned := (← liftM (m := MetaM) getMCtx).decls.foldl
    (fun result identity _ => if previous.decls.contains identity then result else result.push identity)
    (#[] : Array MVarId)
  let retained ← IO.mkRef (Array.replicate parameters.size (none : Option Expr))
  let remember := fun (identity : MVarId) (actual : Expr) => do
    let some index := parameterIds[identity]? | return
    if ← isProof actual then return
    let actual ← liftM (m := MetaM) <| instantiateMVars actual
    if actual.hasMVar || actual.hasLevelMVar then
      malformed "the raw diagram did not supply a complete original parameter"
    if let some previous := (← liftM (m := IO) retained.get)[index]?.bind id then


      checkInput context actual previous
    else
      let bound ← context.bind actual
      liftM (m := IO) <| retained.modify (·.set! index (some bound))
  let rec positions : Expr → Expr → StateCpsT σ TermElabM Unit
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
    let type ← liftM (m := MetaM) <| instantiateMVars statedType
    let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
    let actual ← if type.isAppOfArity ``Quiver.Hom 4 then mapValue context bundle packet
      else operand context type packet
    let actualType ← inferType actual
    liftM (m := TermElabM) <| extendSourceApplicationScope owned
    checkRegisteredDomains actualType statedType
    unless ← isDefEq actual original do
      malformed "the raw diagram changed a fixed native field or original parameter"
    positions original actual
    positions statedType actualType
  let selected ← liftM (m := IO) retained.get
  let mut computational := #[]
  for parameter in parameters, index in [:parameters.size] do
    if ← isProof parameter then continue
    let some actual := selected[index]?.bind id
      | malformed "the raw diagram omitted an original native parameter position"
    computational := computational.push actual
  let declaration ← liftM (m := MetaM) <| instantiateMVars declaration
  let applied ← applySourceArgumentsScoped declaration (Array.replicate computational.size Syntax.missing)
    fun index domain => do
      let some actual := computational[index]?
        | malformed "the raw presentation changed its complete computational telescope"
      context.bindAt actual domain
  let .const selectedDeclaration levels := applied.getAppFn.consumeMData
    | malformed "the raw limit lost its actual declaration spine"
  unless selectedDeclaration == entry.declaration &&
      applied.getAppNumArgs == family.parameterCount do
    malformed "the raw presentation changed its original complete application"
  let construction ← mkFreshUserName `rawLimitConstruction
  let owner ← family.prepareOwner (context.identities (← get)) levels construction
  let template ← context.select {
    value := owner.selection.receiver
    formalBindings := owner.formalBindings
    limit := some owner.selection } none
  let selected ← family.selectedAtOwner owner levels applied.getAppArgs
  let some original := selected.limit
    | malformed "the whole raw cone lost its complete original owner"
  let retained ← NativeLimitSelection.ofSource
    { original.source with ownerFamily := some template } original.receiver
  context.select { selected with limit := some retained } none

private def actionObject (context : PublishedSourceContext σ) (operation : String)
    (edge : EdgeRef) (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  let parameters ← liftM (m := MetaM) <| parameters.mapM instantiateMVars
  let levels ← liftM (m := MetaM) <| levels.mapM instantiateLevelMVars
  context.select (← family.selected levels parameters (← liftM (m := MetaM) <| instantiateMVars receiver)) none




private def universalRequest (context : PublishedSourceContext σ) (operation input : String)
    (family : LimitUniversalFamily) (arguments : Json) : StateCpsT σ TermElabM Expr := do
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
  let some coneProjection := (← liftM (m := MetaM) getEnv).getProjectionFnInfo?
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
  let supplied ← liftM (m := MetaM) <| instantiateMVars supplied
  unless supplied.consumeMData.getAppFn == original.consumeMData.getAppFn &&
      supplied.getAppNumArgs == family.parameterCount do
    malformed "the universal request changed its complete original parameter telescope"
  for expected in original.getAppArgs, actual in supplied.getAppArgs do
    if ← isProof expected then
      unless ← isDefEq (← inferType expected) (← inferType actual) do
        malformed "the universal request changed an original formal hypothesis"
    else
      checkInput context expected (← context.bind actual)
  let parent ← sourceLayout context original
  let #[universal] := parent.fields.filter (·.projection == family.projection)
    | malformed "the universal action lost its original native record position"
  let predecessors ← parent.actionInputs (context.scope (← get)) original #[universal]
  unless bindings.size == predecessors.size do
    malformed "the universal action changed its complete earlier native field inputs"
  for predecessor in predecessors do
    let #[binding] := bindings.filter fun binding =>
        binding.getObjValAs? Nat "slot" == .ok predecessor.sourceIndex
      | malformed "the universal action changed an original predecessor slot"
    let packet ← match binding.getObjVal? "value" with
      | .ok packet => pure packet | .error reason => malformed reason
    let expected ← predecessor.source.inContext (context.scope (← get))
    let actual ← if predecessor.projection == family.presentation.coneProjection then
        pure cone
      else context.bind (← operand context (← inferType expected) packet)
    checkInput context expected actual
  let some ownerFamily := selected.source.ownerFamily
    | malformed "the universal action lost its exact original owner-template binding"
  let template ← SelectedLimitOwner.ofBinding (context.scope (← get))
    (context.selections (← get)) ownerFamily
  let initial ← family.selectedAtOwner template levels original.getAppArgs context.select (some cone)
  let some application := initial.application
    | malformed "the universal action lost its complete original native family"
  let initial := { initial with
    application := some { application with owner := some owner }
    limit := some selected }
  let declaredType ← mkAppM (if selected.source.colimit then
    ``CategoryTheory.Limits.IsColimit else ``CategoryTheory.Limits.IsLimit) #[cone]
  let initial ← context.select initial (some declaredType)
  let mut layout ← sourceLayout context initial
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
  complete context (← layout.source.inContext (context.scope (← get)))
    (← arrayField arguments "arguments")




private def creationRequest (context : PublishedSourceContext σ) (operation input : String)
    (arguments : Json) : StateCpsT σ TermElabM Expr := do
  let packets ← arrayField arguments "parameters"
  unless packets.size ≥ 4 do
    malformed "the creation request requires its target cone, universal data, owner and source diagram"
  let some conePacket := packets[0]? | malformed "the creation request lost its target cone"
  let some universalPacket := packets[1]? | malformed "the creation request lost its universal data"
  let some ownerPacket := packets[2]? | malformed "the creation request lost its original source owner"
  let some diagramPacket := packets[3]? | malformed "the creation request lost its source diagram"
  let some (selected, owner) ← context.creationOwner ownerPacket
    | malformed "the creation request requires its explicit retained original construction owner"
  let some source ← selection? context owner
    | malformed "the retained owner lost its complete original selected source"
  let some (family, target) := source.creationOwner
    | malformed "the retained owner lost its complete original accepted creation families"
  let some prepared ← PreparedCreationFamily.ofSelection (context.scope (← get)) owner
      selected family target (context.selections (← get))
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
  let expectedCone ← prepared.interface.targetCone.inContext (context.scope (← get))
  checkInput context expectedCone cone
  let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
  let universal ← context.bind (← operand context universalType universalPacket)
  checkInput context (← prepared.interface.targetUniversal.inContext (context.scope (← get))) universal
  match checkServiceFields #["ctor", "args"] diagramPacket with
  | .ok () => pure () | .error reason => malformed reason
  unless diagramPacket.getObjValAs? String "ctor" == .ok prepared.inputs.diagramTag do
    malformed "the creation request changed its original native source diagram constructor"
  let fields ← arrayField diagramPacket "args"
  unless fields.size == prepared.inputs.diagramPorts.size do
    malformed "the creation request changed its complete native source diagram fields"
  for field in prepared.inputs.diagramPorts, packet in fields do
    let expected ← field.source.source.inContext (context.scope (← get))
    checkInput context expected
      (← context.bind (← operand context (← inferType expected) packet))
  let captures := prepared.captureSources
  unless packets.size == 4 + captures.size do
    malformed "the creation request changed its full original computational capture table"
  for source in captures, packet in packets.extract 4 packets.size do
    let expected ← source.inContext (context.scope (← get))
    checkInput context expected
      (← context.bind (← operand context (← inferType expected) packet))
  let initial ← prepared.selectedArguments (context.scope (← get)) owner cone universal
  let initial ← context.select initial none
  let role ← match arguments.getObjValAs? String "prepared_role" with
    | .ok role => pure role | .error reason => malformed reason
  let path := ((role.splitOn "/").filter (!·.isEmpty)).toArray.map String.toName
  let mut layout ← sourceLayout context initial
  for projection in path do
    let #[field] := layout.fields.filter (·.projection == projection)
      | malformed "the creation continuation changed its original native result path"
    if field.wireIndex.isNone then
      malformed "a creation law is not a computational result field"
    layout ← field.toLayout
  complete context (← layout.source.inContext (context.scope (← get)))
    (← arrayField arguments "arguments")




opaque prepare (context : PublishedSourceContext σ) (call : Json) : StateCpsT σ TermElabM Expr := do
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
      let some info := (← liftM (m := MetaM) getEnv).getProjectionFnInfo? projection
        | malformed "the retained source field lost its native projection"
      let value := Expr.proj (← liftM (m := MetaM) <| getConstInfoCtor info.ctorName).induct info.i source
      check value
      pure value
    else if operation == "$cas.apply" then do
      let some source ← context.actionSource ((arguments.getObjVal? "value").toOption.getD .null)
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
      let (initial, prescribed, reference) ← if let some (row, family, path) ←
          LiftFamily.forAddress? state operation then do
          let (head, levels) ← family.instantiate
          let applied ← complete context head (← arrayField arguments "parameters")
          let levels ← liftM (m := MetaM) <| levels.mapM instantiateLevelMVars
          let selected ← family.selected levels applied.getAppArgs
          let computationFamily ← LiftFamily.forLift row .computation
          let bindings ← arrayField arguments "bindings"
          let mut retained : Option (Expr × SourceSelection Expr × Name) := none
          let mut positions : Std.HashSet Nat := {}
          for binding in bindings do
            match checkServiceFields #["slot", "value"] binding with
            | .ok () => pure () | .error reason => malformed reason
            let position ← match binding.getObjValAs? Nat "slot" with
              | .ok position => pure position | .error reason => malformed reason
            unless !positions.contains position do
              malformed "the lift request repeats an original predecessor field slot"
            positions := positions.insert position
            let packet ← match binding.getObjVal? "value" with
              | .ok packet => pure packet | .error reason => malformed reason
            let some actual ← context.retained (← get) packet
              | malformed "a lift predecessor must retain its original actual field occurrence"
            let some fieldSource ← selection? context actual
              | malformed "a lift predecessor lost its complete original selected source"
            let some field := fieldSource.field
              | malformed "a lift predecessor lost its original selected field owner"
            let .fvar ownerId := field.owner
              | malformed "a lift predecessor lost its exact original computation binding"
            let some original ← selection? context field.owner
              | malformed "the lift predecessor owner lost its complete selected computation"
            let some application := original.application
              | malformed "the lift predecessor owner lost its original native family"
            let .lift originalFamily := application.family
              | malformed "the lift predecessor came from another selected operation"
            unless (SelectedApplicationFamily.lift originalFamily).exactlyMatches
                (.lift computationFamily) do
              malformed "the lift predecessor changed its complete original computation family"
            let layout ← sourceLayout context field.owner
            let some declared := layout.fields[position]?
              | malformed "the lift predecessor is outside its original native record"
            unless declared.sourceIndex == position && declared.projection == field.projection &&
                declared.wireIndex.isSome do
              malformed "the lift predecessor changed its original native field position"
            if let some selection := original.recordSelection then
              unless selection == field.selection do
                malformed "the lift predecessor changed its original whole-record selection"
            match retained with
            | some (previous, _, selection) =>
              unless previous.fvarId! == ownerId && selection == field.selection do
                malformed "the lift predecessors came from different original computations"
            | none => retained := some (field.owner, original, field.selection)
          if let some (_, original, _) := retained then
            let some application := original.application
              | malformed "the retained lift lost its original application"
            unless application.parameters.size == applied.getAppNumArgs do
              malformed "the lift continuation changed its complete original parameter table"
            for expected in application.parameters, actual in applied.getAppArgs do
              if ← isProof expected then
                (context.scope (← get)).withOriginalSources
                  #[← inferType expected, ← inferType actual] fun native => do
                    unless ← isDefEq native[0]! native[1]! do
                      malformed "the lift continuation changed an original formal hypothesis"
              else
                checkInput context expected (← context.bind actual)
          let initial ← match family.port, retained with
            | .computation, some (owner, _, _) => pure owner
            | .computation, none => context.select selected none
            | .factor, some (owner, _, selection) =>
              let some application := selected.application
                | malformed "the selected factor lost its complete native family"
              context.select { selected with
                application := some { application with owner := some owner }
                recordSelection := some selection } none
            | .factor, none =>
              malformed "the factor requires its actual original computation predecessors"
          pure (initial, some path, none)
        else do
          let some family ← PublishedPorts.family? state operation
            | malformed "the operation is not a published address"
          if let .method _ := family then
            malformed "a method requires its complete routed invocation"
          let reference ← SelectedSourceReference.forComputation family
          let some declaration := reference.declaration
            | malformed "the published family lost its complete original declaration"
          discard <| checkedDeclaration declaration
          let applied ← complete context (← mkConstWithFreshMVarLevels declaration)
            (← arrayField arguments "parameters")
          let selected ← sourceReferenceAt reference applied applied
          pure (← context.select selected none, none, some family)
      let role ← match arguments.getObjValAs? String "prepared_role" with
        | .ok role => pure role
        | .error reason => malformed reason
      let path := ((role.splitOn "/").filter (!·.isEmpty)).toArray.map String.toName
      if let some prescribed := prescribed then
        unless path == prescribed do malformed "the requested field differs from its published lift address"
      let mut layout ← sourceLayout context initial
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
      let term ← layout.source.inContext (context.scope (← get))
      complete context term (← arrayField arguments "arguments")
  let term ← liftM (m := MetaM) <| instantiateMVars term
  if term.hasMVar || term.hasLevelMVar then malformed "the call leaves a complete native parameter undetermined"
  check term
  return term

end PublishedSource
end CasCompiler
