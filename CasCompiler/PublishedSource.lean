module

public import CasCompiler.SourceTypeOrigin
public import CasCompiler.SourceCarrier
public import CasCompiler.PointFamily
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

private def point (context : PublishedSourceContext) (operation : String)
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

private def actionObject (context : PublishedSourceContext) (operation : String)
    (edge : EdgeRef) (arguments : Json) : TermElabM Expr := do
  match checkServiceFields #["ctor", "args", "receiver"] arguments with
  | .error reason => malformed reason
  | .ok () => pure ()
  let packet ← match ConstructionInvocation.decodeAction operation arguments with
    | .ok packet => pure packet
    | .error reason => malformed reason
  let (functor, _) ← action context edge packet.parameters[0]!
  let (source, target) ← functorCategoryBundles functor
  let receiver ← operand context (← mkAppM ``CategoryTheory.Bundled.α #[source]) packet.receiver
  return ← functorObject functor receiver target (some source)

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
    else if let .ok (some (entry, constructors)) := PublishedPorts.component? state operation then
      component context operation entry constructors arguments
    else if let .ok (some (edge, false)) := PublishedPorts.edge? state operation then
      actionObject context operation edge arguments
    else if let some entry := state.methods.find? (·.id.raw == operation) then
      method context entry (← input) arguments
    else if let some entry := state.properties.find? (·.id.raw == operation) then
      property context entry (← input) arguments
    else if (arguments.getObjValAs? String "ctor").toOption == some "apply" then
      point context operation arguments
    else if let some row := state.presentations.find? (·.id.raw == operation) then
      presentation context row arguments
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
