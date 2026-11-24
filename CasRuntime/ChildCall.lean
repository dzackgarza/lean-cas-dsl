module

public import CasRuntime.ExecutionContext
public import CasCompiler.SourceReference
public import CasRuntime.Literal
public import CasRuntime.Encode
public import CasCompiler.PointFamily
public import CasRuntime.RoutedMethod
public import CasRuntime.Property

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

mutual

/-- An operand of a child call at its declared type. A scoped reference is its retained value; a
structure given as an array is read field by field at the constructor's field types, so a
reference may stand at any position (`[resultRef, 46]` for a pair); anything else is a scalar
literal. Reuse: Lean structure constructors and ScalarLiteral.readAt. -/
private partial def childOperand (marks : IO.Ref (Array ValueBinding)) (context : OpenContext)
    (retained : Json → MetaM (Option ValueBinding)) (domain : Expr) (packet : Json) :
    MetaM Expr := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred operand {packet.compress}: {reason}"
  if let some binding ← retained packet then
    let source ← binding.role.source.inContext context
    unless ← isDefEq (← inferType source) domain do
      malformed "a referenced operand has a different declared type"
    return ← markValue marks binding source
  if let .ok address := packet.getObjValAs? String "ctor" then
    if let some row := (← semanticState).objects.find? (·.id.raw == address) then
      match checkServiceFields #["ctor", "args"] packet with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← match (packet.getObjVal? "args").bind (·.getArr?) with
        | .ok fields => pure fields
        | .error reason => malformed reason
      discard <| checkedDeclaration row.declaration
      let head ← mkConstWithFreshMVarLevels row.declaration
      let value ← childExplicit marks context retained head fields (some domain)
      return sourceReference ``ObjectEntry row.id.raw row.declaration value
    if let some row := (← semanticState).morphisms.find? (·.id.raw == address) then
      match checkServiceFields #["ctor", "args"] packet with
      | .error reason => malformed reason
      | .ok () => pure ()
      let fields ← match (packet.getObjVal? "args").bind (·.getArr?) with
        | .ok fields => pure fields
        | .error reason => malformed reason
      discard <| checkedDeclaration row.declaration
      let head ← mkConstWithFreshMVarLevels row.declaration
      let value ← childExplicit marks context retained head fields (some domain)
      return sourceReference ``MorphismEntry row.id.raw row.declaration value
  let domain ← whnfR (← instantiateMVars domain)
  if let (.arr components, .const owner levels) := (packet, domain.getAppFn) then
    if let some info := getStructureInfo? (← getEnv) owner then
      let constructor := getStructureCtor (← getEnv) owner
      unless components.size == info.fieldNames.size do
        malformed "the structure operand has a different number of fields"
      let mut value := mkAppN (.const constructor.name levels) domain.getAppArgs
      for component in components do
        let .forallE _ field _ _ ← whnf (← inferType value)
          | malformed "the structure operand has more fields than its constructor"
        value := mkApp value (← childOperand marks context retained field component)
      return value
  let some literal ← ScalarLiteral.readAt domain packet
    | malformed "an inline operand has no scalar reading at its declared type"
  return literal

/-- Apply only the explicitly declared computational parameter positions of a named input
family. Native implicit parameters stay in the full telescope and must be determined by the
actual input types. A proof premise is never read from a provider packet. -/
private partial def childExplicit (marks : IO.Ref (Array ValueBinding)) (context : OpenContext)
    (retained : Json → MetaM (Option ValueBinding)) (head : Expr) (packets : Array Json)
    (expected : Option Expr := none) : MetaM Expr := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred named parameters: {reason}"
  let (parameters, binders, result) ← forallMetaTelescopeReducing (← inferType head)
  if let some expected := expected then
    unless ← isDefEq result expected do
      malformed "the named input has a different complete declared type"
  let mut next := 0
  for parameter in parameters, binder in binders do
    let domain ← inferType parameter
    if !binder.isExplicit || (← isProp domain) then continue
    let some packet := packets[next]?
      | malformed "the named input is missing an explicit parameter"
    let value ← childOperand marks context retained domain packet
    unless ← isDefEq parameter value do
      malformed "a named input parameter has a different declared type"
    next := next + 1
  unless next == packets.size do malformed "the named input has extra parameters"
  let value ← instantiateMVars (mkAppN head parameters)
  if value.hasMVar || value.hasLevelMVar then
    malformed "the named input leaves a complete source parameter undetermined"
  return value

end

/-- Read only the complete parameter array of the already decoded public action descriptor.
The outer method decoder owns the grammar; this follows the exact selected native edge. -/
private partial def childActionParameters (edge : EdgeRef) (descriptor : Json) :
    MetaM (Array Json) := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred method action: {reason}"
  let fields ← match (descriptor.getObjVal? "args").bind (·.getArr?) with
    | .ok fields => pure fields
    | .error reason => malformed reason
  let parameters ← match edge with
    | .functor _ => pure fields
    | .classifierForget _ =>
      let #[_, .arr parameters] := fields
        | malformed "classifier forgetting lost its complete parameter array"
      pure parameters
    | .constructMap _ inner =>
      let #[_, action] := fields
        | malformed "the constructor action lost its complete inner action"
      childActionParameters inner action
  unless routedActionDescriptor edge parameters == descriptor do
    malformed "the action descriptor differs from its exact selected edge"
  return parameters

/-- A named method child uses the same checked whole family and actual receiver as source
reading. The packet supplies no mathematical agreement: every alternative is compared before
specialization. Native declaration positions retain every supplied action parameter, and the
ordinary lowerer subsequently performs complete all-boundary realization selection. -/
private def Kernel.childMethod (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (retained : Json → MetaM (Option ValueBinding))
    (entry : MethodEntry) (input : String) (arguments : Json) : MetaM Expr := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred method {entry.id.raw}: {reason}"
  let state ← semanticState
  let registry : RegistryState := { toSemanticState := state }
  let some form := registry.form? input
    | malformed "the explicit input form is not published"
  let some category := state.categories.find? (·.id == form.category)
    | malformed "the input form has no independently selected source category"
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
  for binding in context.bindings do
    if ← isProof binding.expression then evidence := evidence.push binding.expression
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
      let .ok fields := (packet.receiver.getObjVal? "args").bind (·.getArr?)
        | malformed "the Arrow receiver lost its complete native fields"
      unless fields.size == 3 do malformed "the Arrow receiver requires both endpoints and its hom"
      pure (Json.arr fields)
    else pure packet.receiver
  let receiverSource ← childOperand kernel.marks context retained domain receiverPacket
  let receiverSource ← instantiateMVars receiverSource
  let parameters ← parameters.mapM instantiateMVars
  let levels ← levels.mapM instantiateLevelMVars
  if receiverSource.hasMVar || receiverSource.hasLevelMVar ||
      parameters.any (fun parameter => parameter.hasMVar || parameter.hasLevelMVar) then
    malformed "the receiver leaves the complete method category undetermined"
  unless ← CasRuntime.RoutedMethodFamily.admitsSourceForm family receiverSource input do
    malformed "the input form is not the original receiver's source boundary"
  let receiver ← evaluateSource transaction request.program context bound receiverSource
  let edges := family.route.refs.push (.functor family.functor.id)
  let actions ← family.specializeActions levels parameters
  let inputs ← family.actionParameterInputs
  let mut selected := parameters
  let mut supplied : Array (Array ValueBinding) := #[]
  let mut selectedSlots : Std.HashSet Nat := {}
  for edge in edges, action in actions, descriptor in packet.parameters, routes in inputs do
    let expected ← routedActionParameters edge action
    let packets ← childActionParameters edge descriptor
    unless packets.size == expected.size && routes.size == expected.size do
      malformed "an action changed its complete native parameter arity"
    let mut values := #[]
    for (_, source) in expected, packet in packets, route in routes do
      let term ← childOperand kernel.marks context retained (← inferType source) packet
      let term ← instantiateMVars term
      if term.hasMVar || term.hasLevelMVar then
        malformed "an action parameter leaves its native type undetermined"
      let value ← evaluateSource transaction request.program context bound term
      values := values.push value
      if let some index := route then
        unless selectedSlots.contains index do
          let some source := selected[index]?
            | malformed "the action lost its original category parameter position"
          selected := selected.set! index (← markValue kernel.marks value source)
          selectedSlots := selectedSlots.insert index
    supplied := supplied.push values
  selected ← try
      request.environment.methodParameters context transaction kernel.marks kernel.ledger.allocate
        family selected receiver
        (evaluateSource transaction request.program context bound) request.observation.sourceSnapshot
    catch error =>
      malformed s!"the original receiver's category inputs disagree: {← error.toMessageData.toString}"
  let checkedActions ← family.specializeActions levels selected
  let mut retainedInputs := #[]
  for edge in edges, action in checkedActions, values in supplied do
    let expected ← routedActionParameters edge action
    let mut inputs := #[]
    for (_, source) in expected, value in values do
      try
        request.environment.checkDeclaredInput context (← transaction.view)
          (← kernel.marks.get) source value
      catch error =>
        malformed s!"a complete action parameter disagrees: {← error.toMessageData.toString}"
      inputs := inputs.push (← markValue kernel.marks value source)
    retainedInputs := retainedInputs.push inputs
  let marked ← markValue kernel.marks receiver receiverSource
  let mut term ← family.markInputs (mkAppN
    (family.family.instantiateLevelParams family.universeParams levels) (selected.push marked)) retainedInputs
  for proof in agreements.reverse do
    let mut proof := proof.instantiateLevelParams family.universeParams levels
    for parameter in selected do proof ← mkAppM ``congrFun #[proof, parameter]
    checkWithKernel proof
    term ← withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] term
        (usedLetOnly := false) (generalizeNondepLet := false)
  return term

/-- A deferred property uses the same source proposition and complete route comparison as
ordinary source reading. Its raw receiver is independently read in the named source form;
the subsequent lowerer admits that exact retained value before selecting any registration. -/
private def Kernel.childProperty (kernel : Kernel) (context : OpenContext)
    (retained : Json → MetaM (Option ValueBinding)) (entry : PropertyEntry)
    (input : String) (arguments : Json) : MetaM Expr := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred property {entry.id.raw}: {reason}"
  let state ← semanticState
  if let some reason := propertyFormDefect state entry input then malformed reason
  let registry : RegistryState := { toSemanticState := state }
  let some form := registry.form? input
    | malformed "the explicit input form is not published"
  let some category := state.categories.find? (·.id == form.category)
    | malformed "the input form has no independently selected source category"
  let categoryFamily ← nativeCategoryFamily state category.expression fun _ => mkFreshLevelMVar
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  let bundle := mkAppN categoryFamily parameters
  let domain ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let receiver ← childOperand kernel.marks context retained domain arguments
  let receiver ← instantiateMVars receiver
  let bundle ← instantiateMVars bundle
  if receiver.hasMVar || receiver.hasLevelMVar || bundle.hasMVar || bundle.hasLevelMVar then
    malformed "the receiver leaves the complete property category undetermined"
  let (family, source) ← PropertyFamily.forReceiver
    ⟨.object, category.expression, bundle, none, none⟩ entry.id receiver
  let some sourceBoundary := (← routedSourceBoundaries family.route receiver)[0]?
    | malformed "the property lost its original source boundary"
  unless sourceBoundary.forms.contains input do
    malformed "the input form is not the original receiver's source boundary"
  return source

/-- Run one call of a deferred group through the production lowerer and executor.
Source: execution contract v2 §4 and §6; api/python-sdk.md of the leaf contract.
A reference is resolved in the call's own scope and keeps its retained value. An inline
operand is read at the declared type of its position. `$cas.project` and `$cas.apply` act on
a retained value. Any other call names a published operation with its dependent context.
Lean checks the complete call before any dispatch. -/
partial def Kernel.child (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (reservation : DispatchReservation) (scope : RequestScope)
    (call : Json) : MetaM ValueBinding := do
  let malformed : {α : Type} → String → MetaM α := fun reason =>
    throwStratum .malformed m!"deferred call {call.compress}: {reason}"
  let graph ← transaction.view
  let retained : Json → MetaM (Option ValueBinding) := fun packet => do
    match ScopedReference.parse? packet with
    | .error reason => malformed reason
    | .ok none => return none
    | .ok (some reference) =>
      let #[binding] ← scope.resolveMany reservation graph scope.wireId #[reference]
        | throwError "internal: one scoped reference resolved to several values"
      return some binding
  let operation ← match call.getObjValAs? String "op" with
    | .ok operation => pure operation
    | .error reason => malformed reason
  if applicationAddressConflict (← semanticState) operation then
    malformed "the application address also names another registered row"
  let arguments ← match call.getObjVal? "args" with
    | .ok arguments => pure arguments
    | .error reason => malformed reason
  let list : Json → String → MetaM (Array Json) := fun packet key =>
    match (packet.getObjVal? key).bind (·.getArr?) with
    | .ok values => pure values
    | .error reason => malformed reason
  withSourceScope request fun context bound => do
    let reference : Json → MetaM (ValueBinding × Expr) := fun packet => do
      let some binding ← retained packet | malformed "the acted value must be a scoped reference"
      return (binding, ← markValue kernel.marks binding (← binding.role.source.inContext context))
    -- Apply to every wire operand in order. A formal proof premise has no wire position.
    let applied : Expr → Array Json → MetaM Expr := fun function packets => do
      let mut term := function
      for packet in packets do
        let .forallE _ domain _ _ ← whnf (← inferType term)
          | malformed "more operands than the declared interface"
        if ← isProp domain then malformed "the call requires a formal premise that no leaf supplies"
        term := mkApp term (← childOperand kernel.marks context retained domain packet)
      return term
    let term ← if operation == "$cas.project" then do
        let (binding, source) ← reference ((arguments.getObjVal? "value").toOption.getD .null)
        let position ← match arguments.getObjValAs? Nat "field" with
          | .ok position => pure position
          | .error reason => malformed reason
        let some field := binding.role.fields.find? (·.wireIndex == some position)
          | malformed "the field is outside the prepared record interface"
        projectTerm source field
      else if operation == "$cas.apply" then do
        let (_, source) ← reference ((arguments.getObjVal? "value").toOption.getD .null)
        applied source (← list arguments "arguments")
      else if let some entry := (← semanticState).methods.find? (·.id.raw == operation) then do
        let input ← match call.getObjValAs? String "input" with
          | .ok input => pure input
          | .error reason => malformed reason
        kernel.childMethod evaluateSource request transaction context bound retained entry input arguments
      else if let some entry := publishedProperty? (← semanticState) operation then do
        let input ← match call.getObjValAs? String "input" with
          | .ok input => pure input
          | .error reason => malformed reason
        kernel.childProperty context retained entry input arguments
      else if (arguments.getObjValAs? String "ctor").toOption == some "apply" then do
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
        unless packet.operation == operation do
          malformed "the point packet changed its released operation"
        let head ← mkConstWithFreshMVarLevels family.declaration
        let expectedArrow ← childExplicit kernel.marks context retained head packet.parameters
        let (expectedSource, expectedTarget) ← family.endpoints expectedArrow
        let expectedFunction ← family.function expectedArrow
        let .forallE _ pointType _ _ ← whnfR (← inferType expectedFunction)
          | malformed "the named morphism has no complete point-function interface"
        let point ← childOperand kernel.marks context retained pointType packet.argument
        let some original ← sourcePointOrigin? point
          | malformed "the operand has no retained original generalized-point domain"
        let domain ← childOperand kernel.marks context retained (← inferType original.domain)
          packet.domain
        let source ← childOperand kernel.marks context retained (← inferType expectedSource)
          packet.source
        let target ← childOperand kernel.marks context retained (← inferType expectedTarget)
          packet.target
        let arrow ← if let some binding ← retained packet.arrow then do
            match family.owner with
            | .morphism row =>
              discard <| InputDescriptorView.requireMorphism graph (← kernel.codes.get) binding row.id
            | .application row =>
              discard <| InputDescriptorView.requireApplication graph (← kernel.codes.get) binding row.id
            markValue kernel.marks binding (← binding.role.source.inContext context)
          else do
            match checkServiceFields #["ctor", "args"] packet.arrow with
            | .error reason => malformed reason
            | .ok () => pure ()
            unless (packet.arrow.getObjValAs? String "ctor").toOption == some operation do
              malformed "the arrow descriptor belongs to a different released family"
            let value ← childExplicit kernel.marks context retained head (← list packet.arrow "args")
            pure (family.mark value)
        let point ← try family.withRequest expectedArrow domain source target point
          catch error => malformed s!"the complete named point inputs disagree: {← error.toMessageData.toString}"
        let function ← family.function arrow
        pure (mkApp function point)
      else if let some row := publishedPresentation? (← semanticState) operation then do
        match checkServiceFields #["ctor", "args"] arguments with
        | .error reason => malformed reason
        | .ok () => pure ()
        let packet ← match PresentationInvocation.decode arguments with
          | .ok packet => pure packet
          | .error reason => malformed reason
        let family ← PresentationFamily.forEntry row
        let (head, _) ← family.instantiate
        let iso ← childExplicit kernel.marks context retained head packet.parameters
        let (first, second) ← family.endpoints iso
        let (source, target) := if packet.inverse then (second, first) else (first, second)
        let source ← childOperand kernel.marks context retained (← inferType source) packet.source
        let target ← childOperand kernel.marks context retained (← inferType target) packet.target
        let (first, second) := if packet.inverse then (target, source) else (source, target)
        let iso ← try family.withEndpoints iso first second
          catch error => malformed s!"the comparison endpoints do not match the selected family: {← error.toMessageData.toString}"
        let function ← family.function iso packet.inverse
        let .forallE _ domain _ _ ← whnf (← inferType function)
          | malformed "the presentation has no native point function"
        let point ← childOperand kernel.marks context retained domain packet.argument
        pure (mkApp function point)
      else do
        let state ← semanticState
        let mut term ← if let some (row, port) := publishedLift? state operation then do
            -- A lift port: the lift's computation at the evidence parameters, sent to the port.
            let family ← LiftFamily.forLift row port
            let (head, _) ← family.instantiate
            pure (family.mark (← applied head (← list arguments "parameters")))
          else do
            let some family := publishedFamily? state operation
              | malformed "the operation is not a published address"
            let declaration ← family.declaration state
            let selected ← match family with
              | .method _ => malformed "a method requires its complete routed invocation"
              | .construction id => pure (sourceReference ``ConstructionEntry id.raw declaration)
              | .functor id => pure (sourceReference ``EdgeRef.functor id.raw declaration)
              | .operation id => pure (sourceReference ``OperationEntry id.raw declaration)
              | .morphism id => pure (sourceReference ``MorphismEntry id.raw declaration)
            applied (selected (← mkConstWithFreshMVarLevels declaration))
              (← list arguments "parameters")
        let role ← match arguments.getObjValAs? String "prepared_role" with
          | .ok role => pure role
          | .error reason => malformed reason
        for name in (role.splitOn "/").filter (!·.isEmpty) do
          let some info := (← getEnv).getProjectionFnInfo? name.toName
            | malformed s!"{name} is not a field of the published interface"
          term := .proj (← getConstInfoCtor info.ctorName).induct info.i term
        applied term (← list arguments "arguments")
    let term ← instantiateMVars term
    if term.hasMVar || term.hasLevelMVar then malformed "the call leaves a parameter undetermined"
    evaluateSource transaction request.program context bound term

end CasRuntime
