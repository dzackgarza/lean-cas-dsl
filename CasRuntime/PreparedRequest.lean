module

public import CasCompiler.Program
import all CasCompiler.Layout
public import CasRuntime.Value
import all CasRuntime.Value
public import CasRuntime.Environment
import all CasRuntime.Environment
public import CasRuntime.InputRoute
public import CasRuntime.DeclaredInput
public import CasRuntime.RoleMap
public import CasRuntime.Literal
public import CasRuntime.Observation
public import Cslib.Foundations.Data.PFunctor.Free

@[expose] public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue

structure PreparedRequest where
  private mk ::
  program : CasRuntime.RuntimeId .program
  occurrence : CasRuntime.RuntimeId .occurrence
  action : PreparedAction
  source : SourceLayout
  scope : Array CasRuntime.ValueBinding
  outputs : Array SourceLayout
  record : Option RecordLayout
  environment : CasRuntime.RuntimeEnvironment
  origin : CasRuntime.ValueOrigin
  application : Option ApplicationLayout
  roles : RoleTelescope
  observation : ObservationDescriptor
  private actualArguments : Array CasRuntime.RuntimeArgument
  selection : Option Name := none
  selections : SourceSelectionScope ClosedTerm := {}
  selectionBinding : Option BindingId := none

  nativeParent : Option RecordLayout := none

opaque PreparedRequest.withSelection (request : PreparedRequest) (selection : Option Name) :
    PreparedRequest :=
  { request with selection, observation := request.observation.withSelection selection }

opaque PreparedRequest.withSourceSnapshot (request : PreparedRequest)
    (sourceSnapshot : Option Json) : PreparedRequest :=
  { request with observation := request.observation.withSourceSnapshot sourceSnapshot }

def requestPreparationMismatchTag : Name := `CasRuntime.requestPreparationMismatch

opaque PreparedRequest.requirePreparation (request : PreparedRequest) (scope : RoleScope) :
    MetaM Unit := do
  unless request.roles.scope == scope do
    throwError (MessageData.tagged requestPreparationMismatchTag
      m!"the invocation belongs to a different original request preparation")

def PreparedRequest.reference (request : PreparedRequest) : Option ComputationRef :=
  match request.action with
  | .primitive boundary _ => boundary.reference
  | .project .. | .apply .. => none

def PreparedRequest.universeArguments (request : PreparedRequest) : Option (List Level) :=
  match request.action with
  | .primitive _ arguments => some arguments
  | .project .. | .apply .. => none

def PreparedRequest.projectionPath (request : PreparedRequest) : Except String (Array Name) := do
  let .project operand field := request.action
    | throw "the prepared action is not a native projection"
  unless operand.nativeRole.address.toList.isPrefixOf field.address.toList do
    throw "the prepared field is outside its retained operand"
  let path := field.address.extract operand.nativeRole.address.size field.address.size
  unless !path.isEmpty && path.back? == some field.projection &&
      request.origin.accessPath == path do
    throw "the prepared projection lost its exact native field path"
  let some parent := request.origin.access
    | throw "the prepared projection lost its retained operand"
  unless parent.value == operand.value && parent.associationIds == operand.associationIds do
    throw "the prepared projection changed its retained operand"
  return path

opaque PreparedRequest.originFor (request : PreparedRequest) (source : SourceLayout)
    (graph : Option ValueGraph := none) :
    MetaM CasRuntime.ValueOrigin := do
  let environment ← request.environment.withGraph graph
  let application ← request.origin.application.mapM (·.forSource request.source source)
  let accessPath ← if request.origin.access.isSome then
      pure (request.origin.accessPath ++ (← request.source.projectionPathTo source))
    else pure #[]
  let mut fieldPrefix := request.origin.fieldPrefix
  if fieldPrefix.isSome then
    for projection in ← request.source.projectionPathTo source do
      fieldPrefix ← fieldPrefix.mapM (·.descend projection)
  let origin ← environment.origin request.program request.occurrence source
    (fieldPrefix := fieldPrefix) (access := request.origin.access) (accessPath := accessPath)
  return { origin with application }

private def prepareOrigin (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (environment : CasRuntime.RuntimeEnvironment)
    (application : Option ApplicationLayout) (arguments : Array (Option CasRuntime.ValueBinding)) :
    MetaM CasRuntime.ValueOrigin := do
  let origin ← environment.origin program occurrence source
  if let some layout := application then
    let callable := match action with | .apply callable .. => some callable | _ => none
    let .ok application :=
        CasRuntime.ApplicationOrigin.ofArguments layout environment.values arguments callable
      | throwError "the prepared application has an incompatible actual argument table"
    return { origin with application := some application }
  unless arguments.isEmpty do
    throwError "actual arguments require a prepared native application telescope"
  return origin

private def prepareInputInterface (environment : RuntimeEnvironment) (origin : ValueOrigin) :
    MetaM ValueOrigin := do
  let some graph := environment.sourceGraph | return origin
  let some application := origin.application | return origin
  let input ← try application.fixedInputAt graph
    catch failure =>
      if failure.toMessageData.hasTag (· == `CasRuntime.FixedInput.missingInput) then pure none
      else throw failure
  let some input := input | return origin
  let some selected ← input.storedValue? graph | return origin
  let native := selected.nativeInterface
  unless native.role.kind == .function || native.role.kind == .record do return origin
  let original : AdmittedInputInterface := {
    program := origin.program
    occurrence := origin.occurrence
    role := origin.role
    parameters := origin.parameters
    application
    selected
    native
  }
  return { origin with inputInterface := some original }

private def prepareRequest (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (action : PreparedAction)
    (source : SourceLayout) (context : OpenContext) (scope : Array CasRuntime.ValueBinding)
    (environment : CasRuntime.RuntimeEnvironment) (application : Option ApplicationLayout)
    (origin : CasRuntime.ValueOrigin)
    (actualArguments : Array CasRuntime.RuntimeArgument := #[]) :
    MetaM PreparedRequest := do
  let event := Json.mkObj [
    ("program", Observation.identityJson program),
    ("occurrence", Observation.identityJson occurrence)]
  CasTools.Diagnostics.emit "request.prepare.source.started" event
  let specified ← source.inContext context
  unless specified.kind == origin.role.kind && specified.address == origin.role.address &&
      specified.source.expression.equal origin.role.source.expression do
    throwError "request preparation changed its original native source role"
  CasTools.Diagnostics.emit "request.prepare.source.completed" event
  let source := origin.role
  let application := application.map fun layout => { layout with result := source }

  let origin := { origin with application := origin.application.map fun application =>
    if application.path.isEmpty then
      { application with layout := { application.layout with result := source } }
    else application }
  CasTools.Diagnostics.emit "request.prepare.inputInterface.started" event
  let origin ← match action with
    | .project .. => pure origin
    | .primitive .. | .apply .. => prepareInputInterface environment origin
  CasTools.Diagnostics.emit "request.prepare.inputInterface.completed" event
  unless identities.worker == program.worker && program.worker == occurrence.worker do
    throwError "request preparation mixed worker identities"
  CasTools.Diagnostics.emit "request.prepare.scope.started" event
  for binding in scope do
    unless binding.value.worker == program.worker do
      throwError "a request scope value belongs to a different worker"
    discard <| binding.role.source.inContext context
  CasTools.Diagnostics.emit "request.prepare.scope.completed" event
  if source.kind == .proof then
    throwError "a source proof has no computational response positions"
  let traced := (source.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traced then CasTools.Diagnostics.message m!"[inclusion.stage] request {repr occurrence}: before output layouts"
  CasTools.Diagnostics.emit "request.prepare.outputs.started" event
  let mut outputs : Array SourceLayout := #[]
  let record ← if source.kind == .record then
      pure (some (← RecordLayout.ofSource source))
    else pure none
  if let some record := record then
    for prepared in record.fields do
      if prepared.field.wireIndex.isSome then outputs := outputs.push prepared.layout
  else outputs := #[source]
  CasTools.Diagnostics.emit "request.prepare.outputs.completed" event
  if traced then CasTools.Diagnostics.message m!"[inclusion.stage] request {repr occurrence}: before role telescope"
  CasTools.Diagnostics.emit "request.prepare.roles.started" event
  let roles ← RoleTelescope.ofRequest identities program occurrence context application source
    (scope.map (·.role))
  CasTools.Diagnostics.emit "request.prepare.roles.completed" event
  if traced then CasTools.Diagnostics.message m!"[inclusion.stage] request {repr occurrence}: prepared"

  CasTools.Diagnostics.emit "request.prepare.observation.started" event
  let observation ← ObservationDescriptor.prepare program occurrence action source scope outputs
    record environment origin application roles actualArguments
  CasTools.Diagnostics.emit "request.prepare.observation.completed" event
  CasTools.Diagnostics.emit "request.prepared" observation.toJson
  CasTools.Diagnostics.emit "request.prepare.logged" event
  return ⟨program, occurrence, action, source, scope, outputs, record, environment, origin,
    application, roles, observation, actualArguments, none, environment.selections,
    source.selectionBinding, none⟩

private def PreparedRequest.inputValues (request : PreparedRequest) :
    Array (Option CasRuntime.ValueBinding) :=
  match request.action with
    | .apply _ _ values => values
    | .primitive .. => match request.origin.application with
      | none => #[]
      | some application => application.arguments
    | .project .. => #[]

opaque PreparedRequest.admitInputs (request : PreparedRequest) (graph : CasRuntime.ValueGraph) :
    MetaM CasRuntime.InputRoleMap := do
  CasRuntime.InputRoleMap.admit request.roles request.environment graph request.inputValues request.scope
    request.actualArguments

opaque PreparedRequest.admitInputResultInputs (request : PreparedRequest)
    (graph : CasRuntime.ValueGraph) : MetaM CasRuntime.InputRoleMap := do
  let arguments := request.inputValues
  if request.roles.arguments.size == arguments.size &&
      (request.roles.arguments.zip arguments).all (fun (role, value) =>
        role.wireIndex.isNone || value.isSome) then
    return ← request.admitInputs graph
  let some application := request.application
    | throwError "a fixed input result has no complete formal application"
  let contextInputs := (request.environment.context.entries.zip request.environment.values).filterMap
    fun (entry, value) => if value.isSome then some entry.id else none
  let some coverage ← request.roles.inputResultCoverage application contextInputs
    | throwError "missing computational inputs require complete native source coverage"
  CasRuntime.InputRoleMap.admitInputResult request.roles coverage request.environment graph
    arguments request.scope request.actualArguments

private def prepareArguments (environment : CasRuntime.RuntimeEnvironment)
    (arguments : Array ClosedTerm) (actual : Array CasRuntime.RuntimeArgument) :
    MetaM (Array (Option CasRuntime.ValueBinding)) := do
  let mut values := Array.replicate arguments.size none
  for argument in actual do
    let some specified := arguments[argument.index]?
      | throwError "a runtime argument is outside the complete callable argument list"
    if (values[argument.index]?.bind id).isSome then
      throwError "a callable source argument has duplicate runtime bindings"
    let value ← environment.checkArgument specified argument
    values := values.set! argument.index (some value)
  return values

private def withPreparedInputs (identities : IdentitySupply) (context : OpenContext)
    (environment : RuntimeEnvironment) (application : ApplicationLayout)
    (values : Array (Option ValueBinding)) (actual : Array RuntimeArgument)
    (parameters : Array RuntimeParameter)
    (action : OpenContext → SourceSelectionScope Expr → Array ClosedTerm →
      Array RuntimeParameter → MetaM α) : MetaM α := do
  unless application.arguments.size == values.size do
    throwError "typed input preparation lost its complete original argument table"
  let rec visit (remaining : List (Nat × ArgumentLayout)) (context : OpenContext)
      (bound : Std.HashMap BindingId ValueBinding) (parameters : Array RuntimeParameter)
      (selections : SourceSelectionScope Expr) (expressions : Array Expr) : MetaM α := do
    match remaining with
    | [] => do
      action context selections (← expressions.mapM context.close) parameters
    | (index, argument) :: remaining => do
      unless argument.sourceIndex == index do
        throwError "typed input preparation changed the original argument order"
      let source ← argument.source.source.inContext context
      let family ← argument.typeFamily.inContext context
      let type := (mkAppN family expressions).headBeta
      check type
      let value := values[index]!
      let next := fun context bound parameters selections expression =>
        visit remaining context bound parameters selections (expressions.push expression)
      if let some original := context.bindings.find? (·.expression == source) then
        let retains := match value, bound[original.id]? with
          | some value, some retained => retainsReference retained value
          | none, none => true
          | _, _ => false
        if retains && (← withoutModifyingState (isDefEq (← inferType source) type)) then
          return ← next context bound parameters selections source
      let allocated ← identities.fresh .sourceBinding
      let id : BindingId := ⟨allocated.worker, allocated.serial⟩
      let role ← if value.isSome then pure BindingRole.result else do
        if ← isProp type then pure BindingRole.hypothesis else pure BindingRole.parameter
      context.withLocalBinding id role (.num `input index) type
        (fun context binding => do
          let mut bound := bound
          let mut parameters := parameters
          if let some value := value then
            let #[supplied] := actual.filter (·.index == index)
              | throwError "typed input preparation lost its unique original runtime argument"
            unless retainsReference supplied.value value do
              throwError "typed input preparation changed its admitted original operand"
            bound := bound.insert id value
            parameters := parameters.push (supplied.toParameter id)
          let selections ← selections.alias context source binding.expression
          next context bound parameters selections binding.expression)
        (originalSource := some source) (binderInfo := argument.binderInfo)
  visit (application.arguments.mapIdx (fun index argument => (index, argument))).toList
    context environment.bound parameters (← environment.selections.inContext context) #[]

private def withPreparationContext (context : OpenContext) (parameters : Array RuntimeParameter)
    (graph : Option ValueGraph) (references : Array ValueBinding)
    (action : OpenContext → Array RuntimeParameter → MetaM α) : MetaM α := do
  let some graph := graph | return ← action context parameters
  let mut bound : Std.HashMap BindingId ValueBinding := {}
  for parameter in parameters do
    if bound.contains parameter.source then
      throwError "a source binder has duplicate runtime associations"
    unless context.bindings.any (·.id == parameter.source) do
      throwError "a runtime association names a source binder outside the complete telescope"
    bound := bound.insert parameter.source parameter.value
  let rec visit (remaining : List ValueBinding) (context : OpenContext)
      (bound : Std.HashMap BindingId ValueBinding) : MetaM α := do
    match remaining with
    | [] =>
      let mut parameters := #[]
      for entry in context.telescope.entries do
        if let some value := bound[entry.id]? then
          parameters := parameters.push (← IO.ofExcept <|
            (RuntimeParameter.ofValue graph entry.id value).mapError IO.userError)
      action context parameters
    | value :: rest =>
      withBindingContext graph context bound value fun context bound =>
        visit rest context bound
  visit (parameters.map (·.value) ++ references).toList context bound

opaque PreparedRequest.withInputBindings (request : PreparedRequest) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (count : Nat)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → Array Expr →
      Array (Option ValueBinding) → MetaM α) : MetaM α := do
  let formal := request.application.map (·.arguments) |>.getD #[]
  let values := request.origin.application.map (·.arguments) |>.getD #[]
  unless formal.size == values.size && count ≤ formal.size do
    throwError "the prepared input scope lost its complete original argument telescope"
  let mut actual := #[]
  for argument in formal.extract 0 count, index in [:count] do
    unless argument.sourceIndex == index do
      throwError "the prepared input scope changed its original formal argument order"
    let source ← argument.source.source.inContext context
    let family ← argument.typeFamily.inContext context
    let type := (mkAppN family actual).headBeta
    unless ← isDefEq (← inferType source) type do
      throwError "a prepared input binder changed its original dependent domain"
    if let some value := values[index]! then
      let some binding := context.bindings.find? (·.expression == source)
        | throwError "a retained prepared input has no original typed occurrence binder"
      let some retained := bound[binding.id]?
        | throwError "a retained prepared input lost its original runtime occurrence"
      unless retainsReference retained value do
        throwError "a retained prepared input changed its original runtime occurrence"
    actual := actual.push source
  action context bound actual (values.extract 0 count)

opaque PreparedRequest.forBoundary (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (boundary : ProgramBoundary)
    (universeArguments : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm)
    (actual : Array CasRuntime.RuntimeArgument)
    (scope : Array CasRuntime.ValueBinding) (parameters : Array CasRuntime.RuntimeParameter)
    (graph : Option CasRuntime.ValueGraph := none)
    (validatedEnvironment : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {})
    (selectionBinding : Option BindingId := none) : MetaM PreparedRequest := do
  withPreparationContext context parameters graph (actual.map (·.value) ++ scope) fun context parameters => do
    let mut selections := selections
    for value in actual.map (·.value) ++ scope do
      selections ← SourceSelectionScope.merge selections (← value.role.selections.inContext context)
      if value.admittedInterface?.isSome then
        selections ← SourceSelectionScope.merge selections (← value.nativeRole.selections.inContext context)
    if let .property family := boundary then
      unless arguments.size == family.parameterCount + 1 do
        throwError "a property observation requires its complete original source application"
    if let .application family := boundary then
      unless family.owner matches .application _ do
        throwError "an object application boundary requires its exact registered object owner"
    if let .point family := boundary then
      unless arguments.size == family.parameterCount + (if family.invocation then 2 else 0) do
        throwError "a categorical point requires its complete original native input telescope"
    if let .objectAction family := boundary then
      unless arguments.size == family.parameterCount + 1 do
        throwError "an object action requires all original declaration parameters and its receiver"
    if let .limit family owner := boundary then
      unless arguments.size == family.parameterCount do
        throwError "a raw cone requires its complete original declaration telescope"
      discard <| family.ownerAt (← owner.mapM (·.inContext context)) (← arguments.mapM (·.inContext context))
    if let .limitUniversal family owner := boundary then
      unless arguments.size == family.parameterCount && scope.size == 1 do
        throwError "a universal request requires its original parameters and one exact cone capture"
      discard <| family.presentation.ownerAt (← owner.mapM (·.inContext context))
        (← arguments.mapM (·.inContext context))
    unless universeArguments.length == boundary.universeParams.length do
      throwError "request universe arguments do not match the checked source family"
    let universeArguments ← universeArguments.mapM instantiateLevelMVars
    if universeArguments.any (·.hasMVar) then
      throwError "request preparation requires resolved universe arguments"
    let nativeFamily ← boundary.familyIn universeArguments context
    let traced := (nativeFamily.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] primitive {repr occurrence}: before family layout"
    let prepareLayout := fun (context : OpenContext) (selections : SourceSelectionScope Expr)
        (arguments : Array ClosedTerm) => do
      let nativeFamily ← boundary.familyIn universeArguments context
      let (source, application, nativeParent) ← match boundary with
        | .registered family => do
          let (source, application) ← family.applyIn universeArguments context arguments
          pure (source, some application, (none : Option RecordLayout))
        | .limitUniversal family _ => do
          let original ← withLCtx {} #[] do
            let empty ← ContextTelescope.capture #[]
            empty.close (family.presentation.presentationFamily.instantiateLevelParams
              family.universeParams universeArguments)
          let (parent, application) ← ApplicationLayout.ofSource
            (← SourceLayout.ofTerm original) context arguments
          let parent ← RecordLayout.ofSource parent
          let application ← application.forProjection family.projection
          pure (application.result, some application, some parent)
        | .creation family => do
          unless arguments.size == 2 do
            throwError "the fixed creation requires both original target data inputs"
          let (source, application) ← ApplicationLayout.ofSource
            (← SourceLayout.ofTerm family.requestFamily) context arguments
          pure (source, some application, (none : Option RecordLayout))
        | _ => do
          let family ← withLCtx {} #[] do
            let empty ← ContextTelescope.capture #[]
            empty.close nativeFamily
          let layout ← SourceLayout.ofTerm family
          if arguments.isEmpty then
            pure (← layout.inContext context, (none : Option ApplicationLayout),
              (none : Option RecordLayout))
          else do
            let (source, application) ← ApplicationLayout.ofSource layout context arguments
            pure (source, some application, (none : Option RecordLayout))
      let closedSelections ← selections.close context
      let source ← source.withSelections closedSelections
      let application ← application.mapM (·.withSelections context closedSelections)
      let nativeParent ← nativeParent.mapM fun parent => do
        RecordLayout.ofSource (← parent.source.withSelections closedSelections)
      return (source, application, nativeParent)
    let (source, application, nativeParent) ← prepareLayout context selections arguments
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] primitive {repr occurrence}: before environment"
    let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters graph
      validatedEnvironment selections
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] primitive {repr occurrence}: before argument admission"
    let values ← prepareArguments environment arguments actual
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] primitive {repr occurrence}: arguments admitted"
    let finish := fun (context : OpenContext) (source : SourceLayout)
        (application : Option ApplicationLayout) (nativeParent : Option RecordLayout)
        (environment : RuntimeEnvironment) (values : Array (Option ValueBinding)) => do
      let source := { source with selectionBinding }
      let action := PreparedAction.primitive boundary universeArguments
      let origin ← prepareOrigin program occurrence action source environment application values
      let request ← prepareRequest identities program occurrence action source context
        (values.filterMap id ++ scope) environment application origin actual
      return { request with nativeParent }
    match application with
    | none => finish context source application nativeParent environment values
    | some original =>
      withPreparedInputs identities context environment original values actual parameters fun
          context selections arguments parameters => do
        let (source, application, nativeParent) ← prepareLayout context selections arguments
        let environment ← RuntimeEnvironment.capture program.worker context parameters graph
          (selections := selections)
        let values ← prepareArguments environment arguments actual
        finish context source application nativeParent environment values

opaque PreparedRequest.universalCone (request : PreparedRequest) : MetaM ValueBinding := do
  let .primitive (.limitUniversal _ _) _ := request.action
    | throwError "the selected native predecessor requires its universal family"
  let arguments := (request.origin.application.map (·.arguments.filterMap id)).getD #[]
  let count := arguments.size
  let #[cone] := request.scope.extract count request.scope.size
    | throwError "the universal family lost its original cone capture"
  return cone

private def checkPresentationInputs (request : PreparedRequest) (graph : ValueGraph)
    (source target : ValueBinding) : MetaM Unit := do
  let .primitive (.presentation family) _ := request.action
    | throwError "declared endpoint checking requires its original presentation family"
  request.environment.context.withOpenContext fun context => do
    let applied ← request.source.source.inContext context
    context.withOriginalSources #[applied, ← source.role.source.inContext context,
        ← target.role.source.inContext context] fun originals => do
      discard <| family.withEndpoints originals[0]! originals[1]! originals[2]!
    let count := request.application.map (·.arguments.size) |>.getD 0
    request.withInputBindings context request.environment.bound count fun context bound arguments _ => do
      let (expectedSource, expectedTarget) ← family.endpoints (mkAppN applied.getAppFn arguments)
      let environment ← RuntimeEnvironment.captureBound request.program.worker context bound graph
        (selections := ← request.environment.selections.inContext context)
      let checkEndpoint := fun (expected : SourceSelection Expr) (value : ValueBinding) => do
        let some expectedReference := expected.reference
          | throwError "the presentation endpoint lost its complete original source row"
        let some retained ← value.role.selected? context
          | throwError "the presentation endpoint lost its retained typed source selection"
        let some actualReference := retained.reference
          | throwError "the presentation endpoint lost its original registered source row"
        unless expectedReference.exactlyMatches actualReference do
          throwError "the presentation endpoint changed its complete original source row"
        environment.checkDeclaredInput context graph expected.value value
      checkEndpoint expectedSource source
      checkEndpoint expectedTarget target

opaque PreparedRequest.forPresentation (identities : IdentitySupply)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (family : PresentationFamily) (universes : List Level) (context : OpenContext)
    (arguments : Array ClosedTerm) (actual : Array RuntimeArgument)
    (endpoints : Array ClosedTerm) (endpointValues : Array RuntimeArgument)
    (parameters : Array RuntimeParameter) (graph : ValueGraph)
    (selections : SourceSelectionScope Expr := {})
    (selectionBinding : Option BindingId := none) : MetaM PreparedRequest := do
  let #[_, _] := endpoints
    | throwError "the presentation request requires both complete original endpoints"
  let environment ← RuntimeEnvironment.capture program.worker context parameters (some graph)
    (selections := selections)
  let values ← prepareArguments environment endpoints endpointValues
  let #[some source, some target] := values
    | throwError "the presentation request is missing an actual endpoint value"
  let request ← PreparedRequest.forBoundary identities program occurrence (.presentation family)
    universes context arguments actual #[source, target] parameters (some graph)
    (selections := selections) (selectionBinding := selectionBinding)
  discard <| request.admitInputs graph
  checkPresentationInputs request graph source target
  return request

opaque PreparedRequest.presentationEndpoints (request : PreparedRequest)
    (graph : ValueGraph) : MetaM (ValueBinding × ValueBinding) := do
  let .primitive (.presentation family) _ := request.action
    | throwError "endpoint preparation requires a published presentation boundary"
  let count := match request.origin.application with
    | none => 0
    | some application => (application.arguments.filterMap id).size
  let #[source, target] := request.scope.extract count request.scope.size
    | throwError "the presentation request lost its exact endpoint capture positions"
  discard <| request.environment.checkResult graph source.role source
  discard <| request.environment.checkResult graph target.role target
  checkPresentationInputs request graph source target
  return (source, target)

private def prepareProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (path : Array Name)
    (parameters : Array CasRuntime.RuntimeParameter)
    (validatedEnvironment : Option RuntimeEnvironment)
    (selections : SourceSelectionScope Expr := {})
    (selectionBinding : Option BindingId := none) : MetaM PreparedRequest := do
  withPreparationContext context parameters (some graph) #[operand] fun context parameters => do
    let mut selections ← SourceSelectionScope.merge selections (← operand.role.selections.inContext context)
    if operand.admittedInterface?.isSome then
      selections ← SourceSelectionScope.merge selections (← operand.nativeRole.selections.inContext context)
    let traced := (operand.role.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] projection {repr occurrence} {repr path}: before layout"
    let mut layout := operand.nativeRole
    let mut selected : Option FieldLayout := none
    for projection in path do
      let some field := layout.fields.find? (·.projection == projection)
        | throwError "the projection is outside the retained source layout"
      unless field.wireIndex.isSome do
        throwError "a source proof field has no computational projection"
      selected := some field
      layout ← field.toLayout
    let some field := selected | throwError "a projection requires a native field path"
    let source ← layout.inContext context
    let source ← source.withSelections (← selections.close context)
    let source := { source with selectionBinding }
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] projection {repr occurrence}: before environment"
    let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters
      (some graph) validatedEnvironment selections
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] projection {repr occurrence}: before operand admission"
    discard <| environment.checkOperand graph operand.role operand
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] projection {repr occurrence}: operand admitted"
    let .ok original := graph.applicationOrigin operand.nativeInterface
      | throwError "the projected operand is outside the visible graph"
    let mut application := original
    for projection in path do
      application ← application.mapM (·.forProjection projection)
    let action := PreparedAction.project operand field
    let fieldPrefix ← environment.projectionFieldPrefix graph operand source
    let origin ← environment.origin program occurrence source
      (fieldPrefix := fieldPrefix) (access := some operand) (accessPath := path)
    let origin := { origin with application }
    prepareRequest identities program occurrence action source context
      #[operand] environment none origin

opaque PreparedRequest.forProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (index : Nat)
    (parameters : Array CasRuntime.RuntimeParameter)
    (validatedEnvironment : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {})
    (selectionBinding : Option BindingId := none) : MetaM PreparedRequest := do
  let some field := operand.nativeRole.fields[index]?
    | throwError "the projection is outside the retained source layout"
  prepareProjection identities program occurrence context graph operand
    #[field.projection] parameters validatedEnvironment selections selectionBinding

opaque PreparedRequest.forStoredProjection (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (graph : CasRuntime.ValueGraph)
    (operand : CasRuntime.ValueBinding) (path : Array Name)
    (parameters : Array CasRuntime.RuntimeParameter)
    (validatedEnvironment : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {})
    (selectionBinding : Option BindingId := none) : MetaM PreparedRequest := do
  let selected ← IO.ofExcept <| (graph.projectionFrontier operand path).mapError IO.userError
  let some (_, remaining) := selected
    | throwError "the native projection path has no stored field interface"
  unless remaining.isEmpty do
    throwError "a composed projection cannot pass a lazy field boundary"
  prepareProjection identities program occurrence context graph operand path parameters
    validatedEnvironment selections selectionBinding

opaque PreparedRequest.forApplication (identities : CasRuntime.IdentitySupply)
    (program : CasRuntime.RuntimeId .program)
    (occurrence : CasRuntime.RuntimeId .occurrence) (context : OpenContext)
    (callable : CasRuntime.ValueBinding) (arguments : Array ClosedTerm)
    (actual : Array CasRuntime.RuntimeArgument)
    (parameters : Array CasRuntime.RuntimeParameter)
    (graph : Option CasRuntime.ValueGraph := none)
    (validatedEnvironment : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {})
    (selectionBinding : Option BindingId := none) : MetaM PreparedRequest := do
  withPreparationContext context parameters graph (#[callable] ++ actual.map (·.value)) fun context parameters => do
    let mut selections := selections
    for value in #[callable] ++ actual.map (·.value) do
      selections ← SourceSelectionScope.merge selections (← value.role.selections.inContext context)
      if value.admittedInterface?.isSome then
        selections ← SourceSelectionScope.merge selections (← value.nativeRole.selections.inContext context)
    unless callable.nativeRole.kind == .function do
      throwError "the retained value has no prepared callable interface"
    if arguments.isEmpty then throwError "callable application requires a source argument"
    let traced := (callable.role.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] application {repr occurrence}: before layout"
    let (source, application) ← ApplicationLayout.ofSource callable.nativeRole context arguments
      (selections := ← selections.close context)
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] application {repr occurrence}: before environment"
    let environment ← CasRuntime.RuntimeEnvironment.capture program.worker context parameters graph
      validatedEnvironment selections
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] application {repr occurrence}: before argument admission"
    let values ← prepareArguments environment arguments actual
    if traced then CasTools.Diagnostics.message m!"[inclusion.stage] application {repr occurrence}: arguments admitted"
    withPreparedInputs identities context environment application values actual parameters fun
        context selections arguments parameters => do
      let (source, application) ← ApplicationLayout.ofSource callable.nativeRole context arguments
        (selections := ← selections.close context)
      let environment ← RuntimeEnvironment.capture program.worker context parameters graph
          (selections := selections)
      let values ← prepareArguments environment arguments actual
      let source := { source with selectionBinding }
      let action := PreparedAction.apply callable arguments values
      let origin ← prepareOrigin program occurrence action source environment (some application) values
      prepareRequest identities program occurrence action source context
        (#[callable] ++ values.filterMap id) environment (some application) origin actual

structure PreparedResponse (request : PreparedRequest) where
  private mk ::
  roles : CasRuntime.ResultRoleMap

def PreparedResponse.root (response : PreparedResponse request) : CasRuntime.ValueBinding :=
  response.roles.root

opaque PreparedRequest.resultFieldPrefix (request : PreparedRequest) (graph : CasRuntime.ValueGraph)
    (value : CasRuntime.ValueBinding) : MetaM (Option NativeFieldPrefix) := do

  match request.action with
    | .primitive (.limitUniversal family _) _ => do
      let cone ← request.universalCone
      let some node := graph.find value.value
        | throwError "the universal result lost its original producing value"
      let some nativePrefix := node.origin.fieldPrefix
        | throwError "the universal result lost its original native field prefix"
      discard <| IO.ofExcept <|
        (nativePrefix.requireOrigin request.program request.occurrence request.source).mapError
          IO.userError
      let #[frame] := nativePrefix.frames
        | throwError "the universal result changed its original whole-presentation frame"
      let some parent := request.nativeParent
        | throwError "the universal request lost its original whole-presentation layout"
      let original := frame.association.layout.source.source
      let expected := parent.source.source
      unless original.context.exactlyMatches expected.context &&
          original.expression.equal expected.expression && original.type.equal expected.type &&
          original.universeParams == expected.universeParams &&
          original.nativeDeclarations.exactlyMatches expected.nativeDeclarations &&
          frame.field.projection == family.projection do
        throwError "the universal result changed its complete original native presentation"
      let #[preceding] := parent.fields.filter
          (·.field.projection == family.presentation.coneProjection)
        | throwError "the universal request lost its original preceding cone position"
      let some actual := frame.preceding[preceding.field.sourceIndex]?.bind id
        | throwError "the universal result lost its actual preceding cone"
      unless actual.value == cone.value &&
          cone.associationIds.toList.isPrefixOf actual.associationIds.toList do
        throwError "the universal result belongs to another actual cone occurrence"
      discard <| IO.ofExcept <| (graph.requiredOwners #[cone, actual]).mapError IO.userError
      pure (some nativePrefix)
    | _ => pure none

opaque PreparedRequest.admitResult (request : PreparedRequest) (graph : CasRuntime.ValueGraph)
    (value : CasRuntime.ValueBinding) : MetaM (PreparedResponse request) := do
  if let .primitive (.property _) _ := request.action then
    let malformed : {α : Type} → String → MetaM α := fun reason =>
      throwStratum .malformed m!"property observation: {reason}"
    let packet ← match graph.packet? value with
      | .ok (some packet) => pure packet
      | .ok none => malformed "the answer has no complete Option Bool packet"
      | .error reason => malformed reason
    match PropertyObservation.decode packet with
    | .ok _ => pure ()
    | .error reason => malformed reason
  let projectionContext := match request.action with
    | .project operand field => some (operand, field)
    | .primitive .. | .apply .. => none
  let fieldPrefix ← request.resultFieldPrefix graph value
  return ⟨← CasRuntime.ResultRoleMap.admit request.roles request.environment graph value
    projectionContext fieldPrefix⟩

def OperationalSignature : PFunctor.{0, 0} :=
  ⟨PreparedRequest, PreparedResponse⟩

abbrev OperationalProgram := OperationalSignature.FreeM

end CasRuntime
