module

public import CasRuntime.ExecutionContext
public import CasRuntime.Encode
public import CasRuntime.DeclaredInput
public import CasRuntime.Execute
public import CasCatalogue.Admission

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

private def methodIsArrow (category : CategoryExpr) : MetaM Bool := do
  let .construct constructor #[.category _] := category | return false
  return ((← semanticState).constructors.find? (·.id == constructor)).any
    (·.semantics == `CasCatalogue.Constructors.arrow)


/-- Instantiate only the original declaration positions certified by the complete native
input-result family. Both new assembly and validation of an existing parameter use the same
sealed plan; arbitrary source execution and provider dispatch are unavailable here. -/
private def methodParameterAssembly (environment : RuntimeEnvironment) (context : OpenContext)
    (transaction : CellTransaction) (marks : IO.Ref (Array ValueBinding))
    (allocate : BaseIO (RuntimeId .occurrence))
    (declaration : Name) (produced source : Expr) (receiver : ValueBinding)
    (assembly : MethodCategoryAssembly) (evaluate : Expr → MetaM ValueBinding) :
    MetaM ValueBinding := do
  let .const _ levels := produced.getAppFn
    | throwError "a native method parameter view lost its declaration universes"
  unless produced.getAppNumArgs == assembly.arity do
    throwError "a native method parameter view changed its complete producer arity"
  let information ← checkedDeclaration declaration
  let family := assembly.family.instantiateLevelParams information.levelParams levels
  let mut arguments := #[]
  let mut values := #[]
  for position in assembly.positions, index in [:assembly.positions.size] do
    let some original := produced.getAppArgs[position]?
      | throwError "a native method parameter view lost its original argument position"
    if ← isProof original then
      arguments := arguments.push (← context.close original)
      continue
    let graph ← transaction.view
    let some slot ← environment.declaredInputAt? context graph (← marks.get)
        declaration position receiver
      | throwStratum .noImplementation
          "the native method category parameter has no original producer slot"
    let marked ← markValue marks slot.value (← slot.source.inContext context)
    arguments := arguments.push (← context.close marked)
    values := values.push (index, slot.value)
  let callable ← evaluate family
  let graph ← transaction.view
  let actual ← values.mapM fun (index, value) => do
    let .ok argument := RuntimeArgument.ofValue graph index value (← marks.get)
      | throwError "a native method parameter is outside its producing graph"
    return argument
  let mut parameters := #[]
  for (entry, value) in environment.context.entries.zip environment.values do
    if let some value := value then
      let .ok parameter := RuntimeParameter.ofValue graph entry.id value
        | throwError "a native method parameter lost its original source context"
      parameters := parameters.push parameter
  let request ← PreparedRequest.forApplication transaction.owners.identities
    (← transaction.owners.identities.fresh .program) (← allocate)
    context callable arguments actual parameters
  let some plan ← request.inputResultPlan graph
    | throwStratum .noImplementation
        "the method category parameter requires unavailable native input fields"
  let resolve := fun (input : FixedInput) => input.resolveInContext context
    (liftM (m := IO) transaction.view) marks evaluate
  if ← environment.hasRetainedSource context source then
    let value ← evaluate source
    let resolved ← plan.resolve (liftM (m := IO) transaction.view) (some resolve)
    let graph ← transaction.view
    let response ← request.admitResult graph value
    discard <| IO.ofExcept <| (resolved.admit graph response).mapError IO.userError
    return value
  let response ← Execute.run
    (fun _ _ => throwError "a certified native method parameter attempted source execution")
    (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction (some resolve)
  return response.root

/-- Reuse category parameters at the receiver producer's exact native declaration positions.
The abstract source type family determines each slot/path before actual values are inspected.
A missing required slot cannot be replaced by re-evaluating an equal closed source expression. -/
partial def RuntimeEnvironment.methodParameters (environment : RuntimeEnvironment)
    (context : OpenContext) (transaction : CellTransaction) (marks : IO.Ref (Array ValueBinding))
    (allocate : BaseIO (RuntimeId .occurrence))
    (family : RoutedMethodFamily) (arguments : Array Expr) (receiver : ValueBinding)
    (evaluate : Expr → MetaM ValueBinding) : MetaM (Array Expr) := do
  let graph ← transaction.view
  let some node := graph.find receiver.value
    | throwError "the method receiver is outside its original graph"
  let produced ← sourceDomain (← node.origin.role.source.inContext context)
  let declaration := produced.getAppFn.constName?
  let routes ← match declaration with
    | some declaration => family.receiverParameterRoutes declaration
    | none => pure (Array.replicate arguments.size MethodCategoryParameter.unavailable)
  unless routes.size == arguments.size do
    throwError "the method category parameters changed their original formal arity"
  let mut origins := routes.map fun route => (receiver, produced, declaration, route)
  if routes.any (fun route => match route with | .unavailable => true | _ => false) &&
      (← methodIsArrow family.route.source) then
    let some field := receiver.role.fields.find? (·.projection == ``CategoryTheory.Comma.hom)
      | throwError "the native method Arrow lost its original hom field"
    let retained ← IO.ofExcept <|
      (graph.projectionFrontier receiver #[field.projection]).mapError IO.userError
    if let some (stored, #[]) := retained then
      -- Read-only discovery must finish before ordinary projection preparation. The selected
      -- hom already exists; its checked projection retains the actual Arrow prefix needed
      -- when the immutable hom producer's original inputs are subsequently admitted.
      let marked ← markValue marks receiver (← receiver.role.source.inContext context)
      let hom ← evaluate (← projectTerm marked field)
      unless hom.value == stored.value &&
          stored.associationIds.toList.isPrefixOf hom.associationIds.toList do
        throwError "the method hom changed its original stored input"
      let graph ← transaction.view
      let some homNode := graph.find hom.value
        | throwError "the original method hom is outside its producing graph"
      let homSource ← sourceDomain (← homNode.origin.role.source.inContext context)
      if let some homDeclaration := homSource.getAppFn.constName? then
        let homRoutes ← family.receiverParameterRoutes homDeclaration (morphism := true)
        unless homRoutes.size == routes.size do
          throwError "the method hom changed its original category parameter arity"
        origins ← origins.mapIdxM fun index original => do
          match original with
          | (_, _, _, .unavailable) =>
            let some route := homRoutes[index]?
              | throwError "the method hom lost an original category parameter position"
            return (hom, homSource, some homDeclaration, route)
          | _ => return original
  -- A named universal apex is a projection of its selected producer, not an application
  -- of the generic pt accessor alone. Compose only that sealed native result path with
  -- its one original retained input producer; rigid declaration typing supplies the routes.
  if origins.any (fun original => match original with
      | (_, _, _, .unavailable) => true | _ => false) then
    if let some selectedSource ← environment.declaredResultSource? context graph receiver then
      if let some slot ← environment.declaredInputAt? context graph (← marks.get)
          selectedSource.declaration selectedSource.position receiver then
        let some inputNode := graph.find slot.value.value
          | throwError "the selected producer input is outside its original graph"
        let inputSource ← sourceDomain (← inputNode.origin.role.source.inContext context)
        if let some inputDeclaration := inputSource.getAppFn.constName? then
          let information ← checkedDeclaration inputDeclaration
          let arity ← forallTelescopeReducing information.type
            fun parameters _ => pure parameters.size
          unless inputSource.getAppNumArgs == arity do
            throwError "the selected producer input lost its complete declaration telescope"
          let inputRoutes ← family.receiverProjectionInputRoutes selectedSource.declaration
            selectedSource.path selectedSource.position inputDeclaration
          unless inputRoutes.size == origins.size do
            throwError "the selected producer input changed its category parameter arity"
          origins ← origins.mapIdxM fun index original => do
            match original with
            | (_, _, _, .unavailable) =>
              let some route := inputRoutes[index]?
                | throwError "the selected producer input lost a category parameter position"
              return (slot.value, inputSource, some inputDeclaration, route)
            | _ => return original
  let mut selected := #[]
  for source in arguments, index in [:arguments.size] do
    if ← isProof source then
      selected := selected.push source
      continue
    let some (producer, produced, declaration, route) := origins[index]?
      | throwError "the method lost its original category parameter position"
    match declaration, route with
    | some declaration, .input position path =>
      let graph ← transaction.view
      let slot ← environment.declaredInputAt? context graph
        (← marks.get) declaration position producer
      match slot with
      | some slot =>
        let mut value := slot.value
        let mut expression ← slot.source.inContext context
        for projection in path do
          let some field := value.role.fields.find? (·.projection == projection)
            | throwError "a method category parameter lost its native source projection"
          let marked ← markValue marks value expression
          let some information := (← getEnv).getProjectionFnInfo? field.projection
            | throwError "the method parameter lost its native projection metadata"
          expression := .proj (← getConstInfoCtor information.ctorName).induct information.i marked
          value ← evaluate expression
        let graph ← transaction.view
        let .ok actual := RuntimeArgument.ofValue graph index value (← marks.get)
          | throwError "a method category parameter is outside its producing graph"
        discard <| environment.checkArgument (← context.close source) actual
        selected := selected.push (← markValue marks value source)
      | none =>
        unless ← environment.hasRetainedSource context source do
          throwStratum .noImplementation "the method category parameter has no original producer slot"
        selected := selected.push source
    | some declaration, .assembly assembly =>
      dbg_trace s!"[method.parameters] before assembly declaration={declaration}; node={reprStr producer.value}; positions={reprStr assembly.positions}"
      let value ← methodParameterAssembly environment context transaction marks allocate
        declaration produced source producer assembly evaluate
      dbg_trace s!"[method.parameters] after assembly declaration={declaration}; node={reprStr value.value}"
      let graph ← transaction.view
      environment.checkDeclaredInput context graph (← marks.get) source value
      selected := selected.push (← markValue marks value source)
    | some declaration, .fixed fixed =>
      let .const _ levels := produced.getAppFn
        | throwError "a fixed method category parameter lost its declared universes"
      let information ← getConstInfo declaration
      let fixed := fixed.instantiateLevelParams information.levelParams levels
      unless ← isDefEq fixed source do
        throwError "the method changed an independently fixed declaration parameter"
      selected := selected.push source
    | _, _ =>
      -- An explicitly retained source binding remains its own authority. Unanchored
      -- category data require the producer mapping above; their type alone supplies no value.
      unless ← environment.hasRetainedSource context source do
        throwStratum .noImplementation "the method category parameter has no source input route"
      selected := selected.push source
  return selected

/-- Re-admit a complete positioned action-input table and install its exact references in the
already selected native actions. The caller's ordinary prepared scope owns every supplied
value; a missing entry cannot be replaced by replaying an equal source expression. -/
def RuntimeEnvironment.methodActionsWithInputs (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (marks : IO.Ref (Array ValueBinding))
    (family : RoutedMethodFamily) (actions : Array Expr) (inputs : Array (Array ValueBinding)) :
    MetaM (Array Expr) := do
  let edges := family.route.refs.push (.functor family.functor.id)
  unless actions.size == edges.size && inputs.size == edges.size do
    throwError "the method lost its complete original action-input table"
  let mut result := #[]
  for edge in edges, action in actions, values in inputs do
    let expected ← routedActionParameters edge action
    unless expected.size == values.size do
      throwError "the method lost an exact native action parameter position"
    let mut parameters := #[]
    for (_, source) in expected, value in values do
      environment.checkDeclaredInput context graph (← marks.get) source value
      parameters := parameters.push (← markValue marks value source)
    result := result.push (← routedActionWithParameters edge action parameters)
  return result

/-- One exact source position. Its forms are read before any prefix is evaluated; the full
native source family fixes the receiver type and the residual route at this offset. -/
structure RoutedMethodBoundary where
  private mk ::
  offset : Nat
  category : CategoryExpr
  forms : Array String

/-- Original source data of one applied routed callable, before realization selection. -/
structure PreparedMethodRoute where
  private mk ::
  family : RoutedMethodFamily
  actions : Array ClosedTerm
  receiverSource : ClosedTerm
  receiver : ValueBinding
  boundaries : Array RoutedMethodBoundary
  dependencies : Array ValueBinding

private def exactMethodInput (left right : ValueBinding) : Bool :=
  left.value == right.value && left.associationIds == right.associationIds

private def methodImageCategory? (state : SemanticState) (target : CategoryExpr) :
    Option NamedCategoryEntry := do
  let exact := state.categories.filter (·.expression.syntacticEq target)
  if let #[category] := exact then return category
  unless exact.isEmpty do none
  let .familyApp family _ := target | none
  let #[category] := state.categories.filter (fun category => match category.expression with
    | .familyApp other _ => family == other
    | _ => false) | none
  return category

/-- The existing image form at the independently selected target schema. Reuse:
CasCatalogue.Realize.imageForm; actual dictionaries and declaration parameters remain native. -/
private def methodImageForm (state : SemanticState) (edge : EdgeRef)
    (category : NamedCategoryEntry) : Form :=
  match category.expression with
  | .construct constructor #[.category _] =>
    if (state.constructors.find? (·.id == constructor)).any
        (·.semantics == `CasCatalogue.Constructors.subobjects) then .subobject category
    else if (state.constructors.find? (·.id == constructor)).any
        (·.semantics == `CasCatalogue.Constructors.arrow) then .arrow category
    else .edgeImage edge category
  | _ => match edge with
    | .functor id => match state.functor? id with
      | some entry => .functorImage entry category.id
      | none => .edgeImage edge category
    | _ => .edgeImage edge category

/-- Read only the native accessor spine emitted by functorObject. An inherited parent
accessor may be an ordinary declared wrapper instead of a primitive structure projection;
its exact name and single explicit parent still identify the same original source. -/
private def methodSourceParent? (projection : Name) (source : Expr) : MetaM (Option Expr) := do
  if let some selected ← SourceProjection.ofExpr? source then
    return if selected.declaration == projection then some selected.parent else none
  unless source.getAppFn.isConstOf projection do return none
  let information ← getFunInfoNArgs source.getAppFn source.getAppNumArgs
  let mut explicit := #[]
  for argument in source.getAppArgs, index in [:source.getAppNumArgs] do
    if (information.paramInfo[index]?.map (·.isExplicit)).getD false then
      explicit := explicit.push argument
  let #[parent] := explicit | return none
  return some parent

/-- The original native object action at this source boundary. The receiver's returned
payload and definitionally equal expressions never choose an incoming edge. -/
private def methodSourceAction? (receiver : Expr) : MetaM (Option Expr) := do
  let .app function _ := ← sourceDomain receiver | return none
  let some prefunctor ← methodSourceParent? ``Prefunctor.obj function | return none
  methodSourceParent? ``CategoryTheory.Functor.toPrefunctor prefunctor

/-- Read the selected incoming edge before inspecting its native action. Ordinary source views
already retain their functor/classifier reference; materialized method prefixes retain the full
edge tree. Only native aliases are traversed, never a catalogue or expression search. -/
private partial def methodSourceImageReference? (receiver : Expr) :
    MetaM (Option (EdgeRef × Name × Expr)) := do
  match ← instantiateMVars receiver with
  | .mdata data body =>
    let kind := data.getName `CasCompiler.source.kind
    let edge ← if kind == ``EdgeRef then do
        let selected ← IO.ofExcept <| ((Json.parse (data.getString `CasCompiler.source.id)).bind
          (fromJson? (α := EdgeRef))).mapError IO.userError
        pure (some selected)
      else if kind == ``EdgeRef.functor then
        pure (some (.functor ⟨data.getString `CasCompiler.source.id⟩))
      else if kind == ``EdgeRef.classifierForget then
        pure (some (.classifierForget ⟨data.getString `CasCompiler.source.id⟩))
      else pure none
    if let some edge := edge then
      return some (edge, data.getName `CasCompiler.source.declaration, body)
    methodSourceImageReference? body
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => methodSourceImageReference? value
    | none => pure none
  | .letE _ _ value body _ => methodSourceImageReference? (body.instantiate1 value)
  | value =>
    let reduced := value.headBeta
    if reduced == value then pure none else methodSourceImageReference? reduced

/-- The target of this already selected edge, read only from its exact registered rows.
Constructor images retain their whole unary edge tree and therefore their nominal target. -/
private partial def methodImageTarget (state : SemanticState) : EdgeRef → MetaM CategoryExpr
  | .functor id => do
    let some entry := state.functor? id
      | throwError "the method image lost its selected functor reference"
    return entry.target
  | .classifierForget id => do
    let some entry := state.classifier? id
      | throwError "the method image lost its selected classifier reference"
    return entry.host
  | .constructMap id inner => do
    let some entry := state.constructor? id
      | throwError "the method image lost its selected constructor reference"
    unless entry.functorialAction.isSome do
      throwError "the method image constructor has no declared action"
    return .construct id #[.category (← methodImageTarget state inner)]

/-- Validate the retained edge against its exact native object-action spine, then read only
that edge's published image form. Equal declarations under another ID are not source choices. -/
private def methodSourceImageForms (state : SemanticState) (schema : NamedCategoryEntry)
    (receiver : Expr) : MetaM (Array String) := do
  let some (edge, declaration, source) ← methodSourceImageReference? receiver | return #[]
  let some action ← methodSourceAction? source
    | throwError "the selected method image lost its native object action"
  let declared ← routedActionApplication edge action
  unless declared.getAppFn.constName? == some declaration do
    throwError "the selected method image changed its native declaration"
  let some category := methodImageCategory? state (← methodImageTarget state edge) | return #[]
  unless category.id == schema.id do return #[]
  return #[(methodImageForm state edge schema).id]

private def methodBoundaryForms (family : RoutedMethodFamily) (receiver : Expr) :
    MetaM (Array RoutedMethodBoundary) := do
  let state ← semanticState
  let registry : RegistryState := { toSemanticState := state }
  let named ← match ← sourceObjectReference? receiver with
    | none => pure none
    | some (id, declaration) =>
      let some entry := state.objects.find? (·.id == id)
        | throwError "the method receiver lost its registered source object"
      unless entry.declaration == declaration do
        throwError "the method receiver changed its selected object declaration"
      pure (some entry)
  let categories := #[family.route.source] ++ family.route.steps.map (·.target)
  unless categories.size == family.route.refs.size + 1 do
    throwError "the method source lost a complete route boundary"
  let mut boundaries := #[]
  for category in categories, offset in [:categories.size] do
    let mut forms := #[]
    if let some schema := methodImageCategory? state category then
      -- Category-wide and exact forms are peers; both are collected at this position.
      forms := forms.push schema.id.raw
      if offset == 0 then
        for image in ← methodSourceImageForms state schema receiver do
          unless forms.contains image do forms := forms.push image
      let mut object : Option ObjectEntry := none
      if let some original := named then
        let (selected, remaining) := registry.transport original
          (family.route.refs.extract 0 offset)
        if remaining.isEmpty then
          let some declared := state.categories.find? (·.id == selected.category)
            | throwError "the method source object lost its complete selected category"
          unless declared.expression.syntacticEq category do
            throwError "the object refinement changed its declared route position"
          -- CC-TRANSPORT admits the named form only at the boundary where its remaining
          -- refinement is consumed. The actual prefix is still executed after selection.
          let (effective, _) := registry.transport selected
            (family.route.refs.extract offset family.route.refs.size)
          if effective.id == selected.id then object := some selected
      if let some selectedObject := object then
        unless forms.contains selectedObject.id.raw do forms := forms.push selectedObject.id.raw
      else if 0 < offset then
        let some edge := family.route.refs[offset - 1]?
          | throwError "the method image lost its original edge position"
        let form := methodImageForm state edge schema
        unless forms.contains form.id do forms := forms.push form.id
    boundaries := boundaries.push ⟨offset, category, forms⟩
  return boundaries

/-- Validate the deferred call's explicit input form against its original receiver and nominal
source category, using the same boundary inventory that realization selection consumes. -/
def RoutedMethodFamily.admitsSourceForm (family : RoutedMethodFamily) (receiver : Expr)
    (input : String) : MetaM Bool := do
  let some source := (← methodBoundaryForms family receiver)[0]? | return false
  return source.forms.contains input

/-- Seal original captures, formal slots and the receiver before inspecting any registration.
Every supplied value is admitted by its existing prepared request. Source inspection uses native
substitution of those exact retained arguments, never catalogue equality to find a value. -/
opaque PreparedMethodRoute.prepare (kernel : Kernel) (graph : ValueGraph)
    (request original : PreparedRequest) (path : Array FieldLayout)
    (captures : Array ValueBinding) : MetaM PreparedMethodRoute := do
  let .primitive (.routedMethod family) levels := original.action
    | throwError "the method demand lost its checked routed family"
  unless path.isEmpty do
    throwError "a routed method callable acquired an unrelated selected field"
  unless captures.size == original.scope.size &&
      (captures.zip original.scope).all (fun (left, right) => exactMethodInput left right) do
    throwError "the routed method changed its original complete captures"
  dbg_trace "[routed.phase] route original input admission"
  discard <| original.admitInputs graph
  dbg_trace "[routed.phase] route application input admission"
  discard <| request.admitInputs graph
  dbg_trace "[routed.phase] route inputs admitted"
  let .apply _ arguments values := request.action
    | throwError "a routed method requires its actual original receiver"
  let #[source] := arguments
    | throwError "the routed method changed its complete receiver telescope"
  let #[some receiver] := values
    | throwError "the routed method has no actual original receiver"
  withSourceScope request fun context _ => do
    let mut parameters := #[]
    if let some application := original.application then
      let some retained := original.origin.application
        | throwError "the routed method lost its original native argument table"
      for parameter in application.arguments do
        let term ← parameter.source.source.inContext context
        let term ← match retained.arguments[parameter.sourceIndex]?.bind id with
          | some actual => markValue kernel.marks actual term
          | none =>
            unless parameter.wireIndex.isNone do
              throwError "the routed method is missing a complete category parameter"
            pure term
        parameters := parameters.push term
    let mut actions ← family.specializeActions levels parameters
    let base := original.origin.application.map (fun application =>
      (application.arguments.filterMap id).size) |>.getD 0
    if base < original.scope.size then
      let mut inputs := #[]
      let mut next := base
      let edges := family.route.refs.push (.functor family.functor.id)
      for edge in edges, action in actions do
        let count := (← routedActionParameters edge action).size
        let selected := original.scope.extract next (next + count)
        unless selected.size == count do
          throwError "the original method scope lost a supplied action parameter"
        inputs := inputs.push selected
        next := next + count
      unless next == original.scope.size do
        throwError "the original method scope has unrelated extra action inputs"
      actions ← request.environment.methodActionsWithInputs context graph kernel.marks
        family actions inputs
    let receiverTerm ← source.inContext context
    let boundaries ← methodBoundaryForms family receiverTerm
    return ⟨family, ← actions.mapM (fun action => context.close action), source, receiver, boundaries,
      original.scope ++ request.scope⟩

/-- One unique grounded realization at one exact source boundary. Only complete selection
can create this witness; materialization cannot be requested at an arbitrary route offset. -/
structure SelectedMethodBoundary where
  private mk ::
  route : PreparedMethodRoute
  boundary : RoutedMethodBoundary
  realization : Realization

/-- Collect every exact boundary before permitting any selected prefix to execute. -/
def PreparedMethodRoute.select (route : PreparedMethodRoute) (profile : RealizationProfile)
    (manifest : Manifest) : MetaM SelectedMethodBoundary := do
  let (offset, realization) ← profile.selectMethod manifest route.family.entry.id
    (route.boundaries.map (·.forms))
  let some boundary := route.boundaries[offset]?
    | throwError "the selected method boundary is outside its original route"
  unless boundary.offset == offset && offset <= route.family.route.refs.size do
    throwError "the selected method boundary changed its original source position"
  return ⟨route, boundary, realization⟩

/-- The chosen prefix has been executed in order through ordinary kernel source demands.
It retains the actual last receiver and every intermediate value in that execution. -/
structure MaterializedMethodBoundary where
  private mk ::
  selection : SelectedMethodBoundary
  receiver : ValueBinding
  receiverSource : ClosedTerm
  dependencies : Array ValueBinding

def MaterializedMethodBoundary.route (selected : MaterializedMethodBoundary) : PreparedMethodRoute :=
  selected.selection.route

def MaterializedMethodBoundary.boundary (selected : MaterializedMethodBoundary) : RoutedMethodBoundary :=
  selected.selection.boundary

/-- Selection precedes this function. No missing registration can fall back to a prepared
boundary, and no failed prefix can be skipped by sending the original source receiver. -/
def SelectedMethodBoundary.materialize (selection : SelectedMethodBoundary) (kernel : Kernel)
    (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM MaterializedMethodBoundary := do
  let route := selection.route
  let offset := selection.boundary.offset
  withSourceScope request fun context bound => do
    let mut receiver := route.receiver
    let mut source ← route.receiverSource.inContext context
    let mut dependencies := route.dependencies
    for index in [:offset] do
      let some action := route.actions[index]?
        | throwError "the method prefix lost an original native action"
      let action ← action.inContext context
      let (_, target) ← functorCategoryBundles action
      let marked ← markValue kernel.marks receiver source
      let image ← functorObject action marked target
      dbg_trace s!"[routed.prefix] {index} before evaluate"
      receiver ← evaluateSource transaction request.program context bound image
      dbg_trace s!"[routed.prefix] {index} after evaluate before source admission"
      source ← functorObject action source target
      let some edge := route.family.route.refs[index]?
        | throwError "the method prefix lost its original selected edge"
      let .const declaration _ := (← routedActionApplication edge action).getAppFn
        | throwError "the method image lost its original declaration application"
      source := sourceReference ``EdgeRef (toJson edge).compress declaration source
      -- Retain the exact selected edge, complete native application and actual returned node.
      -- Deferred children read this witness without recovering an address from a declaration.
      receiver := (← request.environment.checkResult (← transaction.view)
        (← SourceLayout.ofTerm (← context.close source)) receiver).root
      dependencies := dependencies.push receiver
    return ⟨selection, receiver, ← context.close source, dependencies.push receiver⟩

/-- Exact positioned public data of a selected method invocation. The final action is always
the registered method functor, including the zero-parameter and zero-residual cases. -/
structure PreparedMethodInvocation where
  private mk ::
  registration : Registration
  method : MethodId
  offset : Nat
  edges : Array EdgeRef
  parameters : Array (Array ValueBinding)
  receiver : ValueBinding
  dependencies : Array ValueBinding
  views : Array InputDescriptorView


/-- After unique selection, read the declaration's exact original explicit parameter slots.
The selected Arrow view reads its genuine native fields; it creates no record or hom value.
Synthetic isoInvariant Core is absent here because the callable's receiver is the original
source object. An actual source Core receiver retains its own ordinary complete data. -/
def MaterializedMethodBoundary.invocation (selected : MaterializedMethodBoundary)
    (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM PreparedMethodInvocation := do
  let .registration registration := selected.selection.realization
    | throwError "a source derivation has no provider method packet"
  let route := selected.route
  let count := route.family.route.refs.size
  let offset := selected.boundary.offset
  let edges := (route.family.route.refs.extract offset count).push (.functor route.family.functor.id)
  withSourceScope request fun context bound => do
    let mut parameters : Array (Array ValueBinding) := #[]
    let mut dependencies := selected.dependencies
    for edge in edges, index in [:edges.size] do
      let some action := route.actions[offset + index]?
        | throwError "the method request lost an original residual action"
      let action ← action.inContext context
      let declared ← routedActionParameters edge action
      let mut actual := #[]
      for (_, term) in declared do
        let value ← evaluateSource transaction request.program context bound term
        let source ← SourceLayout.ofTerm (← context.close term)
        discard <| request.environment.checkResult (← transaction.view) source value
        actual := actual.push value
        dependencies := dependencies.push value
      parameters := parameters.push actual
    unless edges.size == count - offset + 1 && parameters.size == edges.size do
      throwError "the complete method request lost its final functor or parameter positions"
    let mut preparedViews := #[]
    if ← methodIsArrow selected.boundary.category then
      let mut fields := #[]
      let parentTerm ← selected.receiverSource.inContext context
      for projection in #[``CategoryTheory.Comma.left, ``CategoryTheory.Comma.right,
          ``CategoryTheory.Comma.hom] do
        let some field := selected.receiver.role.fields.find? (·.projection == projection)
          | throwError "the selected arrow lost its complete native fields"
        let marked ← markValue kernel.marks selected.receiver parentTerm
        fields := fields.push (← evaluateSource transaction request.program context bound
          (← projectTerm marked field))
      let descriptorView ← InputDescriptorView.nativeArrow (← transaction.view) selected.receiver fields
      preparedViews := #[descriptorView]
    let roots := parameters.flatten.push selected.receiver
    let views ← InputDescriptorView.collect (← transaction.view) (← kernel.codes.get)
      roots preparedViews
    for descriptorView in views do dependencies := dependencies ++ descriptorView.dependencies
    return ⟨registration, route.family.entry.id, offset, edges, parameters, selected.receiver,
      dependencies, views⟩

/-- The actual input paths inside ConstructionInvocation, including nested constructor and
classifier action descriptors. Each occurrence retains its own source-ordered authority. -/
def PreparedMethodInvocation.roots (invocation : PreparedMethodInvocation) : Array InputPosition := Id.run do
  let mut roots := #[]
  for (edge, values) in invocation.edges.zip invocation.parameters,
      actionIndex in [:invocation.edges.size] do
    for binding in values, dataIndex in [:values.size] do
      roots := roots.push {
        path := #[.field "args", .index actionIndex] ++ routedActionParameterPath edge dataIndex,
        binding }
  return roots.push { path := #[.field "receiver"], binding := invocation.receiver }

/-- Encode with the released method envelope, retaining raw packet paths as scoped inputs.
There is no receiver-only compatibility branch. -/
def PreparedMethodInvocation.encode (invocation : PreparedMethodInvocation)
    (graph : ValueGraph) (connection : ConnectionGeneration) : Except String (EncodedInputs × Json) := do
  let encoded ← graph.encodeInputs connection invocation.roots invocation.views
  let mut descriptors := #[]
  let mut next := 0
  for (edge, values) in invocation.edges.zip invocation.parameters do
    let parameters := encoded.values.extract next (next + values.size)
    unless parameters.size == values.size do throw "the method descriptor lost a parameter occurrence"
    descriptors := descriptors.push (routedActionDescriptor edge parameters)
    next := next + values.size
  let #[receiver] := encoded.values.extract next encoded.values.size
    | throw "the method packet lost its original chosen receiver"
  let packet : ConstructionInvocation := {
    construction := invocation.method.raw, parameters := descriptors, receiver }
  return (encoded, packet.encode)

/-- Evaluate a selected owner derivation at the same exact final declaration parameters and
actually transported receiver. This uses the common checked source evaluator and completion. -/
def MaterializedMethodBoundary.derivation (selected : MaterializedMethodBoundary)
    (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (PreparedResponse request) := do
  let .derivation checked := selected.selection.realization
    | throwError "a provider method packet has no selected source derivation"
  unless selected.boundary.offset == selected.route.family.route.refs.size do
    throwError "a method derivation was selected outside its declared owner boundary"
  withSourceScope request fun context bound => do
    let some action := selected.route.actions.back?
      | throwError "the method derivation lost its complete final declaration"
    let action ← action.inContext context
    let declared ← routedActionApplication (.functor selected.route.family.functor.id) action
    let .const _ levels := declared.getAppFn
      | throwError "the method derivation lost its declaration universes"
    unless checked.entry.target == .method selected.route.family.entry.id do
      throwError "the selected method derivation belongs to another published target"
    let plan := checked.plan.instantiateLevelParams checked.universeParams levels
    let function := mkAppN plan declared.getAppArgs
    let function ← if (← whnfR (← inferType function)).isAppOf ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[function]
      else pure function
    let source ← selected.receiverSource.inContext context
    let receiver ← markValue kernel.marks selected.receiver source
    let receiver ← match selected.route.family.entry.shape with
      | .object => pure receiver
      | .isoInvariant => mkAppM ``CategoryTheory.Core.mk #[receiver]
    let (_, target) ← functorCategoryBundles function
    let value ← evaluateSource transaction request.program context bound
      (← functorObject function receiver target)
    kernelCompletion request transaction value
      (some (kernel.resolveFixedInput evaluateSource transaction request.program))

end CasRuntime
