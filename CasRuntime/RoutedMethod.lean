module

public import CasRuntime.ExecutionContext
public import CasRuntime.Encode
public import CasRuntime.DeclaredInput
public import CasRuntime.Execute
import all CasRuntime.Value
public import CasCatalogue.Admission

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

private def methodIsArrow (category : CategoryExpr)
    (view : Option ConstructorEntry) : MetaM Bool := do
  match category, view with
  | .construct constructor arguments, some original => do
    unless original.id == constructor && original.signature.size == arguments.size do
      throwError "the source receiver changed its original complete category constructor"
    unless original.semantics == `CasCatalogue.Constructors.arrow do return false
    let #[.category] := original.signature
      | throwError "the selected Arrow lost its original unary category interface"
    return true
  | .construct .., none =>
    throwError "the constructed source receiver lost its original complete constructor"
  | _, some _ =>
    throwError "the ordinary source receiver gained another category constructor"
  | _, none => return false





private def methodParameterAssembly (environment : RuntimeEnvironment) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (transaction : CellTransaction)
    (allocate : BaseIO (RuntimeId .occurrence))
    (declaration : Name) (produced source : Expr) (receiver : ValueBinding)
    (assembly : MethodCategoryAssembly)
    (evaluate : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Expr → MetaM ValueBinding)
    (sourceSnapshot : Option Json) : MetaM ValueBinding := do
  let .const _ levels := produced.getAppFn
    | throwError "a native method parameter view lost its declaration universes"
  unless produced.getAppNumArgs == assembly.arity do
    throwError "a native method parameter view changed its complete producer arity"
  let information ← checkedDeclaration declaration
  let family := assembly.family.instantiateLevelParams information.levelParams levels
  let finish := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
      (arguments : Array ClosedTerm) (values : Array (Nat × ValueBinding)) => do
    let environment ← RuntimeEnvironment.captureBound environment.worker context bound
      (← transaction.view) (some environment) (← environment.selections.inContext context)
    let selections ← environment.selections.inContext context
    let callable ← evaluate context bound selections family
    let graph ← transaction.view
    let environment ← RuntimeEnvironment.captureBound environment.worker context bound graph
      (some environment) selections
    let actual ← values.mapM fun (index, value) => do
      let .ok argument := RuntimeArgument.ofValue graph index value
        | throwError "a native method parameter is outside its producing graph"
      return argument
    let mut parameters := #[]
    for entry in context.bindings do
      if let some value := bound[entry.id]? then
        let .ok parameter := RuntimeParameter.ofValue graph entry.id value
          | throwError "a native method parameter lost its original source context"
        parameters := parameters.push parameter
    let request ← PreparedRequest.forApplication transaction.owners.identities
      (← transaction.owners.identities.fresh .program) (← allocate)
      context callable arguments actual parameters (some graph) (some environment)
      (← environment.selections.inContext context)
    let request := request.withSourceSnapshot sourceSnapshot
    let some plan ← request.inputResultPlan graph
      | throwStratum .noImplementation
          "the method category parameter requires unavailable native input fields"
    let resolve := fun (input : FixedInput) => do
      input.resolveInContext transaction.owners.identities
        context bound (← environment.selections.inContext context)
        (liftM (m := IO) transaction.view) evaluate
    if ← environment.hasRetainedSource context source then
      let value ← evaluate context bound (← environment.selections.inContext context) source
      let resolved ← plan.resolve (liftM (m := IO) transaction.view) (some resolve)
      let graph ← transaction.view
      let response ← request.admitResult graph value
      discard <| IO.ofExcept <| (resolved.admit graph response).mapError IO.userError
      return value
    let response ← Execute.run
      (fun _ _ => throwError "a certified native method parameter attempted source execution")
      (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction (some resolve)
    return response.root
  let rec prepare (remaining : List Nat) (index : Nat) (context : OpenContext)
      (bound : Std.HashMap BindingId ValueBinding) (arguments : Array ClosedTerm)
      (values : Array (Nat × ValueBinding)) : MetaM ValueBinding := do
    match remaining with
    | [] => finish context bound arguments values
    | position :: remaining =>
      let some original := produced.getAppArgs[position]?
        | throwError "a native method parameter view lost its original argument position"
      if ← isProof original then
        return ← prepare remaining (index + 1) context bound
          (arguments.push (← context.close original)) values
      let graph ← transaction.view
      let some slot ← environment.declaredInputAt? context graph declaration position receiver
        | throwStratum .noImplementation
            "the native method category parameter has no original producer slot"
      withBoundValue transaction.owners.identities context bound
          (← slot.source.inContext context) slot.value fun context bound argument => do
        prepare remaining (index + 1) context bound
          (arguments.push (← context.close argument)) (values.push (index, slot.value))
  prepare assembly.positions.toList 0 context bound #[] #[]




partial def RuntimeEnvironment.sourceCategoryParameters (environment : RuntimeEnvironment)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (transaction : CellTransaction) (allocate : BaseIO (RuntimeId .occurrence))
    (categorySource : CategoryExpr) (receiverView : Option ConstructorEntry)
    (categoryFamily : Expr) (universeParams : List Name)
    (parameterCount : Nat) (arguments : Array Expr) (receiver : ValueBinding)
    (evaluate : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Expr → MetaM ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Array Expr → MetaM α)
    (sourceSnapshot : Option Json := none) : MetaM α := do
  let arrowView ← methodIsArrow categorySource receiverView
  withNativeInterface transaction.owners.identities (← transaction.view) context bound
      (← environment.selections.inContext context) receiver
    fun context bound selections receiverTerm => do
      let graph ← transaction.view
      let some node := graph.find receiver.value
        | throwError "the method receiver is outside its original graph"
      let produced := node.origin.role.source
      let declaration ← produced.withOpen fun _ expression => do
        return (← sourceDomain expression).getAppFn.constName?
      let environment ← RuntimeEnvironment.captureBound environment.worker context bound graph
        (some environment) selections
      let routes ← match declaration with
        | some declaration => sourceCategoryParameterRoutes categoryFamily universeParams parameterCount declaration
        | none => pure (Array.replicate arguments.size MethodCategoryParameter.unavailable)
      unless routes.size == arguments.size do
        throwError "the method category parameters changed their original formal arity"
      let mut origins := routes.map fun route => (receiver, produced, declaration, route)
      if routes.any (fun route => match route with | .unavailable => true | _ => false) &&
          arrowView then
        let some field := receiver.nativeRole.fields.find? (·.projection == ``CategoryTheory.Comma.hom)
          | throwError "the native method Arrow lost its original hom field"
        let retained ← IO.ofExcept <|
          (graph.projectionFrontier receiver #[field.projection]).mapError IO.userError
        if let some (stored, #[]) := retained then



          let hom ← evaluate context bound selections (← projectTerm receiverTerm field)
          unless hom.value == stored.value &&
              stored.associationIds.toList.isPrefixOf hom.associationIds.toList do
            throwError "the method hom changed its original stored input"
          let graph ← transaction.view
          let some homNode := graph.find hom.value
            | throwError "the original method hom is outside its producing graph"
          let homSource := homNode.origin.role.source
          let homDeclaration ← homSource.withOpen fun _ expression => do
            return (← sourceDomain expression).getAppFn.constName?
          if let some homDeclaration := homDeclaration then
            let homRoutes ← sourceCategoryParameterRoutes categoryFamily universeParams parameterCount homDeclaration (morphism := true)
            unless homRoutes.size == routes.size do
              throwError "the method hom changed its original category parameter arity"
            origins ← origins.mapIdxM fun index original => do
              match original with
              | (_, _, _, .unavailable) =>
                let some route := homRoutes[index]?
                  | throwError "the method hom lost an original category parameter position"
                return (hom, homSource, some homDeclaration, route)
              | _ => return original



      if origins.any (fun original => match original with
          | (_, _, _, .unavailable) => true | _ => false) then
        if let some selectedSource ← environment.declaredResultSource? context graph receiver then
          if let some slot ← environment.declaredInputAt? context graph
              selectedSource.declaration selectedSource.position receiver then
            let some inputNode := graph.find slot.value.value
              | throwError "the selected producer input is outside its original graph"
            let inputSource := inputNode.origin.role.source
            let (inputDeclaration, inputArity) ← inputSource.withOpen fun _ expression => do
              let expression ← sourceDomain expression
              return (expression.getAppFn.constName?, expression.getAppNumArgs)
            if let some inputDeclaration := inputDeclaration then
              let information ← checkedDeclaration inputDeclaration
              let arity ← forallTelescopeReducing information.type
                fun parameters _ => pure parameters.size
              unless inputArity == arity do
                throwError "the selected producer input lost its complete declaration telescope"
              let inputRoutes ← sourceCategoryProjectionInputRoutes categoryFamily universeParams parameterCount selectedSource.declaration
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
      let rec visit (remaining : List Expr) (index : Nat) (context : OpenContext)
          (bound : Std.HashMap BindingId ValueBinding) (selections : SourceSelectionScope Expr)
          (selected : Array Expr) : MetaM α := do
        match remaining with
        | [] => action context bound selections selected
        | source :: remaining =>
          if ← isProof source then
            return ← visit remaining (index + 1) context bound selections (selected.push source)
          let some (producer, produced, declaration, route) := origins[index]?
            | throwError "the method lost its original category parameter position"
          let graph ← transaction.view
          let some producerNode := graph.find producer.value
            | throwError "the original method parameter producer is outside its graph"
          withBindingContext graph context bound
              (.direct producerNode.id producerNode.origin.role) fun context bound => do
            let selections ← SourceSelectionScope.merge selections
              (← producerNode.origin.role.selections.inContext context)
            let produced ← sourceDomain (← produced.inContext context)
            let environment ← RuntimeEnvironment.captureBound environment.worker context bound graph
              (some environment) selections
            let retain := fun context bound selections value =>
              withBoundValue transaction.owners.identities context bound source value
                fun context bound actual => do
                  let current ← RuntimeEnvironment.captureBound environment.worker
                    context bound (← transaction.view) (some environment) selections
                  visit remaining (index + 1) context bound
                    (← current.selections.inContext context) (selected.push actual)
            match declaration, route with
            | some declaration, .input position path =>
              let graph ← transaction.view
              let slot ← environment.declaredInputAt? context graph declaration position producer
              match slot with
              | some slot =>
                let rec project (path : List Name) (context : OpenContext)
                    (bound : Std.HashMap BindingId ValueBinding)
                    (selections : SourceSelectionScope Expr) (value : ValueBinding) : MetaM α := do
                  match path with
                  | [] =>
                    let graph ← transaction.view
                    let environment ← RuntimeEnvironment.captureBound environment.worker
                      context bound graph (some environment) selections
                    let .ok actual := RuntimeArgument.ofValue graph index value
                      | throwError "a method category parameter is outside its producing graph"
                    discard <| environment.checkArgument (← context.close source) actual
                    retain context bound (← environment.selections.inContext context) value
                  | projection :: path =>
                    withNativeInterface transaction.owners.identities (← transaction.view)
                        context bound selections value fun context bound selections parent => do
                      let some field := value.nativeRole.fields.find? (·.projection == projection)
                        | throwError "a method category parameter lost its native source projection"
                      let expression ← projectTerm parent field
                      let value ← evaluate context bound selections expression
                      project path context bound selections value
                withBindingContext graph context bound slot.value fun context bound => do
                  discard <| slot.source.inContext context
                  let environment ← RuntimeEnvironment.captureBound environment.worker
                    context bound graph (some environment) selections
                  project path.toList context bound
                    (← environment.selections.inContext context) slot.value
              | none =>
                unless ← environment.hasRetainedSource context source do
                  throwStratum .noImplementation "the method category parameter has no original producer slot"
                visit remaining (index + 1) context bound selections (selected.push source)
            | some declaration, .assembly assembly =>
              let value ← methodParameterAssembly environment context bound transaction allocate
                declaration produced source producer assembly evaluate sourceSnapshot
              environment.checkDeclaredInput context (← transaction.view) source value
              retain context bound selections value
            | some declaration, .fixed fixed =>
              let .const _ levels := produced.getAppFn
                | throwError "a fixed method category parameter lost its declared universes"
              let information ← getConstInfo declaration
              let fixed := fixed.instantiateLevelParams information.levelParams levels
              unless ← isDefEq fixed source do
                throwError "the method changed an independently fixed declaration parameter"
              visit remaining (index + 1) context bound selections (selected.push source)
            | _, _ =>
              unless ← environment.hasRetainedSource context source do
                throwStratum .noImplementation "the method category parameter has no source input route"
              visit remaining (index + 1) context bound selections (selected.push source)
      visit arguments.toList 0 context bound (← environment.selections.inContext context) #[]


def RuntimeEnvironment.methodParameters (environment : RuntimeEnvironment)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (transaction : CellTransaction) (allocate : BaseIO (RuntimeId .occurrence))
    (family : RoutedMethodFamily) (arguments : Array Expr) (receiver : ValueBinding)
    (evaluate : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Expr → MetaM ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Array Expr → MetaM α)
    (sourceSnapshot : Option Json := none) : MetaM α := do
  unless family.receiverViews.size == family.route.refs.size + 1 do
    throwError "the method lost its complete original category-constructor positions"
  let some receiverView := family.receiverViews[0]?
    | throwError "the method lost its original source category constructor position"
  environment.sourceCategoryParameters context bound transaction allocate family.route.source
    receiverView family.categoryFamily family.universeParams family.parameterCount arguments receiver evaluate
    action sourceSnapshot



def RuntimeEnvironment.methodActionsWithInputs (environment : RuntimeEnvironment)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (identities : IdentitySupply) (graph : ValueGraph) (family : RoutedMethodFamily)
    (actions : Array Expr) (inputs : Array (Array ValueBinding))
    (continuation : OpenContext → Std.HashMap BindingId ValueBinding →
      SourceSelectionScope Expr → Array Expr → MetaM α) :
    MetaM α := do
  let edges := family.route.refs.push (.functor family.functor.id)
  unless actions.size == edges.size && inputs.size == edges.size &&
      family.actionFamilies.size == edges.size &&
      (family.actionFamilies.zip edges).all (fun (original, edge) => original.edge == edge) do
    throwError "the method lost its complete original action-input table"
  let rec visit (remaining : List (SourceActionFamily × Expr × Array ValueBinding))
      (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
      (selections : SourceSelectionScope Expr) (result : Array Expr) : MetaM α := do
    match remaining with
    | [] => continuation context bound selections result
    | (original, action, values) :: remaining => do
      let expected ← routedActionParameters original action
      unless expected.size == values.size do
        throwError "the method lost an exact native action parameter position"
      let rec parameters (remainingParameters : List (Expr × ValueBinding))
          (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
          (selections : SourceSelectionScope Expr) (selected : Array Expr) : MetaM α := do
        match remainingParameters with
        | [] => do
          visit remaining context bound selections
            (result.push (← routedActionWithParameters original action selected))
        | (source, value) :: remainingParameters => do
          let environment ← RuntimeEnvironment.captureBound environment.worker context bound graph
            (some environment) selections
          environment.checkDeclaredInput context graph source value
          withBoundValue identities context bound source value fun context bound source => do
            let current ← RuntimeEnvironment.captureBound environment.worker
              context bound graph (some environment) selections
            parameters remainingParameters context bound
              (← current.selections.inContext context) (selected.push source)
      parameters ((expected.map (·.2)).zip values).toList context bound selections #[]
  visit ((family.actionFamilies.zip actions).zip inputs |>.map fun ((original, action), values) =>
    (original, action, values)).toList context bound
      (← environment.selections.inContext context) #[]



structure RoutedSourceBoundary where
  private mk ::
  offset : Nat
  category : CategoryExpr
  forms : Array String


structure PreparedMethodRoute where
  private mk ::
  preparation : RoleScope
  family : RoutedMethodFamily
  actions : Array ClosedTerm
  environment : RuntimeEnvironment
  receiverSource : ClosedTerm
  receiver : ValueBinding
  boundaries : Array RoutedSourceBoundary
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



private def methodSourceImageForms (context : OpenContext)
    (selections : SourceSelectionScope Expr) (state : SemanticState)
    (schema : NamedCategoryEntry) (receiver : Expr) : MetaM (Array String) := do
  let some selected := selections.findAt? context receiver | return #[]
  let some application := selected.application | return #[]
  let .objectAction family := application.family | return #[]
  let expected := mkAppN
    (family.family.instantiateLevelParams family.universeParams application.universes)
    (application.parameters ++ application.arguments)
  context.withOriginalSources #[selected.value, expected] fun original => do
    unless ← isDefEq original[0]! original[1]! do
      throwError "the selected method image changed its original complete native action"
  let some category := methodImageCategory? state family.category | return #[]
  unless category.id == schema.id do return #[]
  return #[(methodImageForm state family.edge schema).id]

opaque routedSourceBoundaries (context : OpenContext) (selections : SourceSelectionScope Expr)
    (route : Route) (receiver : Expr) : MetaM (Array RoutedSourceBoundary) := do
  let state ← semanticState
  let registry : RegistryState := { toSemanticState := state }
  let named := (← sourceObjectSelection? context selections receiver).map (·.1)
  let categories := #[route.source] ++ route.steps.map (·.target)
  unless categories.size == route.refs.size + 1 do
    throwError "the method source lost a complete route boundary"
  let mut boundaries := #[]
  for category in categories, offset in [:categories.size] do
    let mut forms := #[]
    if let some schema := methodImageCategory? state category then

      forms := forms.push schema.id.raw
      if offset == 0 then
        for image in ← methodSourceImageForms context selections state schema receiver do
          unless forms.contains image do forms := forms.push image
      let mut object : Option ObjectEntry := none
      if let some original := named then
        let (selected, remaining) := registry.transport original
          (route.refs.extract 0 offset)
        if remaining.isEmpty then
          let some declared := state.categories.find? (·.id == selected.category)
            | throwError "the method source object lost its complete selected category"
          unless declared.expression.syntacticEq category do
            throwError "the object refinement changed its declared route position"


          let (effective, _) := registry.transport selected
            (route.refs.extract offset route.refs.size)
          if effective.id == selected.id then object := some selected
      if let some selectedObject := object then
        unless forms.contains selectedObject.id.raw do forms := forms.push selectedObject.id.raw
      else if 0 < offset then
        let some edge := route.refs[offset - 1]?
          | throwError "the method image lost its original edge position"
        let form := methodImageForm state edge schema
        unless forms.contains form.id do forms := forms.push form.id
    boundaries := boundaries.push ⟨offset, category, forms⟩
  return boundaries



def RoutedMethodFamily.admitsSourceForm (context : OpenContext)
    (selections : SourceSelectionScope Expr) (family : RoutedMethodFamily) (receiver : Expr)
    (input : String) : MetaM Bool := do
  let some source := (← routedSourceBoundaries context selections family.route receiver)[0]?
    | return false
  return source.forms.contains input




opaque PreparedMethodRoute.prepare (kernel : Kernel) (graph : ValueGraph)
    (request original : PreparedRequest) (path : Array FieldLayout)
    (captures : Array ValueBinding) : MetaM PreparedMethodRoute := do
  let .primitive (.routedMethod family) levels := original.action
    | throwError "the method demand lost its checked routed family"
  request.requireFamily original path graph (← kernel.codes.get)
  unless path.isEmpty do
    throwError "a routed method callable acquired an unrelated selected field"
  unless captures.size == original.scope.size &&
      (captures.zip original.scope).all (fun (left, right) => exactMethodInput left right) do
    throwError "the routed method changed its original complete captures"
  discard <| original.admitInputs graph
  discard <| request.admitInputs graph
  let .apply _ arguments values := request.action
    | throwError "a routed method requires its actual original receiver"
  let #[source] := arguments
    | throwError "the routed method changed its complete receiver telescope"
  let #[some receiver] := values
    | throwError "the routed method has no actual original receiver"
  withSourceScope request fun context bound => do
    let count := original.application.map (·.arguments.size) |>.getD 0
    original.withArguments kernel.ledger.owners.identities context bound count
        fun context bound parameters _ => do
      let selections ← SourceSelectionScope.merge
        (← request.environment.selections.inContext context)
        (← original.environment.selections.inContext context)
      let selections ← SourceSelectionScope.merge selections (← request.selections.inContext context)
      let selections ← SourceSelectionScope.merge selections (← original.selections.inContext context)
      let environment ← RuntimeEnvironment.captureBound request.environment.worker context bound
        graph (some request.environment) selections
      let actions ← family.specializeActions levels parameters
      let finish := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
          (selections : SourceSelectionScope Expr) (actions : Array Expr) => do
        let receiverTerm ← receiver.selectedSource context
        let selections ← SourceSelectionScope.merge selections
          (← environment.selections.inContext context)
        let selections ← SourceSelectionScope.merge selections
          (← receiver.role.selections.inContext context)
        let boundaries ← routedSourceBoundaries context selections family.route receiverTerm
        withBoundValue kernel.ledger.owners.identities context bound receiverTerm receiver
            fun context bound receiverTerm => do
          let environment ← RuntimeEnvironment.captureBound request.environment.worker
            context bound graph (some environment) selections
          return ⟨request.roles.scope, family, ← actions.mapM context.close, environment,
            ← context.close receiverTerm, receiver, boundaries, original.scope ++ request.scope⟩
      let base := original.origin.application.map (fun application =>
        (application.arguments.filterMap id).size) |>.getD 0
      if base < original.scope.size then
        let mut inputs := #[]
        let mut next := base
        let edges := family.route.refs.push (.functor family.functor.id)
        unless family.actionFamilies.size == edges.size && actions.size == edges.size do
          throwError "the original method lost its complete selected action table"
        for edge in edges, originalAction in family.actionFamilies, action in actions do
          unless originalAction.edge == edge do
            throwError "the original method changed an exact selected action position"
          let count := (← routedActionParameters originalAction action).size
          let selected := original.scope.extract next (next + count)
          unless selected.size == count do
            throwError "the original method scope lost a supplied action parameter"
          inputs := inputs.push selected
          next := next + count
        unless next == original.scope.size do
          throwError "the original method scope has unrelated extra action inputs"
        return ← environment.methodActionsWithInputs context bound
          kernel.ledger.owners.identities graph family actions inputs finish
      finish context bound (← environment.selections.inContext context) actions



structure SelectedMethodBoundary where
  private mk ::
  route : PreparedMethodRoute
  boundary : RoutedSourceBoundary
  realization : Realization


def PreparedMethodRoute.select (route : PreparedMethodRoute) (profile : RealizationProfile)
    (manifest : Manifest) : MetaM SelectedMethodBoundary := do
  let (offset, realization) ← profile.selectMethod manifest route.family.entry.id
    (route.boundaries.map (·.forms))
  let some boundary := route.boundaries[offset]?
    | throwError "the selected method boundary is outside its original route"
  unless boundary.offset == offset && offset <= route.family.route.refs.size do
    throwError "the selected method boundary changed its original source position"
  return ⟨route, boundary, realization⟩



structure MaterializedMethodBoundary where
  private mk ::
  selection : SelectedMethodBoundary
  receiver : ValueBinding
  receiverSource : ClosedTerm
  environment : RuntimeEnvironment
  dependencies : Array ValueBinding

def MaterializedMethodBoundary.route (selected : MaterializedMethodBoundary) : PreparedMethodRoute :=
  selected.selection.route

def MaterializedMethodBoundary.boundary (selected : MaterializedMethodBoundary) : RoutedSourceBoundary :=
  selected.selection.boundary



def materializeSourcePrefix (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (route : Route)
    (actionFamilies : Array SourceActionFamily) (actions : Array ClosedTerm)
    (receiverSource : ClosedTerm) (originalReceiver : ValueBinding)
    (originalDependencies : Array ValueBinding) (offset : Nat)
    (environment : RuntimeEnvironment := request.environment) :
    MetaM (ValueBinding × ClosedTerm × Array ValueBinding × RuntimeEnvironment) := do
  unless offset <= route.refs.size && route.refs.size <= actions.size &&
      actionFamilies.size == actions.size &&
      ((actionFamilies.extract 0 route.refs.size).zip route.refs).all
        (fun (family, edge) => family.edge == edge) do
    throwError "the selected source prefix is outside its complete native route"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let rec visit (remaining : List (SourceActionFamily × ClosedTerm)) (context : OpenContext)
        (bound : Std.HashMap BindingId ValueBinding) (selections : SourceSelectionScope Expr)
        (receiver : ValueBinding) (source : Expr) (dependencies : Array ValueBinding) :
        MetaM (ValueBinding × ClosedTerm × Array ValueBinding × RuntimeEnvironment) := do
      withBindingContext (← transaction.view) context bound receiver fun context bound => do
        withBoundValue kernel.ledger.owners.identities context bound source receiver
            fun context bound actual => do
          match remaining with
          | [] =>
            let environment ← RuntimeEnvironment.captureBound environment.worker context bound
              (← transaction.view) (some environment) selections
            return (receiver, ← context.close actual, dependencies.push receiver, environment)
          | (selected, action) :: remaining =>
            let action ← action.inContext context
            let (_, target) ← functorCategoryBundles action
            let image ← functorObject action actual target
            let declared ← routedActionApplication selected action
            let .const declaration universes := declared.getAppFn
              | throwError "the method image lost its original declaration application"
            unless selected.declaration == declaration do
              throwError "the method image changed its selected complete declaration"
            let selection ← selected.selected universes declared.getAppArgs actual
            context.withOriginalSources #[image, selection.value] fun native => do
              unless ← isDefEq native[0]! native[1]! do
                throwError "the selected method image changed its original native action"
            SourceSelectionScope.withBinding kernel.ledger.owners.identities selections
                context selection fun context selections source => do
              let receiver ← environment.evaluateSource evaluateSource transaction request.program
                context bound source selections
              let environment ← RuntimeEnvironment.captureBound environment.worker context bound
                (← transaction.view) (some environment) selections
              let some binding := context.bindings.find? (·.expression.fvarId! == source.fvarId!)
                | throwError "the method image lost its selected native binder"
              let layout ← SourceLayout.ofTerm (← context.close source)
                (← selections.close context) (some binding.id)
              let receiver := (← environment.checkResult (← transaction.view) layout receiver).root
              visit remaining context bound selections receiver source (dependencies.push receiver)
    visit ((actionFamilies.extract 0 offset).zip (actions.extract 0 offset)).toList
      context environment.bound (← environment.selections.inContext context)
      originalReceiver (← originalReceiver.selectedSource context) originalDependencies

def SelectedMethodBoundary.materialize (selection : SelectedMethodBoundary) (kernel : Kernel)
    (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM MaterializedMethodBoundary := do
  let route := selection.route
  request.requirePreparation route.preparation
  let (receiver, source, dependencies, environment) ← materializeSourcePrefix kernel
    evaluateSource request transaction route.family.route route.family.actionFamilies
    route.actions route.receiverSource
    route.receiver route.dependencies selection.boundary.offset route.environment
  return ⟨selection, receiver, source, environment, dependencies⟩



structure PreparedMethodInvocation where
  private mk ::
  preparation : RoleScope
  registration : Registration
  method : MethodId
  offset : Nat
  edges : Array EdgeRef
  parameters : Array (Array ValueBinding)
  receiver : ValueBinding
  dependencies : Array ValueBinding
  views : Array InputDescriptorView




def sourceReceiverViews (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (category : CategoryExpr)
    (receiverView : Option ConstructorEntry) (receiverSource : ClosedTerm) (receiver : ValueBinding)
    (environment : RuntimeEnvironment := request.environment) : MetaM (Array InputDescriptorView) := do
  unless ← methodIsArrow category receiverView do return #[]
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    withNativeInterface kernel.ledger.owners.identities (← transaction.view)
        context environment.bound (← environment.selections.inContext context) receiver
        fun context bound selections parent => do
      let mut fields := #[]
      for projection in #[``CategoryTheory.Comma.left, ``CategoryTheory.Comma.right,
          ``CategoryTheory.Comma.hom] do
        let some field := receiver.nativeRole.fields.find? (·.projection == projection)
          | throwError "the selected Arrow lost its complete native fields"
        fields := fields.push (← environment.evaluateSource evaluateSource transaction request.program context bound
          (← projectTerm parent field) selections)
      return #[← InputDescriptorView.nativeArrow (← transaction.view) receiver fields]





def MaterializedMethodBoundary.invocation (selected : MaterializedMethodBoundary)
    (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM PreparedMethodInvocation := do
  request.requirePreparation selected.route.preparation
  let .registration registration := selected.selection.realization
    | throwError "a source derivation has no provider method packet"
  let route := selected.route
  let count := route.family.route.refs.size
  let offset := selected.boundary.offset
  let edges := (route.family.route.refs.extract offset count).push (.functor route.family.functor.id)
  selected.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let bound := selected.environment.bound
    let mut parameters : Array (Array ValueBinding) := #[]
    let mut dependencies := selected.dependencies
    for edge in edges, index in [:edges.size] do
      let some action := route.actions[offset + index]?
        | throwError "the method request lost an original residual action"
      let some originalAction := route.family.actionFamilies[offset + index]?
        | throwError "the method request lost an original residual action family"
      unless originalAction.edge == edge do
        throwError "the method request changed an exact residual action position"
      let action ← action.inContext context
      let declared ← routedActionParameters originalAction action
      let mut actual := #[]
      for (_, term) in declared do
        let value ← selected.environment.evaluateSource evaluateSource transaction request.program context bound term
        let source ← SourceLayout.ofTerm (← context.close term)
        discard <| selected.environment.checkResult (← transaction.view) source value
        actual := actual.push value
        dependencies := dependencies.push value
      parameters := parameters.push actual
    unless edges.size == count - offset + 1 && parameters.size == edges.size do
      throwError "the complete method request lost its final functor or parameter positions"
    unless route.family.receiverViews.size == route.family.route.refs.size + 1 do
      throwError "the method lost its complete original category-constructor positions"
    let some receiverView := route.family.receiverViews[offset]?
      | throwError "the method receiver lost its original selected route position"
    let preparedViews ← sourceReceiverViews kernel evaluateSource request transaction
      selected.boundary.category receiverView selected.receiverSource selected.receiver selected.environment
    let roots := parameters.flatten.push selected.receiver
    let views ← InputDescriptorView.collect (← transaction.view) (← kernel.codes.get)
      roots preparedViews
    for descriptorView in views do dependencies := dependencies ++ descriptorView.dependencies
    return ⟨route.preparation, registration, route.family.entry.id, offset, edges, parameters,
      selected.receiver, dependencies, views⟩



def PreparedMethodInvocation.roots (invocation : PreparedMethodInvocation) : Array InputPosition := Id.run do
  let mut roots := #[]
  for (edge, values) in invocation.edges.zip invocation.parameters,
      actionIndex in [:invocation.edges.size] do
    for binding in values, dataIndex in [:values.size] do
      roots := roots.push {
        path := #[.field "args", .index actionIndex] ++ routedActionParameterPath edge dataIndex,
        binding }
  return roots.push { path := #[.field "receiver"], binding := invocation.receiver }



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



def MaterializedMethodBoundary.derivation (selected : MaterializedMethodBoundary)
    (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (PreparedResponse request) := do
  request.requirePreparation selected.route.preparation
  let .derivation checked := selected.selection.realization
    | throwError "a provider method packet has no selected source derivation"
  unless selected.boundary.offset == selected.route.family.route.refs.size do
    throwError "a method derivation was selected outside its declared owner boundary"
  selected.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let bound := selected.environment.bound
    let some action := selected.route.actions.back?
      | throwError "the method derivation lost its complete final declaration"
    let action ← action.inContext context
    let some originalAction := selected.route.family.actionFamilies.back?
      | throwError "the method derivation lost its selected final action family"
    unless originalAction.edge == .functor selected.route.family.functor.id do
      throwError "the method derivation changed its selected final action"
    let declared ← routedActionApplication originalAction action
    let .const _ levels := declared.getAppFn
      | throwError "the method derivation lost its declaration universes"
    unless checked.source.entry.target == .method selected.route.family.entry.id do
      throwError "the selected method derivation belongs to another published target"
    checked.instantiate levels kernel.ledger.owners.identities context
        (← selected.environment.selections.inContext context) fun context selections plan => do
      let function := mkAppN plan declared.getAppArgs
      let function ← if (← whnfR (← inferType function)).isAppOf ``CategoryTheory.Cat.Hom then
          mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[function]
        else pure function
      let source ← selected.receiver.selectedSource context
      withBoundValue kernel.ledger.owners.identities context bound source selected.receiver
          fun context bound receiver => do
        let receiver ← match selected.route.family.entry.shape with
          | .object => pure receiver
          | .isoInvariant => mkAppM ``CategoryTheory.Core.mk #[receiver]
        let (_, target) ← functorCategoryBundles function
        let value ← selected.environment.evaluateSource evaluateSource transaction request.program
          context bound (← functorObject function receiver target) selections
        kernelCompletion request transaction value
          (some (kernel.resolveFixedInput evaluateSource transaction request.program))

end CasRuntime
