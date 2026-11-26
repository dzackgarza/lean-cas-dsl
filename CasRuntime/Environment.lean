module

public import CasRuntime.Value
import all CasRuntime.Value
public import CasTools.Diagnostics
public import CasCompiler.SelectedMorphism

public section

namespace CasRuntime

open Lean Meta CasCompiler

initialize registerTraceClass `cas.environment

structure RuntimeParameter where
  private mk ::
  source : BindingId
  value : ValueBinding
  private origin : ValueOrigin
  private graph : ValueGraph

opaque RuntimeParameter.ofValue (graph : ValueGraph) (source : BindingId) (value : ValueBinding) :
    Except String RuntimeParameter := do
  discard <| graph.requiredOwners #[value]
  let some node := graph.find value.value
    | throw "the runtime parameter is outside the visible graph"
  return ⟨source, value, node.origin, graph⟩

structure RuntimeArgument where
  private mk ::
  index : Nat
  value : ValueBinding
  private origin : ValueOrigin
  private graph : ValueGraph

opaque RuntimeArgument.ofValue (graph : ValueGraph) (index : Nat) (value : ValueBinding)
    :
    Except String RuntimeArgument := do
  discard <| graph.requiredOwners #[value]
  let some node := graph.find value.value
    | throw "the runtime argument is outside the visible graph"
  return ⟨index, value, node.origin, graph⟩

def RuntimeArgument.toParameter (argument : RuntimeArgument) (source : BindingId) :
    RuntimeParameter :=
  ⟨source, argument.value, argument.origin, argument.graph⟩

structure RuntimeEnvironment where
  private mk ::
  worker : String
  context : ContextTelescope
  bound : Std.HashMap BindingId ValueBinding
  private inputProjections : Std.HashMap BindingId InputProjection
  private sourceGraph : Option ValueGraph
  selections : SourceSelectionScope ClosedTerm := {}

def RuntimeEnvironment.values (environment : RuntimeEnvironment) : Array (Option ValueBinding) :=
  environment.context.entries.map fun entry => environment.bound[entry.id]?

def RuntimeEnvironment.references (environment : RuntimeEnvironment) : Array ValueBinding :=
  environment.values.filterMap id

opaque RuntimeEnvironment.withGraph (environment : RuntimeEnvironment)
    (graph : Option ValueGraph := none) : MetaM RuntimeEnvironment := do
  let sourceGraph := match graph with
    | some current => some current
    | none => environment.sourceGraph
  if let some current := sourceGraph then
    unless current.worker == environment.worker do
      throwError "source preparation belongs to a different worker"

    unless environment.sourceGraph.any (·.sameRevision current) do
      discard <| IO.ofExcept <| (current.requiredOwners environment.references).mapError IO.userError
  return { environment with sourceGraph }

def RuntimeEnvironment.lookup (environment : RuntimeEnvironment) (source : BindingId) :
    Except String (Option ValueBinding) := do
  unless environment.context.entries.any (·.id == source) do
    throw "the runtime binding identity is outside its source telescope"
  return environment.bound[source]?

private def sameReference (original current : ValueBinding) : Bool :=
  original.value == current.value &&
    (original.associationIds.toList.isPrefixOf current.associationIds.toList ||
      current.associationIds.toList.isPrefixOf original.associationIds.toList)

def retainsReference (bound operand : ValueBinding) : Bool :=
  bound.value == operand.value &&
    bound.associationIds.toList.isPrefixOf operand.associationIds.toList

private abbrev NativeTelescopeViews := Array (ConstructorProjectionTransport × Expr)

private def sameAdmittedSource (left right : ClosedTerm) : Bool :=
  left.context.exactlyMatches right.context && left.expression.equal right.expression &&
    left.type.equal right.type && left.universeParams == right.universeParams &&
    left.nativeDeclarations.exactlyMatches right.nativeDeclarations

private def nativeTypeInContext (context : OpenContext) (views : NativeTelescopeViews)
    (source : ClosedTerm) (fieldType : Option (ClosedTerm × ClosedTerm) := none) : MetaM Expr := do
  let mut type ← inferType (← source.inContext context)
  if let some (original, annotated) := fieldType then

    if sameAdmittedSource original source then
      let annotated ← annotated.inContext context
      unless ← context.withOriginalSources #[type, annotated]
          (fun types => isDefEq types[0]! types[1]!) do
        throwError "the producing field prefix changed its original native type"
      type := annotated
  for (transport, replacement) in views do
    type ← transport.instantiateSchema context type replacement
  return type

private def nativeSchemaInContext (context : OpenContext) (views : NativeTelescopeViews)
    (source : ClosedTerm) : MetaM Expr := do
  let mut schema ← source.inContext context
  for (transport, replacement) in views do
    schema ← transport.instantiateSchema context schema replacement
  return schema

private def withNativeTelescopeViews (context : OpenContext)
    (supplied : Std.HashMap BindingId ValueBinding)
    (graph : ValueGraph) (value : ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      NativeTelescopeViews → MetaM α) : MetaM α := do
  let rec visit (scopes : List TelescopeInstantiation) (context : OpenContext)
      (supplied : Std.HashMap BindingId ValueBinding)
      (views : NativeTelescopeViews) : MetaM α := do
    match scopes with
    | [] => action context supplied views
    | scope :: rest =>
      scope.transport.withContext context fun context => do
        unless scope.parameters.size == scope.transport.plan.context.entries.size do
          throwError "native transport lost its complete original parameter table"
        let mut supplied := supplied
        for entry in scope.transport.plan.context.entries, actual in scope.parameters do
          if let some actual := actual then
            if let some current := supplied[entry.id]? then
              unless retainsReference actual current do
                throwError "native transport changed an original dependent supplier"
            else supplied := supplied.insert entry.id actual
        discard <| IO.ofExcept <|
          (graph.requiredOwners (scope.parameters.filterMap id ++ #[scope.selected])).mapError
            IO.userError
        let original ← scope.transport.target.source.inContext context
        let mut type ← inferType original
        for (transport, replacement) in views do
          type ← transport.instantiateSchema context type replacement
        let next := fun (context : OpenContext) (binding : LocalBinding) => do
          let supplied ← match supplied[scope.sourceBinding]? with
            | none => pure (supplied.insert scope.sourceBinding scope.selected)
            | some actual =>
              unless retainsReference scope.selected actual do
                throwError "native transport changed its exact selected occurrence"
              pure supplied
          visit rest context supplied (views.push (scope.transport, binding.expression))
        if let some binding := context.bindings.find? (·.id == scope.sourceBinding) then
          let some source := binding.originalSource
            | throwError "native transport lost its original source correspondence"
          unless source.equal original do
            throwError "native transport changed its original source position"
          unless ← context.withOriginalSources #[← inferType binding.expression, type]
              (fun types => isDefEq types[0]! types[1]!) do
            throwError "native transport changed its original selected slot type"
          next context binding
        else
          context.withLocalBinding scope.sourceBinding .result `constructorPort type next
            (originalSource := some original)
  visit value.telescopeInstantiations.toList context supplied #[]

private def checkNativeType (context : OpenContext) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin)
    (views : NativeTelescopeViews := #[])
    (fieldType : Option (ClosedTerm × ClosedTerm) := none) : MetaM Unit := do
  let original ← nativeTypeInContext context views value.role.source fieldType
  unless ← context.withOriginalSources #[original, expected]
      (fun types => isDefEq types[0]! types[1]!) do
    trace[cas.environment] "retained type {original}, expected {expected}"
    throwError "the runtime value has an incompatible complete source type"
  let producing ← nativeTypeInContext context views origin.role.source fieldType
  unless ← context.withOriginalSources #[producing, expected]
      (fun types => isDefEq types[0]! types[1]!) do
    trace[cas.environment] "producing type {producing}, expected {expected}"
    throwError "the producing runtime value has an incompatible complete source type"
  for scope in value.telescopeInstantiations do
    unless ← context.withOriginalSources
        #[← nativeTypeInContext context views scope.source.source fieldType, expected]
        (fun types => isDefEq types[0]! types[1]!) do
      throwError "the original constructor port has an incompatible complete source type"

def missingValueTag (id : BindingId) : Name :=
  .num (.str `CasRuntime.missingValue id.session) id.serial

def missingValueOf (error : Exception) (id : BindingId) : Bool :=
  error.toMessageData.hasTag (· == missingValueTag id)

private partial def dependencySource (source : ClosedTerm) : MetaM ClosedTerm := do
  let source ← source.inputProjectionSource
  source.withOpen fun bindings stated => do
    let declared ← declaredEndpoint stated
    let context ← ContextTelescope.capture bindings
    if declared != stated then return ← dependencySource (← context.close declared)
    if let some projection ← SourceProjection.ofExpr? stated then
      let parent ← dependencySource (← context.close projection.parent)
      let parent ← parent.inContext context
      if parent != projection.parent then
        let constructor ← getConstInfoCtor projection.info.ctorName
        return ← dependencySource (← context.close (mkProj constructor.induct projection.info.i parent))
    return source

private partial def dependencyReference (context : OpenContext) (inputs : Array BindingId)
    (source : ClosedTerm) (path : Array Name := #[]) :
    MetaM (Option (BindingId × Array Name)) := do

  let source ← context.close (← source.inContext context)
  let source ← dependencySource source
  let some selected ← source.inputProjectionAt path inputs | return none
  let .context id := selected.target
    | throwError "a context dependency selected a nonexistent application argument"
  let some binding := context.bindings.find? (·.id == id)
    | throwError "a dependent source reference is outside its context"
  if let some definition := (← getFVarLocalDecl binding.expression).value? then
    if definition.hasFVar then
      if let some original ← dependencyReference context inputs
          (← context.close definition) selected.path then
        return some original
  return some (id, selected.path)

private inductive DependencyStep where
  | metadata | function | argument | domain | body | projection
  deriving BEq

private structure DependencyTerm where
  index : Nat
  term : Expr
  position : Option (Array DependencyStep)

private def dependencyPositionAfterMetadata (position : Option (Array DependencyStep)) :
    Expr → Option (Array DependencyStep)
  | .mdata _ body =>
    dependencyPositionAfterMetadata (position.map (·.push .metadata)) body
  | _ => position

private partial def dependencyTerms (sameContextReference : Expr → Expr → MetaM Bool)
    (locals : Array Expr) (formal expected : Expr)
    (binders : Array (Expr × Expr) := #[])
    (capturedReference : Option (Bool → Expr → Expr →
      Option (Array DependencyStep) → Option (Array DependencyStep) →
      MetaM (Option Bool)) := none)
    (sourceView : Option (Expr → MetaM Expr) := none) (capturedReduction : Bool := true)
    (allowClosedExpected : Bool := true)
    (formalPosition : Option (Array DependencyStep) := some #[])
    (expectedPosition : Option (Array DependencyStep) := some #[]) :
    MetaM (Option (Array DependencyTerm)) := do
  let allowClosedExpected := allowClosedExpected && (match expected with
    | .mdata .. => false
    | _ => true)
  let expectedHasMetadata := (expected.find? fun
    | .mdata .. => true
    | _ => false).isSome
  let originalFormal := formal
  let originalExpected := expected
  let formalBodyPosition := dependencyPositionAfterMetadata formalPosition formal
  let expectedBodyPosition := dependencyPositionAfterMetadata expectedPosition expected
  let formal := formal.consumeMData
  let expected := expected.consumeMData
  if let some compare := capturedReference then
    if let some same ← compare capturedReduction originalFormal originalExpected
        formalPosition expectedPosition then
      unless same do
        throwError "the runtime value has a different marked source type dependency"
      return some #[]

    match originalFormal, originalExpected with
    | .mdata _ body, .mdata _ other =>
      return ← dependencyTerms sameContextReference locals body other binders
        capturedReference sourceView capturedReduction allowClosedExpected
        (formalPosition.map (·.push .metadata)) (expectedPosition.map (·.push .metadata))
    | .mdata _ body, _ =>
      return ← dependencyTerms sameContextReference locals body originalExpected binders
        capturedReference sourceView capturedReduction allowClosedExpected
        (formalPosition.map (·.push .metadata)) expectedPosition
    | _, .mdata _ body =>
      return ← dependencyTerms sameContextReference locals originalFormal body binders
        capturedReference sourceView capturedReduction allowClosedExpected
        formalPosition (expectedPosition.map (·.push .metadata))
    | _, _ => pure ()
  if let some index := locals.findIdx? (· == formal) then
    if expected.hasLooseBVars then return none
    let proof ← isProof formal
    let freeVariables := collectFVars {} expected
    if !proof && binders.any (fun (_, bound) => freeVariables.fvarSet.contains bound.fvarId!) then
      return none
    let some preceding ← dependencyTerms sameContextReference (locals.extract 0 index)
        (← inferType formal) (← inferType expected) binders
        capturedReference sourceView capturedReduction allowClosedExpected none none | return none
    if proof then return some preceding
    return some (preceding.push ⟨index, originalExpected, expectedPosition⟩)
  if let some (_, bound) := binders.find? (fun (source, _) => source == formal) then
    return if bound == expected then some #[] else none
  if formal == expected then return some #[]
  let merge (left right : MetaM (Option (Array DependencyTerm))) :
      MetaM (Option (Array DependencyTerm)) := do
    let some left ← left | return none
    let some right ← right | return none
    return some (left ++ right)
  let matched ← match formal, expected with
    | .sort _, .sort _ => pure (some #[])
    | .const name _, .const other _ =>
      if name == other then pure (some #[]) else pure none
    | .app f a, .app g b =>
      merge (dependencyTerms sameContextReference locals f g binders
        capturedReference sourceView capturedReduction allowClosedExpected
        (formalBodyPosition.map (·.push .function)) (expectedBodyPosition.map (·.push .function)))
        (dependencyTerms sameContextReference locals a b binders
          capturedReference sourceView capturedReduction allowClosedExpected
          (formalBodyPosition.map (·.push .argument)) (expectedBodyPosition.map (·.push .argument)))
    | .forallE name a b info, .forallE other c d otherInfo
    | .lam name a b info, .lam other c d otherInfo => do
      let some domains ← dependencyTerms sameContextReference locals a c binders
          capturedReference sourceView capturedReduction allowClosedExpected
          (formalBodyPosition.map (·.push .domain)) (expectedBodyPosition.map (·.push .domain))
        | return none
      withLocalDecl name info a fun source =>
        withLocalDecl other otherInfo c fun target => do
          let some bodies ← dependencyTerms sameContextReference locals
              (b.instantiate1 source) (d.instantiate1 target) (binders.push (source, target))
              capturedReference sourceView capturedReduction allowClosedExpected
              (formalBodyPosition.map (·.push .body)) (expectedBodyPosition.map (·.push .body))
            | return none
          return some (domains ++ bodies)
    | .proj owner index parent, .proj other otherIndex otherParent =>
      if owner == other && index == otherIndex then
        dependencyTerms sameContextReference locals parent otherParent binders
          capturedReference sourceView capturedReduction allowClosedExpected
          (formalBodyPosition.map (·.push .projection)) (expectedBodyPosition.map (·.push .projection))
      else pure none
    | _, _ => pure none
  if matched.isSome then return matched
  if ← sameContextReference originalFormal originalExpected then return some #[]

  let formalVars := collectFVars {} formal
  let hasAbstract := locals.any (fun parameter => formalVars.fvarSet.contains parameter.fvarId!) ||
    binders.any (fun (source, _) => formalVars.fvarSet.contains source.fvarId!)
  if allowClosedExpected && !expectedHasMetadata && !expected.hasFVar &&
      !expected.hasLooseBVars && !formal.hasLooseBVars && !hasAbstract then
    let converts ← withoutModifyingState do
      withConfig (fun config => { config with zetaDelta := true }) (isDefEq formal expected)
    if converts then return some #[]
  let normalize := fun (original expression : Expr) => do
    if let some view := sourceView then
      if capturedReduction && !original.hasLooseBVars then view original else pure original
    else if expression.hasLooseBVars then pure expression
    else withConfig (fun config => { config with zetaDelta := false }) (whnf expression)
  let normalizedFormal ← normalize originalFormal formal
  let normalizedExpected ← normalize originalExpected expected
  if normalizedFormal == formal && normalizedExpected == expected then return none
  dependencyTerms sameContextReference locals normalizedFormal normalizedExpected binders
    capturedReference sourceView capturedReduction (allowClosedExpected && !expectedHasMetadata)
    (if normalizedFormal.equal originalFormal then formalPosition else none)
    (if normalizedExpected.equal originalExpected then expectedPosition else none)

private def storedDependency (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : MetaM (Option ValueBinding) := do
  let mut value := parent
  for projection in path do
    let some field := value.nativeRole.fields.find? (·.projection == projection)
      | throwError "a consuming dependent reference is outside its native record"
    let some index := field.wireIndex
      | throwError "a consuming runtime dependency selected a proof field"
    let some node := graph.find value.value
      | throwError "a consuming dependent reference is outside its actual graph"
    if node.payload.data.storedFields?.isNone then
      let some retained ← IO.ofExcept <|
          (graph.projected? value #[projection]).mapError IO.userError
        | return none
      value := retained
      continue
    value ← IO.ofExcept <| (graph.project value index).mapError IO.userError
  return some value

private structure PendingResultProjection where
  parent : ValueBinding
  projection : Name
  result : ValueBinding

private partial def pendingDependency (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) (pending : Option PendingResultProjection) :
    MetaM (Option ValueBinding) := do
  if path.isEmpty then return some parent
  let cached ← IO.ofExcept <| (graph.projected? parent path).mapError IO.userError
  let some projection := path[0]?
    | throwError "a pending dependent reference lost its native projection"
  let some field := parent.nativeRole.fields.find? (·.projection == projection)
    | throwError "a consuming dependent reference is outside its native record"
  let some index := field.wireIndex
    | throwError "a consuming runtime dependency selected a proof field"
  let some node := graph.find parent.value
    | throwError "a consuming dependent reference is outside its actual graph"
  let existing ← IO.ofExcept <|
    (graph.projected? parent #[projection]).mapError IO.userError
  let step ← if node.payload.data.storedFields?.isSome then do
      let stored ← IO.ofExcept <| (graph.project parent index).mapError IO.userError
      if let some existing := existing then
        unless sameReference stored existing do
          throwError "the runtime value has a different consuming dependent reference \
            in its retained projection"
      pure (some stored)
    else pure existing
  let rest := path.extract 1 path.size
  let selected ← match step with
    | some next => pendingDependency graph next rest pending
    | none => match pending with
      | some access =>
        if projection == access.projection && sameReference parent access.parent then
          pendingDependency graph access.result rest none
        else pure none
      | none => pure none
  if let some cached := cached then
    if let some selected := selected then
      unless sameReference cached selected do
        throwError "the runtime value has a different consuming dependent reference \
          in its retained projection"
    return some cached
  return selected

private partial def hasDependencyAccess (graph : ValueGraph) (value parent : ValueBinding)
    (path : Array Name) : Bool := Id.run do
  if path.isEmpty then return sameReference parent value
  let mut accesses := value.projectionAccesses
  if let some node := graph.find value.value then
    if let some original := node.origin.access then
      accesses := accesses.push (original, node.origin.accessPath)
  for (original, suffix) in accesses do
    if suffix.isEmpty || suffix.size > path.size then continue
    let prefixSize := path.size - suffix.size
    if path.extract prefixSize path.size == suffix &&
        hasDependencyAccess graph original parent (path.extract 0 prefixSize) then return true
  return false

private structure ResultFieldPrefix where
  parent : Option ValueBinding
  layout : RecordLayout
  field : FieldLayout
  «view» : Option FieldDependencyView := none
  preceding : Option (Array (Option ValueBinding)) := none

private def ResultFieldPrefix.descend (current : ResultFieldPrefix) (projection : Name) :
    MetaM ResultFieldPrefix := do
  let path := ((current.view.map (·.path)).getD #[]).push projection
  return { current with «view» := some (← current.field.dependencyView path) }

private partial def prefixProjection (locals : Array Expr) (term : Expr) :
    MetaM (Option (Nat × Array Name)) := do
  if let some index := locals.findIdx? (· == term) then return some (index, #[])
  let some projection ← SourceProjection.ofExpr? term | return none
  let some (index, path) ← prefixProjection locals projection.parent | return none
  return some (index, path.push projection.declaration)

private def currentPrefixRoutes (context : OpenContext) (inputs : Array BindingId)
    (graph : ValueGraph) (original : FieldInstantiation) (slot : Nat)
    (current : ResultFieldPrefix) (views : NativeTelescopeViews := #[]) :
    MetaM (Option (Array (ValueBinding × Array Name) × Bool)) := do
  let family ← nativeSchemaInContext context views original.typeFamily
  let currentFamily ← nativeSchemaInContext context views
    ((current.view.map (·.typeFamily)).getD current.field.typeFamily)
  let inspect := fun locals type => do
    unless locals.size ≥ original.preceding.size do
      throwError "a consuming runtime dependency lost its complete native prefix"
    let inspectCurrent := fun currentLocals currentType => do
      unless currentLocals.size ≥ current.field.sourceIndex do
        throwError "the current result field lost its complete native prefix"
      let prefixLocals := currentLocals.extract 0 current.field.sourceIndex
      let some terms ← dependencyTerms (fun _ _ => pure false) locals type currentType | return none
      let selected := terms.filterMap fun term => if term.index == slot then some term.term else none
      if selected.isEmpty then return none
      let mut routes := #[]
      let mut complete := true
      for term in selected do
        if let some (index, path) ← prefixProjection prefixLocals term then
          let some prepared := current.layout.fields[index]?
            | throwError "a current result dependency is outside its declared prefix"
          unless prepared.field.wireIndex.isSome do
            complete := false
            continue
          let selected ← match current.parent with
            | some parent => storedDependency graph parent #[prepared.field.projection]
            | none =>
              let some preceding := current.preceding
                | throwError "the current native field lost its original prefix snapshot"
              unless preceding.size == current.field.sourceIndex do
                throwError "the current native field changed its complete prefix telescope"
              pure (preceding[index]?.bind id)
          let some value := selected
            | throwError "the runtime value is missing a required original dependent prefix field"
          routes := routes.push (value, path)
        else
          let freeVars := collectFVars {} term
          if currentLocals.any (fun parameter => freeVars.fvarSet.contains parameter.fvarId!) then
            complete := false
            continue
          let source ← dependencySource (← context.close term)
          let term ← source.inContext context
          if term.hasFVar && (← dependencyReference context inputs source).isNone then
            complete := false
      if routes.isEmpty then return none
      return some (routes, complete)
    if current.view.isSome then lambdaTelescope currentFamily inspectCurrent
    else lambdaBoundedTelescope currentFamily current.field.sourceIndex inspectCurrent
  if original.view.isSome then lambdaTelescope family inspect
  else lambdaBoundedTelescope family original.preceding.size inspect

private partial def capturedTypePosition (context : OpenContext)
    (positions : Std.HashMap BindingId InputProjection) (source : Expr) :
    MetaM (Option (BindingId × Array Name)) := do
  let some source := projectionBody? source | return none
  if source.isFVar then
    let some binding := context.bindings.find? (·.expression == source) | return none
    let some selected := positions[binding.id]? | return none
    let .context original := selected.target | return none
    return some (original, selected.path)
  let some projection ← SourceProjection.ofExpr? source | return none
  let some (binding, path) ← capturedTypePosition context positions projection.parent | return none
  return some (binding, path.push projection.declaration)

private def capturedTypeReferences (context : OpenContext)
    (inputProjections : Std.HashMap BindingId InputProjection) (inputs : Array BindingId)
    (supplied : Std.HashMap BindingId ValueBinding)
    (expression : Expr) (reduce : Bool) : MetaM (Array (ValueBinding × Array Name)) := do
  let captured := context.bindings.map (·.expression)
  if expression.hasLooseBVars || expression.hasExprMVar || expression.hasLevelMVar ||
      (expression.abstract captured).hasFVar then return #[]
  let expression ← if reduce then context.inputProjectionSource expression inputs
    else pure expression
  if let some (id, path) ← boundProjection? context supplied expression then
    let some parent := supplied[id]?
      | throwError "the runtime value has an unresolved consuming dependent type"
    return #[(parent, path)]
  let reference ← if reduce then
      dependencyReference context inputs (← context.close expression)
    else capturedTypePosition context inputProjections expression
  let some reference := reference | return #[]
  let mut references := #[]
  for binding in context.bindings do
    let some value := supplied[binding.id]? | continue
    let some selected := inputProjections[binding.id]? | continue
    let .context source := selected.target | continue
    unless source == reference.1 && selected.path.toList.isPrefixOf reference.2.toList do continue
    references := references.push (value, reference.2.extract selected.path.size reference.2.size)
  return references

private def sameCapturedTypeReference (graph : ValueGraph)
    (left right : ValueBinding × Array Name) : MetaM Bool := do
  if sameReference left.1 right.1 && left.2 == right.2 then return true
  let leftValue ← storedDependency graph left.1 left.2
  let rightValue ← storedDependency graph right.1 right.2
  match leftValue, rightValue with
  | some first, some second => return sameReference first second
  | some first, none => return hasDependencyAccess graph first right.1 right.2
  | none, some second => return hasDependencyAccess graph second left.1 left.2
  | none, none => return false

private def joinedPrefixReferences (context : OpenContext) (inputs : Array BindingId)
    (graph : ValueGraph) (sameContextReference : Expr → Expr → MetaM Bool)
    (formal expected : Expr) (value : ValueBinding) (currentPrefixes : Array ResultFieldPrefix)
    (views : NativeTelescopeViews := #[])
    (producingPrefix : Option NativeFieldPrefix := none) :
    MetaM (Array (Array DependencyStep × ValueBinding) ×
      Array (Array DependencyStep × ValueBinding)) := do
  if currentPrefixes.isEmpty then return (#[], #[])
  let mut formalReferences := #[]
  let mut expectedReferences := #[]
  for original in value.instantiations do
    if original.precedingDependencies.isEmpty then continue
    let producing := producingPrefix.any fun nativePrefix =>
      nativePrefix.frames.any fun frame =>
        frame.association.id == original.association.id &&
        frame.field.sourceIndex == original.field.sourceIndex &&
        frame.field.projection == original.field.projection &&
        (frame.view.map (·.path)).getD #[] == original.projectionPath &&
        frame.preceding.size == original.preceding.size &&
        (frame.preceding.zip original.preceding).all (fun (left, right) =>
          match left, right with
          | none, none => true
          | some left, some right =>
            left.value == right.value && left.associationIds == right.associationIds
          | _, _ => false)
    if currentPrefixes.any (fun current =>
        sameAdmittedSource original.association.layout.source.source
          current.layout.source.source) && !producing then continue
    let family ← nativeSchemaInContext context views original.typeFamily
    let inspect := fun target locals type => do
      unless locals.size ≥ original.preceding.size do
        throwError "a consuming runtime dependency lost its complete native prefix"
      dependencyTerms sameContextReference locals type target
    let positions := fun target =>
      if original.view.isSome then lambdaTelescope family (inspect target)
      else lambdaBoundedTelescope family original.preceding.size (inspect target)
    let some formalTerms ← positions formal | continue
    let some expectedTerms ← positions expected | continue
    for slot in original.precedingDependencies do
      let some previous := original.preceding[slot]?
        | throwError "a consuming runtime dependency is outside its complete field prefix"
      let some previous := previous | continue
      let mut covered := false
      for current in currentPrefixes do
        if let some (routes, complete) ←
            currentPrefixRoutes context inputs graph original slot current views then
          covered := covered || complete
          for (parent, path) in routes do
            match ← storedDependency graph parent path with
            | some actual =>
              unless sameReference previous actual do
                throwError "the runtime value has a different consuming dependent reference \
                  in its current result prefix"
            | none =>
              unless hasDependencyAccess graph previous parent path do
                throwError "the runtime value has an unresolved consuming dependent reference \
                  in its current result prefix"
      unless covered do continue
      for term in formalTerms do
        if term.index == slot then
          if let some position := term.position then
            formalReferences := formalReferences.push (position, previous)
      for term in expectedTerms do
        if term.index == slot then
          if let some position := term.position then
            expectedReferences := expectedReferences.push (position, previous)
  return (formalReferences, expectedReferences)

private partial def joinedTypePosition
    (references : Array (Array DependencyStep × ValueBinding))
    (term : Expr) (position : Option (Array DependencyStep)) :
    MetaM (Array (ValueBinding × Array Name)) := do
  let some position := position | return #[]
  let selected := references.filterMap fun (slot, value) =>
    if slot == position then some (value, #[]) else none
  if !selected.isEmpty then return selected
  let some projection ← SourceProjection.ofExpr? term | return #[]
  let position := dependencyPositionAfterMetadata (some position) term
  let parentPosition := match term.consumeMData with
    | .proj .. => position.map (·.push .projection)
    | .app .. => position.map (·.push .argument)
    | _ => none
  return (← joinedTypePosition references projection.parent parentPosition).map fun (value, path) =>
    (value, path.push projection.declaration)

private partial def nativePrefixPath? (original source : Expr) : MetaM (Option (Array Name)) := do
  if original.equal source then return some #[]
  if let .mdata _ body := source then
    return ← nativePrefixPath? original body
  let some projection ← SourceProjection.ofExpr? source | return none
  let some path ← nativePrefixPath? original projection.parent | return none
  return some (path.push projection.declaration)

private def nativePrefixEndpoint? (nativePrefix : NativeFieldPrefix) (context : OpenContext)
    (graph : ValueGraph) (source : Expr) : MetaM (Option ValueBinding) := do
  let some first := nativePrefix.frames[0]?
    | throwError "a native endpoint prefix lost its original declaration frame"
  let mut root := first.association.layout.source
  for frame in nativePrefix.frames do
    if frame.association.layout.source.address.size < root.address.size then
      root := frame.association.layout.source
  let some path ← nativePrefixPath? (← root.source.inContext context) source | return none
  if path.isEmpty then return none
  let mut result := none
  for frame in nativePrefix.frames do
    let parentPath ← root.projectionPathTo frame.association.layout.source
    unless parentPath.toList.isPrefixOf path.toList && parentPath.size < path.size do continue
    let some projection := path[parentPath.size]? | continue
    let some prepared := frame.association.layout.fields.find? (·.field.projection == projection)
      | throwError "a native endpoint prefix selected an undeclared original field"
    let index := prepared.field.sourceIndex
    if index >= frame.preceding.size then continue
    let some original := frame.preceding[index]?.bind id
      | throwError "a native endpoint prefix selected a formal proof slot"
    discard <| IO.ofExcept <| (graph.requiredOwners #[original]).mapError IO.userError
    let suffix := path.extract (parentPath.size + 1) path.size
    let some (selected, remaining) ← IO.ofExcept <|
        (graph.projectionFrontier original suffix).mapError IO.userError
      | CasCatalogue.throwStratum .noImplementation
          "the original prefix endpoint has no stored native field interface"
    unless remaining.isEmpty do
      CasCatalogue.throwStratum .noImplementation
        "the original prefix endpoint requires its retained field demand"
    if let some previous := result then
      unless sameReference previous selected do
        throwError "native endpoint prefixes disagree about an original field occurrence"
    result := some selected
  return result

private def checkDependencies (context : OpenContext)
    (inputProjections : Std.HashMap BindingId InputProjection)
    (supplied : Std.HashMap BindingId ValueBinding)
    (graph : ValueGraph)
    (graphFor : BindingId → MetaM ValueGraph) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin)
    (currentPrefixes : Array ResultFieldPrefix := #[])
    (pending : Option PendingResultProjection := none)
    (views : NativeTelescopeViews := #[])
    (fieldType : Option (ClosedTerm × ClosedTerm) := none)
    (selections : SourceSelectionScope Expr := {}) : MetaM Unit := do
  for index in origin.role.contextDependencies do
    let some dependency := origin.role.source.context.entries[index]?
      | throwError "a producing runtime dependency is outside its source telescope"
    let some original := origin.parameters[index]?
      | throwError "a producing runtime dependency is outside its complete reference table"
    if let some original := original then
      let some current := supplied[dependency.id]?
        | throwError (MessageData.tagged (missingValueTag dependency.id)
            m!"the runtime value is missing a retained dependent reference")
      unless sameReference original current do
        throwError "the runtime value has a different retained dependent reference"
  let mut inputs := #[]
  for binding in context.bindings do
    unless ← isProp (← inferType binding.expression) do inputs := inputs.push binding.id

  let captured := context.bindings.map (·.expression)
  let fixedContextReference := fun (expression : Expr) => do
    if expression.hasLooseBVars || expression.hasExprMVar || expression.hasLevelMVar ||
        (expression.abstract captured).hasFVar then return none
    dependencyReference context inputs (← context.close expression)
  let sameContextReference := fun (formal expected : Expr) => do
    let some original ← fixedContextReference formal | return false
    let some current ← fixedContextReference expected | return false
    return original == current

  let retainedInputs := inputs.filter (supplied.contains ·)
  let sourceView := fun (expression : Expr) =>
    context.inputProjectionSource expression retainedInputs
  let typeReferences := fun (expression : Expr) =>
    boundContextReferences (some graph) context supplied expression selections
  let expectedReferences ← typeReferences expected
  let typeHasBindings := fun (expression : Expr) => do
    return !(← typeReferences expression).isEmpty
  let mut checkedTypes := #[]
  for source in #[value.role.source, origin.role.source] ++
      value.dependencyRoles.map (·.source) ++
      value.telescopeInstantiations.map (·.source.source) do
    let originalType ← nativeTypeInContext context views source fieldType
    if !expectedReferences.isEmpty || (← typeHasBindings originalType) then
      checkedTypes := checkedTypes.push (source, originalType)
  let compareCaptured := fun
      (formalReferences expectedReferences : Array (Array DependencyStep × ValueBinding))
      (reduce : Bool) (formal current : Expr)
      (formalPosition expectedPosition : Option (Array DependencyStep)) => do
    let originalPrefix ← joinedTypePosition formalReferences formal formalPosition
    let currentPrefix ← joinedTypePosition expectedReferences current expectedPosition

    let hasDescendant := fun (references : Array (Array DependencyStep × ValueBinding))
        (position : Option (Array DependencyStep)) =>
      position.any fun position => references.any fun (selected, _) =>
        position.size < selected.size && position.toList.isPrefixOf selected.toList
    let reduce := reduce && !(hasDescendant formalReferences formalPosition ||
      hasDescendant expectedReferences expectedPosition)
    let originalSource ← if reduce then sourceView formal else pure formal
    let currentSource ← if reduce then sourceView current else pure current
    let originalBound ← boundProjection? context supplied originalSource
    let currentBound ← boundProjection? context supplied currentSource
    if originalBound.isNone && currentBound.isNone &&
        originalPrefix.isEmpty && currentPrefix.isEmpty then return none

    let currentHasMetadata := (currentSource.find? fun
      | .mdata .. => true
      | _ => false).isSome
    if !currentSource.hasFVar && !currentSource.hasLooseBVars &&
        !currentSource.hasExprMVar && !currentSource.hasLevelMVar &&
        !currentHasMetadata && currentPrefix.isEmpty then return none
    let left ←
      capturedTypeReferences context inputProjections retainedInputs supplied
        originalSource reduce
    let right ←
      capturedTypeReferences context inputProjections retainedInputs supplied
        currentSource reduce
    let left := left ++ originalPrefix
    let right := right ++ currentPrefix

    for references in #[left, right] do
      for first in references do
        for second in references do
          unless ← sameCapturedTypeReference graph first second do return some false
    if left.isEmpty || right.isEmpty then

      let unresolved := fun (expression : Expr) => expression.hasFVar
      let accepted := !(if left.isEmpty then unresolved originalSource else unresolved currentSource)
      return some accepted
    for first in left do
      for second in right do
        unless ← sameCapturedTypeReference graph first second do
          return some false
    return some true
  for (_, originalType) in checkedTypes do
      let (formalReferences, expectedReferences) ←
        joinedPrefixReferences context inputs graph sameContextReference
          originalType expected value currentPrefixes views origin.fieldPrefix
      let some _ ← dependencyTerms sameContextReference #[] originalType expected #[]
          (some (compareCaptured formalReferences expectedReferences)) (some sourceView)
        | throwError "the runtime value has a different marked source type dependency"
  if value.instantiations.all (·.precedingDependencies.isEmpty) then

    for current in currentPrefixes do
      let required := (current.view.map (·.precedingDependencies)).getD
        current.field.precedingDependencies
      for index in required do
        let some prepared := current.layout.fields[index]?
          | throwError "a dependent native field is outside its original prefix telescope"
        unless prepared.field.wireIndex.isSome do continue
        let source ← nativeSchemaInContext context views prepared.layout.source
        let mut references ← capturedTypeReferences context inputProjections retainedInputs
          supplied source true
        if let some nativePrefix := origin.fieldPrefix then
          if let some original ← nativePrefixEndpoint? nativePrefix context graph source then
            references := references.push (original, #[])
        if references.isEmpty then

          let structural ← sourceView source
          let mut needsSupplier := !(← boundSourceReferences (some graph) context supplied structural selections).isEmpty
          for position in ← computationalDependencies (context.bindings.map (·.expression)) structural do
            let some binding := context.bindings[position]?
              | throwError "a dependent native field lost its original source context"
            let declaration ← getFVarLocalDecl binding.expression
            if ← isProp declaration.type then continue
            if !(← boundSourceReferences (some graph) context supplied declaration.type selections).isEmpty then
              needsSupplier := true
            match declaration.value? true with
            | none => needsSupplier := true
            | some definition =>
              if !(← boundSourceReferences (some graph) context supplied definition selections).isEmpty then
                needsSupplier := true
          if needsSupplier then
            throwError "the dependent native field has no original supplier for its preceding source position"
          continue
        let actual ← match current.parent with
          | some parent => pure (parent, #[prepared.field.projection])
          | none => do
            let some preceding := current.preceding
              | throwError "a dependent native field lost its original prefix snapshot"
            unless preceding.size == current.field.sourceIndex do
              throwError "a dependent native field changed its complete prefix telescope"
            let some previous := preceding[index]?.bind id
              | throwError "a dependent native field lost a preceding computational slot"
            pure (previous, #[])
        for reference in references do
          unless ← sameCapturedTypeReference graph actual reference do
            throwError "the dependent native field has a different original preceding supplier"
    return ()
  let dependencies ← computationalDependencies (context.bindings.map (·.expression)) expected
  let boundDependencies ← boundSourceReferences (some graph) context supplied expected selections
  let mut references : Array (LocalBinding × (BindingId × Array Name)) := #[]
  for index in dependencies do
    let some dependency := context.bindings[index]?
      | throwError "a consuming runtime dependency is outside its current source telescope"
    if let some reference ← dependencyReference context inputs
        (← context.close dependency.expression) then
      references := references.push (dependency, reference)
  let hasDependencies := !references.isEmpty || !boundDependencies.isEmpty
  for instantiation in value.instantiations do
    if instantiation.precedingDependencies.isEmpty then continue
    let family ← nativeSchemaInContext context views instantiation.typeFamily
    let inspect := fun locals type => do
      unless locals.size ≥ instantiation.preceding.size do
        throwError "a consuming runtime dependency lost its complete native prefix"
      dependencyTerms sameContextReference locals type expected
    let terms ← if instantiation.view.isSome then lambdaTelescope family inspect
      else lambdaBoundedTelescope family instantiation.preceding.size inspect
    for index in instantiation.precedingDependencies do
      let some previous := instantiation.preceding[index]?
        | throwError "a consuming runtime dependency is outside its complete field prefix"
      if let some original := previous then
        unless (instantiation.association.layout.fields[index]?).isSome do
          throwError "a consuming runtime dependency is outside its source record"
        let some terms := terms
          | if !hasDependencies then continue
            throwError "the runtime value has an unresolved consuming dependent type"
        let selected := terms.filterMap fun term =>
          if term.index == index then some term.term else none
        if selected.isEmpty && hasDependencies then
          throwError "the runtime value has an unresolved consuming dependent slot"
        let mut unresolved : Option Expr := none
        for term in selected do
          let source ← dependencySource (← context.close term)
          let term ← source.inContext context
          if let some (id, path) ← boundProjection? context supplied term then
            let some parent := supplied[id]?
              | throwError "a consuming dependent type lost its original occurrence binder"
            let current ← if !currentPrefixes.isEmpty && pending.isSome then
                pendingDependency graph parent path pending
              else storedDependency graph parent path
            match current with
            | some current =>
              unless sameReference original current do
                throwError "the runtime value has a different marked dependent reference ({term})"
            | none =>
              unless hasDependencyAccess graph original parent path do
                throwError "the runtime value has an unresolved marked dependent reference ({term})"
            continue
          let some reference ← dependencyReference context inputs source
            | if term.hasFVar && unresolved.isNone then unresolved := some term
              continue

          let producerMatched ← match origin.fieldPrefix with
            | none => pure false
            | some nativePrefix => do
              let some retained ← nativePrefixEndpoint? nativePrefix context graph term
                | pure false
              unless sameReference original retained do
                throwError "the runtime value changed its original producing prefix reference"
              pure true
          let mut matched := producerMatched
          for (dependency, selectedReference) in references do
            if selectedReference != reference then continue
            matched := true
            let some current := supplied[dependency.id]?
              | if producerMatched then continue
                throwError (MessageData.tagged (missingValueTag dependency.id)
                  m!"the runtime value is missing a consuming dependent reference \
                    ({dependency.expression})")
            unless sameReference original current do
              throwError "the runtime value has a different consuming dependent reference \
                ({dependency.expression})"
          if !reference.2.isEmpty then
            let fieldMatched := matched
            for (dependency, selectedReference) in references do
              unless selectedReference == (reference.1, #[]) do continue
              let some parent := supplied[dependency.id]?
                | if fieldMatched then continue
                  throwError (MessageData.tagged (missingValueTag dependency.id)
                    m!"the runtime value is missing a consuming dependent reference \
                      ({dependency.expression})")
              let current ← if !currentPrefixes.isEmpty && pending.isSome then
                  pendingDependency (← graphFor dependency.id) parent reference.2 pending
                else storedDependency (← graphFor dependency.id) parent reference.2
              match current with
              | some current =>
                unless sameReference original current do
                  CasTools.Diagnostics.message m!"[dependent.identity] field={instantiation.field.projection} slot={index} source={repr reference.1} path={repr reference.2} parent={repr parent.value} parentAssociations={repr parent.associationIds} original={repr original.value} originalAssociations={repr original.associationIds} current={repr current.value} currentAssociations={repr current.associationIds}"

                  try
                    withoutModifyingState do
                      let rec shape (locals : Array Expr) (fuel : Nat) (expression : Expr) :
                          String :=
                        match fuel with
                        | 0 =>
                          match expression.getAppFn with
                          | .const name _ => s!"{name}"
                          | .fvar id => s!"fvar({id.name})"
                          | .forallE .. => "forall"
                          | .lam .. => "lambda"
                          | .mdata .. => "metadata"
                          | .proj name field _ => s!"projection({name},{field})"
                          | _ => "..."
                        | remaining + 1 =>
                          match expression with
                          | .fvar id =>
                            match locals.findIdx? (· == expression) with
                            | some position => s!"prefix({position})"
                            | none =>
                              match context.bindings.find? (·.expression == expression) with
                              | some binding => s!"context({reprStr binding.id})"
                              | none => s!"fvar({id.name})"
                          | .bvar position => s!"bound({position})"
                          | .sort levelValue => s!"sort({reprStr levelValue})"
                          | .const name levels => s!"constant({name},{levels.length})"
                          | .lit literal => s!"literal({reprStr literal})"
                          | .mvar id => s!"metavariable({id.name})"
                          | .mdata _ body => s!"metadata({shape locals remaining body})"
                          | .proj name field body =>
                            s!"projection({name},{field},{shape locals remaining body})"
                          | .app .. =>
                            let arguments := expression.getAppArgs
                            let shown := (arguments.extract 0 4).map
                              (shape locals remaining)
                            s!"application({shape locals remaining expression.getAppFn};arity={arguments.size};{String.intercalate "," shown.toList})"
                          | .forallE name domain body info =>
                            s!"forall({name},{reprStr info};{shape locals remaining domain};{shape locals remaining body})"
                          | .lam name domain body info =>
                            s!"lambda({name},{reprStr info};{shape locals remaining domain};{shape locals remaining body})"
                          | .letE name domain assigned body _ =>
                            s!"let({name};{shape locals remaining domain};{shape locals remaining assigned};{shape locals remaining body})"
                      CasTools.Diagnostics.message m!"[dependent.detail] candidate={repr value.value} associationCount={value.associationIds.size} associations={repr (value.associationIds.extract 0 8)} kind={repr value.role.kind} fieldView={repr instantiation.projectionPath} precedingCount={instantiation.preceding.size} required={repr instantiation.precedingDependencies} currentPrefixCount={currentPrefixes.size}"
                      let payloadKind (binding : ValueBinding) : Option String :=
                        (graph.find binding.value).map fun node =>
                          match node.payload.data with
                          | .portable _ => "portable"
                          | .product fields => s!"product({fields.size})"
                          | .container packet => s!"container(fields={packet.fields.map (·.size)})"
                          | .closure program captures =>
                            s!"closure({reprStr program};captures={captures.size})"
                          | .ownedToken _ _ captures => s!"owned(captures={captures.size})"
                      CasTools.Diagnostics.message m!"[dependent.detail] candidatePayload={payloadKind value} prefixPayload={payloadKind original} suppliedPayload={payloadKind current}"
                      CasTools.Diagnostics.message m!"[dependent.detail] candidateSource={shape #[] 4 value.role.source.expression}"
                      CasTools.Diagnostics.message m!"[dependent.detail] producingSource={shape #[] 4 origin.role.source.expression}"
                      CasTools.Diagnostics.message m!"[dependent.detail] prefixSource={shape #[] 4 original.role.source.expression}"
                      CasTools.Diagnostics.message m!"[dependent.detail] prefixProducer={(graph.find original.value).map (fun node => shape #[] 4 node.origin.role.source.expression)}"
                      CasTools.Diagnostics.message m!"[dependent.detail] suppliedSource={shape #[] 4 current.role.source.expression}"
                      CasTools.Diagnostics.message m!"[dependent.detail] fieldSource={shape #[] 4 instantiation.field.source.expression}"
                      CasTools.Diagnostics.message m!"[dependent.detail] recordSource={shape #[] 4 instantiation.association.layout.source.source.expression}"
                      CasTools.Diagnostics.message m!"[dependent.detail] expected={shape #[] 5 expected}"
                      CasTools.Diagnostics.message m!"[dependent.detail] selectedCount={selected.size} selected={repr ((selected.extract 0 6).map (shape #[] 5))}"
                      let inspectFailure := fun locals body => do
                        CasTools.Diagnostics.message m!"[dependent.detail] formalPrefixCount={locals.size} formalType={shape locals 5 body}"
                        for parameter in locals, position in [:locals.size] do
                          if position < instantiation.preceding.size && position < 8 then
                            CasTools.Diagnostics.message m!"[dependent.detail] prefixSlot={position} type={shape locals 4 (← inferType parameter)} original={repr (((instantiation.preceding[position]?).bind id).map (·.value))}"
                      if instantiation.view.isSome then
                        lambdaTelescope family inspectFailure
                      else
                        lambdaBoundedTelescope family instantiation.preceding.size inspectFailure
                  catch _ => pure ()
                  throwError (MessageData.tagged
                    `CasRuntime.RuntimeEnvironment.dependentReferenceMismatch
                    m!"the runtime value has a different consuming dependent reference ({term})")
              | none =>
                unless hasDependencyAccess graph original parent reference.2 do
                  throwError "the runtime value has an unresolved consuming dependent reference ({term})"
              matched := true
          unless matched do
            let some dependency := context.bindings.find? (·.id == reference.1)
              | throwError "a consuming dependent reference is outside its source telescope"
            throwError (MessageData.tagged (missingValueTag dependency.id)
              m!"the runtime value is missing a consuming dependent reference ({dependency.expression})")
        let mut covered := false
        for current in currentPrefixes do
          if let some (routes, complete) ← currentPrefixRoutes context inputs graph instantiation index current views then
            covered := covered || complete
            for (parent, path) in routes do
              match ← storedDependency graph parent path with
              | some actual =>
                unless sameReference original actual do
                  throwError "the runtime value has a different consuming dependent reference \
                    in its current result prefix; field={instantiation.field.projection}; \
                    slot={index}; currentField={current.field.projection}; \
                    path={reprStr path}; parent={reprStr parent.value}; \
                    original={reprStr original.value}; originalAssociations={reprStr original.associationIds}; \
                    actual={reprStr actual.value}; actualAssociations={reprStr actual.associationIds}; \
                    originalSource={(graph.find original.value).map (·.origin.role.source.expression)}; \
                    actualSource={(graph.find actual.value).map (·.origin.role.source.expression)}; \
                    originalRecord={instantiation.association.layout.source.source.expression}; \
                    currentRecord={current.layout.source.source.expression}; \
                    preceding={reprStr (instantiation.preceding.map (·.map (·.value)))}"
              | none =>
                unless hasDependencyAccess graph original parent path do
                  throwError "the runtime value has an unresolved consuming dependent reference \
                    in its current result prefix"
        if !covered then
          if let some term := unresolved then
            throwError "the runtime value has an unresolved consuming dependent reference ({term})"

private def sameAdmittedRole (left right : SourceLayout) : Bool :=
  left.address == right.address && left.kind == right.kind &&
    left.contextDependencies == right.contextDependencies &&
    sameAdmittedSource left.source right.source &&
    left.selectionBinding == right.selectionBinding &&
    SourceSelectionScope.exactlyMatches sameAdmittedSource left.selections right.selections

private def sameAdmittedValue (left right : ValueBinding) : Bool :=
  left.exactlyMatches right

private def sameAdmittedParameters (environment : RuntimeEnvironment)
    (parameters : Array RuntimeParameter) : Bool := Id.run do
  unless parameters.size == environment.bound.size do return false
  let mut seen : Std.HashSet BindingId := {}
  for parameter in parameters do
    if seen.contains parameter.source then return false
    let some original := environment.bound[parameter.source]? | return false
    unless sameAdmittedValue original parameter.value do return false
    seen := seen.insert parameter.source
  return true

private def nativeFieldPrefixes (nativePrefix : NativeFieldPrefix) : Array ResultFieldPrefix :=
  nativePrefix.frames.map fun frame =>
    ⟨none, frame.association.layout, frame.field, frame.view, some frame.preceding⟩

private def checkTransportedValue (context : OpenContext)
    (inputProjections : Std.HashMap BindingId InputProjection)
    (supplied : Std.HashMap BindingId ValueBinding)
    (graph : ValueGraph) (graphFor : BindingId → MetaM ValueGraph) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin)
    (currentPrefixes : Array ResultFieldPrefix := #[])
    (pending : Option PendingResultProjection := none)
    (fieldPrefix : Option NativeFieldPrefix := none)
    (selections : SourceSelectionScope Expr := {})
    (expectedRole : Option SourceLayout := none) : MetaM Unit := do
  if value.telescopeInstantiations.isEmpty && origin.fieldPrefix.isNone && fieldPrefix.isNone then
    checkDependencies context inputProjections supplied graph graphFor expected value origin
      currentPrefixes pending (selections := selections)
    return
  withNativeTelescopeViews context supplied graph value fun context joined views => do
    let check := fun (context : OpenContext) (joined : Std.HashMap BindingId ValueBinding)
        (fieldType : Option (ClosedTerm × ClosedTerm)) (expected : Expr) => do
      let mut expected := expected
      for (transport, replacement) in views do
        expected ← transport.instantiateSchema context expected replacement
      checkNativeType context expected value origin views fieldType
      let positions ← context.inputProjections
      let graphFor := fun id =>
        if supplied.contains id then graphFor id else pure graph
      checkDependencies context positions joined graph graphFor expected value origin
        currentPrefixes pending views fieldType selections
    let withExpected := fun (context : OpenContext)
        (joined : Std.HashMap BindingId ValueBinding)
        (fieldType : Option (ClosedTerm × ClosedTerm)) (producingType : Option Expr) => do
      match fieldPrefix with
      | none => do
        let expected ← if expectedRole.any (sameAdmittedRole · origin.role) then do
            match producingType with
            | none => pure expected
            | some type => do
              unless ← context.withOriginalSources #[expected, type]
                  (fun types => isDefEq types[0]! types[1]!) do
                throwError "the original native field changed its complete declared type"
              pure type
          else pure expected
        check context joined fieldType expected
      | some nativePrefix =>
        nativePrefix.withBoundType context graph joined fun context type joined => do
          unless ← context.withOriginalSources #[expected, type]
              (fun types => isDefEq types[0]! types[1]!) do
            throwError "the consuming field prefix changed its original native type"
          check context joined fieldType type
    match origin.fieldPrefix with
    | none => withExpected context joined none none
    | some nativePrefix =>
      nativePrefix.withBoundType context graph joined fun context type joined => do
        withExpected context joined (some (origin.role.source, ← context.close type)) (some type)

opaque RuntimeEnvironment.capture (worker : String) (context : OpenContext)
    (parameters : Array RuntimeParameter)
    (sourceGraph : Option ValueGraph := none)
    (validatedEnvironment : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {}) : MetaM RuntimeEnvironment := do
  if worker.isEmpty then throwError "runtime association requires an actual worker identity"
  let mut openSelections := selections
  for parameter in parameters do
    openSelections ← SourceSelectionScope.merge openSelections
      (← parameter.value.role.selections.inContext context)
    if parameter.value.admittedInterface?.isSome then
      openSelections ← SourceSelectionScope.merge openSelections
        (← parameter.value.nativeRole.selections.inContext context)
  if let some validated := validatedEnvironment then
    if validated.context.exactlyMatches context.telescope then
      openSelections ← SourceSelectionScope.merge openSelections (← validated.selections.inContext context)
  for (id, _) in openSelections do
    unless context.bindings.any (·.id == id) do
      throwError "a runtime selection is outside its complete typed context"
  let selections ← openSelections.close context
  if let some validated := validatedEnvironment then
    if validated.worker == worker && validated.context.exactlyMatches context.telescope &&
        sameAdmittedParameters validated parameters then
      if let some graph := sourceGraph then
        unless graph.worker == worker do
          throwError "source preparation belongs to a different worker"
        let current ← ContextTelescope.capture context.bindings
        if validated.context.exactlyMatches current.telescope then
          validated.context.ensureDeclarations
          return { (← validated.withGraph (some graph)) with selections }
  let inputProjections ← context.inputProjections
  if let some graph := sourceGraph then
    unless graph.worker == worker do
      throwError "source preparation belongs to a different worker"
    discard <| IO.ofExcept <|
      (graph.requiredOwners (parameters.map (·.value))).mapError IO.userError
  let mut supplied : Std.HashMap BindingId ValueBinding := {}
  for parameter in parameters do
    if supplied.contains parameter.source then
      throwError "a source binder has duplicate runtime associations"
    unless parameter.value.value.worker == worker do
      throwError "a runtime source binding belongs to a different worker"
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a runtime association names a source binder outside the complete telescope"
    let expected ← inferType source.expression
    if ← isProp expected then
      throwError "a source proof has no runtime value association"
    if parameter.value.telescopeInstantiations.isEmpty && parameter.origin.fieldPrefix.isNone then
      checkNativeType context expected parameter.value parameter.origin
    supplied := supplied.insert parameter.source parameter.value

  let originalScope := context.telescope.entries.map fun entry => supplied[entry.id]?
  for source in context.bindings do
    let some original := supplied[source.id]? | continue
    let role ← SourceLayout.ofTerm (← context.close source.expression) selections
      original.role.selectionBinding
    let dependencies ← boundTypeReferences sourceGraph role.source supplied role.selections
    let .ok value := original.withRole role dependencies (some originalScope)
      | throwError "the source binder has no computational runtime role"
    supplied := supplied.insert source.id value
  for parameter in parameters do
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a consuming runtime binding is outside its source telescope"
    let graphFor := fun id => do
      let some parameter := parameters.find? (·.source == id)
        | throwError "a retained dependent reference lost its supplying graph"
      pure parameter.graph
    checkTransportedValue context inputProjections supplied
      (sourceGraph.getD parameter.graph) graphFor
      (← inferType source.expression) parameter.value parameter.origin
      (selections := ← selections.inContext context)

  for parameter in parameters do
    let native := parameter.value.nativeInterface
    if native.role.kind == .function || native.role.kind == .record then
      let some admitted := supplied[parameter.source]?
        | throwError "an admitted input lost its exact original source binding"
      supplied := supplied.insert parameter.source (admitted.attachNativeInterface native)
  return ⟨worker, context.telescope, supplied, inputProjections, sourceGraph, selections⟩

opaque RuntimeEnvironment.captureBound (worker : String) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (graph : ValueGraph)
    (validated : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {}) : MetaM RuntimeEnvironment := do
  let mut parameters := #[]
  for binding in context.bindings do
    if let some value := bound[binding.id]? then
      parameters := parameters.push (← IO.ofExcept <|
        (RuntimeParameter.ofValue graph binding.id value).mapError IO.userError)
  unless parameters.size == bound.size do
    throwError "a runtime occurrence table contains a binding outside its complete context"
  RuntimeEnvironment.capture worker context parameters (some graph) validated selections

private def withRetainedContext (source : ContextTelescope)
    (original : Std.HashMap BindingId ValueBinding) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → MetaM α) : MetaM α :=
  source.withInContext context fun context => do
    let mut bound := bound
    for entry in source.entries do
      let some retained := original[entry.id]? | continue
      match bound[entry.id]? with
      | none => bound := bound.insert entry.id retained
      | some current =>
        if retainsReference retained current then pure ()
        else if retainsReference current retained then
          bound := bound.insert entry.id retained
        else throwError (MessageData.tagged `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch
          m!"runtime context import changed an original source occurrence")
    action context bound

opaque RuntimeEnvironment.withContext (environment : RuntimeEnvironment) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → MetaM α) : MetaM α :=
  withRetainedContext environment.context environment.bound context bound action

def withBindingContext [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (graph : ValueGraph) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (binding : ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → m α) : m α :=
  controlAt MetaM fun run => do
    let rec visit (remaining : List ValueBinding) (context : OpenContext)
        (bound : Std.HashMap BindingId ValueBinding) : MetaM _ := do
      match remaining with
      | [] => run (action context bound)
      | current :: remaining =>
        let (source, parameters) ← IO.ofExcept <|
          (graph.bindingContext current).mapError IO.userError
        unless source.entries.size == parameters.size do
          throwError "a retained value lost its complete displayed source context"
        let mut original : Std.HashMap BindingId ValueBinding := {}
        for (entry, value) in source.entries.zip parameters do
          if let some value := value then original := original.insert entry.id value
        withRetainedContext source original context bound fun context bound =>
          visit remaining context bound
    visit (binding :: binding.admittedInterface?.toList) context bound

partial def RuntimeEnvironment.hasRetainedSource (environment : RuntimeEnvironment)
    (context : OpenContext) (specified : Expr) : MetaM Bool := do
  if let .mdata _ body := specified then
    return ← environment.hasRetainedSource context body
  if let .letE _ _ value body _ := specified then
    return ← environment.hasRetainedSource context (body.instantiate1 value)
  if specified.isFVar then
    let some binding := context.bindings.find? (·.expression == specified)
      | throwError "the source argument is outside the complete runtime telescope"
    match environment.lookup binding.id with
    | .ok (some _) => return true
    | .ok none =>
      if binding.role == .selectedStructure && !environment.selections.contains binding.id then
        throwError "the source lost its retained typed selection"
      if binding.role == .result then
        throwError "the source lost a retained runtime binding"
      if let some definition := (← specified.fvarId!.getDecl).value? then
        return ← environment.hasRetainedSource context definition
      return false
    | .error reason => throwError "the source argument is outside its telescope: {reason}"
  if let some projection ← SourceProjection.ofExpr? specified then
    return ← environment.hasRetainedSource context projection.parent
  return false

private partial def RuntimeEnvironment.retainsSourceReference (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph)
    (specified : Expr) (value : ValueBinding) (requireAnchor : Bool := false)
    (anchored : Bool := false) (fieldPrefix : Option NativeFieldPrefix := none) : MetaM Bool := do
  if let .mdata _ body := specified then
    return ← environment.retainsSourceReference context graph body value requireAnchor anchored fieldPrefix
  if let some nativePrefix := fieldPrefix then
    if let some selected ← nativePrefixEndpoint? nativePrefix context graph specified then
      return retainsReference selected value
  if specified.isFVar then
    let some binding := context.bindings.find? (·.expression == specified)
      | throwError "the source argument is outside the complete runtime telescope"
    match environment.lookup binding.id with
    | .ok (some retained) => return retainsReference retained value
    | .ok none =>
      let some definition := (← specified.fvarId!.getDecl).value?
        | throwError "the source argument has no retained runtime binding"
      return ← environment.retainsSourceReference context graph definition value requireAnchor anchored fieldPrefix
    | .error reason => throwError "the source argument is outside its telescope: {reason}"
  let projection ← SourceProjection.ofExpr? specified
  let runtimeProjection ← match projection with
    | none => pure false
    | some projection =>
      if !projection.info.fromClass then pure true
      else environment.hasRetainedSource context projection.parent
  if runtimeProjection then
    let some node := graph.find value.value
      | throwError "the runtime argument is outside the visible graph"
    let mut selected := value.projectionAccesses
    if let some parent := node.origin.access then
      selected := selected.push (parent, node.origin.accessPath)
    for (parent, path) in selected do
      if path.isEmpty then continue
      let mut original := specified
      let mut matchedPath := true
      for projection in path.reverse do
        let some step ← SourceProjection.ofExpr? original
          | matchedPath := false; break
        unless step.declaration == projection do
          matchedPath := false
          break
        original := step.parent
      if matchedPath then

        if ← environment.retainsSourceReference context graph original parent true anchored fieldPrefix then
          return true

    if !requireAnchor && value.role.kind == .typeValue &&
        node.origin.role.kind == .typeValue then
      if let some projection := projection then
        unless ← environment.hasRetainedSource context projection.parent do
          let original ← value.role.source.inContext context
          let producing ← node.origin.role.source.inContext context
          if specified == original && specified == producing then return true
    trace[cas.environment] "unmatched projection: {repr (projection.map (·.declaration))}; parent retained: {← environment.hasRetainedSource context (projection.map (·.parent) |>.getD specified)}; access paths: {repr (selected.map (fun (parent, path) => (parent.value, path)))}"
    return false
  if requireAnchor && !anchored then return false
  let original ← value.role.source.inContext context
  let some node := graph.find value.value
    | throwError "the runtime argument is outside the visible graph"
  let producing ← node.origin.role.source.inContext context
  return original.equal specified && producing.equal specified

opaque RuntimeEnvironment.checkArgument (environment : RuntimeEnvironment) (source : ClosedTerm)
    (argument : RuntimeArgument) : MetaM ValueBinding := do
  unless argument.value.value.worker == environment.worker do
    throwError "the runtime argument belongs to a different worker"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let specified ← source.inContext context
    let expected ← inferType specified
    let selections ← SourceSelectionScope.merge (← environment.selections.inContext context)
      (← argument.value.role.selections.inContext context)
    if ← isProp expected then throwError "a formal proof argument has no runtime value binding"
    if argument.value.telescopeInstantiations.isEmpty && argument.origin.fieldPrefix.isNone then
      checkNativeType context expected argument.value argument.origin
    checkTransportedValue context environment.inputProjections environment.bound
      argument.graph (fun _ => pure argument.graph)
      expected argument.value argument.origin (selections := selections)
    unless ← environment.retainsSourceReference context argument.graph
        specified argument.value do
      trace[cas.environment] "argument {argument.index}: {specified}; retained source {← argument.value.role.source.inContext context}"
      throwError (MessageData.tagged `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch
        "the runtime argument does not retain its specified source value")
    let mut selectionBinding := argument.value.role.selectionBinding
    if let .fvar localId := specified then
      let some binding := context.bindings.find? (·.expression.fvarId! == localId)
        | throwError "the specified source argument is outside its complete native context"
      if selections.contains binding.id then
        selectionBinding := some binding.id
    let role ← SourceLayout.ofTerm (← context.close specified) (← selections.close context)
      selectionBinding
    let dependencies ← boundTypeReferences (some argument.graph) role.source environment.bound role.selections
    let .ok value := argument.value.withRole role dependencies (some environment.values)
      | throwError "the source argument has no computational runtime role"
    let native := argument.value.nativeInterface
    if native.role.kind == .function || native.role.kind == .record then
      return value.attachNativeInterface native
    return value

private partial def checkResultValue (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding)
    (currentPrefixes : Array ResultFieldPrefix := #[])
    (pending : Option PendingResultProjection := none)
    (fieldPrefix : Option NativeFieldPrefix := none)
    (admitted : Array Nat → ValueBinding → MetaM Unit := fun _ _ => pure ())
    (wirePath : Array Nat := #[]) : MetaM (CandidateResponse source) := do
  unless graph.worker == environment.worker do
    throwError "the prepared result belongs to a different worker"
  let .ok _ := graph.requiredOwners (environment.references.push value)
    | throwError "the prepared result or its runtime context is outside the visible graph"
  let some node := graph.find value.value
    | throwError "the prepared result is outside the visible graph"
  let checkSelections : ContextTelescope → SourceSelectionScope ClosedTerm → MetaM Unit :=
    fun sourceContext selections => sourceContext.withOpenContext fun context => do
      checkSelectedSourceContext context (← selections.inContext context)

  checkSelections environment.context environment.selections
  checkSelections source.source.context source.selections
  for retained in (value :: value.admittedInterface?.toList) do
    checkSelections retained.role.source.context retained.role.selections
  environment.context.withOpenContext fun context => do
    withBindingContext graph context environment.bound value fun context imported => do

      let mut bound := imported
      for entry in environment.context.entries do
        bound := match environment.bound[entry.id]? with
          | some original => bound.insert entry.id original
          | none => bound.erase entry.id
      let mut retainedSelections ← SourceSelectionScope.merge
        (← environment.selections.inContext context) (← source.selections.inContext context)
      for retained in (value :: value.admittedInterface?.toList) do
        retainedSelections ← SourceSelectionScope.merge retainedSelections
          (← retained.role.selections.inContext context)
      checkSelectedSourceContext context retainedSelections
      let positions ← context.inputProjections
      let expected ← inferType (← source.source.inContext context)
      if value.telescopeInstantiations.isEmpty && node.origin.fieldPrefix.isNone && fieldPrefix.isNone then
        checkNativeType context expected value node.origin
      checkTransportedValue context positions bound graph
        (fun _ => pure graph) expected value node.origin currentPrefixes pending fieldPrefix retainedSelections
        (expectedRole := some source)
      let capturePrefix := match fieldPrefix with
        | some nativePrefix => some nativePrefix
        | none => if sameAdmittedRole source node.origin.role then node.origin.fieldPrefix else none
      let dependencies ← match capturePrefix with
        | none => boundTypeReferences (some graph) source.source environment.bound source.selections
        | some nativePrefix =>
          nativePrefix.withBoundType context graph environment.bound fun context type bound => do
            boundContextReferences (some graph) context bound type
              (← source.selections.inContext context)
      let retainedInterface := value.admittedInterface?
      let value ← IO.ofExcept <|
        (value.withRole source dependencies
          (some (source.source.context.entries.map fun entry => environment.bound[entry.id]?))).mapError IO.userError
      let value := match retainedInterface with
        | none => value
        | some native => value.attachNativeInterface native
      let candidate ← match CandidateResponse.ofValue source graph value with
        | .ok candidate => pure candidate
        | .error reason =>
          throwError "the prepared result has an incompatible computational interface: {reason} \
            at {← source.source.inContext context}"
      let stored := node.payload.data.storedFields?.isSome
      if source.kind == .record && stored then
        let layout ← RecordLayout.ofSource source
        for prepared in layout.fields do
          if let some index := prepared.field.wireIndex then
            let field ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
            let prefixes ← currentPrefixes.mapM (·.descend prepared.field.projection)
            let fieldPrefix ← fieldPrefix.mapM (·.descend prepared.field.projection)
            discard <| checkResultValue environment graph prepared.layout field
              (prefixes.push ⟨some candidate.root, layout, prepared.field, none, none⟩)
              pending fieldPrefix admitted (wirePath.push index)
      admitted wirePath candidate.root
      return candidate

opaque RuntimeEnvironment.checkResult (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding)
    (fieldPrefix : Option NativeFieldPrefix := none)
    (admitted : Array Nat → ValueBinding → MetaM Unit := fun _ _ => pure ()) :
    MetaM (CandidateResponse source) :=
  checkResultValue environment graph source value
    ((fieldPrefix.map nativeFieldPrefixes).getD #[]) none fieldPrefix admitted

private def projectionPrefixes (graph : ValueGraph) (operand : ValueBinding)
    (path : Array Name) : MetaM (Array ResultFieldPrefix × FieldLayout) := do
  let mut parent := operand
  let mut parentSource := operand.nativeRole
  let mut prefixes : Array ResultFieldPrefix := #[]
  let mut selectedField : Option FieldLayout := none
  for projection in path, index in [:path.size] do
    let layout ← RecordLayout.ofSource parentSource
    let some declared := layout.fields.find? (·.field.projection == projection)
      | throwError "the pending projection is outside its original native parent"
    unless declared.field.wireIndex.isSome do
      throwError "a composed projection passed through a proof field"
    let some actualField := parent.nativeRole.fields.find? (·.projection == projection)
      | throwError "the retained projection parent lost its declared field"
    unless actualField.sourceIndex == declared.field.sourceIndex &&
        actualField.wireIndex == declared.field.wireIndex do
      throwError "the retained projection parent changed its native field position"
    prefixes ← prefixes.mapM (·.descend projection)
    prefixes := prefixes.push ⟨some parent, layout, declared.field, none, none⟩
    selectedField := some declared.field
    if index + 1 < path.size then
      let selected ← IO.ofExcept <|
        (graph.projectionFrontier parent #[projection]).mapError IO.userError
      let some (selected, remaining) := selected
        | throwError "a composed projection lost its retained intermediate parent"
      unless remaining.isEmpty do
        throwError "a composed projection cannot manufacture an intermediate parent"
      parent := selected
      parentSource := declared.layout
  let some field := selectedField
    | throwError "a retained projection requires its original native field path"
  return (prefixes, field)

private partial def retainedOperandPrefixes (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (operand : ValueBinding) :
    MetaM (Array ResultFieldPrefix × Option NativeFieldPrefix) := do
  let selected ← IO.ofExcept <| (graph.projectionSelection operand).mapError IO.userError
  let some (originalSource, parent, path) := selected
    | do
      let some node := graph.find operand.value
        | throwError "the retained operand lost its original producing value"
      let some nativePrefix := node.origin.fieldPrefix | return (#[], none)
      discard <| IO.ofExcept <|
        node.origin.checkFieldPrefix.mapError IO.userError

      let originalMatches ← environment.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        return (← source.source.inContext context).equal
          (← node.origin.role.source.inContext context)
      unless originalMatches do return (#[], none)
      return (nativeFieldPrefixes nativePrefix, some nativePrefix)
  let (prefixes, field) ← projectionPrefixes graph parent path
  let nativeSource ← field.toLayout
  let originalMatches ← originalSource.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let mut previous : Option Nat := none
    for entry in nativeSource.source.context.entries do
      let some index := bindings.findIdx? (·.id == entry.id) | return false
      if let some prior := previous then
        if index ≤ prior then return false
      previous := some index
    return (← originalSource.source.inContext context) ==
      (← nativeSource.source.inContext context)
  unless originalMatches do return (#[], none)
  let authentic ← environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let mut inputs := #[]
    for binding in bindings do
      unless ← isProp (← inferType binding.expression) do inputs := inputs.push binding.id
    if let some (id, aliasPath) ← dependencyReference context inputs source.source then
      let some supplied := environment.bound[id]? | return false
      match ← storedDependency graph supplied aliasPath with
      | some actual => return retainsReference actual operand
      | none => return false
    let stated ← source.source.inContext context
    let original ← originalSource.source.inContext context
    return stated == original
  unless authentic do return (#[], none)
  let retained ← IO.ofExcept <|
    (graph.projectionFrontier parent path).mapError IO.userError
  let some (baseline, remaining) := retained
    | throwError "the retained operand lost its original selected field"
  unless remaining.isEmpty && retainsReference baseline operand do
    throwError "the retained operand changed its original selected field"
  let (inherited, nativePrefix) ← retainedOperandPrefixes environment graph parent.nativeRole parent
  let mut inherited := inherited
  let mut nativePrefix := nativePrefix
  for projection in path do
    inherited ← inherited.mapM (·.descend projection)
    nativePrefix ← nativePrefix.mapM (·.descend projection)
  return (inherited ++ prefixes, nativePrefix)

opaque RuntimeEnvironment.checkProjectionResult (environment : RuntimeEnvironment)
    (graph : ValueGraph) (source : SourceLayout) (value operand : ValueBinding)
    (field : FieldLayout)
    (admitted : Array Nat → ValueBinding → MetaM Unit := fun _ _ => pure ()) :
    MetaM (CandidateResponse source) := do
  let path ← operand.nativeRole.projectionPathTo source
  unless !path.isEmpty && path.back? == some field.projection do
    throwError "the pending projection changed its exact native source field"
  let (current, declared) ← projectionPrefixes graph operand path
  unless field.sourceIndex == declared.sourceIndex && field.projection == declared.projection do
    throwError "the pending projection changed its original native field"
  let (prefixes, nativePrefix) ← retainedOperandPrefixes environment graph operand.nativeRole operand
  let mut prefixes := prefixes
  let mut nativePrefix := nativePrefix
  for projection in path do
    prefixes ← prefixes.mapM (·.descend projection)
    nativePrefix ← nativePrefix.mapM (·.descend projection)
  prefixes := prefixes ++ current
  let pending : Option PendingResultProjection ← if path.size > 1 then do
      let selected ← IO.ofExcept <|
        (graph.projectionFrontier operand path).mapError IO.userError
      let some (retained, remaining) := selected
        | throwError "a composed projection lost its complete stored source path"
      unless remaining.isEmpty && retainsReference retained value do
        throwError "a composed projection changed its retained field reference"
      pure none
    else do
      if let some retained ← pendingDependency graph operand #[field.projection] none then
        unless retainsReference retained value do
          throwError "the projection changed its retained field reference"
      pure (some ⟨operand, field.projection, value⟩)

  checkResultValue environment graph source value prefixes pending nativePrefix admitted

opaque RuntimeEnvironment.checkOperand (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (operand : ValueBinding) : MetaM (CandidateResponse source) := do
  let (prefixes, nativePrefix) ← retainedOperandPrefixes environment graph source operand
  checkResultValue environment graph source operand prefixes none nativePrefix

opaque RuntimeEnvironment.projectionFieldPrefix (environment : RuntimeEnvironment)
    (graph : ValueGraph) (operand : ValueBinding) (source : SourceLayout) :
    MetaM (Option NativeFieldPrefix) := do
  let path ← operand.nativeRole.projectionPathTo source
  unless !path.isEmpty do
    throwError "an inherited native field prefix requires its original projection path"
  let (_, nativePrefix) ← retainedOperandPrefixes environment graph operand.nativeRole operand
  let mut nativePrefix := nativePrefix
  for projection in path do
    nativePrefix ← nativePrefix.mapM (·.descend projection)
  return nativePrefix

opaque RuntimeEnvironment.origin (environment : RuntimeEnvironment)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (role : SourceLayout) (fieldPrefix : Option NativeFieldPrefix := none)
    (access : Option ValueBinding := none) (accessPath : Array Name := #[]) :
    MetaM ValueOrigin := do
  unless program.worker == environment.worker && occurrence.worker == environment.worker do
    throwError "the producing runtime context belongs to a different worker"
  let role ← if role.source.context.exactlyMatches environment.context then pure role
    else environment.context.withOpenContext fun context => do
      role.inContext context
  let role ← role.withSelections environment.selections
  if let some parent := access then
    unless !accessPath.isEmpty && (← parent.nativeRole.projectionPathTo role) == accessPath do
      throwError "a producing access changed its actual parent's native projection path"
  else unless accessPath.isEmpty do
    throwError "a producing access path has no original actual parent"
  let dependencies ← match fieldPrefix with
    | none => SourceDependencyCapture.capture environment.sourceGraph role environment.bound
    | some nativePrefix => do
      let some graph := environment.sourceGraph
        | throwError "a native field producer requires its actual source graph"
      match access with
      | some parent =>
        SourceDependencyCapture.captureProjection graph role environment.bound
          nativePrefix parent accessPath
      | none => do
        discard <| IO.ofExcept <|
          (nativePrefix.requireOrigin program occurrence role).mapError IO.userError
        SourceDependencyCapture.capturePrefix graph role environment.bound nativePrefix
  return {
    program, occurrence, role, parameters := environment.values
    sourceDependencies := some dependencies, fieldPrefix := dependencies.fieldPrefix,
    access, accessPath }

opaque NativeFieldPrefix.checkResult (nativePrefix : NativeFieldPrefix)
    (environment : RuntimeEnvironment) (graph : ValueGraph) (value : ValueBinding) :
    MetaM (CandidateResponse nativePrefix.native) :=
  checkResultValue environment graph nativePrefix.native value (nativeFieldPrefixes nativePrefix) none
    (some nativePrefix)

opaque NativeFieldPrefix.checkEndpoint (nativePrefix : NativeFieldPrefix)
    (environment : RuntimeEnvironment) (context : OpenContext) (graph : ValueGraph)
    (expected : Expr) (value : ValueBinding) : MetaM Bool := do
  let some selected ← nativePrefixEndpoint? nativePrefix context graph expected | return false
  unless retainsReference selected value do
    throwError "the native field endpoint changed its original preceding occurrence"
  discard <| IO.ofExcept <| (graph.requiredOwners #[value]).mapError IO.userError
  let some node := graph.find value.value
    | throwError "the native field endpoint is outside the visible graph"
  let type ← inferType expected
  if value.telescopeInstantiations.isEmpty && node.origin.fieldPrefix.isNone then
    checkNativeType context type value node.origin
  checkTransportedValue context environment.inputProjections environment.bound graph
    (fun _ => pure graph) type value node.origin
    (selections := ← environment.selections.inContext context)
  unless ← environment.retainsSourceReference context graph expected value
      (fieldPrefix := some nativePrefix) do
    throwError "the native field endpoint lost its original source or retained mark"
  return true

opaque NativeFieldPrefix.attachOrigin (nativePrefix : NativeFieldPrefix) (origin : ValueOrigin)
    (graph : ValueGraph) : MetaM ValueOrigin := do
  discard <| IO.ofExcept <|
    (nativePrefix.requireOrigin origin.program origin.occurrence origin.role).mapError IO.userError
  let nativePrefix ← match origin.fieldPrefix with
    | none => pure nativePrefix
    | some original => original.join nativePrefix
  discard <| IO.ofExcept <| (graph.requiredOwners nativePrefix.references).mapError IO.userError
  return { origin with fieldPrefix := some nativePrefix }

opaque NativeFieldPrefix.origin (nativePrefix : NativeFieldPrefix) (environment : RuntimeEnvironment)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence) (graph : ValueGraph) :
    MetaM ValueOrigin := do
  let environment ← environment.withGraph (some graph)
  environment.origin program occurrence nativePrefix.native (fieldPrefix := some nativePrefix)

def ValueBinding.selectedSource (value : ValueBinding) (context : OpenContext) : MetaM Expr := do
  let some id := value.role.selectionBinding | return ← value.role.source.inContext context
  let selections ← value.role.selections.inContext context
  let some selected := selections[id]?
    | throwError "the displayed role lost its original selected source binding"
  unless selected.formalBindings.isEmpty do
    throwError "the displayed role retains an unapplied source selection template"
  let some binding := context.bindings.find? (·.id == id)
    | throwError "the displayed role's selected source is outside its complete context"
  let original ← value.role.source.inContext context
  context.withOriginalSources #[binding.expression, original, selected.value] fun sources => do
    let expected ← inferType sources[0]!
    unless ← isDefEq expected (← inferType sources[1]!) <&&>
        isDefEq expected (← inferType sources[2]!) do
      throwError "the displayed role changed its selected source's complete native type"
  return binding.expression

end CasRuntime
