module

public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private structure OperationDomain where
  category : NativeSourceCategory
  value : Expr
  comparison : Option Expr
  originEvidence : Array Expr

private def refinementDomain (state : SemanticState) (entry : ObjectEntry) (domain : Expr) :
    TermElabM (Option OperationDomain) := do
  let some refinement := entry.refines | return none
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration refinement.identification
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let comparison ← applyObjectParameters entry.id.raw refinement.identification arguments
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the source operation refinement requires its actual isomorphism"
  checkRegisteredDomains domain type.getAppArgs[3]!
  unless ← isDefEq type.getAppArgs[3]! domain do return none
  for argument in arguments, info in infos do
    if info.isInstImplicit && (← instantiateMVars argument).isMVar then
      let some instanceValue ← synthInstance? (← inferType argument) | return none
      unless ← isDefEq argument instanceValue do return none
  let arguments ← arguments.mapM instantiateMVars
  if arguments.any (fun argument => argument.hasMVar || argument.hasLevelMVar) then return none
  unless arguments.isEmpty do
    throwUnsupportedSource
      "operation refinement coherence requires the whole declared parameter families"
  let #[category] := state.categories.filter (·.id == entry.category)
    | throwError "the source refinement requires one complete category"
  let (bundle, value) ← registeredExpressions (.inl entry) category fun function _ => do
    unless ← isDefEq (← inferType function) (← inferType declaration) do
      throwError "the source refinement changed its complete declaration parameters"
    return mkAppN function arguments
  let selection ← objectCarrierSelection entry bundle value
  return some ⟨⟨.object, category.expression, bundle, selection⟩, value,
    some (← instantiateMVars comparison), #[]⟩

private def scopedOperationDomains
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (expected : Expr) (hints : Array Expr) : TermElabM (Array OperationDomain) := do
  return (← sourceElementOwners categoryOf expected hints).map fun owner =>
    ⟨owner.category, owner.value, none, #[owner.evidence]⟩

-- Selected source objects precede default literal selectors. Every matching original
-- structure is retained; native carrier coincidence does not identify their dictionaries.
private def operationDomains
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory)) (expected : Expr)
    (contextual : Option Expr) (hints : Array Expr) :
    TermElabM (Array OperationDomain) := do
  let state ← semanticState
  let (domain, entries) ← registeredDomain expected
  if entries.isEmpty then
    let hints := contextual.toArray ++ hints
    let selected ← scopedOperationDomains categoryOf expected hints
    if !selected.isEmpty then return selected
  let bases := entries
  let bases ← if bases.isEmpty then sourceLiteralDomains domain else pure bases
  let mut domains := #[]
  for entry in state.objects do
    unless entry.refines.any (fun refinement => bases.any (·.id == refinement.base)) do continue
    if let some candidate ← refinementDomain state entry expected then
      domains := domains.push candidate
  return domains

private def operationRoutes (source : CategoryExpr) (name : String) :
    TermElabM (Array Route) := do
  let routes ← SourceRoutes.forOperation source name
  let some candidates ← routes.finiteRoutes
    | throwUnsupportedSource "the operation route family requires its supplied uniform comparison"
  return candidates

private structure OperationRoot where
  domain : OperationDomain
  domains : Array OperationDomain
  routes : Array Route
  images : Array (Array Route)

-- A common supplied refinement gives one generic comparison context. Selection uses
-- symbolic structural incidence only; operation values and operands are not inspected.
private def operationRoot (domains : Array OperationDomain) (name : String) :
    TermElabM OperationRoot := do
  let mut active := #[]
  for domain in domains do
    let routes ← operationRoutes domain.category.expression name
    if !routes.isEmpty then active := active.push (domain, routes)
  if active.isEmpty then throwError "the source domain has no binding for operation {name}"
  let mut roots := #[]
  for (domain, routes) in active do
    let mut images := #[]
    for (target, _) in active do
      let family ← SourceRoutes.forOwner domain.category.expression target.category.expression
      let some candidates ← family.finiteRoutes
        | throwUnsupportedSource "the source refinement cone requires its uniform comparison"
      images := images.push candidates
    if images.all (! ·.isEmpty) then roots := roots.push (domain, routes, images)
  let #[(domain, routes, images)] := roots
    | throwSemanticAmbiguity "the source operation requires its selected common refinement"
  return ⟨domain, active.map (·.1), routes, images⟩

private structure NativeOperationFamily where
  route : Route
  binding : OperationEntry
  value : Expr

/-- A native operation whose whole source families have been checked before specialization. -/
structure NativeSourceOperation where
  value : Expr
  arity : Nat
  comparison : Option Expr
  inputTransports : Array Bool
  outputTransport : Bool

private partial def operationInputs (type : Expr) (arity : Nat) : MetaM (Array Expr) := do
  if arity == 1 then return #[type]
  unless arity > 1 do throwError "a source element operation requires its operand domain"
  let pair ← whnf type
  unless pair.isAppOfArity ``Prod 2 do
    throwUnsupportedSource "the source operation requires its declared product mediation"
  return #[pair.getAppArgs[0]!] ++ (← operationInputs pair.getAppArgs[1]! (arity - 1))

/-- Resolve element juxtaposition from selected owners and whole input families.
Reuse: Language.juxtapose's common-object rule, first-hit operation routes and
nativeOperationFamily. A pending numeral has no selected object; heterogeneous action
roles are compared before any actual scalar or module is substituted. -/
def sourceJuxtapositionName
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (left : Option NativeSourceJudgement) (right : NativeSourceJudgement) :
    TermElabM String := do
  let state ← semanticState
  let rightType ← inferType right.value
  let rightDomains ← operationDomains categoryOf rightType none #[rightType]
  let leftDomains ← match left with
    | none => pure #[]
    | some left => do
      let type ← inferType left.value
      operationDomains categoryOf type none #[type]
  if !leftDomains.isEmpty && !rightDomains.isEmpty then
    let domains := leftDomains ++ rightDomains
    for root in domains do
      if (← operationRoutes root.category.expression "·").isEmpty then continue
      let mut common := true
      for target in domains do
        let family ← SourceRoutes.forOwner root.category.expression target.category.expression
        let some routes ← family.finiteRoutes
          | throwUnsupportedSource "juxtaposition requires its uniform source comparison"
        if routes.isEmpty then common := false
      if common then return "·"
  if let some left := left then
    if leftDomains.isEmpty && (left.category.any (·.role == .morphism) ||
        (← whnf (← inferType left.value)).isForall) then
      throwUnsupportedSource
        "callable juxtaposition requires its declared action and application comparison"
  let mut heterogeneous := #[]
  for domain in rightDomains do
    let routes ← operationRoutes domain.category.expression "•"
    if routes.isEmpty then continue
    let categoryFamily ← nativeCategoryFamily state domain.category.expression
      fun _ => mkFreshLevelMVar
    for route in routes do
      for binding in state.operationBindings route.target "•" do
        unless binding.arity == 2 && binding.numerals == 0 do
          throwError "the first juxtaposition action has a different declared signature"
        let value ← nativeOperationFamily state domain.category.expression categoryFamily route binding
        discard <| levelMVarToParam (← instantiateMVars value)
        let value ← instantiateMVars value
        if value.hasMVar || value.hasLevelMVar then
          throwError "the whole juxtaposition action has undetermined parameters"
        let same ← lambdaTelescope value fun parameters body => do
          let arrow ← whnfR (← inferType body)
          unless arrow.isAppOfArity ``Quiver.Hom 4 do
            throwError "the juxtaposition action lost its native morphism boundary"
          let inputs ← operationInputs arrow.getAppArgs[2]! 2
          let first ← mkLambdaFVars parameters inputs[0]!
          let second ← mkLambdaFVars parameters inputs[1]!
          withoutModifyingState <| isDefEq (← inferType first) (← inferType second) <&&>
            isDefEq first second
        heterogeneous := heterogeneous.push (!same)
  if heterogeneous.isEmpty || heterogeneous.all (! ·) then return "·"
  unless heterogeneous.all id do
    throwSemanticAmbiguity "juxtaposition requires its selected whole action family"
  return "•"

-- Classify transport roles at the entire rigid source family. A scalar argument and
-- an object argument remain distinct even if their carriers coincide after substitution.
private def operationTransportRoles (state : SemanticState) (root : OperationRoot)
    (categoryFamily : Expr) (family : NativeOperationFamily) :
    TermElabM (Array Bool × Bool × Array Expr) := do
  if root.domain.comparison.isNone then
    return (Array.replicate family.binding.arity false, false, #[])
  let some selected := root.domain.category.carrier
    | throwError "the operation refinement lost its supplied carrier action"
  unless selected.target.syntacticEq (.atom CategoryId.sets) do
    throwUnsupportedSource "operation transport requires its actual carrier comparison"
  let some steps := state.routeEdges? root.domain.category.expression selected.target selected.refs
    | throwError "the operation refinement lost its complete carrier route"
  let route : Route :=
    { source := root.domain.category.expression, target := selected.target, steps }
  let parameterCount ← forallTelescopeReducing (← inferType categoryFamily) fun parameters _ =>
    pure parameters.size
  lambdaTelescope family.value fun parameters body => do
    let category := mkAppN categoryFamily (parameters.take parameterCount)
    let objectIndex := parameters.size - 1 - family.binding.numerals
    let native ← nativeRouteFunctor state route category
    let carrier ← functorObject native.functor parameters[objectIndex]! native.target
    let arrow ← whnfR (← inferType body)
    unless arrow.isAppOfArity ``Quiver.Hom 4 do
      throwError "the whole source operation lost its typed morphism"
    let inputs ← operationInputs arrow.getAppArgs[2]! family.binding.arity
    let carrierFamily ← mkLambdaFVars parameters carrier
    let mut flags := #[]
    let mut evidence := #[]
    for type in inputs.push arrow.getAppArgs[3]! do
      let typeFamily ← mkLambdaFVars parameters type
      let agrees ← withoutModifyingState do
        isDefEq (← inferType typeFamily) (← inferType carrierFamily) <&&>
          isDefEq typeFamily carrierFamily
      flags := flags.push agrees
      if agrees then
        let proof ← mkExpectedTypeHint (← mkEqRefl typeFamily)
          (← mkEq typeFamily carrierFamily)
        checkWithKernel proof
        evidence := evidence.push proof
    let some output := flags[family.binding.arity]?
      | throwError "the whole operation lost its actual result transport role"
    return (flags.take family.binding.arity, output, evidence)

private def retainOperationEvidence (value : Expr) (proofs : Array Expr) : MetaM Expr := do
  let mut value := value
  for proof in proofs.reverse do
    let body := value
    value ← withLetDecl (← mkFreshUserName `operationAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] body
        (usedLetOnly := false) (generalizeNondepLet := false)
  return value

/-- Prepare first-hit source bindings and their complete rigid morphism families.
Reuse: SourceRoutes, nativeOperationFamily, native conversion, ObjectRefinement and
congruFun. The supplied refinement cone is checked at complete structured objects after
universal operation agreement; all original source data remain in the resulting term. -/
opaque sourceOperation
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory)) (name : String)
    (domain : Expr) (contextual : Option Expr) (hints : Array Expr) (arity : Nat)
    (numerals : Array (Expr → TermElabM Expr)) :
    TermElabM NativeSourceOperation := do
  let state ← semanticState
  let domains ← operationDomains categoryOf domain contextual hints
  if domains.isEmpty then
    throwUnsupportedSource "the source operation requires its interpreted element domain"
  let root ← operationRoot domains name
  -- These level variables are constrained only by the unapplied source declarations.
  -- Lean's level generalizer freezes every remaining variable before comparison.
  let categoryFamily ← nativeCategoryFamily state root.domain.category.expression
    fun _ => mkFreshLevelMVar
  let mut families : Array NativeOperationFamily := #[]
  for route in root.routes do
    for binding in state.operationBindings route.target name do
      unless binding.arity == arity && binding.numerals == numerals.size do continue
      let value ← nativeOperationFamily state root.domain.category.expression categoryFamily
        route binding
      families := families.push ⟨route, binding, value⟩
  if families.isEmpty then throwError "the first source binding has a different operation arity"
  for family in families do discard <| levelMVarToParam (← instantiateMVars family.value)
  let categoryFamily ← instantiateMVars categoryFamily
  families := ← families.mapM fun family => do
    let value ← instantiateMVars family.value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the complete source operation family has undetermined parameters"
    return { family with value }
  let some first := families[0]?
    | throwError "operation preparation requires its complete first binding"
  let mut proofs := #[]
  for other in families do
    unless ← isDefEq (← inferType first.value) (← inferType other.value) <&&>
        isDefEq first.value other.value do
      throwSemanticAmbiguity "the whole operation families require their supplied agreement"
    let proof ← mkExpectedTypeHint (← mkEqRefl first.value) (← mkEq first.value other.value)
    checkWithKernel proof
    proofs := proofs.push proof
  let (inputTransports, outputTransport, roleProofs) ←
    operationTransportRoles state root categoryFamily first
  proofs := proofs ++ roleProofs
  -- Specialize already checked universal evidence at the exact category parameters.
  let mut levelParameters : CollectLevelParams.State := {}
  levelParameters := levelParameters.collect categoryFamily
  for family in families do levelParameters := levelParameters.collect family.value
  let universes := levelParameters.params.toList
  let levels ← universes.mapM fun _ => mkFreshLevelMVar
  let actualCategoryFamily := categoryFamily.instantiateLevelParams universes levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType actualCategoryFamily)
  unless ← isDefEq (mkAppN actualCategoryFamily parameters) root.domain.category.bundle do
    throwError "the source operation has a different complete selected category"
  let value := first.value.instantiateLevelParams universes levels
  let value := mkAppN value parameters
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType value)
  unless arguments.size > first.binding.numerals do
    throwError "the source operation lost its original object argument"
  let objectIndex := arguments.size - 1 - first.binding.numerals
  unless ← isDefEq arguments[objectIndex]! root.domain.value do
    throwError "the source operation changed its actual selected object"
  for numeral in numerals, index in [:numerals.size] do
    let argument := arguments[objectIndex + 1 + index]!
    let value ← numeral (← instantiateMVars (← inferType argument))
    unless ← isDefEq argument value do
      throwError "the source operation numeral has a different complete parameter type"
  let allArguments ← (parameters ++ arguments).mapM instantiateMVars
  let mut evidence := #[]
  for proof in proofs do
    let mut proof := proof.instantiateLevelParams universes levels
    for argument in allArguments do proof ← mkAppM ``congrFun #[proof, argument]
    evidence := evidence.push (← instantiateMVars proof)
  -- The actual objects of the supplied cone are compared with every original
  -- refinement. These are structured-object equations, not operation agreement.
  for routes in root.images, target in root.domains do
    evidence := evidence ++ (← sourceRouteAgreements state root.domain.category routes)
    for route in routes do
      let native ← nativeRouteFunctor state route root.domain.category.bundle
      let image ← functorObject native.functor root.domain.value native.target
      unless ← isDefEq native.target target.category.bundle <&&>
          isDefEq image target.value do
        throwSemanticAmbiguity "the supplied source refinements require their structured comparison"
      let proof ← mkExpectedTypeHint (← mkEqRefl image) (← mkEq image target.value)
      checkWithKernel (← instantiateMVars proof)
      evidence := evidence.push proof
      if let some original := root.domain.comparison then
        let some other := target.comparison
          | throwError "the source refinement cone lost its comparison datum"
        let some originalCarrier := root.domain.category.carrier
          | throwError "the source refinement cone lost its source carrier"
        let some targetCarrier := target.category.carrier
          | throwError "the source refinement cone lost its target carrier"
        let some originalSteps := state.routeEdges? root.domain.category.expression
            originalCarrier.target originalCarrier.refs
          | throwError "the source refinement cone has an invalid carrier route"
        let some composedSteps := state.routeEdges? root.domain.category.expression
            originalCarrier.target (route.refs ++ targetCarrier.refs)
          | throwError "the source refinement cone has an invalid composed carrier route"
        let originalRoute : Route := {
          source := root.domain.category.expression
          target := originalCarrier.target
          steps := originalSteps }
        let composedRoute : Route := {
          source := root.domain.category.expression
          target := originalCarrier.target
          steps := composedSteps }
        evidence := evidence ++ (← sourceRouteAgreements state root.domain.category
          #[originalRoute, composedRoute])
        let forward ← mkAppM ``CategoryTheory.Iso.hom #[original]
        let otherForward ← mkAppM ``CategoryTheory.Iso.hom #[other]
        unless ← isDefEq (← inferType forward) (← inferType otherForward) <&&>
            isDefEq forward otherForward do
          throwSemanticAmbiguity "the supplied presentation maps require their coherent comparison"
        let proof ← mkExpectedTypeHint (← mkEqRefl forward) (← mkEq forward otherForward)
        checkWithKernel (← instantiateMVars proof)
        evidence := evidence.push proof
  for candidate in root.domains do
    evidence := evidence ++ candidate.originEvidence
    if let some comparison := candidate.comparison then evidence := evidence.push comparison
  let mut operation := mkAppN value arguments
  operation ← retainOperationEvidence operation evidence
  let refs := reprStr (families.map fun family => (family.route.refs, family.binding.id))
  operation := sourceReference ``OperationEntry first.binding.id.raw first.binding.declaration
    operation
  operation := .mdata (KVMap.empty.setString `CasCompiler.source.operationRoutes refs) operation
  let cone := (root.domains.zip root.images).map fun (domain, routes) =>
    (domain.category.expression, routes.map Route.refs)
  operation := .mdata
    (KVMap.empty.setString `CasCompiler.source.operationRefinements (reprStr cone)) operation
  return ⟨operation, arity, root.domain.comparison, inputTransports, outputTransport⟩

end CasCompiler
