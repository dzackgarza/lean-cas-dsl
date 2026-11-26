module

public import CasCompiler.OperationFamily
public import CasCompiler.FamilyConversion
import CasCompiler.SourceCarrier
public import CasCompiler.SourceProof

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue



structure NativeSourceOperationDomain where
  private mk ::
  category : NativeSourceCategory
  value : Expr
  comparison : Option Expr
  originEvidence : Array Expr

private def refinementDomainCandidate (state : SemanticState) (entry : ObjectEntry) (domain : Expr) :
    SourceReadM (Option NativeSourceOperationDomain) := do
  let some refinement := entry.refines | return none
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration refinement.identification
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let comparison ← applyObjectParameters entry.id.raw refinement.identification arguments
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    liftM (m := TermElabM) <| throwError "the source operation refinement requires its actual isomorphism"
  let some base := state.objects.find? (·.id == refinement.base)
    | liftM (m := TermElabM) <| throwError "the source refinement lost its declared base object"
  let (original, _) ← registeredSourceDomain domain
  let declared := type.getAppArgs[3]!.headBeta.consumeMData
  let mut retainedArguments : Array (Option Expr) := Array.replicate arguments.size none
  if original.getAppFn.isConstOf base.declaration then
    let some retained ← alignSourceArguments? base.declaration arguments declared original
      | return none
    retainedArguments := retained


  let determined ← liftM (m := MetaM) <| if arguments.isEmpty then isDefEq type.getAppArgs[3]! original
    else withReducible <| isDefEq type.getAppArgs[3]! original
  unless determined do return none
  for argument in arguments, info in infos do
    if info.isInstImplicit && (← liftM (m := MetaM) <| instantiateMVars argument).isMVar then
      let some instanceValue ← synthInstance? (← inferType argument) | return none
      unless ← isDefEq argument instanceValue do return none
  let mut arguments ← liftM (m := MetaM) <| arguments.mapM instantiateMVars
  for original in retainedArguments, index in [:retainedArguments.size] do
    if let some original := original then
      arguments := arguments.set! index (← liftM (m := MetaM) <| instantiateMVars original)
  if arguments.any (fun argument => argument.hasMVar || argument.hasLevelMVar) then return none


  let comparison := mkAppN (← liftM (m := MetaM) <| instantiateMVars comparison.getAppFn) arguments
  let comparison ← SourceReadM.select (← sourceReferenceAt
    (.refinement entry refinement) comparison comparison)
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    liftM (m := TermElabM) <| throwError "the specialized source refinement lost its actual isomorphism"

  checkRegisteredSourceDomains domain (← liftM (m := MetaM) <| instantiateMVars type.getAppArgs[3]!)
  let #[category] := state.categories.filter (·.id == entry.category)
    | liftM (m := TermElabM) <| throwError "the source refinement requires one complete category"
  let (bundle, value) ← registeredExpressions (.inl entry) category fun function _ => do
    unless ← isDefEq (← inferType function) (← inferType declaration) do
      liftM (m := TermElabM) <| throwError "the source refinement changed its complete declaration parameters"
    return mkAppN function arguments
  let selection ← objectCarrierSelection entry bundle value
  return some ⟨⟨.object, category.expression, bundle, selection, none⟩, value,
    some (← liftM (m := MetaM) <| instantiateMVars comparison), #[]⟩

private def refinementDomain (state : SemanticState) (entry : ObjectEntry) (domain : Expr) :
    SourceReadM (Option NativeSourceOperationDomain) := do


  let absent : MessageData := m!"the source refinement does not apply to this domain"
  let candidate ← SourceReadM.chooseApplicable #[do
      let some value ← refinementDomainCandidate state entry domain
        | return .error absent
      return .ok value]
    absent m!"the source refinement producer has several readings" (restoreInfo := true)
  match candidate with
  | .ok value => return some value
  | .error _ => return none

private def scopedOperationDomains
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (expected : Expr) (hints : Array Expr) : SourceReadM (Array NativeSourceOperationDomain) := do
  return (← sourceElementOwners categoryOf expected hints).map fun owner =>
    ⟨owner.category, owner.value, none, #[owner.evidence]⟩




opaque sourceOperationDomains
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory)) (expected : Expr)
    (contextual : Option Expr) (hints : Array Expr) :
    SourceReadM (Array NativeSourceOperationDomain) := do
  let state ← semanticState
  let (domain, entries) ← registeredSourceDomain expected
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
  domain : NativeSourceOperationDomain
  domains : Array NativeSourceOperationDomain
  routes : Array Route
  images : Array (Array Route)



private def operationRoot (domains : Array NativeSourceOperationDomain) (name : String) :
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


structure NativeSourceOperation where
  value : Expr
  arity : Nat
  comparison : Option Expr
  inputDomains : Array Bool
  outputDomain : Bool
  inputTransports : Array Bool
  outputTransport : Bool

private partial def operationInputs (type : Expr) (arity : Nat) : MetaM (Array Expr) := do
  if arity == 1 then return #[type]
  unless arity > 1 do throwError "a source element operation requires its operand domain"
  let pair ← whnf type
  unless pair.isAppOfArity ``Prod 2 do
    throwUnsupportedSource "the source operation requires its declared product mediation"
  return #[pair.getAppArgs[0]!] ++ (← operationInputs pair.getAppArgs[1]! (arity - 1))





def sourceJuxtapositionNames
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (left : Option NativeSourceJudgement) (right : NativeSourceJudgement) :
    SourceReadM (Array String) := do
  let state ← semanticState
  let rightType ← inferType right.value
  let rightDomains ← sourceOperationDomains categoryOf rightType none #[rightType]
  let leftDomains ← match left with
    | none => pure #[]
    | some left => do
      let type ← inferType left.value
      sourceOperationDomains categoryOf type none #[type]
  let mut names : Array String := #[]
  if !leftDomains.isEmpty && !rightDomains.isEmpty then
    let domains := leftDomains ++ rightDomains
    for root in domains do
      if (← operationRoutes root.category.expression "·").isEmpty then continue
      let mut common := true
      for target in domains do
        let family ← SourceRoutes.forOwner root.category.expression target.category.expression
        let some routes ← family.finiteRoutes
          | liftM (m := TermElabM) <| throwUnsupportedSource "juxtaposition requires its uniform source comparison"
        if routes.isEmpty then common := false
      if common && !names.contains "·" then names := names.push "·"
  let mut heterogeneous := #[]
  for domain in rightDomains do
    let routes ← operationRoutes domain.category.expression "•"
    if routes.isEmpty then continue
    let categoryFamily ← nativeCategoryFamily state domain.category.expression
      fun _ => mkFreshLevelMVar
    for route in routes do
      for binding in state.operationBindings route.target "•" do
        unless binding.arity == 2 && binding.numerals == 0 do
          liftM (m := TermElabM) <| throwError "the first juxtaposition action has a different declared signature"
        let value ← nativeOperationFamily state domain.category.expression categoryFamily route binding
        discard <| levelMVarToParam (← liftM (m := MetaM) <| instantiateMVars value)
        let value ← liftM (m := MetaM) <| instantiateMVars value
        if value.hasMVar || value.hasLevelMVar then
          liftM (m := TermElabM) <| throwError "the whole juxtaposition action has undetermined parameters"
        let same ← liftM (m := TermElabM) <| lambdaTelescope value fun parameters body => do
          let arrow ← whnfR (← inferType body)
          unless arrow.isAppOfArity ``Quiver.Hom 4 do
            throwError "the juxtaposition action lost its native morphism boundary"
          let inputs ← operationInputs arrow.getAppArgs[2]! 2
          let first ← mkLambdaFVars parameters inputs[0]!
          let second ← mkLambdaFVars parameters inputs[1]!
          withoutModifyingState <| isDefEq (← inferType first) (← inferType second) <&&>
            isDefEq first second
        heterogeneous := heterogeneous.push (!same)
  if heterogeneous.isEmpty || heterogeneous.all (! ·) then
    for domain in rightDomains do
      unless (← operationRoutes domain.category.expression "·").isEmpty do
        if !names.contains "·" then names := names.push "·"
  else
    unless heterogeneous.all id do
      liftM (m := TermElabM) <| throwSemanticAmbiguity "juxtaposition requires its selected whole action family"
    names := names.push "•"
  return names



private def operationTransportRoles (root : OperationRoot)
    (categoryFamily : Expr) (family : NativeOperationFamily) :
    TermElabM (Array Bool × Bool × Array Expr) := do
  let parameterCount ← forallTelescopeReducing (← inferType categoryFamily) fun parameters _ =>
    pure parameters.size
  lambdaTelescope family.value fun parameters body => do
    let category := mkAppN categoryFamily (parameters.take parameterCount)
    let objectIndex := parameters.size - 1 - family.binding.numerals
    let carrier ← sourceCarrierFamilyObject root.domain.category category parameters[objectIndex]!
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

private structure RefinedConstantParameter where
  value : Expr
  category : NativeSourceCategory
  comparison : Expr
  evidence : Array Expr



private def refinedConstantParameter? (state : SemanticState) (entry : ObjectEntry)
    (domain : Expr) (target : CategoryExpr) :
    SourceReadM (Option RefinedConstantParameter) := do
  let some refined ← refinementDomain state entry domain | return none
  let some carrier := refined.category.carrier
    | liftM (m := TermElabM) <| throwError "the named parameter refinement lost its declared carrier"
  let some comparison := refined.comparison
    | liftM (m := TermElabM) <| throwError "the named parameter refinement lost its base identification"
  let mut routes : Array Route := #[]
  for count in [:carrier.refs.size + 1] do
    if let some steps := state.routeEdges? refined.category.expression target
        (carrier.refs.take count) then
      routes := routes.push { source := refined.category.expression, target, steps }
  let some route := routes[0]? | return none
  let evidence ← sourceRouteAgreements state refined.category routes
  let selected ← nativeRouteFunctor state route refined.category.bundle
  let value ← functorObject selected.functor refined.value selected.target
  let remaining := { carrier with
    refs := carrier.refs.drop route.refs.size
    actions := carrier.actions.drop route.refs.size }
  return some ⟨← liftM (m := MetaM) <| instantiateMVars value,
    ⟨.object, target, ← liftM (m := MetaM) <| instantiateMVars selected.target, some remaining, none⟩,
    comparison, evidence⟩



private def operationAgreement (left right : Expr) (evidence : Array Expr)
    (failure : MessageData) : SourceReadM Expr := do


  if evidence.isEmpty && left.equal right then
    let context := (← get).context
    let locals := context.bindings.map (·.expression)
    let eligible := fun (expression : Expr) =>
      !expression.hasExprMVar && !expression.hasLevelMVar &&
        !expression.hasLooseBVars && !(expression.abstract locals).hasFVar
    if eligible left && eligible right then
      let candidate ← liftM (m := MetaM) <| withoutModifyingState do
        context.telescope.ensureDeclarations
        let proposition ← mkEq left right
        if !eligible proposition then return none
        let proof ← mkExpectedTypeHint (← mkEqRefl left) proposition
        if !eligible proof then return none
        checkWithKernel proof
        return some (proof, ← Meta.saveState)
      if let some (proof, checked) := candidate then


        liftM (m := MetaM) checked.restore
        discard <| SourceReadM.selection? right
        return proof
  let agrees ← (← get).context.withOriginalSources (#[left, right] ++ evidence) fun values =>
    return (← sourceFamilyConversion values[0]! values[1]!
      (values.extract 2 values.size)).isSome
  unless agrees do liftM (m := TermElabM) <| throwSemanticAmbiguity failure
  let selected := (← SourceReadM.selection? right).getD { value := right }
  let nativeFits ← liftM (m := MetaM) <| withoutModifyingState do
    isDefEq (← inferType right) (← inferType left)
  let right ← if nativeFits then do


      let agrees ← liftM (m := MetaM) do
        isDefEq (← inferType right) (← inferType left)
      unless agrees do
        liftM (m := TermElabM) <| throwError
          "the source operation agreement changed its checked native type"
      pure right
    else
      SourceReadM.select { selected with value := right } (some (← inferType left))
  SourceReadM.prove (← mkEq left right) (fun proposition sources => do
    let proposition ← whnfR proposition
    unless proposition.isAppOfArity ``Eq 3 do
      throwError "the source operation lost its complete agreement proposition"
    let some proof ← sourceFamilyConversion proposition.getAppArgs[1]!
        proposition.getAppArgs[2]! sources
      | throwSemanticAmbiguity failure
    return proof) evidence






opaque sourceNamedConstantParameter? (domain : Expr) (target : CategoryExpr) :
    SourceReadM (Option NativeSourceJudgement) := do
  let state ← semanticState
  let (original, bases) ← registeredSourceDomain domain
  let #[base] := bases
    | if bases.isEmpty then return none
      else liftM (m := TermElabM) <| throwSemanticAmbiguity "the named parameter requires its exact registered base"
  unless original.getAppArgs.isEmpty do return none
  if (← whnfR (← checkedDeclaration base.declaration).type).isForall then return none
  let mut candidates : Array RefinedConstantParameter := #[]
  for entry in state.objects do
    unless entry.refines.any (·.base == base.id) do continue
    if let some candidate ← refinedConstantParameter? state entry domain target then
      candidates := candidates.push candidate
  let some first := candidates[0]? | return none
  let forward ← mkAppM ``CategoryTheory.Iso.hom #[first.comparison]
  let mut evidence := #[]
  for candidate in candidates do
    let categoryAgreement ← operationAgreement first.category.bundle candidate.category.bundle #[]
      "the named parameter refinements have different complete categories"
    let objectAgreement ← operationAgreement first.value candidate.value #[]
      "the named parameter refinements require their complete structural comparison"
    let otherForward ← mkAppM ``CategoryTheory.Iso.hom #[candidate.comparison]
    let comparisonAgreement ← operationAgreement forward otherForward #[]
      "the named parameter refinements require coherent base identifications"
    evidence := evidence ++ candidate.evidence ++
      #[candidate.comparison, categoryAgreement, objectAgreement, comparisonAgreement]
  let value ← retainOperationEvidence first.value evidence
  let selected := (← SourceReadM.selection? first.value).getD { value := first.value }
  return some ⟨← SourceReadM.select { selected with value, category := some first.category },
    some first.category⟩





opaque sourceOperation
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory)) (name : String)
    (domain : Expr) (contextual : Option Expr) (hints : Array Expr) (arity : Nat)
    (numerals : Array (Expr → SourceReadM Expr)) :
    SourceReadM NativeSourceOperation := do
  let state ← semanticState
  let phase : String → List (String × Json) → SourceReadM Unit := fun event details => do
    try
      let scope ← get
      let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
      liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj ([
        ("operation", toJson name),
        ("heartbeats", toJson heartbeats),
        ("contextBindings", toJson scope.context.bindings.size),
        ("formals", toJson scope.formals.size),
        ("arity", toJson arity),
        ("numerals", toJson numerals.size)] ++ details))
    catch _ => pure ()
  phase "source.operation.prepare.started" []
  let domains ← sourceOperationDomains categoryOf domain contextual hints
  phase "source.operation.domains.finished" [("domains", toJson domains.size)]
  if domains.isEmpty then
    liftM (m := TermElabM) <| throwUnsupportedSource "the source operation requires its interpreted element domain"
  let root ← operationRoot domains name
  phase "source.operation.root.finished" [
    ("domains", toJson root.domains.size), ("routes", toJson root.routes.size),
    ("imageRoutes", toJson (root.images.foldl (fun count routes => count + routes.size) 0))]


  let categoryFamily ← nativeCategoryFamily state root.domain.category.expression
    fun _ => mkFreshLevelMVar
  let mut families : Array NativeOperationFamily := #[]
  for route in root.routes do
    for binding in state.operationBindings route.target name do
      unless binding.arity == arity && binding.numerals == numerals.size do continue
      let value ← nativeOperationFamily state root.domain.category.expression categoryFamily
        route binding
      families := families.push ⟨route, binding, value⟩
  if families.isEmpty then liftM (m := TermElabM) <| throwError "the first source binding has a different operation arity"
  for family in families do discard <| levelMVarToParam (← liftM (m := MetaM) <| instantiateMVars family.value)
  let categoryFamily ← liftM (m := MetaM) <| instantiateMVars categoryFamily
  families := ← families.mapM fun family => do
    let value ← liftM (m := MetaM) <| instantiateMVars family.value
    if value.hasMVar || value.hasLevelMVar then
      liftM (m := TermElabM) <| throwError "the complete source operation family has undetermined parameters"
    return { family with value }
  let some first := families[0]?
    | liftM (m := TermElabM) <| throwError "operation preparation requires its complete first binding"
  let mut proofs := #[]
  let agreementEvidence := root.domains.flatMap fun domain =>
    domain.originEvidence ++ domain.category.carrier.toArray.flatMap (·.comparisons)
  for other in families do
    let some proof ← sourceFamilyConversion first.value other.value agreementEvidence
      | liftM (m := TermElabM) <| throwSemanticAmbiguity "the whole operation families require their supplied agreement"
    proofs := proofs.push proof
  let (inputDomains, outputDomain, roleProofs) ←
    operationTransportRoles root categoryFamily first
  let inputTransports := inputDomains.map (· && root.domain.comparison.isSome)
  let outputTransport := outputDomain && root.domain.comparison.isSome
  proofs := proofs ++ roleProofs
  phase "source.operation.families.finished" [
    ("families", toJson families.size), ("proofs", toJson proofs.size)]

  let mut levelParameters : CollectLevelParams.State := {}
  levelParameters := levelParameters.collect categoryFamily
  for family in families do levelParameters := levelParameters.collect family.value
  let universes := levelParameters.params.toList
  let levels ← universes.mapM fun _ => mkFreshLevelMVar
  let actualCategoryFamily := categoryFamily.instantiateLevelParams universes levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType actualCategoryFamily)
  let supplied := root.domain.category.bundle.consumeMData
  let declared := mkAppN actualCategoryFamily.consumeMData parameters
  let mut originals : Array (Option Expr) := Array.replicate parameters.size none
  if let some declaration := declared.getAppFn.constName? then
    if supplied.getAppFn.isConstOf declaration then
      let some aligned ← alignSourceArguments? declaration parameters declared supplied
        | liftM (m := TermElabM) <| throwError "the source operation lost its exact category arguments"
      originals := aligned
  unless ← isDefEq (mkAppN actualCategoryFamily parameters) root.domain.category.bundle do
    liftM (m := TermElabM) <| throwError "the source operation has a different complete selected category"
  let mut parameters ← liftM (m := MetaM) <| parameters.mapM instantiateMVars
  for original in originals, index in [:originals.size] do
    if let some original := original then
      parameters := parameters.set! index (← liftM (m := MetaM) <| instantiateMVars original)
  let value := first.value.instantiateLevelParams universes levels
  let value := mkAppN value parameters
  let previous ← liftM (m := MetaM) getMCtx
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType value)
  unless arguments.size > first.binding.numerals do
    liftM (m := TermElabM) <| throwError "the source operation lost its original object argument"
  let objectIndex := arguments.size - 1 - first.binding.numerals
  unless ← isDefEq arguments[objectIndex]! root.domain.value do
    liftM (m := TermElabM) <| throwError "the source operation changed its actual selected object"


  let mut actualArguments := arguments.set! objectIndex root.domain.value
  let owned := (← liftM (m := MetaM) getMCtx).decls.foldl (fun result identity _ =>
    if previous.decls.contains identity then result else result.push identity) #[]
  for numeral in numerals, index in [:numerals.size] do
    let position := objectIndex + 1 + index
    let argument := arguments[position]!
    let value ← numeral (← liftM (m := MetaM) <| instantiateMVars (← inferType argument))
    extendSourceApplicationScope owned
    unless ← isDefEq argument value do
      liftM (m := TermElabM) <| throwError "the source operation numeral has a different complete parameter type"
    actualArguments := actualArguments.set! position value
  let arguments ← liftM (m := MetaM) <| actualArguments.mapM instantiateMVars
  let allArguments ← liftM (m := MetaM) <| (parameters ++ arguments).mapM instantiateMVars
  let mut evidence := #[]
  for proof in proofs do
    let mut proof := proof.instantiateLevelParams universes levels
    for argument in allArguments do proof ← mkAppM ``congrFun #[proof, argument]
    evidence := evidence.push (← liftM (m := MetaM) <| instantiateMVars proof)
  phase "source.operation.specialization.finished" [
    ("parameters", toJson parameters.size), ("arguments", toJson arguments.size),
    ("evidence", toJson evidence.size)]


  for routes in root.images, target in root.domains do
    evidence := evidence ++ (← sourceRouteAgreements state root.domain.category routes)
    for route in routes do
      let native ← nativeRouteFunctor state route root.domain.category.bundle
      let image ← functorObject native.functor root.domain.value native.target
      let categoryProof ← operationAgreement native.target target.category.bundle #[]
        "the supplied source refinements require their complete category comparison"
      let proof ← operationAgreement image target.value #[]
        "the supplied source refinements require their structured comparison"
      evidence := evidence ++ #[categoryProof, proof]
      if let some original := root.domain.comparison then
        let some other := target.comparison
          | liftM (m := TermElabM) <| throwError "the source refinement cone lost its comparison datum"
        let some originalCarrier := root.domain.category.carrier
          | liftM (m := TermElabM) <| throwError "the source refinement cone lost its source carrier"
        let some targetCarrier := target.category.carrier
          | liftM (m := TermElabM) <| throwError "the source refinement cone lost its target carrier"
        let some originalSteps := state.routeEdges? root.domain.category.expression
            originalCarrier.target originalCarrier.refs
          | liftM (m := TermElabM) <| throwError "the source refinement cone has an invalid carrier route"
        let some composedSteps := state.routeEdges? root.domain.category.expression
            originalCarrier.target (route.refs ++ targetCarrier.refs)
          | liftM (m := TermElabM) <| throwError "the source refinement cone has an invalid composed carrier route"
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
        let proof ← operationAgreement forward otherForward #[]
          "the supplied presentation maps require their coherent comparison"
        evidence := evidence.push proof
  for candidate in root.domains do
    evidence := evidence ++ candidate.originEvidence
    if let some comparison := candidate.comparison then evidence := evidence.push comparison
  phase "source.operation.cone.finished" [("evidence", toJson evidence.size)]
  let original := (mkAppN value arguments).headBeta
  let operation ← retainOperationEvidence original evidence
  let selected ← sourceReferenceAt (.operation first.binding) original operation
  let cone := (root.domains.zip root.images).map fun (domain, routes) =>
    (domain.category.expression, routes.map Route.refs)
  let operation ← SourceReadM.select { selected with
    alternatives := families.map fun family => (.operation family.binding, family.route.refs)
    operationRefinements := cone }
  phase "source.operation.selection.finished" []
  return ⟨operation, arity, root.domain.comparison, inputDomains, outputDomain,
    inputTransports, outputTransport⟩

end CasCompiler
