module

public import CasCompiler.OperationFamily
public import CasCompiler.FamilyConversion
public import CasCompiler.SourcePointOrigin
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private structure RoutedNumeral where
  owner : NativeSourceElementOwner
  route : Route
  categoryFamily : Expr
  family : NativeOwnedFamily
  evidence : Array Expr := #[]
  alternatives : Array (SelectedSourceReference × Array EdgeRef) := #[]
  terminal : Option Expr := none

private inductive NumeralContext where
  | direct
  | carrier (owner : NativeSourceElementOwner) (comparison : Expr)
      (refinement : Option ObjectEntry)
  | selected (routed : RoutedNumeral)
  | refinement (entry : ObjectEntry)



private def numeralCarrierAgreement (routed : RoutedNumeral) : TermElabM Expr := do
  let count ← forallTelescopeReducing (← inferType routed.categoryFamily) fun parameters _ =>
    pure parameters.size
  lambdaTelescope routed.family.value fun parameters body => do
    let category := mkAppN routed.categoryFamily (parameters.take count)
    let object := parameters[routed.family.objectIndex]!
    let carrier ← sourceCarrierFamilyObject routed.owner.category category object
    let type ← whnfR (← inferType body)
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the whole numeral family lost its point-map boundary"
    let target ← mkLambdaFVars parameters type.getAppArgs[3]!
    let expected ← mkLambdaFVars parameters carrier
    unless ← isDefEq (← inferType target) (← inferType expected) <&&> isDefEq target expected do
      throwError "the numeral has a different complete selected carrier family"
    let proof ← mkExpectedTypeHint (← mkEqRefl target) (← mkEq target expected)
    checkWithKernel proof
    return proof


private def numeralProof (proposition : Expr) : MetaM (Option Expr) := do
  if proposition.isAppOfArity ``Eq 3 then
    let arguments := proposition.getAppArgs
    if ← withoutModifyingState <| isDefEq arguments[1]! arguments[2]! then
      return some (← mkEqRefl arguments[1]!)
  let decision ← mkDecide proposition
  unless (← withAtLeastTransparency .default <| whnf decision).isConstOf ``Bool.true do
    return none
  return some (← mkDecideProof proposition)



private def completePointParameters (arguments : Array Expr) (binders : Array BinderInfo)
    (proofs : Array Term) (start : Nat) : TermElabM (Option Nat) := do
  let mut proofIndex := start
  for argument in arguments, binder in binders do
    unless (← instantiateMVars argument).hasMVar do continue
    let type ← instantiateMVars (← inferType argument)
    if binder.isInstImplicit then
      unless ← isDefEq argument (← synthInstance type) do return none
    else if ← isProp type then
      let proof ← if proofs.isEmpty then do
          let some proof ← numeralProof type | return none
          pure proof
        else do
          let some evidence := proofs[proofIndex]?
            | throwError "the source numeral requires explicit evidence for its domain obligation"
          proofIndex := proofIndex + 1
          elabTermEnsuringType evidence (some type)
      unless ← isDefEq argument proof do return none
    else throwSemanticAmbiguity "the source numeral requires an actual declaration parameter"
  return some proofIndex



private def numeralRefinementParameters (entry : ObjectEntry) (expected : Expr)
    (proofs : Array Term) : SourceReadM (Option (SourceSelection Expr × Expr × Nat)) := do
  let some refinement := entry.refines
    | liftM (m := TermElabM) <| throwError "a source numeral refinement has no declared comparison"
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration refinement.identification
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (parameters, binders, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let comparison ← applyObjectParameters entry.id.raw refinement.identification parameters
  let type ← whnfR (← inferType comparison)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    liftM (m := TermElabM) <| throwError "a source numeral refinement requires its complete native isomorphism"
  unless ← isDefEq type.getAppArgs[3]! expected do return none
  let some proofIndex ← completePointParameters parameters binders proofs 0
    | liftM (m := TermElabM) <| throwError "the source numeral's declared domain obligation is not established"
  let #[category] := (← semanticState).categories.filter (·.id == entry.category)
    | liftM (m := TermElabM) <| throwError "the source numeral refinement lost its original category row"
  let object ← liftM (m := MetaM) <| instantiateMVars (mkAppN declaration parameters)
  let object ← sourceReferenceAt (.named (.registered (.inl entry) category)) object object
  let comparison ← liftM (m := MetaM) <| instantiateMVars comparison
  let comparison ← SourceReadM.select
    (← sourceReferenceAt (.refinement entry refinement) comparison comparison)
  return some (object, comparison, proofIndex)



private def numeralApplication (function : Expr) (arguments : Array Expr) :
    SourceReadM Expr := do
  let mut result := function
  for original in arguments do
    let .forallE _ type _ _ ← whnfR (← inferType result)
      | liftM (m := TermElabM) <| throwError "the numeral lost its complete declaration telescope"
    let argument ← if ← isDefEq (← inferType original) type then pure original else do
      let selected := (← SourceReadM.selection? original).getD { value := original }
      SourceReadM.select { selected with value := original } (some type)
    result := mkApp result argument
    check result
  return result




private def numeralCandidate (row : NumeralEntry) (context : NumeralContext)
    (number : Nat) (expected : Expr) (proofs : Array Term) : SourceReadM (Option Expr) := do
  let (object, comparison, proofIndex) ← match context with
    | .direct => pure (none, none, 0)
    | .carrier _ comparison refinement => do
      let comparison ← mkAppM ``CategoryTheory.Iso.symm #[comparison]
      let type ← whnfR (← inferType comparison)
      unless ← isDefEq type.getAppArgs[3]! expected do return none
      match refinement with
      | none => pure (none, some comparison, 0)
      | some entry => do
        let some (object, baseComparison, proofIndex) ←
            numeralRefinementParameters entry type.getAppArgs[2]! proofs | return none
        let comparison ← mkAppM ``CategoryTheory.Iso.trans #[baseComparison, comparison]
        pure (some object, some comparison, proofIndex)
    | .selected routed => do
      let selected ← nativeRouteFunctor (← semanticState) routed.route routed.owner.category.bundle
      let value ← functorObject selected.functor routed.owner.value selected.target
      pure (some ({ value } : SourceSelection Expr), none, 0)
    | .refinement entry => do
      let some (object, comparison, proofIndex) ←
          numeralRefinementParameters entry expected proofs | return none
      pure (some object, some comparison, proofIndex)
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (arguments, binders, type) ← forallMetaTelescopeReducing (← inferType declaration)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "a registered numeral requires its complete native point signature"
  let explicit := (List.range arguments.size).toArray.filter (binders[·]!.isExplicit)
  let some literal ← explicit.reverse.findM? fun index =>
      return (← inferType arguments[index]!).isConstOf ``Nat
    | liftM (m := TermElabM) <| throwError "a registered numeral has no declared natural parameter"
  if let some object := object then
    let some first := explicit[0]?
      | liftM (m := TermElabM) <| throwError "a registered numeral has no declared structural object parameter"
    unless ← isDefEq arguments[first]! object.value do return none
  unless ← isDefEq arguments[literal]! (mkNatLit number) do return none
  let target := type.getAppArgs[3]!
  let destination ← match comparison with
    | none => pure expected
    | some comparison => do
      let type ← whnfR (← inferType comparison)
      pure type.getAppArgs[2]!
  if row.over.isNone then
    let source ← sourceDomain destination
    let target ← sourceDomain target
    unless source.getAppFn.constName?.isSome &&
        source.getAppFn.constName? == target.getAppFn.constName? do return none
  unless ← isDefEq target destination do return none
  for index in explicit.filter (· > literal) do
    let proposition ← liftM (m := MetaM) <| instantiateMVars (← inferType arguments[index]!)
    unless ← isProp proposition do
      liftM (m := TermElabM) <| throwError "a registered numeral's trailing obligations must be propositions"
  let some proofIndex ← completePointParameters arguments binders proofs proofIndex
    | liftM (m := TermElabM) <| throwError "the source numeral's declared domain obligation is not established"
  unless proofIndex == proofs.size do
    liftM (m := TermElabM) <| throwError "the source numeral has evidence beyond its declared domain obligations"
  let point ← liftM (m := MetaM) <| instantiateMVars (mkAppN declaration arguments)
  if point.hasMVar || point.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the registered source numeral is not determined at its complete boundary"
  let mut actual ← liftM (m := MetaM) <| arguments.mapM instantiateMVars
  if let some object := object then
    let some first := explicit[0]?
      | liftM (m := TermElabM) <| throwError "the selected numeral lost its original structural argument position"
    let object ← liftM (m := MetaM) <| object.mapM instantiateMVars
    let object ← SourceReadM.select object
    actual := actual.set! first object
  let point ← numeralApplication (← liftM (m := MetaM) <| instantiateMVars declaration) actual
  let application := point
  let point ← match comparison with
    | none => do
      let type ← inferType point
      let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
      unless type.isAppOfArity ``Quiver.Hom 4 do
        liftM (m := TermElabM) <| throwError "the selected numeral lost its complete point type"
      let stated := mkAppN type.getAppFn (type.getAppArgs.set! 3 expected)
      SourceReadM.select { value := point } (some stated)
    | some comparison => do
      let comparison ← liftM (m := MetaM) <| instantiateMVars comparison
      let type ← whnfR (← inferType comparison)
      let pointType ← inferType point
      let pointType ← if pointType.isAppOfArity ``Quiver.Hom 4 then pure pointType
        else whnfR pointType
      unless pointType.isAppOfArity ``Quiver.Hom 4 do
        liftM (m := TermElabM) <| throwError "the transported numeral lost its original point domain"
      let stated := mkAppN type.getAppFn
        (type.getAppArgs.set! 2 pointType.getAppArgs[3]! |>.set! 3 expected)
      let selected := (← SourceReadM.selection? comparison).getD { value := comparison }
      let comparison ← SourceReadM.select { selected with value := comparison } (some stated)
      let type ← whnfR (← inferType comparison)
      let hom ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
      let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
      let pointType ← inferType point
      let pointType ← if pointType.isAppOfArity ``Quiver.Hom 4 then pure pointType
        else whnfR pointType
      unless pointType.isAppOfArity ``Quiver.Hom 4 do
        liftM (m := TermElabM) <| throwError "the transported numeral lost its original point domain"


      mkAppOptM ``CategoryTheory.CategoryStruct.comp
        #[some type.getAppArgs[0]!, some categoryStructure,
          some pointType.getAppArgs[2]!, some pointType.getAppArgs[3]!, some expected,
          some point, some hom]
  let type ← inferType point
  unless type.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the admitted numeral is not a native point map"
  let source := type.getAppArgs[2]!
  let terminalPoint ← mkAppOptM ``default #[some source, none]
  let function ← sourceSetFunction point
  let value ← elabAppArgs function #[] #[Arg.expr terminalPoint] (some expected) false false
  let selected ← retainSourcePoint point (← sourceReferenceAt (.numeral row) application value)
  let value ← match context with
    | .carrier owner _ _ =>
      liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `numeralCarrierAgreement)
        (← inferType owner.evidence) owner.evidence fun binding =>
          mkLetFVars #[binding] value (usedLetOnly := false) (generalizeNondepLet := false)
    | .selected routed => do
      let mut value := value
      for evidence in (routed.evidence.push routed.owner.evidence).reverse do
        let body := value
        value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `numeralOwnerAgreement)
          (← inferType evidence) evidence fun binding =>
            mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
      pure value
    | _ => pure value
  let selected := { selected with
    value
    elementOwner := match context with
      | .carrier owner _ _ => some owner
      | .selected routed => some routed.owner
      | _ => none
    alternatives := match context with
      | .selected routed => routed.alternatives
      | _ => #[] }
  return some (← SourceReadM.select selected (some expected))




private def nullaryPointTerminal (family : Expr) : TermElabM Expr := do
  let value ← lambdaTelescope family fun parameters body => do
    let type ← whnfR (← inferType body)
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "the nullary point family lost its complete native map"
    let source ← declaredEndpoint type.getAppArgs[2]!
    let some unique ← synthInstance? (← mkAppM ``Unique #[source])
      | throwUnsupportedSource "the nullary operation requires its complete terminal-source witness"
    mkLambdaFVars parameters unique (usedOnly := false) (usedLetOnly := false)
  if value.hasMVar || value.hasLevelMVar then
    throwError "the nullary terminal family has undetermined native parameters"
  checkWithKernel value
  return value



private def uniquePoint (unique : Expr) : MetaM Expr := do
  let inhabited ← mkProjection unique `toInhabited
  mkProjection inhabited `default




private def nullaryNumeralCandidate (routed : RoutedNumeral) (expected : Expr)
    (proofs : Array Term) : SourceReadM Expr := do
  unless proofs.isEmpty do
    liftM (m := TermElabM) <| throwError "the nullary source operation has no numeral obligations"
  let some terminal := routed.terminal
    | liftM (m := TermElabM) <| throwError "the nullary source operation lost its terminal family"
  let mut collected : CollectLevelParams.State := {}
  collected := collected.collect routed.categoryFamily
  collected := collected.collect routed.family.value
  collected := collected.collect terminal
  let universes := collected.params.toList
  let levels ← universes.mapM fun _ => mkFreshLevelMVar
  let categoryFamily := routed.categoryFamily.instantiateLevelParams universes levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  unless ← isDefEq (mkAppN categoryFamily parameters) routed.owner.category.bundle do
    liftM (m := TermElabM) <| throwError "the nullary operation has a different complete selected category"
  let family := routed.family.value.instantiateLevelParams universes levels
  let function := mkAppN family parameters
  let (arguments, binders, _) ← forallMetaTelescopeReducing (← inferType function)
  let objectIndex := routed.family.objectIndex - parameters.size
  let some object := arguments[objectIndex]?
    | liftM (m := TermElabM) <| throwError "the nullary operation lost its selected object parameter"
  unless ← isDefEq object routed.owner.value do
    liftM (m := TermElabM) <| throwError "the nullary operation changed its actual selected object"
  let some _ ← completePointParameters arguments binders #[] 0
    | liftM (m := TermElabM) <| throwError "the nullary operation has unestablished native obligations"
  let actual ← liftM (m := MetaM) <| (parameters ++ arguments).mapM instantiateMVars
  let point ← liftM (m := MetaM) <| instantiateMVars (mkAppN family actual)
  let terminal ← liftM (m := MetaM) <| instantiateMVars
    (mkAppN (terminal.instantiateLevelParams universes levels) actual)
  if point.hasMVar || point.hasLevelMVar || terminal.hasMVar || terminal.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the nullary operation requires its complete original parameters"
  let type ← whnfR (← inferType point)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the nullary operation lost its complete native point"
  unless ← isDefEq (← inferType terminal)
      (← mkAppM ``Unique #[← declaredEndpoint type.getAppArgs[2]!]) do
    liftM (m := TermElabM) <| throwError "the nullary operation changed its complete terminal source"
  unless ← isDefEq type.getAppArgs[3]! expected do
    liftM (m := TermElabM) <| throwError "the nullary operation has a different complete selected carrier"
  let argument ← uniquePoint terminal
  let function ← sourceSetFunction point
  let value ← elabAppArgs function #[] #[Arg.expr argument] (some expected) false false
  let selected ← retainSourcePoint point { value }
  let mut value := value
  for evidence in (routed.evidence.push routed.owner.evidence).reverse do
    let body := value
    value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `numeralOwnerAgreement)
      (← inferType evidence) evidence fun binding =>
        mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
  SourceReadM.select { selected with
    value
    elementOwner := some routed.owner
    alternatives := routed.alternatives } (some expected)






private def sourceNullaryNumeral (state : SemanticState)
    (ownerFamilies : Array (NativeSourceElementOwner × Expr))
    (number : Nat) (expected : Expr) (proofs : Array Term) : SourceReadM (Option Expr) := do
  let mut candidates : Array (OperationEntry × RoutedNumeral) := #[]
  let mut hasBinding := false
  for (selected, categoryFamily) in ownerFamilies do
    let paths ← SourceRoutes.forOperation selected.category.expression (toString number)
    let some routes ← paths.finiteRoutes
      | liftM (m := TermElabM) <| throwUnsupportedSource "nullary numeral inheritance requires its supplied uniform comparison"
    for route in routes do
      for row in state.operationBindings route.target (toString number) do
        hasBinding := true
        unless row.arity == 0 && row.numerals == 0 do continue
        let family ← nativeOwnedFamily state selected.category.expression categoryFamily route
          row.declaration (fun infos => if infos.isEmpty then none else some (infos.size - 1))
          (some (.operation row))
        candidates := candidates.push
          (row, ⟨selected, route, categoryFamily, family,
            #[], #[(.operation row, route.refs)], none⟩)
  for (_, routed) in candidates do
    discard <| levelMVarToParam (← liftM (m := MetaM) <| instantiateMVars routed.family.value)
  candidates ← candidates.mapM fun (row, routed) => do
    let value ← liftM (m := MetaM) <| instantiateMVars routed.family.value
    if value.hasMVar || value.hasLevelMVar then
      liftM (m := TermElabM) <| throwError "the complete nullary point family has undetermined parameters"
    let routed := { routed with
      categoryFamily := ← liftM (m := MetaM) <| instantiateMVars routed.categoryFamily
      family := { routed.family with value } }
    let proof ← numeralCarrierAgreement routed
    let terminal ← nullaryPointTerminal value
    return (row, { routed with evidence := #[proof], terminal := some terminal })
  let some (row, first) := candidates[0]?
    | if hasBinding then
        liftM (m := TermElabM) <| throwError "the first source numeral operation has a different nullary signature"
      else
        return none
  let mut evidence := first.evidence
  let mut alternatives := #[]
  for (_, other) in candidates do
    unless first.owner.value == other.owner.value &&
        first.owner.category.expression.syntacticEq other.owner.category.expression &&
        (← isDefEq first.owner.category.bundle other.owner.category.bundle) do
      liftM (m := TermElabM) <| throwSemanticAmbiguity "the source numeral requires its selected original structure"
    let comparisons := first.owner.category.carrier.toArray.flatMap (·.comparisons) ++
      other.owner.category.carrier.toArray.flatMap (·.comparisons)
    let some proof ← sourceFamilyConversion first.family.value other.family.value comparisons
      | liftM (m := TermElabM) <| throwSemanticAmbiguity
          s!"inherited point families require their supplied whole agreement: {repr (first.alternatives.map fun (reference, route) => (reference.declaration, route))} and {repr (other.alternatives.map fun (reference, route) => (reference.declaration, route))}"
    evidence := evidence ++ other.evidence.push proof
    alternatives := alternatives ++ other.alternatives
  let value ← nullaryNumeralCandidate { first with evidence, alternatives } expected proofs
  let selected := (← SourceReadM.selection? value).getD { value }
  return some (← SourceReadM.select { selected with value, observation := some (.operation row) })





private def firstNumeralBinding (state : SemanticState) (route : Route) : Bool :=
  route.steps.all fun edge => !state.categories.any fun entry =>
    entry.expression.syntacticEq edge.source && state.numerals.any (·.over == some entry.id)







opaque sourceNumeral? (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (number : Nat) (expected : Expr) (proofs : Array Term := #[]) : SourceReadM (Option Expr) := do
  if expected.headBeta.isConstOf ``Nat then
    unless proofs.isEmpty do liftM (m := TermElabM) <| throwError "a natural parameter literal has no domain obligations"
    return some (mkNatLit number)
  let state ← semanticState
  let (domain, bases) ← registeredSourceDomain expected
  let originalType ← SourceReadM.selection? expected
  let nativeExpected := if bases.isEmpty then
      (originalType.bind (·.typeOrigin)).map (·.type) |>.getD expected
    else domain
  let finish := fun (value : Expr) => do
    let selected := (← SourceReadM.selection? value).getD { value }
    SourceReadM.select { selected with value } (some expected)
  let owners ← if bases.isEmpty then sourceElementOwners categoryOf expected #[expected]
    else pure #[]
  let ownerFamilies ← owners.mapM fun owner => do
    let family ← nativeCategoryFamily state owner.category.expression fun _ => mkFreshLevelMVar
    return (owner, family)




  let mut carrierBases : Array (NativeSourceElementOwner × Expr × Array ObjectEntry) := #[]
  for owner in owners do
    for comparison in owner.category.carrier.toArray.flatMap (·.comparisons) do
      let type ← whnfR (← inferType comparison)
      unless type.isAppOfArity ``CategoryTheory.Iso 4 do continue
      unless ← liftM (m := MetaM) <| withoutModifyingState <|
          isDefEq type.getAppArgs[2]! expected do continue
      let (_, namedBases) ← registeredSourceDomain type.getAppArgs[3]!
      carrierBases := carrierBases.push (owner, comparison, namedBases)
  let mut candidates : Array (NumeralEntry × NumeralContext) := #[]
  let mut carrierRefinements : Array (NumeralEntry × NumeralContext) := #[]
  for row in state.numerals do
    discard <| checkedDeclaration row.declaration
    match row.over with
    | none =>
      candidates := candidates.push (row, .direct)
      for (owner, comparison, _) in carrierBases do
        candidates := candidates.push (row, .carrier owner comparison none)
    | some owner =>
      let #[category] := state.categories.filter (·.id == owner)
        | liftM (m := TermElabM) <| throwError "the source numeral requires one registered structural category"
      for (selected, categoryFamily) in ownerFamilies do
        let paths ← SourceRoutes.forOwner selected.category.expression category.expression
        let some routes ← paths.finiteRoutes
          | liftM (m := TermElabM) <| throwUnsupportedSource "numeral inheritance requires its supplied uniform comparison"
        for route in routes do
          unless firstNumeralBinding state route do continue
          let family ← nativeOwnedFamily state selected.category.expression categoryFamily route
            row.declaration (fun infos => infos.findIdx? (·.isExplicit)) (some (.numeral row))
          candidates := candidates.push
            (row, .selected ⟨selected, route, categoryFamily, family,
              #[], #[(.numeral row, route.refs)], none⟩)
      for entry in state.objects.filter (·.category == owner) do
        if let some refinement := entry.refines then
          if bases.any (·.id == refinement.base) then
            candidates := candidates.push (row, .refinement entry)
          for (selected, comparison, namedBases) in carrierBases do
            if namedBases.any (·.id == refinement.base) then
              carrierRefinements := carrierRefinements.push
                (row, .carrier selected comparison (some entry))
  let hasSelectedStructure := candidates.any fun (_, context) =>
    match context with
    | .selected _ => true
    | _ => false
  if bases.isEmpty && !hasSelectedStructure then
    let defaults ← sourceLiteralDomains domain
    for base in defaults do
      for row in state.numerals do
        if let some owner := row.over then
          for entry in state.objects.filter (·.category == owner) do
            if entry.refines.any (·.base == base.id) then
              candidates := candidates.push (row, .refinement entry)

  for (_, context) in candidates do
    if let .selected routed := context then
      discard <| levelMVarToParam (← liftM (m := MetaM) <| instantiateMVars routed.family.value)
  candidates ← candidates.mapM fun (row, context) => do
    let .selected routed := context | return (row, context)
    let value ← liftM (m := MetaM) <| instantiateMVars routed.family.value
    if value.hasMVar || value.hasLevelMVar then
      liftM (m := TermElabM) <| throwError "the complete inherited numeral family has undetermined parameters"
    let routed := { routed with
      categoryFamily := ← liftM (m := MetaM) <| instantiateMVars routed.categoryFamily
      family := { routed.family with value } }
    let proof ← numeralCarrierAgreement routed
    return (row, .selected { routed with evidence := #[proof] })
  let mut admitted := #[]
  for (row, context) in candidates do
    let applicable ← SourceReadM.inspect do
      return (← numeralCandidate row context number nativeExpected proofs).isSome
    if applicable then
      admitted := admitted.push (row, context)




  if admitted.isEmpty then
    for (row, context) in carrierRefinements do
      let applicable ← SourceReadM.inspect do
        return (← numeralCandidate row context number nativeExpected proofs).isSome
      if applicable then admitted := admitted.push (row, context)
  let some (row, context) := admitted[0]?
    | do
      let some value ← sourceNullaryNumeral state ownerFamilies number nativeExpected proofs
        | return none
      return some (← finish value)
  let context ← if admitted.size == 1 then pure context else do
    let .selected first := context
      | liftM (m := TermElabM) <| throwSemanticAmbiguity "several declared source point numerals apply in this domain"
    let mut evidence := first.evidence
    let mut alternatives := #[]
    for (_, other) in admitted do
      let .selected other := other
        | liftM (m := TermElabM) <| throwSemanticAmbiguity "several declared source point numerals apply in this domain"
      unless first.owner.value == other.owner.value &&
          first.owner.category.expression.syntacticEq other.owner.category.expression &&
          (← isDefEq first.owner.category.bundle other.owner.category.bundle) do
        liftM (m := TermElabM) <| throwSemanticAmbiguity "the source numeral requires its selected original structure"
      let comparisons := first.owner.category.carrier.toArray.flatMap (·.comparisons) ++
        other.owner.category.carrier.toArray.flatMap (·.comparisons)
      let some proof ← sourceFamilyConversion first.family.value other.family.value comparisons
        | do
        liftM (m := TermElabM) <| throwSemanticAmbiguity
          s!"inherited point families require their supplied whole agreement: {repr (first.alternatives.map fun (reference, route) => (reference.declaration, route))} and {repr (other.alternatives.map fun (reference, route) => (reference.declaration, route))}"
      evidence := evidence ++ other.evidence.push proof
      alternatives := alternatives ++ other.alternatives
    pure (.selected { first with evidence, alternatives })
  let some value ← numeralCandidate row context number nativeExpected proofs
    | liftM (m := TermElabM) <| throwError "the selected source numeral changed its admitted boundary"
  return some (← finish value)



opaque sourceNumeral (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (number : Nat) (expected : Expr) (proofs : Array Term := #[]) : SourceReadM Expr := do
  let some value ← sourceNumeral? categoryOf number expected proofs
    | liftM (m := TermElabM) <| throwError (MessageData.tagged `CasCompiler.sourceNumeral.noAdmittedPoint
      "no declared source point numeral was admitted in the supplied domain")
  return value



private def sourceObjectLiteral (selected : NativeSourceCategory) (expected : Expr)
    (readLiteral : Name → Expr → TermElabM Expr) :
    SourceReadM (Option NativeSourceJudgement) := do
  unless selected.role == .object do return none
  let .atom category := selected.expression | return none
  let rows := (← semanticState).literals.filter (·.category == category)
  if rows.isEmpty then return none
  let #[row] := rows
    | liftM (m := TermElabM) <| throwSemanticAmbiguity "the selected category requires its literal form"
  discard <| checkedDeclaration row.type
  discard <| checkedDeclaration row.denotation
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[selected.bundle]
  unless ← isDefEq expected carrier do
    liftM (m := TermElabM) <| throwError "the object literal has a different complete selected category"
  let literalType ← mkConstWithFreshMVarLevels row.type
  let literal ← readLiteral row.type literalType
  let value ← mkAppM row.denotation #[literal]
  unless ← isDefEq (← inferType value) carrier do
    liftM (m := TermElabM) <| throwError "the registered literal denotation has a different selected category"
  let value ← liftM (m := MetaM) <| instantiateMVars value
  if value.hasMVar || value.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the registered object literal has undetermined parameters"
  let value ← SourceReadM.select { (← sourceReferenceAt (.literal row) value value) with
    category := some selected } (some expected)
  return some ⟨value, some selected⟩



def sourceObjectNumeral (number : Nat) (selected : NativeSourceCategory)
    (expected : Expr) : SourceReadM (Option NativeSourceJudgement) :=
  sourceObjectLiteral selected expected fun _ literalType => do
    let source : Term := ⟨Syntax.mkNumLit (toString number)⟩
    elabTermEnsuringType source (some literalType)



def sourceObjectNamedLiteral (name : Name) (selected : NativeSourceCategory)
    (expected : Expr) : SourceReadM (Option NativeSourceJudgement) :=
  sourceObjectLiteral selected expected fun typeName literalType => do
    let declaration := typeName ++ name
    discard <| checkedDeclaration declaration
    elabTermEnsuringType (mkIdent declaration) (some literalType)

end CasCompiler
