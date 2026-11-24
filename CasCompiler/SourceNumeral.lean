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
  alternatives : Array (String × Array EdgeRef) := #[]
  terminal : Option Expr := none

private inductive NumeralContext where
  | direct
  | carrier (owner : NativeSourceElementOwner) (comparison : Expr)
  | selected (routed : RoutedNumeral)
  | refinement (entry : ObjectEntry)

-- The point must land in the complete selected carrier family before specialization.
-- Reuse sourceCarrier's explicit prefix and whole-functor agreement rules.
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

-- Source rule: CasCatalogue.Language.decideObligation, using native checked decisions.
private def numeralProof (proposition : Expr) : MetaM (Option Expr) := do
  if proposition.isAppOfArity ``Eq 3 then
    let arguments := proposition.getAppArgs
    if ← withoutModifyingState <| isDefEq arguments[1]! arguments[2]! then
      return some (← mkEqRefl arguments[1]!)
  let decision ← mkDecide proposition
  unless (← withAtLeastTransparency .default <| whnf decision).isConstOf ``Bool.true do
    return none
  return some (← mkDecideProof proposition)

-- Resolve only proof and instance fields, in declaration order. All mathematical data
-- parameters must already come from the actual domain, literal or selected structure.
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

/-- Form only the source's actual point map, with its actual refinement comparison.
Reuse: NumeralEntry's last natural parameter and explicit proof obligations;
ObjectRefinement's checked shared telescope and directed identification. -/
private def numeralCandidate (row : NumeralEntry) (context : NumeralContext)
    (number : Nat) (expected : Expr) (proofs : Array Term) : TermElabM (Option Expr) := do
  let (object, comparison, proofIndex) ← match context with
    | .direct => pure (none, none, 0)
    | .carrier _ comparison => do
      let comparison ← mkAppM ``CategoryTheory.Iso.symm #[comparison]
      let type ← whnfR (← inferType comparison)
      unless ← isDefEq type.getAppArgs[3]! expected do return none
      pure (none, some comparison, 0)
    | .selected routed => do
      let selected ← nativeRouteFunctor (← semanticState) routed.route routed.owner.category.bundle
      let value ← functorObject selected.functor routed.owner.value selected.target
      pure (some value, none, 0)
    | .refinement entry => do
      let some refinement := entry.refines
        | throwError "a source numeral refinement has no declared comparison"
      discard <| checkedDeclaration entry.declaration
      discard <| checkedDeclaration refinement.identification
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (parameters, binders, _) ← forallMetaTelescopeReducing (← inferType declaration)
      let comparison ← applyObjectParameters entry.id.raw refinement.identification parameters
      let type ← whnfR (← inferType comparison)
      unless type.isAppOfArity ``CategoryTheory.Iso 4 do
        throwError "a source numeral refinement requires its complete native isomorphism"
      unless ← isDefEq type.getAppArgs[3]! expected do return none
      let some proofIndex ← completePointParameters parameters binders proofs 0
        | throwError "the source numeral's declared domain obligation is not established"
      let object := sourceReference ``ObjectEntry entry.id.raw entry.declaration
        (mkAppN declaration parameters)
      pure (some object, some comparison, proofIndex)
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (arguments, binders, type) ← forallMetaTelescopeReducing (← inferType declaration)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "a registered numeral requires its complete native point signature"
  let explicit := (List.range arguments.size).toArray.filter (binders[·]!.isExplicit)
  let some literal ← explicit.reverse.findM? fun index =>
      return (← inferType arguments[index]!).isConstOf ``Nat
    | throwError "a registered numeral has no declared natural parameter"
  if let some object := object then
    let some first := explicit[0]?
      | throwError "a registered numeral has no declared structural object parameter"
    unless ← isDefEq arguments[first]! object do return none
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
    let proposition ← instantiateMVars (← inferType arguments[index]!)
    unless ← isProp proposition do
      throwError "a registered numeral's trailing obligations must be propositions"
  let some proofIndex ← completePointParameters arguments binders proofs proofIndex
    | throwError "the source numeral's declared domain obligation is not established"
  unless proofIndex == proofs.size do
    throwError "the source numeral has evidence beyond its declared domain obligations"
  let point ← instantiateMVars (mkAppN declaration arguments)
  if point.hasMVar || point.hasLevelMVar then
    throwError "the registered source numeral is not determined at its complete boundary"
  let point ← match comparison with
    | none => pure point
    | some comparison => do
      let comparison ← instantiateMVars comparison
      let type ← whnfR (← inferType comparison)
      let hom ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
      let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
      let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
        #[some type.getAppArgs[0]!, some categoryStructure]
      elabAppArgs composition #[] #[Arg.expr point, Arg.expr hom] none false false
  let type ← inferType point
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the admitted numeral is not a native point map"
  let source := type.getAppArgs[2]!
  let terminalPoint ← mkAppOptM ``default #[some source, none]
  let function ← sourceSetFunction point
  let value ← elabAppArgs function #[] #[Arg.expr terminalPoint] (some expected) false false
  let value ← retainSourcePoint point value
  let value ← match context with
    | .carrier owner _ =>
      withLetDecl (← mkFreshUserName `numeralCarrierAgreement)
        (← inferType owner.evidence) owner.evidence fun binding =>
          mkLetFVars #[binding] value (usedLetOnly := false) (generalizeNondepLet := false)
    | .selected routed => do
      let mut value := value
      for evidence in (routed.evidence.push routed.owner.evidence).reverse do
        let body := value
        value ← withLetDecl (← mkFreshUserName `numeralOwnerAgreement)
          (← inferType evidence) evidence fun binding =>
            mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
      pure <| Expr.mdata
        (KVMap.empty.setString `CasCompiler.source.numeralRoutes
          (reprStr routed.alternatives)) value
    | _ => pure value
  return some value

-- A nullary row's arity does not itself prove that its complete native source is
-- terminal. Retain the existing Unique dictionary at the rigid family, before an
-- actual object or category parameter is substituted.
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

-- Apply the native default field of this already checked Unique dictionary.
-- No unrelated Inhabited or OfNat instance can replace its selected point.
private def uniquePoint (unique : Expr) : MetaM Expr := do
  let inhabited ← mkProjection unique `toInhabited
  mkProjection inhabited `default

-- Specialize only the already checked nullary family, against the complete
-- selected category and its exact original object. The terminal dictionary is
-- specialized with the same arguments, rather than inferred again from a value.
private def nullaryNumeralCandidate (routed : RoutedNumeral) (expected : Expr)
    (proofs : Array Term) : TermElabM Expr := do
  unless proofs.isEmpty do
    throwError "the nullary source operation has no numeral obligations"
  let some terminal := routed.terminal
    | throwError "the nullary source operation lost its terminal family"
  let mut collected : CollectLevelParams.State := {}
  collected := collected.collect routed.categoryFamily
  collected := collected.collect routed.family.value
  collected := collected.collect terminal
  let universes := collected.params.toList
  let levels ← universes.mapM fun _ => mkFreshLevelMVar
  let categoryFamily := routed.categoryFamily.instantiateLevelParams universes levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  unless ← isDefEq (mkAppN categoryFamily parameters) routed.owner.category.bundle do
    throwError "the nullary operation has a different complete selected category"
  let family := routed.family.value.instantiateLevelParams universes levels
  let function := mkAppN family parameters
  let (arguments, binders, _) ← forallMetaTelescopeReducing (← inferType function)
  let objectIndex := routed.family.objectIndex - parameters.size
  let some object := arguments[objectIndex]?
    | throwError "the nullary operation lost its selected object parameter"
  unless ← isDefEq object routed.owner.value do
    throwError "the nullary operation changed its actual selected object"
  let some _ ← completePointParameters arguments binders #[] 0
    | throwError "the nullary operation has unestablished native obligations"
  let actual ← (parameters ++ arguments).mapM instantiateMVars
  let point ← instantiateMVars (mkAppN family actual)
  let terminal ← instantiateMVars
    (mkAppN (terminal.instantiateLevelParams universes levels) actual)
  if point.hasMVar || point.hasLevelMVar || terminal.hasMVar || terminal.hasLevelMVar then
    throwError "the nullary operation requires its complete original parameters"
  let type ← whnfR (← inferType point)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "the nullary operation lost its complete native point"
  unless ← isDefEq (← inferType terminal)
      (← mkAppM ``Unique #[← declaredEndpoint type.getAppArgs[2]!]) do
    throwError "the nullary operation changed its complete terminal source"
  unless ← isDefEq type.getAppArgs[3]! expected do
    throwError "the nullary operation has a different complete selected carrier"
  let argument ← uniquePoint terminal
  let function ← sourceSetFunction point
  let value ← elabAppArgs function #[] #[Arg.expr argument] (some expected) false false
  let mut value ← retainSourcePoint point value
  for evidence in (routed.evidence.push routed.owner.evidence).reverse do
    let body := value
    value ← withLetDecl (← mkFreshUserName `numeralOwnerAgreement)
      (← inferType evidence) evidence fun binding =>
        mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
  return .mdata
    (KVMap.empty.setString `CasCompiler.source.numeralRoutes (reprStr routed.alternatives)) value

-- T034's existing numeric syntax resolves registered numerals before an inherited
-- nullary operation (Language at 92916e1, lines 8015-8017 and 8143-8154). Enter
-- this lookup only when no numeral reading applies; semantic failures are not
-- absence. The exact token selects first-hit operations, whose complete native
-- families must agree before any actual source object is supplied.
private def sourceNullaryNumeral (state : SemanticState)
    (ownerFamilies : Array (NativeSourceElementOwner × Expr))
    (number : Nat) (expected : Expr) (proofs : Array Term) : TermElabM Expr := do
  let mut candidates : Array (OperationEntry × RoutedNumeral) := #[]
  let mut hasBinding := false
  for (selected, categoryFamily) in ownerFamilies do
    let paths ← SourceRoutes.forOperation selected.category.expression (toString number)
    let some routes ← paths.finiteRoutes
      | throwUnsupportedSource "nullary numeral inheritance requires its supplied uniform comparison"
    for route in routes do
      for row in state.operationBindings route.target (toString number) do
        hasBinding := true
        unless row.arity == 0 && row.numerals == 0 do continue
        let family ← nativeOwnedFamily state selected.category.expression categoryFamily route
          row.declaration (fun infos => if infos.isEmpty then none else some (infos.size - 1))
        candidates := candidates.push
          (row, ⟨selected, route, categoryFamily, family,
            #[], #[(row.id.raw, route.refs)], none⟩)
  for (_, routed) in candidates do
    discard <| levelMVarToParam (← instantiateMVars routed.family.value)
  candidates ← candidates.mapM fun (row, routed) => do
    let value ← instantiateMVars routed.family.value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the complete nullary point family has undetermined parameters"
    let routed := { routed with
      categoryFamily := ← instantiateMVars routed.categoryFamily
      family := { routed.family with value } }
    let proof ← numeralCarrierAgreement routed
    let terminal ← nullaryPointTerminal value
    return (row, { routed with evidence := #[proof], terminal := some terminal })
  let some (row, first) := candidates[0]?
    | if hasBinding then
        throwError "the first source numeral operation has a different nullary signature"
      else
        throwError "no declared source point numeral was admitted in the supplied domain; numeral={number}; expected={expected}; owners={ownerFamilies.map (fun (owner, _) => (toJson owner.category.expression).compress)}; values={ownerFamilies.map (fun (owner, _) => owner.value)}"
  let mut evidence := first.evidence
  let mut alternatives := #[]
  for (_, other) in candidates do
    unless first.owner.value == other.owner.value &&
        first.owner.category.expression.syntacticEq other.owner.category.expression &&
        (← isDefEq first.owner.category.bundle other.owner.category.bundle) do
      throwSemanticAmbiguity "the source numeral requires its selected original structure"
    let comparisons := first.owner.category.carrier.toArray.flatMap (·.comparisons) ++
      other.owner.category.carrier.toArray.flatMap (·.comparisons)
    let some proof ← sourceFamilyConversion first.family.value other.family.value comparisons
      | throwSemanticAmbiguity
          s!"inherited point families require their supplied whole agreement: {repr first.alternatives} and {repr other.alternatives}"
    evidence := evidence ++ other.evidence.push proof
    alternatives := alternatives ++ other.alternatives
  let value ← nullaryNumeralCandidate { first with evidence, alternatives } expected proofs
  return sourceReference ``OperationEntry row.id.raw row.declaration value

/-- First-binding lookup for numerals (constitution C6): an inherited numeral route is a reading
only when no numeral row binds at a category before its target. This is the rule that
`SemanticState.isFirstOperationBindingRoute` states for operation names; a farther binding
cannot replace one already found on the same path. -/
private def firstNumeralBinding (state : SemanticState) (route : Route) : Bool :=
  route.steps.all fun edge => !state.categories.any fun entry =>
    entry.expression.syntacticEq edge.source && state.numerals.any (·.over == some entry.id)

/-- Read a numeral from its independent point declarations, not a host OfNat instance.
Nat parameters use the kernel's natural literal. Point domains retain their original source
object identity; refinements require the actual registered object and directed comparison.
Source: Registry.Entry.NumeralEntry and ObjectRefinement, LC-15; #66 source intake contract. -/
opaque sourceNumeral (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (number : Nat) (expected : Expr) (proofs : Array Term := #[]) : TermElabM Expr := do
  if expected.headBeta.isConstOf ``Nat then
    unless proofs.isEmpty do throwError "a natural parameter literal has no domain obligations"
    return mkNatLit number
  let state ← semanticState
  let (domain, bases) ← registeredDomain expected
  let owners ← if bases.isEmpty then sourceElementOwners categoryOf expected #[expected]
    else pure #[]
  let ownerFamilies ← owners.mapM fun owner => do
    let family ← nativeCategoryFamily state owner.category.expression fun _ => mkFreshLevelMVar
    return (owner, family)
  let mut candidates : Array (NumeralEntry × NumeralContext) := #[]
  for row in state.numerals do
    discard <| checkedDeclaration row.declaration
    match row.over with
    | none =>
      candidates := candidates.push (row, .direct)
      -- The selected object's checked carrier presentation licenses transport of a
      -- base point. Native carrier equality alone does not identify that base.
      -- Reuse ObjectRefinement's directed isomorphism and its complete-family validation.
      for owner in owners do
        for comparison in owner.category.carrier.toArray.flatMap (·.comparisons) do
          let type ← whnfR (← inferType comparison)
          unless type.isAppOfArity ``CategoryTheory.Iso 4 do continue
          unless ← withoutModifyingState <| isDefEq type.getAppArgs[2]! expected do continue
          candidates := candidates.push (row, .carrier owner comparison)
    | some owner =>
      let #[category] := state.categories.filter (·.id == owner)
        | throwError "the source numeral requires one registered structural category"
      for (selected, categoryFamily) in ownerFamilies do
        let paths ← SourceRoutes.forOwner selected.category.expression category.expression
        let some routes ← paths.finiteRoutes
          | throwUnsupportedSource "numeral inheritance requires its supplied uniform comparison"
        for route in routes do
          unless firstNumeralBinding state route do continue
          let family ← nativeOwnedFamily state selected.category.expression categoryFamily route
            row.declaration (fun infos => infos.findIdx? (·.isExplicit))
          candidates := candidates.push
            (row, .selected ⟨selected, route, categoryFamily, family,
              #[], #[(row.id.raw, route.refs)], none⟩)
      for entry in state.objects.filter (·.category == owner) do
        if let some refinement := entry.refines then
          if bases.any (·.id == refinement.base) then
            candidates := candidates.push (row, .refinement entry)
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
  -- Freeze every whole-family universe before checking carriers or point agreement.
  for (_, context) in candidates do
    if let .selected routed := context then
      discard <| levelMVarToParam (← instantiateMVars routed.family.value)
  candidates ← candidates.mapM fun (row, context) => do
    let .selected routed := context | return (row, context)
    let value ← instantiateMVars routed.family.value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the complete inherited numeral family has undetermined parameters"
    let routed := { routed with
      categoryFamily := ← instantiateMVars routed.categoryFamily
      family := { routed.family with value } }
    let proof ← numeralCarrierAgreement routed
    return (row, .selected { routed with evidence := #[proof] })
  let mut admitted := #[]
  for (row, context) in candidates do
    let applicable ← withoutModifyingState do
      return (← numeralCandidate row context number expected proofs).isSome
    if applicable then
      admitted := admitted.push (row, context)
  let some (row, context) := admitted[0]?
    | return ← sourceNullaryNumeral state ownerFamilies number expected proofs
  let context ← if admitted.size == 1 then pure context else do
    let .selected first := context
      | throwSemanticAmbiguity "several declared source point numerals apply in this domain"
    let mut evidence := first.evidence
    let mut alternatives := #[]
    for (_, other) in admitted do
      let .selected other := other
        | throwSemanticAmbiguity "several declared source point numerals apply in this domain"
      unless first.owner.value == other.owner.value &&
          first.owner.category.expression.syntacticEq other.owner.category.expression &&
          (← isDefEq first.owner.category.bundle other.owner.category.bundle) do
        throwSemanticAmbiguity "the source numeral requires its selected original structure"
      let comparisons := first.owner.category.carrier.toArray.flatMap (·.comparisons) ++
        other.owner.category.carrier.toArray.flatMap (·.comparisons)
      let some proof ← sourceFamilyConversion first.family.value other.family.value comparisons
        | do
        throwSemanticAmbiguity
          s!"inherited point families require their supplied whole agreement: {repr first.alternatives} and {repr other.alternatives}"
      evidence := evidence ++ other.evidence.push proof
      alternatives := alternatives ++ other.alternatives
    pure (.selected { first with evidence, alternatives })
  let some value ← numeralCandidate row context number expected proofs
    | throwError "the selected source numeral changed its admitted boundary"
  return sourceReference ``NumeralEntry row.id.raw row.declaration value

-- Reuse Registry.Entry.LiteralEntry: category identity selects the complete literal
-- boundary before elaborating either existing literal syntax form at its native type.
private def sourceObjectLiteral (selected : NativeSourceCategory) (expected : Expr)
    (readLiteral : Name → Expr → TermElabM Expr) :
    TermElabM (Option NativeSourceJudgement) := do
  unless selected.role == .object do return none
  let .atom category := selected.expression | return none
  let rows := (← semanticState).literals.filter (·.category == category)
  if rows.isEmpty then return none
  let #[row] := rows
    | throwSemanticAmbiguity "the selected category requires its literal form"
  discard <| checkedDeclaration row.type
  discard <| checkedDeclaration row.denotation
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[selected.bundle]
  unless ← isDefEq expected carrier do
    throwError "the object literal has a different complete selected category"
  let literalType ← mkConstWithFreshMVarLevels row.type
  let literal ← readLiteral row.type literalType
  let value ← mkAppM row.denotation #[literal]
  unless ← isDefEq (← inferType value) carrier do
    throwError "the registered literal denotation has a different selected category"
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar then
    throwError "the registered object literal has undetermined parameters"
  return some ⟨sourceReference ``LiteralEntry row.id.raw row.denotation value, some selected⟩

/-- OfNat acts only on the registered literal type; the denotation supplies the object.
Reuse: LiteralEntry and Lean's typed numeral elaborator, not a carrier OfNat instance. -/
def sourceObjectNumeral (number : Nat) (selected : NativeSourceCategory)
    (expected : Expr) : TermElabM (Option NativeSourceJudgement) :=
  sourceObjectLiteral selected expected fun _ literalType => do
    let source : Term := ⟨Syntax.mkNumLit (toString number)⟩
    elabTermEnsuringType source (some literalType)

/-- Named literals use the actual declaration in their registered type's namespace.
Reuse: the public literalExpr namespace rule and LiteralEntry; source is never replayed. -/
def sourceObjectNamedLiteral (name : Name) (selected : NativeSourceCategory)
    (expected : Expr) : TermElabM (Option NativeSourceJudgement) :=
  sourceObjectLiteral selected expected fun typeName literalType => do
    let declaration := typeName ++ name
    discard <| checkedDeclaration declaration
    elabTermEnsuringType (mkIdent declaration) (some literalType)

end CasCompiler
