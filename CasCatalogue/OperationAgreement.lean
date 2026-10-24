/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.CategoryContext
public import CasCatalogue.Decide

@[expose] public section

/-!
# Checked agreement of complete routed operation families

This consumes `lean-categories/Catalogue/Registry/operation-agreement.md`.
The source category's entire dependent telescope and the source object are rigid
before either registered operation is formed. Numeral parameters remain variables.
Only a checked equality of those whole families can join different bindings.
The selected object, numeral values and operands enter after that proof exists.
-/

open Lean Meta Elab Term

namespace CasCatalogue.OperationAgreement

def closed (value : Expr) : Bool :=
  !value.hasMVar && !value.hasLevelMVar && !value.hasFVar && !value.hasLooseBVars

/-- Compare every ordered declaration argument before the returned map can unfold.
This is also required after instantiating a universal comparison: an ignored
argument must not disappear merely because its returned function is constant. -/
def sameApplication (left right : Expr) : MetaM Bool := withoutModifyingState do
  let mut left := left.consumeMData
  let mut right := right.consumeMData
  while left.isAppOfArity ``id 2 do left := left.appArg!.consumeMData
  while right.isAppOfArity ``id 2 do right := right.appArg!.consumeMData
  if left == right then return true
  unless left.getAppFn.constName?.isSome &&
      left.getAppFn.constName? == right.getAppFn.constName? &&
      left.getAppArgs.size == right.getAppArgs.size do return false
  if left.hasMVar || left.hasLevelMVar || right.hasMVar || right.hasLevelMVar then return false
  for (a, b) in left.getAppArgs.zip right.getAppArgs do
    unless ← withTransparency .all <|
        isDefEq (← inferType a) (← inferType b) <&&> isDefEq a b do return false
  withTransparency .all <|
    isDefEq (← inferType left) (← inferType right) <&&> isDefEq left right

/-- Both routes must start at the very same complete selected source. The category
dictionary and the source declaration's parameters are checked before conversion. -/
def sameSource (left right : OperationSource) : TermElabM Bool := withoutModifyingState do
  unless left.context.expression.syntacticEq right.context.expression do return false
  unless ← sameApplication left.context.bundle right.context.bundle do return false
  sameApplication left.receiver right.receiver

/-- The registered schema of the complete source category, without choosing any of
its parameters from a selected object. Derived constructors use their accepted schema. -/
def sourceSchema (state : RegistryState) (expression : CategoryExpr) :
    TermElabM (Name × Bool) := do
  if let some row := CategoryContext.named? state expression then
    return (row.declaration, false)
  match expression with
  | .construct id _ =>
      let some row := state.constructor? id
        | throwStratum .invalid "an operation source has no registered category constructor"
      return (row.semantics, false)
  | .familyTotal id =>
      let some row := state.categoryFamily? id
        | throwStratum .invalid "an operation source has no registered category family"
      return (row.realization, true)
  | _ => throwStratum .invalid "an operation source has no complete registered category schema"

def sourceBundle (application : Expr) (total : Bool) : MetaM Expr :=
  if total then mkAppM ``CasCatalogue.CategoryFamilyRealization.totalCat #[application]
  else pure application

/-- Form a whole operation from the supplied rigid owner and numeral parameters.
Any other dependent argument must be fixed by that complete context; an unresolved
argument is not universal evidence and cannot be specialized from a selected object. -/
def applicationAt (entry : OperationEntry) (owner : Expr) (numerals : Array Expr) :
    TermElabM Expr := do
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  unless arguments.size > entry.numerals && numerals.size == entry.numerals do
    throwStratum .invalid "an operation family has an incomplete dependent telescope"
  let ownerSlot := arguments.size - 1 - entry.numerals
  for earlier in arguments.extract 0 ownerSlot do
    let earlier ← instantiateMVars earlier
    unless earlier.isMVar do continue
    let expected ← whnfR (← inferType earlier)
    let some typeName := expected.getAppFn.constName? | continue
    unless isStructure (← getEnv) typeName do continue
    let .inductInfo info ← getConstInfo typeName | continue
    let [constructor] := info.ctors | continue
    let constructor ← mkConstWithFreshMVarLevels constructor
    let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
    unless ← withTransparency .all <| isDefEq result expected do
      throwStratum .invalid "an operation parameter has no complete structure constructor"
    unless ← isDefEq earlier (mkAppN constructor fields) do
      throwStratum .invalid "an operation parameter cannot retain its complete fields"
  unless ← withTransparency .all <|
      isDefEq (← inferType owner) (← inferType arguments[ownerSlot]!) <&&>
        isDefEq arguments[ownerSlot]! owner do
    throwStratum .invalid "the routed object is outside the complete operation owner"
  for (parameter, numeral) in (arguments.extract (ownerSlot + 1) arguments.size).zip numerals do
    unless (← inferType parameter).isConstOf ``Nat &&
        (← isDefEq parameter numeral) do
      throwStratum .invalid "an operation family lost a rigid numeral parameter"
  for (argument, info) in arguments.zip infos do
    unless info.isInstImplicit && (← instantiateMVars argument).isMVar do continue
    let type ← instantiateMVars (← inferType argument)
    unless !type.hasMVar do continue
    if let some instanceValue ← synthInstance? type then
      discard <| isDefEq argument instanceValue
  let application ← instantiateMVars (mkAppN constant arguments)
  if application.hasMVar || application.hasLevelMVar || !(← isTypeCorrect application) then
    throwStratum .invalid "the operation family retains an unresolved declaration parameter"
  return application

/-- The exact registered route action, formed before substituting the selected object. -/
def routedApplication (state : RegistryState) (entry : OperationEntry)
    (context : CategoryContext) (receiver : Expr) (route : Array EdgeRef)
    (numerals : Array Expr) : TermElabM Expr := do
  let some owner := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid "an operation family has no registered owner"
  let some steps := state.toSemanticState.routeEdges? context.expression owner.expression route
    | throwStratum .invalid "an operation family has an invalid structural route"
  let routeDescription : Route :=
    { source := context.expression, target := owner.expression, steps }
  unless state.toSemanticState.isFirstOperationBindingRoute entry.name routeDescription do
    throwStratum .invalid "an operation family crosses an earlier explicit binding"
  let (image, applications) ← if route.isEmpty then pure (receiver, #[]) else do
    let (action, applications) ← Semantic.routeFunctorWithApplications state route
    let (source, _) ← functorCategoryBundles action
    unless ← withTransparency .all <| isDefEq source context.bundle do
      throwStratum .invalid "an operation family changed its complete source category"
    pure (← Semantic.objOf action receiver, applications)
  let application ← applicationAt entry image numerals
  let applications ← applications.mapM instantiateMVars
  unless applications.all (fun value => !value.hasMVar && !value.hasLevelMVar) do
    throwStratum .invalid "an operation family retains an unresolved route parameter"
  return application

/-- Introduce every numeral parameter as a rigid local in its declared order. -/
def withNumerals {α : Type} (count : Nat) (body : Array Expr → TermElabM α) : TermElabM α :=
  let rec go (remaining : Nat) (parameters : Array Expr) : TermElabM α := do
    match remaining with
    | 0 => body parameters
    | n + 1 =>
        withLocalDeclD (Name.mkSimple s!"numeral{parameters.size}") (mkConst ``Nat) fun parameter =>
          go n (parameters.push parameter)
  go count #[]

/-- Reconstruct both complete families in one shared rigid dependent context.
No actual selected source, category parameter, or numeral value enters this construction. -/
def universalFamilies (state : RegistryState) (expression : CategoryExpr)
    (left right : OperationEntry) (leftRoute rightRoute : Array EdgeRef) :
    TermElabM (Expr × Expr) := do
  unless left.name == right.name && left.arity == right.arity &&
      left.numerals == right.numerals && left.result == right.result do
    throwStratum .invalid "the inherited operation families have different complete signatures"
  let (schema, total) ← sourceSchema state expression
  let constant ← mkConstWithFreshMVarLevels schema
  forallTelescopeReducing (← inferType constant) fun parameters _ => do
    let bundle ← sourceBundle (mkAppN constant parameters) total
    let context : CategoryContext := { expression, bundle }
    let carrier ← CategoryContext.carrier context
    withLocalDeclD `selected carrier fun receiver => do
      withNumerals left.numerals fun numerals => do
        let left ← routedApplication state left context receiver leftRoute numerals
        let right ← routedApplication state right context receiver rightRoute numerals
        let locals := parameters ++ #[receiver] ++ numerals
        let left ← instantiateMVars (← mkLambdaFVars locals left)
        let right ← instantiateMVars (← mkLambdaFVars locals right)
        unless closed left && closed right do
          throwStratum .invalid "the operation comparison omitted part of its universal context"
        return (left, right)

/-- Stable serialization keys are consulted only after the entire class is checked.
They have no role in applicability, mathematical equality, or computational availability. -/
def candidateLess (left right : OperationCandidate) : Bool :=
  if left.operation == right.operation then left.application.lt right.application
  else left.operation.raw < right.operation.raw

def sourceKey (source : OperationSource) : String :=
  reprStr source.context.expression ++ ":" ++ reprStr source.context.bundle ++ ":" ++
    reprStr source.receiver ++ ":" ++ reprStr source.route ++ ":" ++ reprStr source.applications ++
    ":" ++ reprStr source.comparisons ++ ":" ++ reprStr source.comparisonWitnesses

/-- Exact duplicate provenance may be shared; different routes or comparison witnesses
remain separate even when they produce the same complete owner application. -/
def sameSourceData (left right : OperationSource) : Bool :=
  left.context.expression.syntacticEq right.context.expression &&
    left.context.bundle == right.context.bundle && left.receiver == right.receiver &&
    left.route == right.route && left.applications == right.applications &&
    left.comparisons == right.comparisons && left.comparisonWitnesses == right.comparisonWitnesses

/-- The complete declaration suffix reserved by the public operation signature. -/
def numeralArguments (entry : OperationEntry) (application : Expr) : TermElabM (Array Expr) := do
  let mut application := application.consumeMData
  while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
  unless application.getAppFn.isConstOf entry.declaration do
    throwStratum .invalid "an operation candidate has a different registered declaration"
  let arguments := application.getAppArgs
  unless arguments.size > entry.numerals do
    throwStratum .invalid "an operation candidate omitted its complete owner"
  let numerals := arguments.extract (arguments.size - entry.numerals) arguments.size
  for numeral in numerals do
    unless closed numeral && (← inferType numeral).isConstOf ``Nat do
      throwStratum .invalid "an operation candidate has an incomplete numeral parameter"
  return numerals

/-- Recover only the instantiation of an already proved universal family. The complete
selected bundle is matched as its registered declaration, including every argument. -/
def selectedParameters (state : RegistryState) (source : OperationSource)
    (entry : OperationEntry) (application : Expr) : TermElabM (Array Expr) := do
  let (schema, total) ← sourceSchema state source.context.expression
  let presented ← CategoryContext.presented source.context
  let constant ← mkConstWithFreshMVarLevels schema
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  let bundle ← sourceBundle (mkAppN constant parameters) total
  unless ← withTransparency .all <| isDefEq bundle presented.bundle do
    throwStratum .invalid "the operation comparison has a different selected category bundle"
  let bundle ← instantiateMVars bundle
  let parameters ← parameters.mapM instantiateMVars
  unless closed bundle && parameters.all closed &&
      (← sameApplication bundle presented.bundle) do
    throwStratum .invalid "the operation comparison did not retain every selected category parameter"
  return parameters ++ #[source.receiver] ++ (← numeralArguments entry application)

/-- Match an exact registered edge application argument by argument, before its functor
body can erase a selected parameter. Fresh schema parameters must all close. -/
def checkEdgeApplication (state : RegistryState) (edge : EdgeRef) (actual : Expr) :
    TermElabM Unit := do
  unless closed actual && (← isTypeCorrect actual) do
    throwStratum .invalid "an operation route contains an incomplete edge application"
  let expected ← Semantic.edgeFunctor state edge
  unless expected.getAppFn.constName? == actual.getAppFn.constName? &&
      expected.getAppArgs.size == actual.getAppArgs.size &&
      (← isDefEq expected.getAppFn actual.getAppFn) do
    throwStratum .invalid "an operation route replaced a registered edge declaration"
  for (parameter, argument) in expected.getAppArgs.zip actual.getAppArgs do
    unless ← withTransparency .all <|
        isDefEq (← inferType parameter) (← inferType argument) <&&>
          isDefEq parameter argument do
      throwStratum .invalid "an operation route changed an ordered edge parameter"
  let expected ← instantiateMVars expected
  unless closed expected && (← sameApplication expected actual) do
    throwStratum .invalid "an operation route erased an undetermined edge parameter"
  discard <| Semantic.edgeEndpoints? state edge actual

/-- Recheck the complete selected route, its actual comparison witnesses, and its owner
application. This does not decide agreement with any other candidate. -/
def validateSource (state : RegistryState) (entry : OperationEntry)
    (application : Expr) (source : OperationSource) : TermElabM Unit := do
  unless closed source.context.bundle && closed source.receiver &&
      source.route.size == source.applications.size &&
      source.comparisons.size == source.comparisonWitnesses.size do
    throwStratum .invalid "an operation source lost complete route or comparison data"
  CategoryContext.checkObject source.context source.receiver
  let some owner := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid "an operation candidate has no registered owner category"
  let some steps := state.toSemanticState.routeEdges?
      source.context.expression owner.expression source.route
    | throwStratum .invalid "an operation source has no accepted structural route"
  unless state.toSemanticState.isFirstOperationBindingRoute entry.name
      { source := source.context.expression, target := owner.expression, steps } do
    throwStratum .invalid "an operation source crosses an earlier binding"
  for (edge, application) in source.route.zip source.applications do
    checkEdgeApplication state edge application
  let witnesses ← Semantic.validateRouteComparisons state source.comparisons (some source.receiver)
  for (expected, actual) in witnesses.zip source.comparisonWitnesses do
    unless closed actual && (← isTypeCorrect actual) &&
        (← sameApplication expected actual) do
      throwStratum .invalid "an operation source changed its accepted comparison witness"
  let owner ← if source.route.isEmpty then pure source.receiver else do
    let action ← Semantic.compositeOfApplications source.applications
    let (actualSource, _) ← functorCategoryBundles action
    unless ← withTransparency .all <| isDefEq actualSource source.context.bundle do
      throwStratum .invalid "an operation source changed its complete category dictionary"
    Semantic.objOf action source.receiver
  let actual ← applicationAt entry owner (← numeralArguments entry application)
  unless ← sameApplication actual application do
    throwStratum .invalid "an operation candidate changed a complete selected owner or parameter"

/-- Prove the universal equation first; only afterward close its actual selected
instantiation and compare every ordered argument with both original applications. -/
def compareSources (state : RegistryState) (left right : OperationCandidate)
    (leftSource rightSource : OperationSource) :
    TermElabM (Option OperationFamilyComparison) := withoutModifyingState do
  unless ← sameSource leftSource rightSource do return none
  let some leftEntry := state.operations.find? (·.id == left.operation)
    | throwStratum .invalid "an operation comparison names an absent left binding"
  let some rightEntry := state.operations.find? (·.id == right.operation)
    | throwStratum .invalid "an operation comparison names an absent right binding"
  let families ← try
      some <$> universalFamilies state leftSource.context.expression leftEntry rightEntry
        leftSource.route rightSource.route
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
  let some (leftFamily, rightFamily) := families | return none
  let leftType ← inferType leftFamily
  let rightType ← inferType rightFamily
  unless closed leftType && closed rightType &&
      (← withTransparency .all <| isDefEq leftType rightType <&&>
        isDefEq leftFamily rightFamily) do return none
  let equality ← mkEq leftFamily rightFamily
  let identity ← mkEqRefl leftFamily
  unless closed identity && (← Decide.kernelAccepts equality identity) do return none
  let parameters ← selectedParameters state leftSource leftEntry left.application
  let otherParameters ← selectedParameters state rightSource rightEntry right.application
  unless parameters.size == otherParameters.size do return none
  for (left, right) in parameters.zip otherParameters do
    unless ← sameApplication left right do return none
  unless (← sameApplication (mkAppN leftFamily parameters).headBeta left.application) &&
      (← sameApplication (mkAppN rightFamily parameters).headBeta right.application) do
    return none
  return some {
    left := 0, right := 0, leftSource := 0, rightSource := 0, parameters
    leftFamily, rightFamily, leftType, rightType, identity }

/-- Build one edge of the candidate equivalence class, retaining the exact pair of
complete source witnesses used by its universal equality. -/
def compare (leftIndex rightIndex : Nat) (left right : OperationCandidate) :
    TermElabM (Option OperationFamilyComparison) := do
  let state ← registryState
  for leftSourceIndex in [:left.sources.size] do
    for rightSourceIndex in [:right.sources.size] do
      let some leftSource := left.sources[leftSourceIndex]? | unreachable!
      let some rightSource := right.sources[rightSourceIndex]? | unreachable!
      if let some comparison ← compareSources state left right leftSource rightSource then
        return some { comparison with
          left := leftIndex, right := rightIndex
          leftSource := leftSourceIndex, rightSource := rightSourceIndex }
  return none

/-- Independently revalidate the exact closed universal equality and its rigid actual
instantiation. An equality merely true after selected values are substituted is rejected. -/
def validateComparison (state : RegistryState) (candidates : Array OperationCandidate)
    (comparison : OperationFamilyComparison) : TermElabM Unit := do
  let some left := candidates[comparison.left]?
    | throwStratum .invalid "an operation comparison has an invalid left index"
  let some right := candidates[comparison.right]?
    | throwStratum .invalid "an operation comparison has an invalid right index"
  let some leftSource := left.sources[comparison.leftSource]?
    | throwStratum .invalid "an operation comparison omitted its left source"
  let some rightSource := right.sources[comparison.rightSource]?
    | throwStratum .invalid "an operation comparison omitted its right source"
  let some expected ← compareSources state left right leftSource rightSource
    | throwStratum .invalid "the retained operation families have no universal agreement"
  unless comparison.parameters.size == expected.parameters.size do
    throwStratum .invalid "an operation comparison omitted a dependent parameter"
  for (actual, expected) in comparison.parameters.zip expected.parameters do
    unless closed actual && (← sameApplication actual expected) do
      throwStratum .invalid "an operation comparison changed an ordered selected parameter"
  for (actual, expected) in #[
      (comparison.leftFamily, expected.leftFamily),
      (comparison.rightFamily, expected.rightFamily),
      (comparison.leftType, expected.leftType),
      (comparison.rightType, expected.rightType)] do
    -- Exact alpha equivalence retains the original routed declaration syntax. A
    -- constant family may otherwise hide a selected-value substitution or omission.
    unless closed actual && actual == expected && (← isTypeCorrect actual) do
      throwStratum .invalid "an operation comparison changed its complete universal family or type"
  let equality ← mkEq comparison.leftFamily comparison.rightFamily
  unless closed comparison.identity && comparison.identity == expected.identity &&
      (← Decide.kernelAccepts equality comparison.identity) do
    throwStratum .invalid "the operation's universal equality is not accepted by Lean"

/-- Validate the full closed equivalence class before computational forwarding.
Candidate order is a deterministic serialization order after proof, independent of
registry storage order and leaf availability. Every original binding and route remains. -/
def validate (representative : Expr) (chosen : Nat)
    (candidates : Array OperationCandidate) (comparisons : Array OperationFamilyComparison) :
    TermElabM Unit := do
  let state ← registryState
  let some selected := candidates[chosen]?
    | throwStratum .invalid "the operation class has no selected representative"
  unless chosen == 0 && representative == selected.result && closed representative &&
      (← isTypeCorrect representative) do
    throwStratum .invalid "the operation class changed its exact representation child"
  for index in [:candidates.size] do
    let some candidate := candidates[index]? | unreachable!
    if index > 0 then
      let some previous := candidates[index - 1]? | unreachable!
      if candidateLess candidate previous then
        throwStratum .invalid "the checked operation class is not canonically ordered"
    let some entry := state.operations.find? (·.id == candidate.operation)
      | throwStratum .invalid "the operation class contains an absent binding"
    unless closed candidate.application && closed candidate.result &&
        !candidate.sources.isEmpty && (← isTypeCorrect candidate.application) &&
        (← isTypeCorrect candidate.result) do
      throwStratum .invalid "the operation class contains an incomplete typed candidate"
    discard <| numeralArguments entry candidate.application
    for source in candidate.sources do
      validateSource state entry candidate.application source
  for comparison in comparisons do validateComparison state candidates comparison
  let mut reached := Array.replicate candidates.size false
  reached := reached.set! chosen true
  for _ in [:candidates.size] do
    for comparison in comparisons do
      if reached[comparison.left]! || reached[comparison.right]! then
        reached := reached.set! comparison.left true
        reached := reached.set! comparison.right true
  unless reached.all id do
    throwStratum .invalid "the retained comparisons do not establish one complete operation class"
  for candidate in candidates do
    unless ← withTransparency .all <|
        isDefEq (← inferType candidate.result) (← inferType representative) <&&>
          isDefEq candidate.result representative do
      throwStratum .invalid "an operation result changed the checked class's actual operands or target"

end CasCatalogue.OperationAgreement
