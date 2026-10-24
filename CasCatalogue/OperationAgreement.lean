/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.CategoryContext
public import CasCatalogue.Decide
public import CasCatalogue.QuestionIdentity

@[expose] public section

/-!
# Checked agreement of complete routed operation families

This consumes `lean-categories/Catalogue/Registry/operation-agreement.md`.
The source category's entire dependent telescope is rigid while the registered
signatures are formed. The source object, numerals and every independent route or
declaration parameter are abstracted before the whole families are compared.
Only a checked equality of those closed universal families can join different bindings.
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

def sourceBundle (application : Expr) (total : Bool) : MetaM Expr :=
  if total then mkAppM ``CasCatalogue.CategoryFamilyRealization.totalCat #[application]
  else pure application

/-- Instantiate a declaration's entire telescope without selecting any actual
parameter. Remaining variables will become rigid binders before comparison. -/
def freshTemplate (declaration : Name) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  return mkAppN constant parameters

/-- Reconstruct the fixed category expression, including every nested constructor
argument. In particular `K(A(p))` is not replaced by `K(C)` for an arbitrary C.
Repeated symbolic arguments share their declared context; no selected value enters. -/
partial def sourceTemplateWith (state : RegistryState)
    (categories : IO.Ref (Array (CategoryExpr × Expr)))
    (objects functors : IO.Ref (Std.HashMap String Expr))
    (expression : CategoryExpr) : TermElabM Expr := do
  if let some (_, value) := (← categories.get).find? (·.1.syntacticEq expression) then
    return value
  let value ← if let some row := CategoryContext.named? state expression then
      freshTemplate row.declaration
    else match expression with
    | .familyTotal id =>
        let some row := state.categoryFamily? id
          | throwStratum .invalid "the complete source names an absent category family"
        sourceBundle (← freshTemplate row.realization) true
    | .construct id arguments => do
        let some row := state.constructor? id
          | throwStratum .invalid "the complete source names an absent category constructor"
        unless arguments.size == row.signature.size do
          throwStratum .invalid "the complete source has the wrong constructor signature"
        let constant ← mkConstWithFreshMVarLevels row.semantics
        let (parameters, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
        let explicit := (parameters.zip infos).filterMap fun (parameter, info) =>
          if info.isExplicit then some parameter else none
        unless explicit.size == arguments.size do
          throwStratum .invalid "the accepted category constructor lost an argument"
        let mut bundles : Array Expr := #[]
        let mut inputs : Array Expr := #[]
        for ((kind, argument), parameter) in (row.signature.zip arguments).zip explicit do
          let input ← match kind, argument with
            | .category, .category inner => do
                let bundle ← sourceTemplateWith state categories objects functors inner
                bundles := bundles.push bundle
                pure bundle
            | .object, .object name => do
                if let some object := (← objects.get)[name.raw]? then pure object
                else
                  objects.modify (·.insert name.raw parameter)
                  pure parameter
            | .functor, .functor id => do
                if let some action := (← functors.get)[id.raw]? then pure action
                else
                  let some entry := state.functor? id
                    | throwStratum .invalid "the constructor names an absent functor argument"
                  let action ← freshTemplate entry.declaration
                  let action ← if ← withoutModifyingState <|
                      isDefEq (← inferType action) (← inferType parameter) then pure action
                    else Semantic.asFunctor action
                  functors.modify (·.insert id.raw action)
                  pure action
            | _, _ => throwStratum .invalid "the constructor argument has a different declared kind"
          unless ← withTransparency .all <|
              isDefEq (← inferType parameter) (← inferType input) <&&>
                isDefEq parameter input do
            throwStratum .invalid "the constructor argument changed its complete dependent type"
          inputs := inputs.push input
        -- The accepted interface pins the full category dictionaries and their
        -- universes, including parameters hidden by a carrier coercion.
        applyConstructorInterface row.semantics bundles inputs
    | _ => throwStratum .invalid "the source expression has no accepted complete realization"
  categories.modify (·.push (expression, value))
  return value

def sourceTemplate (state : RegistryState) (expression : CategoryExpr) : TermElabM Expr := do
  let categories ← IO.mkRef (#[] : Array (CategoryExpr × Expr))
  let objects ← IO.mkRef ({} : Std.HashMap String Expr)
  let functors ← IO.mkRef ({} : Std.HashMap String Expr)
  sourceTemplateWith state categories objects functors expression

/-- Abstract a heterogeneous collection of typed templates through one metavariable
context. Dependencies are introduced before their users; no equation between the
two operations has been tested while these parameters were assignable. -/
def abstractTemplates (templates : Array Expr) (levels : Bool := false) : MetaM (Array Expr) := do
  let templates ← templates.mapM instantiateMVars
  let initial : AbstractMVars.State := {
    mctx := ← getMCtx, lctx := ← getLCtx, ngen := ← getNGen, abstractLevels := levels }
  let (templates, final) := (templates.mapM AbstractMVars.abstractExprMVars).run initial
  setNGen final.ngen
  setMCtx final.mctx
  return templates.map (final.lctx.mkLambda final.fvars)

/-- Source-category parameters are rigid before route or operation signatures can
constrain them. Constructor contexts retain their fixed inner expression. -/
def withSourceTemplate {α : Type} (state : RegistryState) (expression : CategoryExpr)
    (body : Array Expr → CategoryContext → TermElabM α) : TermElabM α := do
  let #[family] ← abstractTemplates #[← sourceTemplate state expression] | unreachable!
  lambdaTelescope family fun parameters bundle =>
    body parameters { expression, bundle }

/-- Form the whole declared operation at its complete owner and numeral context.
Independent declaration parameters remain explicit template variables: consumers
must abstract them before comparison or fill them from an exact actual application. -/
def applicationTemplate (entry : OperationEntry) (owner : Expr) (numerals : Array Expr) :
    TermElabM Expr := do
  let constant ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  unless arguments.size > entry.numerals && numerals.size == entry.numerals do
    throwStratum .invalid "an operation family has an incomplete dependent telescope"
  let ownerSlot := arguments.size - 1 - entry.numerals
  let ownerType ← inferType arguments[ownerSlot]!
  for earlier in arguments.extract 0 ownerSlot do
    let earlier ← instantiateMVars earlier
    unless earlier.isMVar do continue
    -- Only context parameters occurring in the owner's type are exposed to
    -- recover that complete owner. An independent q stays one whole parameter.
    unless (ownerType.findMVar? (· == earlier.mvarId!)).isSome do continue
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
  let application ← instantiateMVars (mkAppN constant arguments)
  unless ← isTypeCorrect application do
    throwStratum .invalid "the operation template is outside its complete dependent declaration"
  return application

/-- One exact common route prefix. Sharing this template relates only the same
ordered structural action from the same rigid source, never coincident actual q's. -/
structure RouteTemplate where
  pathPrefix : Array EdgeRef
  action : Expr
  applications : Array Expr
  targetRealization : Option Expr

/-- All fields are functions of the same complete universal telescope. Besides
the whole maps, the schema retains each category, receiver, numeral and route
application needed to check the later selected instantiation argument by argument. -/
structure FamilyPlan where
  bundle : Expr
  receiver : Expr
  numerals : Array Expr
  left : Expr
  right : Expr
  leftApplications : Array Expr
  rightApplications : Array Expr

def routedTemplate (state : RegistryState) (entry : OperationEntry)
    (context : CategoryContext) (receiver : Expr) (route : Array EdgeRef)
    (numerals : Array Expr) (cache : IO.Ref (Array RouteTemplate)) :
    TermElabM (Expr × Array Expr) := do
  let some owner := state.categories.find? (·.id == entry.category)
    | throwStratum .invalid "an operation family has no registered owner"
  let some steps := state.toSemanticState.routeEdges? context.expression owner.expression route
    | throwStratum .invalid "an operation family has an invalid structural route"
  unless state.toSemanticState.isFirstOperationBindingRoute entry.name
      { source := context.expression, target := owner.expression, steps } do
    throwStratum .invalid "an operation family crosses an earlier explicit binding"
  let mut pathPrefix := #[]
  let mut composite : Option Expr := none
  let mut applications := #[]
  let mut previousTarget : Option Expr := none
  for edge in route do
    pathPrefix := pathPrefix.push edge
    if let some retained := (← cache.get).find? (·.pathPrefix == pathPrefix) then
      composite := some retained.action
      applications := retained.applications
      previousTarget := retained.targetRealization
      continue
    let application ← Semantic.edgeFunctor state edge
    let endpoints ← Semantic.edgeEndpoints? state edge application
    if let some previous := previousTarget then
      if let some (source, _) := endpoints then Semantic.alignCategoryParameters previous source
    let action ← Semantic.asFunctor application
    let next ← match composite with
      | none => pure action
      | some previous => mkFunctorComp previous action
    let (source, _) ← functorCategoryBundles next
    unless ← withTransparency .all <| isDefEq source context.bundle do
      throwStratum .invalid "a route template changed the complete rigid source category"
    applications := applications.push application
    previousTarget := endpoints.map (·.2)
    cache.modify (·.push {
      pathPrefix, action := next, applications, targetRealization := previousTarget })
    composite := some next
  let image ← match composite with
    | none => pure receiver
    | some action => Semantic.objOf action receiver
  return (← applicationTemplate entry image numerals, applications)

/-- Build both universal maps before any selected value is available. Source p
is rigid first. Every remaining route/declaration q, the source object and all
numerals are then abstracted together, preserving dependencies and common exact
route prefixes. Independent slots from unrelated declarations stay independent. -/
def universalPlan (state : RegistryState) (expression : CategoryExpr)
    (left right : OperationEntry) (leftRoute rightRoute : Array EdgeRef) :
    TermElabM FamilyPlan := do
  unless left.name == right.name && left.arity == right.arity &&
      left.numerals == right.numerals && left.result == right.result do
    throwStratum .invalid "the inherited operation families have different complete signatures"
  withSourceTemplate state expression fun parameters context => do
    let receiver ← mkFreshExprMVar (some (← CategoryContext.carrier context))
      (userName := `selected)
    let numerals ← (List.range left.numerals).toArray.mapM fun index =>
      mkFreshExprMVar (some (mkConst ``Nat)) (userName := Name.mkSimple s!"numeral{index}")
    let cache ← IO.mkRef (#[] : Array RouteTemplate)
    let (leftApplication, leftApplications) ←
      routedTemplate state left context receiver leftRoute numerals cache
    let (rightApplication, rightApplications) ←
      routedTemplate state right context receiver rightRoute numerals cache
    unless (← instantiateMVars receiver).isMVar &&
        (← numerals.allM fun numeral => return (← instantiateMVars numeral).isMVar) do
      throwStratum .invalid "an operation signature specialized a universal source or numeral"
    -- Visit route and declaration parameters before their dependent source object.
    -- Every whole application is included even if its returned map ignores q.
    let leftPrefix := leftApplication.getAppArgs.extract 0
      (leftApplication.getAppArgs.size - 1 - left.numerals)
    let rightPrefix := rightApplication.getAppArgs.extract 0
      (rightApplication.getAppArgs.size - 1 - right.numerals)
    let ordered := leftApplications ++ rightApplications ++ leftPrefix ++ rightPrefix
    let payload := #[context.bundle, receiver] ++ numerals ++
      #[leftApplication, rightApplication] ++ leftApplications ++ rightApplications
    let all ← abstractTemplates (ordered ++ payload)
    let all ← all.mapM fun term => do instantiateMVars (← mkLambdaFVars parameters term)
    -- Universe parameters are also rigid in the checked theorem. Their actual
    -- levels are retained as explicit Sort terms in its selected instantiation.
    let all ← abstractTemplates all true
    unless all.all closed do
      throwStratum .invalid "the operation comparison omitted part of its universal context"
    let fields := all.extract ordered.size all.size
    let some bundle := fields[0]? | unreachable!
    let some receiver := fields[1]? | unreachable!
    let numerals := fields.extract 2 (2 + numerals.size)
    let some left := fields[2 + numerals.size]? | unreachable!
    let some right := fields[3 + numerals.size]? | unreachable!
    let routeStart := 4 + numerals.size
    return {
      bundle, receiver, numerals, left, right
      leftApplications := fields.extract routeStart (routeStart + leftApplications.size)
      rightApplications := fields.extract (routeStart + leftApplications.size) fields.size }

def universalFamilies (state : RegistryState) (expression : CategoryExpr)
    (left right : OperationEntry) (leftRoute rightRoute : Array EdgeRef) :
    TermElabM (Expr × Expr) := do
  let plan ← universalPlan state expression left right leftRoute rightRoute
  return (plan.left, plan.right)

/-- Synchronous kernel checking for the entire universally quantified family,
including any independent universe parameters of its declared context. -/
def kernelAcceptsFamily (equality identity : Expr) : MetaM Bool := do
  let levels := (collectLevelParams (collectLevelParams {} equality) identity).params.toList
  if levels.isEmpty then return ← Decide.kernelAccepts equality identity
  let declaration := Declaration.thmDecl {
    name := `CasCatalogue.OperationAgreement.checkedFamily
    levelParams := levels, type := equality, value := identity }
  return match (← getEnv).addDeclCore (USize.ofNat (Decide.decideBudget * 1000))
      (USize.ofNat maxRecDepth.defValue) declaration none with
    | .ok _ => true
    | .error _ => false

/-- Complete source records use the same typed term quotient and field traversal
for their ordering keys and final snapshots. Route/cell identities are never erased. -/
def encodeSource (encode : Expr → TermElabM Nat) (source : OperationSource) :
    TermElabM Json := do
  let comparisons := source.comparisons.map fun comparison => Json.arr #[
    toJson comparison.cell.raw, toJson (comparison.constructors.map (·.raw)),
    toJson (comparison.before.map reprStr), toJson (comparison.after.map reprStr)]
  return Json.arr #[
    Json.arr #[toJson (reprStr source.context.expression), toJson (← encode source.context.bundle)],
    toJson (← encode source.receiver), toJson (source.route.map reprStr),
    toJson (← source.applications.mapM encode), Json.arr comparisons,
    toJson (← source.comparisonWitnesses.mapM encode)]

def encodeCandidate (encode : Expr → TermElabM Nat) (candidate : OperationCandidate) :
    TermElabM Json := do
  return Json.arr #[toJson candidate.operation.raw, toJson (← encode candidate.application),
    toJson (← encode candidate.result), Json.arr (← candidate.sources.mapM (encodeSource encode))]

/-- These finished complete-record keys order retained evidence only. They never
decide applicability, mathematical agreement, or computational availability. -/
def sourceKey (source : OperationSource) : TermElabM String := do
  let table ← Realize.TermTable.new
  table.finish (← encodeSource table.encode source)

def candidateKey (candidate : OperationCandidate) : TermElabM String := do
  let table ← Realize.TermTable.new
  table.finish (← encodeCandidate table.encode candidate)

def orderSources (sources : Array OperationSource) : TermElabM (Array OperationSource) := do
  let keyed ← sources.mapM fun source => return (← sourceKey source, source)
  return (keyed.qsort fun left right => left.1 < right.1).map (·.2)

def orderCandidates (candidates : Array OperationCandidate) :
    TermElabM (Array OperationCandidate) := do
  let keyed ← candidates.mapM fun candidate => return (← candidateKey candidate, candidate)
  return (keyed.qsort fun left right => left.1 < right.1).map (·.2)

/-- Duplicate provenance is shared only under the existing typed alpha/proof-
proposition quotient. All complete dictionaries, routes, applications and witness
propositions still participate; changing proof implementation cannot alter multiplicity. -/
def sameSourceData (left right : OperationSource) : TermElabM Bool := do
  unless left.context.expression.syntacticEq right.context.expression &&
      left.route == right.route && left.comparisons == right.comparisons &&
      left.applications.size == right.applications.size &&
      left.comparisonWitnesses.size == right.comparisonWitnesses.size do return false
  for (a, b) in #[(left.context.bundle, right.context.bundle), (left.receiver, right.receiver)] ++
      left.applications.zip right.applications ++
      left.comparisonWitnesses.zip right.comparisonWitnesses do
    unless ← QuestionIdentity.equivalent a b do return false
  return true

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

/-- Resolve the exact accepted operation address at a complete application. A
declaration may have several accepted bindings; its first row is never an address.
The explicit consumer supplies the chosen ID. Generic callers must have a unique
binding with this complete owner, declaration and operand signature. -/
def selectedEntry (state : RegistryState) (declaration : Name) (application : Expr)
    (arity : Nat) (selected : Option OperationId := none) :
    TermElabM (Option OperationEntry) := do
  unless !application.hasMVar && !application.hasLevelMVar &&
      !application.hasLooseBVars && application.getAppFn.isConstOf declaration &&
      (← isTypeCorrect application) do
    throwStratum .invalid "an operation address requires its complete typed declaration"
  let rows := state.operations.filter fun row =>
    row.declaration == declaration && (selected.isNone || selected == some row.id)
  if selected.isSome && rows.size != 1 then
    throwStratum .invalid "the selected operation ID does not name this declaration"
  let mut applicable : Array OperationEntry := #[]
  for row in rows do
    let accepts ← withoutModifyingState do
      if row.arity != arity then return false
      let arguments := application.getAppArgs
      unless arguments.size > row.numerals do return false
      let some category := state.categories.find? (·.id == row.category)
        | throwStratum .invalid "the selected operation's owner category is absent"
      try
        discard <| numeralArguments row application
        discard <| CategoryContext.ofNamed category arguments[arguments.size - 1 - row.numerals]!
        return true
      catch error =>
        if Exception.interpretationKind error == .invalid then pure false else throw error
    if accepts then applicable := applicable.push row
  match applicable with
  | #[row] => return some row
  | #[] =>
      if selected.isSome then
        throwStratum .invalid "the selected operation has a different complete owner or operand signature"
      return none
  | _ => throwSemanticAmbiguity "several accepted operation IDs share this complete declaration; select the binding"

/-- Match actual parameters of an already proved family before conversion could
erase them. Constructor/declaration heads are matched recursively, and unresolved
variables are filled only by the corresponding complete actual typed argument. -/
partial def bindTemplate (expected actual : Expr) : TermElabM Unit := do
  let expected ← instantiateMVars expected
  let actual ← instantiateMVars actual
  unless closed actual && (← isTypeCorrect actual) do
    throwStratum .invalid "a universal instantiation contains an incomplete actual argument"
  if expected.isMVar then
    unless ← withTransparency .all <|
        isDefEq (← inferType expected) (← inferType actual) <&&> isDefEq expected actual do
      throwStratum .invalid "a selected argument is outside its rigid universal parameter type"
    return
  if expected == actual then return
  if expected.getAppFn.constName?.isSome &&
      expected.getAppFn.constName? == actual.getAppFn.constName? &&
      expected.getAppArgs.size == actual.getAppArgs.size then
    unless ← isDefEq expected.getAppFn actual.getAppFn do
      throwStratum .invalid "a selected declaration changed its universal signature"
    for (parameter, argument) in expected.getAppArgs.zip actual.getAppArgs do
      bindTemplate parameter argument
    return
  unless closed expected &&
      ((← QuestionIdentity.equivalent expected actual) || (← sameApplication expected actual)) do
    throwStratum .invalid "a selected argument changed a complete universal declaration parameter"

/-- The owner has already been fixed by the complete retained source and its
ordered route applications. Its full structure may have another transparent
presentation, such as a named ring and the forgetful image of that same named
commutative ring. Compare this one rigid owner as a whole; every independent
declaration parameter still uses the recursive argument-preserving check.
Neither an operation's returned map nor its operands can determine the owner. -/
def bindOperationTemplate (entry : OperationEntry) (expected actual : Expr) :
    TermElabM Unit := do
  let expected ← instantiateMVars expected
  let actual ← instantiateMVars actual
  unless expected.getAppFn.isConstOf entry.declaration &&
      actual.getAppFn.isConstOf entry.declaration &&
      expected.getAppNumArgs == actual.getAppNumArgs &&
      expected.getAppNumArgs > entry.numerals && closed actual &&
      (← isTypeCorrect actual) && (← isDefEq expected.getAppFn actual.getAppFn) do
    throwStratum .invalid "an operation instantiation changed its complete registered declaration"
  let parameters := expected.getAppArgs
  let arguments := actual.getAppArgs
  let ownerSlot := parameters.size - 1 - entry.numerals
  let owner ← instantiateMVars parameters[ownerSlot]!
  let supplied := arguments[ownerSlot]!
  unless closed owner && closed supplied &&
      (← withTransparency .all <|
        isDefEq (← inferType owner) (← inferType supplied) <&&> isDefEq owner supplied) do
    throwStratum .invalid "the operation changed its independently fixed complete owner"
  for index in [:parameters.size] do
    unless index == ownerSlot do bindTemplate parameters[index]! arguments[index]!

/-- Instantiate only an already checked closed plan. Every complete source,
ordered edge application, declaration argument and numeral is matched before
conversion. Shared template parameters must accept both actual presentations;
unrelated q slots remain separate entries in the recorded parameter vector. -/
def instantiatePlan (plan : FamilyPlan) (leftEntry rightEntry : OperationEntry)
    (leftSource rightSource : OperationSource) (leftApplication rightApplication : Expr) :
    TermElabM (Array Expr) := do
  let names := (collectLevelParams (collectLevelParams {} plan.left) plan.right).params
  let levels ← names.mapM fun _ => mkFreshLevelMVar
  let atLevels (term : Expr) := term.instantiateLevelParamsArray names levels
  let (parameters, _, _) ← lambdaMetaTelescope (atLevels plan.bundle)
  let instantiateField (term : Expr) := (mkAppN (atLevels term) parameters).headBeta
  for source in #[leftSource, rightSource] do
    bindTemplate (instantiateField plan.bundle) source.context.bundle
    bindTemplate (instantiateField plan.receiver) source.receiver
  let leftNumerals ← numeralArguments leftEntry leftApplication
  let rightNumerals ← numeralArguments rightEntry rightApplication
  unless plan.numerals.size == leftNumerals.size && plan.numerals.size == rightNumerals.size &&
      plan.leftApplications.size == leftSource.applications.size &&
      plan.rightApplications.size == rightSource.applications.size do
    throwStratum .invalid "a universal instantiation omitted an ordered route or numeral parameter"
  for ((parameter, left), right) in (plan.numerals.zip leftNumerals).zip rightNumerals do
    bindTemplate (instantiateField parameter) left
    bindTemplate (instantiateField parameter) right
  for (expected, actual) in plan.leftApplications.zip leftSource.applications do
    bindTemplate (instantiateField expected) actual
  for (expected, actual) in plan.rightApplications.zip rightSource.applications do
    bindTemplate (instantiateField expected) actual
  bindOperationTemplate leftEntry (instantiateField plan.left) leftApplication
  bindOperationTemplate rightEntry (instantiateField plan.right) rightApplication
  let parameters ← parameters.mapM instantiateMVars
  let levels ← levels.mapM instantiateLevelMVars
  unless parameters.all closed && levels.all (fun level => !level.hasMVar) do
    throwStratum .invalid "the operation comparison omitted a complete selected universal parameter"
  let left ← instantiateMVars (instantiateField plan.left)
  let right ← instantiateMVars (instantiateField plan.right)
  unless (← sameApplication left leftApplication) && (← sameApplication right rightApplication) do
    throwStratum .invalid "the universal instantiation changed a complete selected operation"
  return levels.map Lean.mkSort ++ parameters

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
  bindTemplate expected actual
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
  let actual ← applicationTemplate entry owner (← numeralArguments entry application)
  bindOperationTemplate entry actual application
  let actual ← instantiateMVars actual
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
  let plan ← try
      some <$> universalPlan state leftSource.context.expression leftEntry rightEntry
        leftSource.route rightSource.route
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
  let some plan := plan | return none
  let leftFamily := plan.left
  let rightFamily := plan.right
  let leftType ← inferType leftFamily
  let rightType ← inferType rightFamily
  unless closed leftType && closed rightType &&
      (← withTransparency .all <| isDefEq leftType rightType <&&>
        isDefEq leftFamily rightFamily) do return none
  let equality ← mkEq leftFamily rightFamily
  let identity ← mkEqRefl leftFamily
  unless closed identity && (← kernelAcceptsFamily equality identity) do return none
  let parameters ← try
      some <$> instantiatePlan plan leftEntry rightEntry leftSource rightSource
        left.application right.application
    catch error =>
      if Exception.interpretationKind error == .invalid then pure none else throw error
  let some parameters := parameters | return none
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
      (← kernelAcceptsFamily equality comparison.identity) do
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
      if (← candidateKey candidate) < (← candidateKey previous) then
        throwStratum .invalid "the checked operation class is not canonically ordered"
    let some entry := state.operations.find? (·.id == candidate.operation)
      | throwStratum .invalid "the operation class contains an absent binding"
    unless closed candidate.application && closed candidate.result &&
        !candidate.sources.isEmpty && (← isTypeCorrect candidate.application) &&
        (← isTypeCorrect candidate.result) do
      throwStratum .invalid "the operation class contains an incomplete typed candidate"
    discard <| numeralArguments entry candidate.application
    let mut previousSource : Option String := none
    for source in candidate.sources do
      let key ← sourceKey source
      if let some previous := previousSource then
        if key < previous then
          throwStratum .invalid "the operation's complete sources are not canonically ordered"
      previousSource := some key
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
