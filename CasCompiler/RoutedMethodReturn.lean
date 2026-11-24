module

public import CasCompiler.SourceCarrier
public import CasCompiler.FamilyConversion
public import CasCompiler.LiftFamily
public import CasCompiler.SelectedField
public import LeanCategories.Catalogue.Constructors

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- Actual return data for a whole inherited method. The declarations and their
complete native applications are fixed before any receiver is supplied. -/
structure RoutedMethodReturn where
  route : Route
  rows : Array LiftEntry
  actions : Array Expr
  agreement : Option Expr
  evidences : Array Expr
  category : CategoryExpr
  categoryFamily : Expr
  resultFamily : Expr

/-- All independent lifts at the exact positions of the return route.
Missing rows have a distinct result from a malformed registered lift. -/
def methodReturnRows? (state : SemanticState) (route : Route) :
    Option (Array (Array LiftEntry)) := Id.run do
  let mut alternatives : Array (Array LiftEntry) := #[#[]]
  for edge in route.refs do
    let rows := state.lifts.filter (fun row => row.kind == .subobjects && row.edge == edge)
    if rows.isEmpty then return none
    alternatives := alternatives.flatMap fun chosen => rows.map chosen.push
  return some alternatives

def methodReturnRows (state : SemanticState) (route : Route) :
    MetaM (Array (Array LiftEntry)) := do
  let some rows := methodReturnRows? state route
    | throwUnsupportedSource "source method lifting requires its actual selected return data"
  return rows

/-- Compare complete rigid transport families, not their values at a receiver.
The comparison uses the existing whole-family equality judgment. In particular,
an isomorphism of functors by itself is not accepted as an equality. -/
def methodReturnRouteAgreement? (state : SemanticState) (forward returning : Route)
    (actual : Expr) : MetaM (Option Expr) := do
  unless forward.source.syntacticEq returning.source &&
      forward.target.syntacticEq returning.target do return none
  let family ← nativeCategoryFamily state forward.source fun _ => do
    return .param (← mkFreshUserName `methodReturnUniverse)
  let functions ← #[forward, returning].mapM fun route => do
    forallTelescopeReducing (← inferType family) fun parameters _ => do
      let selected ← nativeRouteFunctor state route (mkAppN family parameters)
      mkLambdaFVars parameters (← instantiateMVars selected.functor)
        (usedOnly := false) (usedLetOnly := false)
  let some proof ← sourceFamilyConversion functions[0]! functions[1]! #[]
    | return none
  -- Specialize an already checked equality, retaining all actual category
  -- parameters. No comparison of computed receiver images occurs here.
  let levels : CollectLevelParams.State := {}
  let universes := (levels.collect family).params.toList
  let fresh ← universes.mapM fun _ => mkFreshLevelMVar
  let native := family.instantiateLevelParams universes fresh
  let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType native)
  unless ← withoutModifyingState <| isDefEq (mkAppN native arguments) actual do
    unless ← expandSourceStructures arguments do
      throwError "the returning route has inconsistent complete source parameters"
  unless ← isDefEq (mkAppN native arguments) actual do
    throwError "the returning route changed its complete native category"
  let mut proof := proof.instantiateLevelParams universes (← fresh.mapM instantiateLevelMVars)
  for argument in arguments do
    proof ← mkAppM ``congrFun #[proof, ← instantiateMVars argument]
  return some (← instantiateMVars proof)

/-- Keep a comparison as inert checked native evidence in the returned source.
This does not replace the independently selected forward or return actions. -/
def retainMethodReturnAgreement (agreement : Option Expr) (result : Expr) : MetaM Expr := do
  let some proof := agreement | return result
  check proof
  withLetDecl (← mkFreshUserName `methodReturnAgreement) (← inferType proof) proof
    fun binding => mkLetFVars #[binding] result
      (usedLetOnly := false) (generalizeNondepLet := false)

/-- Read the actual selected MonoLift at the whole native mapArrow action.
The complete source and target dictionaries participate in this check. -/
def methodReturnEvidence (state : SemanticState) (row : LiftEntry)
    (edge : EdgeRef) (action : Expr) : MetaM Expr := do
  let #[registered] := state.lifts.filter (·.id == row.id)
    | throwSemanticAmbiguity "the selected return lift has no unique registered identity"
  unless registered.edge == edge && row.edge == edge &&
      registered.kind == .subobjects && row.kind == .subobjects &&
      registered.evidence == row.evidence && registered.computation == row.computation do
    throwError "the method return changed its actual selected lift declaration"
  discard <| checkedDeclaration row.evidence
  let head ← mkConstWithFreshMVarLevels row.evidence
  let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType head)
  let type ← whnfR type
  unless type.isAppOfArity ``MonoLift 5 do
    throwError "the selected method return has no complete native MonoLift interface"
  let selected := mkAppN head parameters
  let actionOf := do
    let type ← whnfR (← inferType selected)
    mkAppM ``CategoryTheory.Functor.mapArrow #[type.getAppArgs[4]!]
  let expected ← actionOf
  unless ← withoutModifyingState <| isDefEq expected action do
    unless ← expandSourceStructures parameters do
      throwError "the selected method return has inconsistent native category parameters"
  unless ← isDefEq (← actionOf) action do
    throwError "the selected method return belongs to a different complete route action"
  let evidence ← instantiateMVars selected
  if evidence.hasMVar then
    throwUnsupportedSource "the selected method return requires its complete declaration parameters"
  discard <| LiftFamily.atEvidence row .computation evidence
  return evidence

/-- Recover the complete selected base of the original arrow category; the
returned category is the registered subobjects constructor at that same base. -/
def methodReturnCategory (state : SemanticState) (source : CategoryExpr)
    (selected : Expr) : MetaM (CategoryExpr × Expr) := do
  let .construct id #[.category base] := source
    | throwError "the selected returning method has no original arrow category"
  let some arrow := state.constructor? id
    | throwError "the selected returning method lost its arrow constructor"
  unless arrow.semantics == ``Constructors.arrow do
    throwError "the selected returning method has a different original constructor"
  let #[subobjects] := state.constructors.filter
      (·.semantics == ``Constructors.subobjects)
    | throwSemanticAmbiguity "the returning method requires its unique subobject constructor"
  discard <| checkedDeclaration arrow.semantics
  discard <| checkedDeclaration subobjects.semantics
  let family ← nativeCategoryFamily state base (fun _ => mkFreshLevelMVar)
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let bundle := mkAppN family parameters
  let expected ← applyConstructorInterface arrow.semantics #[bundle] #[bundle]
  unless ← isDefEq expected selected do
    throwError "the returning method changed its complete original source category"
  let bundle ← instantiateMVars bundle
  if bundle.hasMVar then
    throwUnsupportedSource "the returning method requires its complete source category parameters"
  return (.construct subobjects.id #[.category base],
    ← applyConstructorInterface subobjects.semantics #[bundle] #[bundle])

/-- Use the published callable fields and the upstream monicity law. This
forms a native subobject record; it neither computes nor decodes a lift. -/
private def methodReturnSubobject (row : LiftEntry) (evidence receiver value : Expr) :
    MetaM Expr := do
  let object ← mkProjection receiver `left
  let arrow ← mkProjection value `obj
  let domain ← mkProjection arrow `left
  let inclusion ← mkProjection arrow `hom
  let monicity ← mkProjection value `property
  let evidenceType ← whnfR (← inferType evidence)
  unless evidenceType.isAppOfArity ``MonoLift 5 do
    throwError "the method return lost its actual selected MonoLift"
  let computation ← LiftFamily.atEvidence row .computation evidence
  -- Each actual source application owns a fresh field-selection identity.
  let selection ← mkFreshUserName `methodReturn
  let computation ← selectRecordActions selection computation
  let function ← mkAppM ``MonoLiftComputation.hom #[computation]
  let hom := selectedField selection ``MonoLiftComputation.hom
    (mkAppN function #[object, domain, inclusion, monicity])
  check hom
  let arguments := evidenceType.getAppArgs.map some ++
    #[some evidence, some object, some domain, some inclusion, some monicity]
  let mono ← mkAppOptM ``MonoLift.computation_hom_mono arguments
  let mono ← mkExpectedTypeHint mono (← mkAppM ``CategoryTheory.Mono #[hom])
  check mono
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[hom]
  let (source, _) ← functorCategoryBundles evidenceType.getAppArgs[4]!
  let bundle ← applyConstructorInterface ``Constructors.subobjects #[source] #[source]
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let constructor ← mkConstWithFreshMVarLevels
    ``CategoryTheory.ObjectProperty.FullSubcategory.mk
  let (fields, _, resultType) ← forallMetaTelescopeReducing (← inferType constructor)
  unless fields.size >= 2 && (← isDefEq resultType expected) do
    throwError "the returning subobject changed its complete native constructor"
  unless ← isDefEq fields[fields.size - 2]! arrow do
    throwError "the returning subobject changed its actual defining arrow"
  unless ← isDefEq fields.back! mono do
    throwError "the returning subobject changed its actual defining-map monicity"
  let result ← instantiateMVars (mkAppN constructor fields)
  if result.hasMVar then
    throwError "the returning subobject has undetermined selected data"
  check result
  return result

/-- Return in reverse route order using the original receiver at each position.
The forward native actions, lift evidence and base subobject remain unchanged. -/
def applyMethodReturns (rows : Array LiftEntry) (evidences actions : Array Expr)
    (receiver value : Expr) : MetaM Expr := do
  unless rows.size == evidences.size && rows.size == actions.size do
    throwError "the method return lost an original route position"
  let mut receivers := #[]
  let mut current := receiver
  for action in actions do
    receivers := receivers.push current
    let (_, target) ← functorCategoryBundles action
    current ← functorObject action current target
  let mut result := value
  for (row, evidence, original) in (rows.zip (evidences.zip receivers)).reverse do
    result ← methodReturnSubobject row evidence original result
  return result

end CasCompiler
