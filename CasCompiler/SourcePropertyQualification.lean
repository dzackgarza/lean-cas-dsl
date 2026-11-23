module

public import CasCompiler.Surface
public import CasCompiler.FamilyConversion
public import LeanCategories.Catalogue.Holds
public import Lean.Meta.Reduce

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private def classifierAsValue (value : Expr) : MetaM Expr := do
  let type ← whnfR (← inferType value)
  if type.isAppOf ``LeanCategories.PropertyClassifier ||
      type.isAppOf ``LeanCategories.StructureClassifier then
    return ← mkProjection value `toClassifier
  unless type.isAppOf ``LeanCategories.Classifier do
    throwError "the explicit refinement requires its complete native classifier"
  return value

-- Validate the whole registered classifier, including its actual forgetful functor,
-- before specializing any category parameter. A full-subcategory carrier alone is
-- insufficient: a different functor from it is not the property inclusion.
private def propertyClassifierAt (entry : ClassifierEntry) (host : Expr) :
    MetaM (Expr × Expr) := do
  let info ← checkedDeclaration entry.declaration
  let universes ← info.levelParams.mapM fun _ => mkFreshUserName `propertyUniverse
  let family := Lean.mkConst entry.declaration (universes.map Level.param)
  let agreement ← forallTelescopeReducing (← inferType family) fun parameters _ => do
    let classifier ← classifierAsValue (mkAppN family parameters)
    let type ← whnfR (← inferType classifier)
    let completeHost := type.getAppArgs[0]!
    let total ← mkAppM ``LeanCategories.Classifier.total #[classifier]
    let objects ← withTransparency .all <| whnf (← mkAppM ``CategoryTheory.Bundled.α #[total])
    unless objects.isAppOfArity ``CategoryTheory.ObjectProperty.FullSubcategory 3 do
      throwUnsupportedSource
        "explicit refinement requires a proof-only property classifier; chosen data are required"
    let property := objects.getAppArgs[2]!
    let inclusion ← mkAppOptM ``LeanCategories.Classifier.ofProperty
      #[some completeHost, some property]
    let inclusion ← instantiateMVars inclusion
    let some proof ← withTransparency .all <| sourceFamilyConversion classifier inclusion #[]
      | throwUnsupportedSource
          "the explicit classifier is not the complete native property inclusion"
    mkLambdaFVars parameters proof (usedOnly := false) (usedLetOnly := false)
  let levels ← universes.mapM fun _ => mkFreshLevelMVar
  let family := family.instantiateLevelParams universes levels
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  unless ← expandSourceStructures parameters do
    throwError "the explicit classifier has inconsistent complete parameters"
  let classifier ← classifierAsValue (mkAppN family parameters)
  let type ← whnfR (← inferType classifier)
  unless ← isDefEq type.getAppArgs[0]! host do
    throwError "the explicit classifier has a different complete selected host"
  let classifier ← instantiateMVars classifier
  let agreement ← instantiateMVars
    (mkAppN (agreement.instantiateLevelParams universes levels) parameters)
  if classifier.hasMVar || classifier.hasLevelMVar ||
      agreement.hasMVar || agreement.hasLevelMVar then
    throwError "the explicit classifier requires its complete source parameters"
  checkWithKernel agreement
  return (classifier, agreement)

/-- Refine the actual selected object through the explicitly named property classifier.
Reuse: Classifier.holds_ofProperty, the native FullSubcategory constructor, and checked native
family conversion. Only an existing proof-class instance is discharged; an inhabited fibre
never supplies a chosen structure. The original object and universal presentation survive. -/
def sourcePropertyQualification (source : NativeSourceJudgement)
    (required : NamedCategoryEntry) : TermElabM NativeSourceJudgement := do
  let some selected := source.category
    | throwError "the retained source value has no selected category"
  if selected.expression.syntacticEq required.expression then return source
  let .classifierTotal id := required.expression
    | throwError "the retained source value has a different selected category"
  let state ← semanticState
  let some entry := state.classifier? id
    | throwError "the explicitly selected classifier is absent"
  unless selected.role == .object && selected.expression.syntacticEq entry.host do
    throwError "the explicit refinement has a different selected base category"
  let (classifier, agreement) ← propertyClassifierAt entry selected.bundle
  let total ← instantiateMVars (← mkAppM ``LeanCategories.Classifier.total #[classifier])
  discard <| checkedDeclaration required.declaration
  let family ← mkConstWithFreshMVarLevels required.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let bundle := mkAppN family parameters
  unless ← isDefEq bundle total do
    throwError "the requested category is not the complete selected classifier total"
  let bundle ← instantiateMVars bundle
  if bundle.hasMVar || bundle.hasLevelMVar then
    throwError "the requested property category has undetermined source parameters"
  let objects ← withTransparency .all <| whnf (← mkAppM ``CategoryTheory.Bundled.α #[total])
  unless objects.isAppOfArity ``CategoryTheory.ObjectProperty.FullSubcategory 3 do
    throwError "the checked property classifier changed its native constructor"
  let property := objects.getAppArgs[2]!
  let obligation ← instantiateMVars (mkApp property source.value)
  unless (← isProp obligation) && (← isClass? obligation).isSome do
    throwUnsupportedSource "the explicit property requires its independently supplied proof"
  -- Instance search uses instance transparency. Native definitional normalization
  -- here affects only this proof obligation; the constructor below keeps source.value.
  -- The resulting existing class proof is checked against the original obligation.
  let normalized ← withTransparency .all <|
    reduce obligation (explicitOnly := false) (skipTypes := false) (skipProofs := true)
  let some evidence ← synthInstance? normalized
    | throwStratum .invalid m!"the explicit property is not established for the original object"
  let evidence ← instantiateMVars evidence
  if evidence.hasMVar || evidence.hasLevelMVar || evidence.hasSorry then
    throwError "the explicit property has no complete checked proof"
  checkWithKernel (← mkExpectedTypeHint evidence obligation)
  let value ← mkAppOptM ``CategoryTheory.ObjectProperty.FullSubcategory.mk
    ((objects.getAppArgs.map some) ++ #[some source.value, some evidence])
  unless ← isDefEq (← inferType value) (← mkAppM ``CategoryTheory.Bundled.α #[bundle]) do
    throwError "the property constructor has a different complete selected target"
  let forget ← mkAppM ``CategoryTheory.Cat.Hom.toFunctor
    #[← mkAppM ``LeanCategories.Classifier.forget #[classifier]]
  let original ← functorObject forget value selected.bundle
  unless ← isDefEq original source.value do
    throwError "the property inclusion changed the original source object"
  -- The retained cone belongs to the old category even after its apex is refined.
  -- This checks the supplied relation; it never recovers a selection from an apex.
  if let some limit := selected.limit then
    unless limit.category.syntacticEq selected.expression &&
        (← isDefEq limit.bundle selected.bundle) do
      throwError "the retained universal presentation has a different selected category"
    let apex ← mkAppM (if limit.colimit then ``CategoryTheory.Limits.Cocone.pt
      else ``CategoryTheory.Limits.Cone.pt) #[limit.cone]
    unless ← isDefEq apex source.value do
      throwError "the retained universal presentation has a different original apex"
  let equivalence ← mkAppOptM ``CasCatalogue.Classifier.holds_ofProperty
    #[some selected.bundle, some property, some source.value]
  let holds ← mkAppM ``Iff.mpr #[equivalence, evidence]
  let proposition ← mkAppM ``CasCatalogue.Classifier.Holds #[classifier, source.value]
  let holds ← mkExpectedTypeHint holds proposition
  checkWithKernel holds
  let mut value := value
  for proof in #[agreement, holds] do
    value ← withLetDecl (← mkFreshUserName `propertyEvidence) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] value
        (usedLetOnly := false) (generalizeNondepLet := false)
  let carrier : NativeSourceCarrierSelection := match selected.carrier with
    | none => ⟨#[.classifierForget id], selected.expression, #[], #[forget], #[]⟩
    | some original =>
      ⟨#[.classifierForget id] ++ original.refs, original.target, original.identifications,
        #[forget] ++ original.actions, original.comparisons⟩
  return ⟨value, some ⟨.object, required.expression, bundle, some carrier, selected.limit⟩⟩

end CasCompiler
