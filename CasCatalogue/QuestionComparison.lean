/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Realize
public import CasCatalogue.QuestionIdentity

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.QuestionIdentity

/-- Infer a question's types independently of any serialized identity or cached
type list. A supplied list is checked against those actual types; it cannot change
the meaning of the retained operands. An empty list is the reader's unprepared form. -/
def questionTypes (terms recorded : Array Expr) : TermElabM (Array Expr) := do
  let terms ← terms.mapM instantiateMVars
  let types ← terms.mapM fun term => do
    if term.hasMVar || term.hasLevelMVar || term.hasFVar || term.hasLooseBVars then
      throwError "question comparison requires complete closed operands"
    unless ← isTypeCorrect term do
      throwError "question comparison received an ill-typed operand"
    instantiateMVars (← inferType term)
  unless recorded.isEmpty do
    unless recorded.size == types.size do
      throwError "the question's recorded type list has the wrong length"
    for (recordedType, actualType) in recorded.zip types do
      unless ← equivalent recordedType actualType do
        throwError "the question's recorded type differs from its actual operand type"
  return types

/-- Compare complete ordered typed operands without serializing them. -/
def equivalentOperands (left right leftTypes rightTypes : Array Expr) : TermElabM Bool := do
  let actualLeftTypes ← questionTypes left leftTypes
  let actualRightTypes ← questionTypes right rightTypes
  unless left.size == right.size do return false
  for (first, second) in actualLeftTypes.zip actualRightTypes do
    unless ← equivalent first second do return false
  for (first, second) in left.zip right do
    unless ← equivalent first second do return false
  return true

/-- Direct independent comparison of the mathematical question tree. Relation
names, ordered structural routes, selected declaration identities and logical
constructors remain significant. Only the explicitly stated typed-term identity
quotient applies to operands and their actual types. No outcome, backend, revision
label, serialized DAG, or regenerated candidate identity participates. -/
partial def equivalentQuestion (left right : Language.Question) : TermElabM Bool := do
  match left, right with
  | .proposition first, .proposition second =>
      equivalentOperands #[first] #[second] #[] #[]
  | .judgement relation terms route declarations types,
      .judgement other otherTerms otherRoute otherDeclarations otherTypes =>
      unless relation == other && route == otherRoute && declarations == otherDeclarations do
        return false
      equivalentOperands terms otherTerms types otherTypes
  | .conjunction first second, .conjunction otherFirst otherSecond =>
      equivalentQuestion first otherFirst <&&> equivalentQuestion second otherSecond
  | .negation question, .negation other => equivalentQuestion question other
  | _, _ => return false

/-- Ordered complete typed data, with no supplied type list or serialization. -/
def equivalentTerms (left right : Array Expr) : TermElabM Bool :=
  equivalentOperands left right #[] #[]

/-- A derived category retains its exact symbolic expression and selected typed bundle;
an unnamed context cannot be identified merely by its endpoints or printed name. -/
def equivalentCategoryContext (left right : CategoryContext) : TermElabM Bool := do
  unless left.expression.syntacticEq right.expression do return false
  equivalentTerms #[left.bundle] #[right.bundle]

/-- Compare finite unordered records by an equivalence comparison, retaining multiplicities.
Hash-map iteration order and the order of alternative parameter presentations have no meaning;
the routes, arguments and fields inside each record still have their declared order. -/
def equivalentUnordered {α : Type} (same : α → α → TermElabM Bool)
    (left right : Array α) : TermElabM Bool := do
  unless left.size == right.size do return false
  let mut remaining := right
  for first in left do
    let mut found := false
    let mut rest : Array α := #[]
    for second in remaining do
      if found then rest := rest.push second
      else if ← same first second then found := true
      else rest := rest.push second
    unless found do return false
    remaining := rest
  return true

/-- A selected parameter retains every complete source presentation, including its
full structural applications, carrier route and proposition of identification. -/
def equivalentParameterPresentation (left right : ParameterPresentation) : TermElabM Bool := do
  unless left.source == right.source && left.sourceCategory == right.sourceCategory &&
      left.targetCategory == right.targetCategory && left.route == right.route &&
      left.carrierRoute == right.carrierRoute && left.identifications == right.identifications do
    return false
  equivalentTerms left.params right.params <&&>
    equivalentTerms left.applications right.applications <&&>
    equivalentTerms #[left.object, left.image, left.identity]
      #[right.object, right.image, right.identity]

/-- An operation's selected source retains its whole dictionary, ordered actions,
and every accepted comparison with its exact constructor and whiskering context. -/
def equivalentOperationSource (left right : OperationSource) : TermElabM Bool := do
  unless left.route == right.route && left.comparisons == right.comparisons do return false
  equivalentCategoryContext left.context right.context <&&>
    equivalentTerms #[left.receiver] #[right.receiver] <&&>
    equivalentTerms left.applications right.applications <&&>
    equivalentTerms left.comparisonWitnesses right.comparisonWitnesses

/-- Compare the retained exact cell applications and their independently typed values. -/
def equivalentRouteComparisons (left right : Array (RouteComparison × Expr)) :
    TermElabM Bool := do
  unless left.size == right.size do return false
  for ((firstContext, first), (secondContext, second)) in left.zip right do
    unless firstContext == secondContext do return false
    unless ← equivalentTerms #[first] #[second] do return false
  return true

/-- Source order is part of a checked class's canonical indexing, not a lookup
priority. Keeping that order preserves the universal comparison's source indices. -/
def equivalentOperationCandidate (left right : OperationCandidate) : TermElabM Bool := do
  unless left.operation == right.operation && left.sources.size == right.sources.size do
    return false
  unless ← equivalentTerms #[left.application, left.result] #[right.application, right.result] do
    return false
  for (first, second) in left.sources.zip right.sources do
    unless ← equivalentOperationSource first second do return false
  return true

/-- The complete universal families, their full dependent types and checked proof
remain visible alongside the exact ordered post-proof instantiation parameters. -/
def equivalentOperationFamilyComparison (left right : OperationFamilyComparison) :
    TermElabM Bool := do
  unless left.left == right.left && left.right == right.right &&
      left.leftSource == right.leftSource && left.rightSource == right.rightSource do
    return false
  equivalentTerms left.parameters right.parameters <&&>
    equivalentTerms #[left.leftFamily, left.rightFamily, left.leftType, left.rightType, left.identity]
      #[right.leftFamily, right.rightFamily, right.leftType, right.rightType, right.identity]

/-- Compare the retained operation itself, independently of its encoded snapshot.
The outer match is exhaustive: a new trace constructor needs an explicit comparison.
No argument is erased on the basis of a field name such as `identity` or `admitted`. -/
def equivalentNode (left right : Node) : TermElabM Bool := do
  match left with
  | .object id params =>
      let .object other otherParams := right | return false
      unless id == other do return false
      equivalentTerms params otherParams
  | .parameterTransport source sourceCategory targetCategory route receiver =>
      let .parameterTransport other otherSource otherTarget otherRoute otherReceiver := right
        | return false
      unless source == other && sourceCategory == otherSource &&
          targetCategory == otherTarget && route == otherRoute do return false
      equivalentTerms #[receiver] #[otherReceiver]
  | .structureTransport source target route receiver =>
      let .structureTransport otherSource otherTarget otherRoute otherReceiver := right
        | return false
      unless source == otherSource && target == otherTarget && route == otherRoute do return false
      equivalentTerms #[receiver] #[otherReceiver]
  | .retainedRoute source target route applications receiver =>
      let .retainedRoute otherSource otherTarget otherRoute otherApplications otherReceiver := right
        | return false
      unless source == otherSource && target == otherTarget && route == otherRoute do return false
      equivalentTerms applications otherApplications <&&>
        equivalentTerms #[receiver] #[otherReceiver]
  | .proofRefinement classifier sourceCategory targetCategory source action identity =>
      let .proofRefinement other otherSource otherTarget
          otherObject otherAction otherIdentity := right
        | return false
      unless classifier == other && sourceCategory == otherSource &&
          targetCategory == otherTarget do return false
      equivalentTerms #[source, action, identity] #[otherObject, otherAction, otherIdentity]
  | .parameterEquivalence expected representative sources =>
      let .parameterEquivalence otherExpected otherRepresentative otherSources := right
        | return false
      equivalentTerms #[expected, representative] #[otherExpected, otherRepresentative] <&&>
        equivalentUnordered equivalentParameterPresentation sources otherSources
  | .namedMorphism id params =>
      let .namedMorphism other otherParams := right | return false
      unless id == other do return false
      equivalentTerms params otherParams
  | .namedInclusion id category params source target =>
      let .namedInclusion other otherCategory otherParams otherSource otherTarget := right
        | return false
      unless id == other && category == otherCategory do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[source, target] #[otherSource, otherTarget]
  | .objectField object field category params =>
      let .objectField other otherField otherCategory otherParams := right | return false
      unless object == other && field == otherField && category == otherCategory do return false
      equivalentTerms params otherParams
  | .powerObjectMap object field params =>
      let .powerObjectMap other otherField otherParams := right | return false
      unless object == other && field == otherField do return false
      equivalentTerms params otherParams
  | .namedCallable address category params =>
      let .namedCallable other otherCategory otherParams := right | return false
      unless address == other && category == otherCategory do return false
      equivalentTerms params otherParams
  | .callableRecipe category domain target body =>
      let .callableRecipe other otherDomain otherTarget otherBody := right | return false
      unless category == other do return false
      equivalentTerms #[domain, target, body] #[otherDomain, otherTarget, otherBody]
  | .admittedPoint object category params original originalCategory source target =>
      let .admittedPoint other otherCategory otherParams otherOriginal otherOriginalCategory
          otherSource otherTarget := right | return false
      unless object == other && category == otherCategory &&
          originalCategory == otherOriginalCategory do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[original, source, target] #[otherOriginal, otherSource, otherTarget]
  | .constrainedPoint constructor category domain source target original =>
      let .constrainedPoint other otherCategory
          otherDomain otherSource otherTarget otherOriginal := right
        | return false
      unless constructor == other && category == otherCategory do return false
      equivalentTerms #[domain, source, target, original]
        #[otherDomain, otherSource, otherTarget, otherOriginal]
  | .presentation id params inverse =>
      let .presentation other otherParams otherInverse := right | return false
      unless id == other && inverse == otherInverse do return false
      equivalentTerms params otherParams
  | .generator id params =>
      let .generator other otherParams := right | return false
      unless id == other do return false
      equivalentTerms params otherParams
  | .presentationApply id params inverse source target argument =>
      let .presentationApply other otherParams otherInverse
          otherSource otherTarget otherArgument := right
        | return false
      unless id == other && inverse == otherInverse do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[source, target, argument] #[otherSource, otherTarget, otherArgument]
  | .operationApply id params operands target selected =>
      let .operationApply other otherParams otherOperands otherTarget otherSelected := right
        | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&> equivalentTerms operands otherOperands <&&>
        equivalentTerms #[target, selected] #[otherTarget, otherSelected]
  | .operationPoint id params comparison operation target selected =>
      let .operationPoint other otherParams
          otherComparison otherOperation otherTarget otherSelected := right
        | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[comparison, operation, target, selected]
          #[otherComparison, otherOperation, otherTarget, otherSelected]
  | .operationEquivalence representative chosen candidates comparisons =>
      let .operationEquivalence otherRepresentative otherChosen otherCandidates otherComparisons := right
        | return false
      OperationAgreement.validate representative chosen candidates comparisons
      OperationAgreement.validate otherRepresentative otherChosen otherCandidates otherComparisons
      unless chosen == otherChosen && candidates.size == otherCandidates.size &&
          comparisons.size == otherComparisons.size do return false
      unless ← equivalentTerms #[representative] #[otherRepresentative] do return false
      for (candidate, other) in candidates.zip otherCandidates do
        unless ← equivalentOperationCandidate candidate other do return false
      for (comparison, other) in comparisons.zip otherComparisons do
        unless ← equivalentOperationFamilyComparison comparison other do return false
      return true
  | .elementNumeral value target selected =>
      let .elementNumeral other otherTarget otherSelected := right | return false
      unless value == other do return false
      equivalentTerms #[target, selected] #[otherTarget, otherSelected]
  | .elementValue point target selected =>
      let .elementValue other otherTarget otherSelected := right | return false
      equivalentTerms #[point, target, selected] #[other, otherTarget, otherSelected]
  | .productMediator category presentation domain first second =>
      let .productMediator other otherPresentation otherDomain otherLeft otherRight := right
        | return false
      unless category == other do return false
      equivalentTerms #[presentation, domain, first, second]
        #[otherPresentation, otherDomain, otherLeft, otherRight]
  | .morphismComposition category first second source middle target =>
      let .morphismComposition other otherFirst otherSecond
          otherSource otherMiddle otherTarget := right
        | return false
      unless category == other do return false
      equivalentTerms #[first, second, source, middle, target]
        #[otherFirst, otherSecond, otherSource, otherMiddle, otherTarget]
  | .morphismIdentity category object =>
      let .morphismIdentity other otherObject := right | return false
      unless category == other do return false
      equivalentTerms #[object] #[otherObject]
  | .contextualRoute source target route applications receiver morphism =>
      let .contextualRoute otherSource otherTarget otherRoute
          otherApplications otherReceiver otherMorphism := right | return false
      unless route == otherRoute && morphism == otherMorphism do return false
      equivalentCategoryContext source otherSource <&&>
        equivalentCategoryContext target otherTarget <&&>
        equivalentTerms applications otherApplications <&&>
        equivalentTerms #[receiver] #[otherReceiver]
  | .contextualComposition context first second source middle target =>
      let .contextualComposition otherContext otherFirst otherSecond
          otherSource otherMiddle otherTarget := right | return false
      equivalentCategoryContext context otherContext <&&>
        equivalentTerms #[first, second, source, middle, target]
          #[otherFirst, otherSecond, otherSource, otherMiddle, otherTarget]
  | .contextualArrow context hom source target =>
      let .contextualArrow otherContext otherHom otherSource otherTarget := right | return false
      equivalentCategoryContext context otherContext <&&>
        equivalentTerms #[hom, source, target] #[otherHom, otherSource, otherTarget]
  | .contextualIdentity context object =>
      let .contextualIdentity otherContext otherObject := right | return false
      equivalentCategoryContext context otherContext <&&>
        equivalentTerms #[object] #[otherObject]
  | .arrowProjection receiver =>
      let .arrowProjection other := right | return false
      equivalentTerms #[receiver] #[other]
  | .limitProjection receiver index =>
      let .limitProjection other otherIndex := right | return false
      equivalentTerms #[receiver, index] #[other, otherIndex]
  | .structuredProjection receiver field index =>
      let .structuredProjection otherReceiver otherField otherIndex := right | return false
      unless field == otherField && index == otherIndex do return false
      equivalentTerms #[receiver] #[otherReceiver]
  | .pointView source target route applications argument =>
      let .pointView otherSource otherTarget otherRoute otherApplications otherArgument := right
        | return false
      unless route == otherRoute do return false
      equivalentTerms applications otherApplications <&&>
        equivalentTerms #[source, target, argument] #[otherSource, otherTarget, otherArgument]
  | .morphismTransport source target route receiver =>
      let .morphismTransport otherSource otherTarget otherRoute otherReceiver := right
        | return false
      unless source == otherSource && target == otherTarget && route == otherRoute do return false
      equivalentTerms #[receiver] #[otherReceiver]
  | .functor id params receiver =>
      let .functor other otherParams otherReceiver := right | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&> equivalentTerms #[receiver] #[otherReceiver]
  | .construction id params receiver =>
      let .construction other otherParams otherReceiver := right | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&> equivalentTerms #[receiver] #[otherReceiver]
  | .constructionMap id params source target morphism =>
      let .constructionMap other otherParams otherSource otherTarget otherMorphism := right
        | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[source, target, morphism] #[otherSource, otherTarget, otherMorphism]
  | .categoryParameter id params =>
      let .categoryParameter other otherParams := right | return false
      unless id == other do return false
      equivalentTerms params otherParams
  | .functorParameter id params =>
      let .functorParameter other otherParams := right | return false
      unless id == other do return false
      equivalentTerms params otherParams
  | .cartesian id params baseMorphism receiver field =>
      let .cartesian other otherParams otherBase otherReceiver otherField := right | return false
      unless id == other && field == otherField do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[baseMorphism, receiver] #[otherBase, otherReceiver]
  | .coreObject context object =>
      let .coreObject otherContext otherObject := right | return false
      equivalentCategoryContext context otherContext <&&>
        equivalentTerms #[object] #[otherObject]
  | .coreIso context source target forward backward =>
      let .coreIso otherContext otherSource otherTarget otherForward otherBackward := right
        | return false
      equivalentCategoryContext context otherContext <&&>
        equivalentTerms #[source, target, forward, backward]
          #[otherSource, otherTarget, otherForward, otherBackward]
  | .selectedLift id params source inclusion monic =>
      let .selectedLift other otherParams otherSource otherInclusion otherMonic := right
        | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[source, inclusion, monic] #[otherSource, otherInclusion, otherMonic]
  | .liftProjection receiver field =>
      let .liftProjection otherReceiver otherField := right | return false
      unless field == otherField do return false
      equivalentTerms #[receiver] #[otherReceiver]
  | .liftFactor receiver baseMap cone proof =>
      let .liftFactor otherReceiver otherBaseMap otherCone otherProof := right | return false
      equivalentTerms #[receiver, baseMap, cone, proof]
        #[otherReceiver, otherBaseMap, otherCone, otherProof]
  | .cellComponent id params constructors inverse receiver =>
      let .cellComponent other otherParams otherConstructors otherInverse otherReceiver := right
        | return false
      unless id == other && constructors == otherConstructors && inverse == otherInverse do
        return false
      equivalentTerms params otherParams <&&> equivalentTerms #[receiver] #[otherReceiver]
  | .cellEndpoint id params constructors inverse isRight receiver =>
      let .cellEndpoint other otherParams otherConstructors
          otherInverse otherRight otherReceiver := right
        | return false
      unless id == other && constructors == otherConstructors && inverse == otherInverse &&
          isRight == otherRight do return false
      equivalentTerms params otherParams <&&> equivalentTerms #[receiver] #[otherReceiver]
  | .binder id params domain body admitted =>
      let .binder other otherParams otherDomain otherBody otherAdmitted := right | return false
      unless id == other do return false
      equivalentTerms params otherParams <&&>
        equivalentTerms #[domain, body, admitted] #[otherDomain, otherBody, otherAdmitted]
  | .arrow category morphism source target =>
      let .arrow other otherMorphism otherSource otherTarget := right | return false
      unless category == other do return false
      equivalentTerms #[morphism, source, target] #[otherMorphism, otherSource, otherTarget]
  | .literal form literal =>
      let .literal other otherLiteral := right | return false
      unless form == other do return false
      equivalentTerms #[literal] #[otherLiteral]
  | .method id route receiver comparisons =>
      let .method other otherRoute otherReceiver otherComparisons := right | return false
      unless id == other && route == otherRoute do return false
      equivalentTerms #[receiver] #[otherReceiver] <&&>
        equivalentRouteComparisons comparisons otherComparisons
  | .methodWithLifts id route lifts receiver comparisons =>
      let .methodWithLifts other otherRoute otherLifts otherReceiver otherComparisons := right
        | return false
      unless id == other && route == otherRoute && lifts == otherLifts do return false
      equivalentTerms #[receiver] #[otherReceiver] <&&>
        equivalentRouteComparisons comparisons otherComparisons
  | .property id route receiver comparisons =>
      let .property other otherRoute otherReceiver otherComparisons := right | return false
      unless id == other && route == otherRoute do return false
      equivalentTerms #[receiver] #[otherReceiver] <&&>
        equivalentRouteComparisons comparisons otherComparisons
  | .limit id diagram lift =>
      let .limit other otherDiagram otherLift := right | return false
      unless id == other && lift == otherLift do return false
      equivalentTerms #[diagram] #[otherDiagram]

/-- Compare every retained keyed operation; neither hashes nor encoded node strings
serve as the identity, and no operation can disappear because its key was proof-irrelevant. -/
def equivalentTrace (left right : Std.HashMap Expr Node) : TermElabM Bool :=
  equivalentUnordered (fun (term, node) (otherTerm, otherNode) =>
    equivalentTerms #[term] #[otherTerm] <&&> equivalentNode node otherNode)
    left.toArray right.toArray

/-- Surface spelling is not a selected category's meaning. Its declared expression,
realization and refinement witness still form part of the retained selection. -/
def equivalentCategory (left right : NamedCategoryEntry) : Bool :=
  left.id == right.id && left.declaration == right.declaration &&
    left.expression.syntacticEq right.expression && left.realization == right.realization &&
    left.refinementRealization == right.refinementRealization

/-- Compare the assertion that is actually evaluated, including expected decisions and
the typed data consumed by each computational branch. Display text and the literal form's
proof procedure do not alter its denotation. A binding is not an assertion question. -/
def equivalentClaim (left right : Language.Claim) : TermElabM Bool := do
  match left with
  | .binding => throwError "a binding has no assertion question to compare"
  | .judged question prop expected _ =>
      let .judged other otherProp otherExpected _ := right | return false
      unless expected == otherExpected do return false
      equivalentQuestion question other <&&> equivalentTerms #[prop] #[otherProp]
  | .implemented value =>
      let .implemented other := right | return false
      equivalentTerms #[value] #[other]
  | .literal value category form literal prop _ _ =>
      let .literal other otherCategory otherForm otherLiteral otherProp _ _ := right | return false
      unless equivalentCategory category otherCategory && form.id == otherForm.id &&
          form.category == otherForm.category && form.type == otherForm.type &&
          form.denotation == otherForm.denotation do return false
      equivalentTerms #[value, literal, prop] #[other, otherLiteral, otherProp]
  | .homs first second category prop _ _ =>
      let .homs otherFirst otherSecond otherCategory otherProp _ _ := right | return false
      unless equivalentCategory category otherCategory do return false
      equivalentTerms #[first, second, prop] #[otherFirst, otherSecond, otherProp]
  | .decision prop expected _ =>
      let .decision other otherExpected _ := right | return false
      unless expected == otherExpected do return false
      equivalentTerms #[prop] #[other]

/-- Independent comparison of the complete prepared request. Neither cached identity,
display strings, runtime answers nor revision labels participate. This comparison is in
the current Lean environment; assessing a declaration's meaning across mathematical
revisions remains an independent obligation and cannot be discharged by a revision label. -/
def equivalentTypedQuestion (left right : Realize.TypedQuestion) : TermElabM Bool :=
  equivalentClaim left.claim right.claim <&&> equivalentTrace left.trace right.trace

end CasCatalogue.QuestionIdentity
