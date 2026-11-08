module

public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private structure MethodFamily where
  entry : MethodEntry
  route : Route
  functor : FunctorEntry
  value : Expr

-- Source: Registry.validateMethodEntry and the actual registered functor boundary.
-- The Core wrapper retains the same object and source-selected category dictionary.
private def methodFunctor (state : SemanticState) (route : Route) (method : MethodEntry)
    (bundle : Expr) : MetaM Expr := do
  if method.returnsToSource then
    throwUnsupportedSource "source method lifting requires its actual selected return data"
  let some entry := state.functor? method.functor
    | throwError "the source method has no registered functor"
  discard <| checkedDeclaration entry.declaration
  let selected ← nativeRouteFunctor state route bundle
  let transport ← match method.shape with
    | .object => pure selected.functor
    | .isoInvariant => mkAppM ``CategoryTheory.Functor.core #[selected.functor]
  let function ← registeredFunctorInstance entry
  unless ← expandSourceStructures ((← getMVars function).map mkMVar) do
    throwError "the method functor has inconsistent native category parameters"
  let (_, expected) ← functorCategoryBundles transport
  let (declared, _) ← functorCategoryBundles function
  unless ← isDefEq declared expected do
    throwError "the method functor has a different complete selected source category"
  let function ← mkFunctorComp transport function
  let function ← instantiateMVars function
  if function.hasMVar || function.hasLevelMVar then
    throwUnsupportedSource "the source method requires its complete declaration parameters"
  return function

private def methodReceiver (state : SemanticState) (receiver : NativeSourceJudgement) :
    TermElabM (Option NativeSourceJudgement) := do
  let some category := receiver.category | return none
  if category.role == .object then return some receiver
  let #[constructor] := state.constructors.filter (·.semantics == `CasCatalogue.Constructors.arrow)
    | throwError "a source morphism method requires its registered arrow constructor"
  discard <| checkedDeclaration constructor.semantics
  let bundle ← applyConstructorInterface constructor.semantics #[category.bundle] #[category.bundle]
  let value ← mkAppM ``CategoryTheory.Arrow.mk #[receiver.value]
  return some ⟨value, some ⟨.object,
    .construct constructor.id #[.category category.expression], bundle, none⟩⟩

/-- Form an inherited method through its whole checked functor families before specialization.
Reuse: MethodEntry/validateMethodEntry, nativeRouteFunctor, the first-hit source grammar and
sourceFamilyConversion. Native conversion or supplied whole-family equality identifies
alternatives; provider availability and a receiver's special value supply no agreement. -/
opaque sourceMethod (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  let state ← semanticState
  unless state.methods.any (·.name == name) do return none
  let some receiver ← methodReceiver state receiver | return none
  let some selected := receiver.category | throwError "the source method lost its selected category"
  let query ← SourceRoutes.forMethod selected.expression name
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "method inheritance requires its supplied uniform comparison"
  if routes.isEmpty then return none
  let categoryFamily ← nativeCategoryFamily state selected.expression fun _ => do
    return .param (← mkFreshUserName `methodUniverse)
  let levels : CollectLevelParams.State := {}
  let universes := (levels.collect categoryFamily).params.toList
  let mut families : Array MethodFamily := #[]
  for route in routes do
    for entry in state.methods do
      unless entry.name == name && entry.owner.syntacticEq route.target do continue
      let some functor := state.functor? entry.functor
        | throwError "the source method functor is absent"
      let value ← forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
        let value ← methodFunctor state route entry (mkAppN categoryFamily parameters)
        mkLambdaFVars parameters value
      families := families.push ⟨entry, route, functor, value⟩
  let some first := families[0]? | throwError "the source method lost its first-hit binding"
  let mut agreements := #[]
  for other in families.drop 1 do
    unless first.functor.target.syntacticEq other.functor.target do
      throwSemanticAmbiguity "method families have different complete result categories"
    let evidence := selected.carrier.toArray.flatMap (·.comparisons)
    let some proof ← sourceFamilyConversion first.value other.value evidence
      | throwSemanticAmbiguity "inherited methods require their supplied whole-family agreement"
    agreements := agreements.push proof
  -- Specialize the same already compared family at the actual source bundle once.
  let arguments ← universes.mapM fun _ => mkFreshLevelMVar
  let family := categoryFamily.instantiateLevelParams universes arguments
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  unless ← isDefEq (mkAppN family parameters) selected.bundle do
    throwError "the source method has different complete category parameters"
  let parameters ← parameters.mapM instantiateMVars
  let arguments ← arguments.mapM instantiateLevelMVars
  let function := (mkAppN (first.value.instantiateLevelParams universes arguments) parameters).headBeta
  if function.hasMVar || function.hasLevelMVar then
    throwError "the specialized source method has undetermined parameters"
  let (_, target) ← functorCategoryBundles function
  let input ← match first.entry.shape with
    | .object => pure receiver.value
    | .isoInvariant => mkAppM ``CategoryTheory.Core.mk #[receiver.value]
  let mut value ← functorObject function input target
  for proof in agreements.reverse do
    let mut proof := proof.instantiateLevelParams universes arguments
    for parameter in parameters do proof ← mkAppM ``congrFun #[proof, parameter]
    checkWithKernel proof
    value ← withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] value
        (usedLetOnly := false) (generalizeNondepLet := false)
  let referenced := sourceReference ``MethodEntry first.entry.id.raw first.functor.declaration value
  let referenced := Expr.mdata (KVMap.empty.setString `CasCompiler.source.methodRoutes
    (reprStr (families.map fun family => (family.entry.id, family.route.refs)))) referenced
  return some ⟨referenced, some ⟨.object, first.functor.target, target, none⟩⟩

end CasCompiler
