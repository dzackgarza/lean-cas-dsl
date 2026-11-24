module

public import CasCompiler.FamilyConversion
public import CasCompiler.Elaborate
import CasCompiler.RoutedMethodFamily
import CasCompiler.PropertyFamily
import CasCatalogue.Admission

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private def methodReceiver (state : SemanticState) (receiver : NativeSourceJudgement) :
    TermElabM (Option NativeSourceJudgement) := do
  let some category := receiver.category | return none
  if category.role == .object then return some receiver
  let #[constructor] := state.constructors.filter (·.semantics == `CasCatalogue.Constructors.arrow)
    | throwError "a source morphism method requires its registered arrow constructor"
  discard <| checkedDeclaration constructor.semantics
  let bundle ← applyConstructorInterface constructor.semantics #[category.bundle] #[category.bundle]
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let function ← mkConstWithFreshMVarLevels ``CategoryTheory.Arrow.mk
  let value ← elabAppArgs function #[] #[Arg.expr receiver.value] (some expected) false false
  return some ⟨value, some ⟨.object,
    .construct constructor.id #[.category category.expression], bundle, none, none⟩⟩

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
  let families ← RoutedMethodFamily.atSource selected.expression name
  if families.isEmpty then return none
  let some first := families[0]? | throwError "the source method lost its first-hit binding"
  let agreements ← first.agreements (selected.carrier.toArray.flatMap (·.comparisons))
  -- Specialize the same already compared family at the actual source bundle once.
  let universes := first.universeParams
  let arguments ← universes.mapM fun _ => mkFreshLevelMVar
  let family := first.categoryFamily.instantiateLevelParams universes arguments
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  unless ← isDefEq (mkAppN family parameters) selected.bundle do
    throwError "the source method has different complete category parameters"
  let parameters ← parameters.mapM instantiateMVars
  let arguments ← arguments.mapM instantiateLevelMVars
  let function := (mkAppN
    (first.functorFamily.instantiateLevelParams universes arguments) parameters).headBeta
  let callable := mkAppN (first.family.instantiateLevelParams universes arguments) parameters
  if callable.hasMVar || callable.hasLevelMVar then
    throwError "the specialized source method has undetermined parameters"
  let (_, target) ← functorCategoryBundles function
  -- The synthetic Core belongs inside the checked native callable. The runtime argument is
  -- always this original receiver, including an actual Core object when the source chose one.
  let mut value := first.mark (mkApp callable receiver.value)

  for proof in agreements.reverse do
    let mut proof := proof.instantiateLevelParams universes arguments
    for parameter in parameters do proof ← mkAppM ``congrFun #[proof, parameter]
    checkWithKernel proof
    value ← withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] value
        (usedLetOnly := false) (generalizeNondepLet := false)
  let referenced := Expr.mdata (KVMap.empty.setString `CasCompiler.source.methodRoutes
    (reprStr (families.map fun family => (family.entry.id, family.route.refs)))) value
  return some ⟨referenced, some ⟨.object, first.functor.target, target, none, none⟩⟩


/-- The proposition that a registered property holds of the receiver (CC-PROP): the fibre of the
property's classifier over the receiver's image in the classifier's host category is inhabited.
Reuse: PropertyEntry, classifierInstance and Classifier.Holds of lean-categories; the first-hit
owner routes with their whole-family agreements, as for an inherited carrier. -/
opaque sourceProperty (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  let state ← semanticState
  let some selected := receiver.category | return none
  unless selected.role == .object do return none
  let rows := state.properties.filter fun row =>
    row.name == name && row.receiver.all (·.syntacticEq selected.expression)
  let #[row] := rows
    | if rows.isEmpty then return none
      else throwSemanticAmbiguity s!"several properties named {name} accept this receiver"
  let (_, value) ← PropertyFamily.forReceiver selected row.id receiver.value
  return some ⟨value, none⟩

end CasCompiler
