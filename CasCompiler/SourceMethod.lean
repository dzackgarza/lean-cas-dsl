module

public import CasCompiler.FamilyConversion
public import CasCompiler.Elaborate
public import CasCompiler.SourceMemberChoice
public import CasCompiler.RoutedMethodFamily
public import CasCompiler.PropertyFamily
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


structure SourceMethodEvidence where
  family : RoutedMethodFamily
  levels : List Level
  parameters : Array Expr


opaque sourceMethodChoices (receiver : NativeSourceJudgement) (name : String) :
    SourceReadM (Array (SourceMemberChoice SourceMethodEvidence)) := do
  let state ← semanticState
  unless state.methods.any (·.name == name) do return #[]
  let some receiver ← methodReceiver state receiver | return #[]
  let some selected := receiver.category
    | liftM (m := TermElabM) <| throwError "the source method lost its selected category"
  let families ← RoutedMethodFamily.atSource selected.expression name
  let (choices, _) ← SourceMemberChoice.collectApplicable <| families.map fun chosen => do
    let universes := chosen.universeParams
    let levels ← universes.mapM fun _ => mkFreshLevelMVar
    let category := chosen.categoryFamily.instantiateLevelParams universes levels
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType category)
    unless ← isDefEq (mkAppN category parameters) selected.bundle do
      liftM (m := TermElabM) <| throwError "the source method has different complete category parameters"
    let parameters ← liftM (m := MetaM) <| parameters.mapM instantiateMVars
    let levels ← liftM (m := MetaM) <| levels.mapM instantiateLevelMVars
    let callable := mkAppN (chosen.family.instantiateLevelParams universes levels) parameters
    if callable.hasMVar || callable.hasLevelMVar then
      liftM (m := TermElabM) <| throwError "the specialized source method has undetermined parameters"
    let (value, target) ← chosen.applyAt levels parameters receiver.value
      (fun selected expected => SourceReadM.select selected expected)
    let retained := (← SourceReadM.selection? value).getD { value }
    let category : NativeSourceCategory := ⟨.object, chosen.resultCategory, target, none, none⟩
    let value ← SourceReadM.select { retained with
      value := value
      category := some category
      alternatives := families.map fun family =>
        (.method family.entry family.functor, family.route.refs) }
    return .ok (some (← SourceMemberChoice.capture ⟨receiver, some chosen.route⟩
      ⟨chosen, levels, parameters⟩ ⟨value, some category⟩))
  return choices



def retainSourceMethodAgreements (choices : Array (SourceMemberChoice SourceMethodEvidence))
    (judgement : NativeSourceJudgement) : SourceReadM NativeSourceJudgement := do
  let some first := choices[0]?
    | liftM (m := TermElabM) <| throwError "the source method lost its first-hit binding"
  let some selected := first.path.receiver.category
    | liftM (m := TermElabM) <| throwError "the source method lost its selected category"
  let proofs ← first.evidence.family.agreementsWith (choices.map (·.evidence.family))
    (selected.carrier.toArray.flatMap (·.comparisons))
  let mut value := judgement.value
  for proof in proofs.reverse do
    let mut proof := proof.instantiateLevelParams
      first.evidence.family.universeParams first.evidence.levels
    for parameter in first.evidence.parameters do proof ← mkAppM ``congrFun #[proof, parameter]
    checkWithKernel proof
    value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] value
        (usedLetOnly := false) (generalizeNondepLet := false)
  let retained := (← SourceReadM.selection? judgement.value).getD { value := judgement.value }
  value ← SourceReadM.select { retained with value, category := judgement.category }
  return { judgement with value }


opaque sourceMethod (receiver : NativeSourceJudgement) (name : String) :
    SourceReadM (Option NativeSourceJudgement) := do
  let choices ← sourceMethodChoices receiver name
  if choices.isEmpty then return none
  let paths := choices.map (·.path)
  let preferred ← sourceMemberPreference name (paths.filterMap (·.receiver.category)) paths
  let surviving := match preferred with
    | none => choices
    | some selected => selected.filterMap fun (selection : Nat × Route) => choices[selection.1]?
  let some first := surviving[0]?
    | liftM (m := TermElabM) <| throwError "the source method lost its first-hit binding"
  first.withScope do
    let value ← retainSourceMethodAgreements surviving first.judgement
    checkSourceMemberSelections surviving
    return some (← retainMemberPreference value (preferred.bind fun selected =>
      selected[0]?.map fun (selection : Nat × Route) => selection.2))


structure SourcePropertyEvidence where
  family : PropertyFamily


opaque sourcePropertyChoices (receiver : NativeSourceJudgement) (name : String) :
    SourceReadM (Array (SourceMemberChoice SourcePropertyEvidence)) := do
  let state ← semanticState
  let some selected := receiver.category | return #[]
  unless selected.role == .object do return #[]
  let rows := state.properties.filter fun row =>
    row.name == name && row.receiver.all (·.syntacticEq selected.expression)
  let mut families : Array PropertyFamily := #[]
  for row in rows do
    let some classifier := state.classifier? row.classifier
      | liftM (m := TermElabM) <| throwError "the property lost its accepted classifier"
    let query ← SourceRoutes.forOwner selected.expression classifier.host
    let some routes ← query.finiteRoutes
      | liftM (m := TermElabM) <|
        throwUnsupportedSource "the property route family requires its supplied uniform comparison"
    if routes.isEmpty then
      liftM (m := TermElabM) <| throwError "the property is not reachable from the receiver's category"
    for route in routes do
      families := families.push (← PropertyFamily.forSelection selected.expression row.id route.refs)
  let (choices, _) ← SourceMemberChoice.collectApplicable <| families.map fun family => do
    let value ← SourceReadM.select (← family.atReceiver selected receiver.value)
    return .ok (some (← SourceMemberChoice.capture ⟨receiver, some family.route⟩
      ⟨family⟩ ⟨value, none⟩))
  return choices


def retainSourcePropertyAgreements (name : String)
    (choices : Array (SourceMemberChoice SourcePropertyEvidence))
    (judgement : NativeSourceJudgement) : SourceReadM NativeSourceJudgement := do
  let some first := choices[0]?
    | liftM (m := TermElabM) <| throwError "the source property lost its selected route"
  unless choices.all (·.evidence.family.entry.id == first.evidence.family.entry.id) do
    liftM (m := TermElabM) <| throwSemanticAmbiguity s!"several properties named {name} accept this receiver"
  let some selected := first.path.receiver.category
    | liftM (m := TermElabM) <| throwError "the source property lost its selected category"
  let agreements ← sourceRouteAgreements (← semanticState) selected
    (choices.map (·.evidence.family.route))
  let mut value := judgement.value
  for proof in agreements.reverse do
    value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `propertyRouteAgreement) (← inferType proof) proof
      fun binding => mkLetFVars #[binding] value
        (usedLetOnly := false) (generalizeNondepLet := false)
  let retained := (← SourceReadM.selection? judgement.value).getD { value := judgement.value }
  value ← SourceReadM.select { retained with value, category := judgement.category }
  return { judgement with value }

opaque sourceProperty (receiver : NativeSourceJudgement) (name : String) :
    SourceReadM (Option NativeSourceJudgement) := do
  let choices ← sourcePropertyChoices receiver name
  if choices.isEmpty then return none
  let paths := choices.map (·.path)
  let preferred ← sourceMemberPreference name (paths.filterMap (·.receiver.category)) paths
  let surviving := match preferred with
    | none => choices
    | some selected => selected.filterMap fun (selection : Nat × Route) => choices[selection.1]?
  let some first := surviving[0]?
    | liftM (m := TermElabM) <| throwError "the source property lost its selected route"
  first.withScope do
    let value ← retainSourcePropertyAgreements name surviving first.judgement
    checkSourceMemberSelections surviving
    return some (← retainMemberPreference value (preferred.bind fun selected =>
      selected[0]?.map fun (selection : Nat × Route) => selection.2))

end CasCompiler
