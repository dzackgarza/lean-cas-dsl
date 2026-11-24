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

/-- The original routed native family and its exact specialization. A candidate retains
the same typed callable and original receiver used by lowering and deferred calls. -/
structure SourceMethodEvidence where
  family : RoutedMethodFamily
  levels : List Level
  parameters : Array Expr

/-- Prepare every actual first-hit method independently. Neither a route preference nor a
same-kind agreement is decided before the other kinds and final native checks compete. -/
opaque sourceMethodChoices (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Array (SourceMemberChoice SourceMethodEvidence)) := do
  let original ← saveState
  try
    prepare
  finally
    original.restore
where
  prepare : TermElabM (Array (SourceMemberChoice SourceMethodEvidence)) := do
    let state ← semanticState
    unless state.methods.any (·.name == name) do return #[]
    let some receiver ← methodReceiver state receiver | return #[]
    let some selected := receiver.category | throwError "the source method lost its selected category"
    let families ← RoutedMethodFamily.atSource selected.expression name
    let prepared ← saveState
    let mut choices : Array (SourceMemberChoice SourceMethodEvidence) := #[]
    for chosen in families do
      prepared.restore
      let universes := chosen.universeParams
      let levels ← universes.mapM fun _ => mkFreshLevelMVar
      let category := chosen.categoryFamily.instantiateLevelParams universes levels
      let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType category)
      unless ← isDefEq (mkAppN category parameters) selected.bundle do
        throwError "the source method has different complete category parameters"
      let parameters ← parameters.mapM instantiateMVars
      let levels ← levels.mapM instantiateLevelMVars
      let callable := mkAppN (chosen.family.instantiateLevelParams universes levels) parameters
      if callable.hasMVar || callable.hasLevelMVar then
        throwError "the specialized source method has undetermined parameters"
      -- Core and the exact return plan are inside the checked whole family.
      let (value, target) ← chosen.applyAt levels parameters receiver.value
      let value := Expr.mdata (KVMap.empty.setString `CasCompiler.source.methodRoutes
        (reprStr (families.map fun family => (family.entry.id, family.route.refs)))) value
      choices := choices.push {
        path := ⟨receiver, some chosen.route⟩
        evidence := ⟨chosen, levels, parameters⟩
        judgement := ⟨value, some ⟨.object, chosen.resultCategory, target, none, none⟩⟩
        nativeState := ← saveState }
    return choices

/-- Compare the surviving complete routed families, then retain their checked specialized
proofs around the already completed result. No result at one receiver proves agreement;
source operands and the completion continuation are never replayed. -/
def retainSourceMethodAgreements (choices : Array (SourceMemberChoice SourceMethodEvidence))
    (judgement : NativeSourceJudgement) : TermElabM NativeSourceJudgement := do
  let some first := choices[0]?
    | throwError "the source method lost its first-hit binding"
  let some selected := first.path.receiver.category
    | throwError "the source method lost its selected category"
  let proofs ← first.evidence.family.agreementsWith (choices.map (·.evidence.family))
    (selected.carrier.toArray.flatMap (·.comparisons))
  let retain := fun initial => do
    let mut value := initial
    for proof in proofs.reverse do
      let mut proof := proof.instantiateLevelParams
        first.evidence.family.universeParams first.evidence.levels
      for parameter in first.evidence.parameters do proof ← mkAppM ``congrFun #[proof, parameter]
      checkWithKernel proof
      value ← withLetDecl (← mkFreshUserName `methodFamilyAgreement) (← inferType proof) proof
        fun binding => mkLetFVars #[binding] value
          (usedLetOnly := false) (generalizeNondepLet := false)
    return value
  -- Preserve the original methodRoutes/proof/routed-mark order for an unchanged result.
  let value ← match judgement.value with
    | .mdata alternatives value =>
      if judgement.value == first.judgement.value then
        pure (.mdata alternatives (← retain value))
      else retain judgement.value
    | _ => retain judgement.value
  return { judgement with value }

/-- The ordinary method entrance uses the same actual candidates and C6 route selection. -/
opaque sourceMethod (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  let original ← saveState
  try
    let choices ← sourceMethodChoices receiver name
    if choices.isEmpty then return none
    let paths := choices.map (·.path)
    let preferred : Option (Array (Nat × Route)) ←
      sourceMemberPreference name (paths.filterMap (·.receiver.category)) paths
    let surviving := match preferred with
      | none => choices
      | some selected => selected.filterMap fun (selection : Nat × Route) => choices[selection.1]?
    let some first := surviving[0]?
      | throwError "the source method lost its first-hit binding"
    first.nativeState.restore
    let value ← retainSourceMethodAgreements surviving first.judgement
    checkSourceMemberSelections surviving
    return some (retainMemberPreference value (preferred.bind fun selected =>
      selected[0]?.map fun (selection : Nat × Route) => selection.2))
  catch error =>
    original.restore
    throw error

/-- The actual registered classifier family, preserving its complete original native
application rather than recovering its parameters from the resulting Holds image. -/
structure SourcePropertyEvidence where
  family : PropertyFamily

/-- Prepare every actual property row and route with the same native producer used by
deferred property calls. Preferences and agreement are decided only after typed survival. -/
opaque sourcePropertyChoices (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Array (SourceMemberChoice SourcePropertyEvidence)) := do
  let original ← saveState
  try
    prepare
  finally
    original.restore
where
  prepare : TermElabM (Array (SourceMemberChoice SourcePropertyEvidence)) := do
    let state ← semanticState
    let some selected := receiver.category | return #[]
    unless selected.role == .object do return #[]
    let rows := state.properties.filter fun row =>
      row.name == name && row.receiver.all (·.syntacticEq selected.expression)
    let prepared ← saveState
    let mut choices : Array (SourceMemberChoice SourcePropertyEvidence) := #[]
    for row in rows do
      prepared.restore
      let some classifier := state.classifier? row.classifier
        | throwError "the property lost its accepted classifier"
      let query ← SourceRoutes.forOwner selected.expression classifier.host
      let some routes ← query.finiteRoutes
        | throwUnsupportedSource "the property route family requires its supplied uniform comparison"
      if routes.isEmpty then
        throwError "the property is not reachable from the receiver's category"
      let routed ← saveState
      for route in routes do
        routed.restore
        let family ← PropertyFamily.forSelection selected.expression row.id route.refs
        let value ← family.atReceiver selected receiver.value
        choices := choices.push {
          path := ⟨receiver, some route⟩
          evidence := ⟨family⟩
          judgement := ⟨value, none⟩
          nativeState := ← saveState }
    return choices

/-- Distinct property rows retain their distinct meanings. For one property, complete
surviving route families must agree; a chosen route asserts no agreement with discarded ones. -/
def retainSourcePropertyAgreements (name : String)
    (choices : Array (SourceMemberChoice SourcePropertyEvidence))
    (judgement : NativeSourceJudgement) : TermElabM NativeSourceJudgement := do
  let some first := choices[0]?
    | throwError "the source property lost its selected route"
  unless choices.all (·.evidence.family.entry.id == first.evidence.family.entry.id) do
    throwSemanticAmbiguity s!"several properties named {name} accept this receiver"
  let some selected := first.path.receiver.category
    | throwError "the source property lost its selected category"
  let agreements ← sourceRouteAgreements (← semanticState) selected
    (choices.map (·.evidence.family.route))
  let retain := fun initial => do
    let mut value := initial
    for proof in agreements.reverse do
      value ← withLetDecl (← mkFreshUserName `propertyRouteAgreement) (← inferType proof) proof
        fun binding => mkLetFVars #[binding] value
          (usedLetOnly := false) (generalizeNondepLet := false)
    return value
  let value ← match judgement.value with
    | .mdata reference value =>
      if judgement.value == first.judgement.value then
        pure (.mdata reference (← retain value))
      else retain judgement.value
    | _ => retain judgement.value
  return { judgement with value }

opaque sourceProperty (receiver : NativeSourceJudgement) (name : String) :
    TermElabM (Option NativeSourceJudgement) := do
  let original ← saveState
  try
    let choices ← sourcePropertyChoices receiver name
    if choices.isEmpty then return none
    let paths := choices.map (·.path)
    let preferred : Option (Array (Nat × Route)) ←
      sourceMemberPreference name (paths.filterMap (·.receiver.category)) paths
    let surviving := match preferred with
      | none => choices
      | some selected => selected.filterMap fun (selection : Nat × Route) => choices[selection.1]?
    let some first := surviving[0]?
      | throwError "the source property lost its selected route"
    first.nativeState.restore
    let value ← retainSourcePropertyAgreements name surviving first.judgement
    checkSourceMemberSelections surviving
    return some (retainMemberPreference value (preferred.bind fun selected =>
      selected[0]?.map fun (selection : Nat × Route) => selection.2))
  catch error =>
    original.restore
    throw error

end CasCompiler
