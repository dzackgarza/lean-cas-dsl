/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Language
meta import CasCatalogue.Language

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/-! Engineering checks for complete source contexts and retained construction
choices. Every mathematical declaration comes from the accepted catalogue or
its existing library imports; these checks add no registration or backend. -/

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some commutative := state.categories.find?
      (·.declaration == `LeanCategories.Algebra.CommutativeRings)
    | throwError "the existing commutative-ring context is absent"
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the existing ring context is absent"
  let trace ← Trace.new
  let context : Ctx := { trace := some trace }
  let original ← (object state "ℤ" #[] (some commutative)).run context
  let handle ← (semanticObject original).run context
  let selected ← (objectContext original).run context
  let derived := Value.derivedObject handle selected #[original]
  let expected ← elabTermAndSynthesize (← `(RingCat)) none
  let actual ← (typedParameter expected derived).run context
  unless !actual.hasMVar && !actual.hasLevelMVar && (← isTypeCorrect actual) &&
      (← withTransparency .all <| isDefEq (← inferType actual) expected) do
    throwError "an unnamed source context did not form its declared structural parameter"
  let parameterView ← (structuredParameterView derived actual rings).run context
  unless (sourceParameterValues parameterView).any (·.sameSource derived) do
    throwError "the structural parameter discarded its original complete source context"
  let .object _ _ _ _ (some (_, retained, route, _, applications)) := parameterView
    | throwError "the structural parameter lost its complete retained action"
  unless !route.isEmpty && route.size == applications.size &&
      (sourceParameterValues retained).any (·.sameSource derived) do
    throwError "the structural parameter replaced its source or exact edge applications"
  let carrierType ← elabTermAndSynthesize (← `(Type)) none
  let carrier ← (typedParameter carrierType derived).run context
  let namedCarrier ← (carrierObject original).run context
  unless ← withTransparency .all <|
      isDefEq carrier (← (semanticObject namedCarrier).run context) do
    throwError "named and unnamed forms of one complete source chose different carriers"
  let anonymous := Value.derivedObject handle selected #[]
  let .element numeral result ← (toElement (.nat 2) anonymous).run context
    | throwError "a complete unnamed structure lost its inherited numeral"
  unless !numeral.hasMVar && !numeral.hasLevelMVar && (← isTypeCorrect numeral) &&
      (sourceParameterValues result).any (·.sameSource anonymous) do
    throwError "the inherited numeral lost its original unnamed structure"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let some modules := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the existing module category schema is absent"
  let source ← elabTermAndSynthesize (← `(ModuleCat.of ℤ (ℤ × ℤ))) none
  let target ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let hom ← elabTermAndSynthesize (← `(ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ))) none
  let selected ← CategoryContext.ofNamed modules source
  let first := Value.derivedObject source selected #[]
  let second := Value.derivedObject target selected #[]
  let original := Value.derivedMorphism hom source target selected (first, second)
  let expected ← elabTermAndSynthesize (← `((ℤ × ℤ) → ℤ)) none
  let trace ← Trace.new
  let actual ← (typedParameter expected original).run { trace := some trace }
  unless !actual.hasMVar && !actual.hasLevelMVar && (← isTypeCorrect actual) &&
      (← withTransparency .all <| isDefEq (← inferType actual) expected) do
    throwError "the complete derived map did not travel through its registered carrier action"
  let some (.contextualRoute retained _ route applications originalHom true) ← trace.node? actual
    | throwError "a raw function parameter lost the original declared morphism action"
  unless retained.expression.syntacticEq selected.expression && !route.isEmpty &&
      route.size == applications.size &&
      (← withTransparency .all <| isDefEq retained.bundle selected.bundle <&&>
        isDefEq originalHom hom) do
    throwError "the map parameter replaced its full original context or edge applications"
  let impossible ← elabTermAndSynthesize (← `(String)) none
  let failure ← try
      discard <| (typedParameter impossible first).run {}
      pure none
    catch error => pure (Exception.stratum? error)
  unless failure == some .invalid do
    throwError "absence of a declared structural route was not classified as invalid"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let state ← registryState
  let trace ← Trace.new
  let context : Ctx := { trace := some trace }
  let coordinate ← (object state "ℤ" #[] none).run context
  let target ← (object state "Vec" #[coordinate, .nat 2] none).run context
  let result ← (tupleOf #[.nat 1, .nat 2] coordinate (target? := some target)).run context
  let .element point retained := result
    | throwError "the complete tuple declarations did not return a point"
  unless !point.hasMVar && !point.hasLevelMVar && (← isTypeCorrect point) &&
      (← withTransparency .all <| isDefEq (← (semanticObject retained).run context)
        (← (semanticObject target).run context)) do
    throwError "the registered tuple construction changed its explicit complete result"
  let first ← (object state "Fin" #[.nat 2] none).run context
  let second ← (object state "Fin" #[.nat 3] none).run context
  let .object _ category .. := first | unreachable!
  for (shape, colimit) in #[("product", false), ("coproduct", true)] do
    let (diagram, selection) ←
      (standardDiagramWithSelection shape #[first, second] colimit).run context
    let some exact := selection
      | throwError "a direct accepted presentation lost its exact selected identity"
    let presentation ← (limitIn colimit shape diagram category selection).run context
    let some (.limit id _ lift) ← trace.node? presentation
      | throwError "the construction lost its exact semantic record"
    unless id == exact.limit && lift == exact.lift do
      throwError "diagram interpretation reselected a different accepted presentation"
  let failure ← try
      discard <| (standardDiagram "coproduct" #[first, second] false).run context
      pure none
    catch error => pure (Exception.stratum? error)
  unless failure == some .invalid do
    throwError "a colimit declaration silently supplied a limit diagram"

/-! Retained full-object presentations preserve each original producer occurrence.
The checks use accepted catalogue objects, structural actions and the public
reader. Occupied keys produce independent handles; unrecorded keys keep their
exact self-records, including on repeated recognition. -/

namespace CasCatalogue.ContextParameterProducerPreservation

private def checkOriginalRecords (trace : Trace) (before : Std.HashMap Expr Node) :
    TermElabM Unit := do
  let current ← trace.get
  for (term, node) in before.toArray do
    unless current[term]? == some node do
      throwError "the reader replaced an exact original producer record"


private def checkFullPresentations (expected representative : Expr)
    (presentations : Array ParameterPresentation) : TermElabM Unit := do
  for presentation in presentations do
    unless !presentation.object.hasMVar && !presentation.object.hasLevelMVar &&
        !presentation.image.hasMVar && !presentation.image.hasLevelMVar &&
        (← isTypeCorrect presentation.object) && (← isTypeCorrect presentation.image) &&
        presentation.route.size == presentation.applications.size &&
        (← withTransparency .all <| isDefEq (← inferType presentation.image) expected) do
      throwError "a retained full presentation changed its closed source, image or action slots"
    let equation ← mkEq presentation.image representative
    unless !presentation.identity.hasSorry &&
        (← Decide.kernelAccepts equation presentation.identity) do
      throwError "a retained full-structure identity failed its original complete kernel target"

private def validateCompleteTrace (trace : Trace) (roots : Array Expr) : TermElabM Unit := do
  let entries ← (← trace.get).toArray.mapM fun (value, node) => do
    return (← instantiateMVars value, ← node.mapTermsM instantiateMVars)
  Trace.checkProducedEntries entries roots

private def checkEquivalentSources (carriers : Bool) : TermElabM Unit := do
  let state ← registryState
  let some rings := state.categories.find? (·.name == "Rings")
    | throwError "the existing Rings category is absent"
  let some commutative := state.categories.find?
      (·.name == "CommutativeRings")
    | throwError "the existing commutative-ring category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the existing Sets category is absent"
  let trace ← Trace.new
  let context : Ctx := { trace := some trace }
  let direct ← (object state "ℤ" #[] (some rings)).run context
  let source ← (object state "ℤ" #[] (some commutative)).run context
  let directHandle ← (semanticObject direct).run context
  let sourceHandle ← (semanticObject source).run context
  let expected ← inferType directHandle
  let actual ← (typedParameter expected source).run context
  let routed ← (structuredParameterView source actual rings).run context
  let some directNode@(.object directId _) ← trace.node? directHandle
    | throwError "the direct accepted object lost its original record"
  let some sourceNode@(.object sourceId _) ← trace.node? sourceHandle
    | throwError "the commutative source lost its original record"
  let some routeNode ← trace.node? actual
    | throwError "the accepted structural action lost its original record"
  Trace.checkProducerRecord directHandle directNode
  Trace.checkProducerRecord sourceHandle sourceNode
  Trace.checkProducerRecord actual routeNode
  unless directId != sourceId && directHandle != actual &&
      !actual.hasMVar && !actual.hasLevelMVar && (← isTypeCorrect actual) &&
      (← withTransparency .all <| isDefEq directHandle actual) &&
      direct.declarations != routed.declarations do
    throwError "the fixture did not retain two distinct accepted full-object sources"
  match routeNode with
  | .retainedRoute _ _ route applications receiver =>
      unless !route.isEmpty && route.size == applications.size && receiver == sourceHandle do
        throwError "the route does not retain the exact original commutative source"
  | _ => throwError "the independently supplied ring has no accepted retained route"
  let (_, _, _, alternatives, _) ←
    (coalesceSelectedParameterViews expected actual #[direct, routed]).run context
  unless alternatives.size == 2 && alternatives.any (·.source == directId) &&
      alternatives.any (·.source == sourceId) do
    throwError "the complete-structure checks did not retain both accepted presentations"
  let (target, targetCategory, representative) ← if carriers then do
      let directCarrier ← (carrierObject direct).run context
      let routedCarrier ← (carrierObject routed).run context
      unless (← (identityCarrierView directCarrier routedCarrier).run context) &&
          (← (identityCarrierView routedCarrier directCarrier).run context) do
        throwError "the declared carrier relation did not retain both maximal sources"
      pure (← (semanticObject directCarrier).run context, sets, directHandle)
    else pure (actual, rings, actual)
  let (expectedOriginals, expectedSource, expectedRoute, expectedPresentations,
      expectedApplications) ← (coalesceSelectedParameterViews
        (← inferType representative) representative #[direct, routed]).run context
  let before ← trace.get
  let label := if carriers then "common-full-source" else "nonsets-multiview"
  let result ← try
      (recognize state target targetCategory #[direct, routed] #[] false).run context
    catch error =>
      checkOriginalRecords trace before
      throwError "{label}: complete accepted sources passed; original records remain; {error.toMessageData}"
  checkOriginalRecords trace before
  let selected ← if carriers then do
      let .object _ _ _ (some selected) _ := result
        | throwError "the common-source carrier lost its complete selected object"
      pure selected
    else pure result
  let retained ← (semanticObject selected).run context
  let some node@(.parameterEquivalence targetType original presentations) ← trace.node? retained
    | throwError "the result lost its checked full-object presentations"
  Trace.checkProducerRecord retained node
  unless retained != representative && original == representative &&
      targetType == (← inferType representative) &&
      (← withTransparency .all <| isDefEq targetType expected) &&
      presentations.size == 2 &&
      presentations.any (·.source == directId) && presentations.any (·.source == sourceId) do
    throwError "the additional presentation failed to preserve its exact original child"
  unless (Trace.producerAnchor? retained).isSome && (before[retained]?).isNone do
    throwError "the additional presentation did not receive its own fresh producer handle"
  Trace.checkProducerRecord retained
    (.parameterEquivalence (← inferType representative) representative expectedPresentations)
  let .object _ selectedCategory _ _ (some (originals, selectedSource, selectedRoute,
      selectedPresentations, selectedApplications)) := selected
    | throwError "the returned complete object lost its original view evidence"
  unless selectedCategory.id == rings.id && selectedCategory.declaration == rings.declaration &&
      originals.size == expectedOriginals.size &&
      (originals.zip expectedOriginals).all (fun (a, b) => a.sameSource b) &&
      selectedSource.sameSource expectedSource && selectedRoute == expectedRoute &&
      selectedPresentations == expectedPresentations &&
      selectedApplications == expectedApplications do
    throwError "the returned view changed an original source, route or ordered evidence child"
  let some directPresentation := presentations.find? (·.source == directId) | unreachable!
  let some routedPresentation := presentations.find? (·.source == sourceId) | unreachable!
  unless directPresentation.object.equal directHandle &&
      directPresentation.image.equal directHandle &&
      routedPresentation.object.equal sourceHandle && routedPresentation.image.equal actual do
    throwError "the checked alternatives replaced an exact original object or action result"
  checkFullPresentations targetType representative presentations
  let refused ← try
      Trace.record (some trace) representative node
      pure false
    catch _ => pure true
  unless refused do
    throwError "the raw overwrite guard admitted a second producer at the original key"
  checkOriginalRecords trace before
  validateCompleteTrace trace #[retained, directHandle, sourceHandle, actual]

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  checkEquivalentSources false

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  checkEquivalentSources true

private def selectedHandle (carriers : Bool) (value : Value) (context : Ctx) :
    TermElabM Expr := do
  let selected ← if carriers then do
      let .object _ _ _ (some selected) _ := value
        | throwError "the recovered carrier has no complete selected object"
      pure selected
    else pure value
  (semanticObject selected).run context

private def checkSelfRecovery (carriers : Bool) : TermElabM Unit := do
  let state ← registryState
  let rings ← categoryNamed state "Rings"
  let sets ← categoryNamed state "Sets"
  let some commutative := state.categories.find?
      (·.name == "CommutativeRings")
    | throwError "the accepted commutative-ring category is absent"
  let trace ← Trace.new
  let context : Ctx := { trace := some trace }
  -- For the carrier case the independent named representative is deliberately
  -- supplied by the ordinary no-recorder interface. No trace key is removed.
  let direct ← (object state "ℤ" #[] (some rings)).run
    (if carriers then {} else context)
  let source ← (object state "ℤ" #[] (some commutative)).run context
  let directHandle ← (semanticObject direct).run context
  let sourceHandle ← (semanticObject source).run context
  let actual ← (typedParameter (← inferType directHandle) source).run context
  let routed ← (structuredParameterView source actual rings).run context
  let (target, category, representative) ← if carriers then do
      let carrier ← (carrierObject direct).run context
      pure (← (semanticObject carrier).run context, sets, directHandle)
    else do
      let unrecorded ← mkAppM ``id #[actual]
      pure (unrecorded, rings, unrecorded)
  let (_, _, _, checkedPresentations, _) ← (coalesceSelectedParameterViews
    (← inferType representative) representative #[direct, routed]).run context
  let before ← trace.get
  unless (before[representative]?).isNone do
    throwError "the self-record fixture already owns its exact representative key"
  let first ← (recognize state target category #[direct, routed] #[] false).run context
  let firstHandle ← selectedHandle carriers first context
  let some firstNode@(.parameterEquivalence expected original alternatives) ←
      pure ((← trace.get)[firstHandle]?)
    | throwError "the unrecorded parameter lost its checked self-presentation"
  unless firstHandle == representative && original == representative &&
      expected == (← inferType representative) && alternatives.size == 2 do
    throwError "the unrecorded complete representative acquired a replacement address"
  unless firstNode == .parameterEquivalence (← inferType representative)
      representative checkedPresentations do
    throwError "the unrecorded self-presentation changed its complete independently checked evidence"
  checkFullPresentations expected representative alternatives
  let beforeRepeat ← trace.get
  let repeated ← (recognize state target category #[direct, routed] #[] false).run context
  let repeatedHandle ← selectedHandle carriers repeated context
  unless repeatedHandle == firstHandle &&
      ((← trace.get)[repeatedHandle]?) == some firstNode do
    throwError "exact recovery changed the complete existing presentation or its address"
  let after ← trace.get
  for (term, node) in before.toArray do
    unless after[term]? == some node do
      throwError "self-record recovery changed an original source or action"
  checkOriginalRecords trace beforeRepeat
  validateCompleteTrace trace #[representative, directHandle, sourceHandle, actual]

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  checkSelfRecovery false

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  checkSelfRecovery true

end CasCatalogue.ContextParameterProducerPreservation
