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
  let view ← (structuredParameterView derived actual rings).run context
  unless (sourceParameterValues view).any (·.sameSource derived) do
    throwError "the structural parameter discarded its original complete source context"
  let .object _ _ _ _ (some (_, retained, route, _, applications)) := view
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
