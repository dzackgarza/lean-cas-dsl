/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for complete Hom representations whose reduced type no
longer has the syntactic `Quiver.Hom` head. The graph-shaped packet checks framing
and retained ownership only; it claims neither graph totality nor a mathematical
answer. Public result validation remains a separate boundary. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_elab do
  let state ← registryState
  let source ← elabTermAndSynthesize (← `(ModuleCat.of ℤ (ℤ × ℤ))) none
  let target ← elabTermAndSynthesize (← `(ModuleCat.of ℤ ℤ)) none
  let declared ← elabTermAndSynthesize
    (← `(ModuleCat.ofHom (LinearMap.fst ℤ ℤ ℤ))) none
  let actual ← withTransparency .all <| whnf declared
  unless (Language.homEnds? (← inferType actual)).isNone do
    throwError "the bundled Hom fixture still has its original syntactic Hom head"
  let some category := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the complete selected category fixture is absent"
  let context ← CategoryContext.ofNamed category source
  CategoryContext.checkMorphism context actual source target
  let (recoveredSource, recoveredTarget) ← contextualMorphismEndpoints context actual
  unless ← withTransparency .all <|
      isDefEq recoveredSource source <&&> isDefEq recoveredTarget target do
    throwError "the selected Hom interface changed one complete endpoint"
  let data := fun token => Json.mkObj [("ctor", "opaqueData"),
    ("args", Json.arr #[toJson (token : String)])]
  let sourceWire : Wire := {
    form := .diagrams category
    payload := .computed source (.owned "hom-framing" 419 (data "actual source"))
    categoryContext := some context }
  let targetWire : Wire := {
    form := .diagrams category
    payload := .computed target (.owned "hom-framing" 419 (data "actual target"))
    categoryContext := some context }
  let graph : Wire := {
    form := .canonicalMorphism category
    payload := .computed actual (.owned "hom-framing" 419 (Json.arr #[])) }
  let trace ← Trace.new
  let harness ← Harness.empty
  harness.results.modify fun cache =>
    ((cache.insert source sourceWire).insert target targetWire).insert actual graph
  let (framed, dependencies) ← frameMorphismData harness trace source target graph (some context)
  let .ok typed := Backend.TypedMap.decode framed
    | throwError "the complete selected Hom did not retain the public typedMap frame"
  unless typed.source == sourceWire.json && typed.target == targetWire.json &&
      typed.callable == graph.json && dependencies.any (·.value == source) &&
      dependencies.any (·.value == target) do
    throwError "the complete Hom frame changed an actual endpoint or callable packet"
  let combined : Wire := { graph with
    payload := ← combinedPayload actual framed (dependencies.push graph) }
  unless combined.owner? == graph.owner? do
    throwError "the full Hom frame discarded the original live ownership"
  let presented ← presentMorphism graph sourceWire targetWire (some context)
  unless presented.morphismFramed && presented.json == graph.json &&
      presented.owner? == graph.owner? && presented.categoryContext.isSome do
    throwError "the bundled Hom lost its full context or actual data when framed"
  let wrongEndpoints ← try
    discard <| frameMorphismData harness trace target source graph (some context)
    pure false
  catch _ => pure true
  unless wrongEndpoints do
    throwError "the bundled Hom accepted swapped independently selected endpoints"
  let wrongPresentation ← try
    discard <| presentMorphism presented targetWire sourceWire (some context)
    pure false
  catch _ => pure true
  unless wrongPresentation do
    throwError "an already framed Hom bypassed its complete selected endpoint check"
