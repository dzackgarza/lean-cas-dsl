/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import Mathlib.CategoryTheory.SingleObj
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
    payload := .computed actual (.inline (Json.arr #[])) }
  let trace ← Trace.new
  let harness ← Harness.empty
  harness.results.modify fun cache =>
    ((cache.insert source sourceWire).insert target targetWire).insert actual graph
  let (framed, dependencies) ← frameMorphismFragment harness trace source target graph (some context)
  let .ok typed := Backend.TypedMap.decode framed.json
    | throwError "the complete selected Hom did not retain the public typedMap frame"
  unless typed.source == sourceWire.json && typed.target == targetWire.json &&
      typed.callable == graph.json && dependencies.any (·.value == source) &&
      dependencies.any (·.value == target) do
    throwError "the complete Hom frame changed an actual endpoint or callable packet"
  let combined : Wire := { graph with
    payload := ← combinedPayload actual framed (dependencies.push graph) }
  unless combined.owner? == sourceWire.owner? &&
      DataOwnership.project #[.field "args", .index 0] combined.ownership == sourceWire.ownership &&
      DataOwnership.project #[.field "args", .index 1] combined.ownership == targetWire.ownership &&
      (DataOwnership.project #[.field "args", .index 2] combined.ownership).isEmpty do
    throwError "the full Hom frame lost an endpoint supplier or assigned one to its portable callable"
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

/- A reflection-only boundary fixture from Mathlib's existing SingleObj
instances. Their object and Hom types reduce to the same types, but the natural
numbers' multiplicative and additive category dictionaries differ. These local
contexts register no semantic row and prescribe no computational answer. -/
run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the framing fixture has no form metadata"
  let multiplicative ← elabTermAndSynthesize (← `(Cat.of (SingleObj ℕ))) none
  let additive ← elabTermAndSynthesize
    (← `(Cat.of (SingleObj (Multiplicative ℕ)))) none
  let endpoint ← elabTermAndSynthesize (← `(SingleObj.star ℕ)) none
  let value := mkNatLit 2
  let retained : CategoryContext := { expression := category.expression, bundle := multiplicative }
  let different : CategoryContext := { retained with bundle := additive }
  CategoryContext.checkMorphism retained value endpoint endpoint
  CategoryContext.checkMorphism different value endpoint endpoint
  if ← withoutModifyingState (withTransparency .all <|
      isDefEq retained.bundle different.bundle) then
    throwError "the framing fixture does not distinguish complete category dictionaries"
  let endpointWire : Wire := {
    form := .diagrams category
    payload := .ordinary endpoint (toJson "retained endpoint")
    categoryContext := some retained }
  let input : Wire := {
    form := .canonicalMorphism category
    payload := .computed value (.owned "context-framing" 421 (Json.arr #[]))
    categoryContext := some retained }
  let reject (label : String) (action : TermElabM Unit) : TermElabM Unit := do
    let rejected ← try
      action
      pure false
    catch error =>
      if Exception.interpretationKind error == .invalid then pure true else throw error
    unless rejected do
      throwError "{label} replaced a complete retained category dictionary"
  let trace ← Trace.new
  let harness ← Harness.empty
  harness.results.modify (·.insert endpoint endpointWire)
  for framed in #[false, true] do
    let wire := { input with morphismFramed := framed }
    reject "whole-map presentation" do
      discard <| presentMorphism wire endpointWire endpointWire (some different)
    reject "map-data framing" do
      discard <| frameMorphismData harness trace endpoint endpoint wire (some different)
    reject "callable endpoint framing" do
      discard <| realizeCallableEndpoint harness trace wire endpoint true (some different)
    reject "retained endpoint presentation" do
      discard <| presentMorphism wire
        { endpointWire with categoryContext := some different } endpointWire (some retained)
    let presented ← presentMorphism wire endpointWire endpointWire
    unless presented.morphismFramed && presented.json == input.json &&
        presented.owner? == input.owner? do
      throwError "compatible framing changed its actual packet or live owner"
  harness.results.modify (·.insert endpoint
    { endpointWire with categoryContext := some different })
  reject "cached callable endpoint" do
    discard <| realizeCallableEndpoint harness trace input endpoint true (some retained)
  let unknown ← mkFreshExprMVar (← inferType retained.bundle)
  reject "incomplete selected context" do
    discard <| presentMorphism input endpointWire endpointWire
      (some { retained with bundle := unknown })
  unless (← instantiateMVars unknown).isMVar do
    throwError "framing inferred missing category data from a retained context"
