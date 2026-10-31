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

meta section

/-- Actual opaque packets are received from the existing protocol-only process.
No mathematical registration or computation is introduced by these controls. -/
private def withFramingSession (backend operation : String)
    (action : Harness → TermElabM Unit) : TermElabM Unit := do
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let harness ← Harness.ofManifest root {
    backends := #[{
      name := backend
      command := "python3"
      args := #["probe_owned_callable.py", operation] }]
    registrations := #[] }
  try action harness
  finally harness.stop

/-- Receive a real response before retaining its live supplier. The returned
ownership table comes only from the public receive boundary. -/
private def receiveFramingData (harness : Harness) (backend operation : String)
    (arguments : Array Json) : TermElabM ComputationData := do
  let .ok session ← harness.connection backend
    | throwError "the framing fixture's ownership process did not start"
  let request := Json.mkObj [("ctor", toJson operation), ("args", Json.arr arguments)]
  let .ok answer ← Backend.call session.connection operation request
    | throwError "the framing fixture did not receive its actual opaque packet"
  match Backend.ComputationalValue.decode answer with
  | .ok (.opaque _) => pure ()
  | _ => throwError "the framing fixture did not receive an anonymous packet"
  let received ← receiveComputationalData harness backend operation answer
  let .scoped data := received
    | throwError "the framing fixture lost its returned packet's scoped supplier"
  checkDataOwners harness data
  return received

/-- These ownership checks follow the original framing assertions, while each
actual packet is still live and then after its producing session has stopped. -/
private def checkFramingOwnership (harness : Harness) (data : DataOwnership.Data) :
    TermElabM Unit := do
  checkDataOwners harness data
  let unavailable (active : Harness) : TermElabM Bool := do
    try
      checkDataOwners active data
      return false
    catch error => return Exception.stratum? error == some .unavailable
  unless ← unavailable (← Harness.empty) do
    throwError "the framed data became available outside its actual owning session"
  harness.stop
  unless ← unavailable harness do
    throwError "the framed data survived expiry of its actual owning session"

run_elab withFramingSession "hom-framing" "hom-framing-field" fun harness => do
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
  let sourceData ← receiveFramingData harness "hom-framing" "hom-framing-field"
    #[toJson ("actual source" : String)]
  let targetData ← receiveFramingData harness "hom-framing" "hom-framing-field"
    #[toJson ("actual target" : String)]
  let sourceWire : Wire := {
    form := .diagrams category
    payload := .computed source sourceData
    categoryContext := some context }
  let targetWire : Wire := {
    form := .diagrams category
    payload := .computed target targetData
    categoryContext := some context }
  let graph : Wire := {
    form := .canonicalMorphism category
    payload := .computed actual (.inline (Json.arr #[])) }
  -- The producer supplies these independently checked complete endpoints before
  -- framing. A reduced Hom and its returned packet do not recover them from a
  -- later expression-keyed cache.
  let graph ← retainCallableEndpoints graph sourceWire targetWire context
  let trace ← Trace.new
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
  checkFramingOwnership harness combined.fragment

/- A reflection-only boundary fixture from Mathlib's existing SingleObj
instances. Their object and Hom types reduce to the same types, but the natural
numbers' multiplicative and additive category dictionaries differ. These local
contexts register no semantic row and prescribe no computational answer. -/
run_elab withFramingSession "context-framing" "context-framing-callable" fun harness => do
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
  -- This initial slot has not captured an endpoint occurrence. Its cache
  -- compatibility is checked separately from the completed producer below.
  let pending : Wire := {
    form := .canonicalMorphism category
    payload := .ordinary value (Json.arr #[])
    categoryContext := some retained }
  let inputData ← receiveFramingData harness "context-framing" "context-framing-callable"
    #[Json.arr #[]]
  let input : Wire := {
    form := .canonicalMorphism category
    payload := .computed value inputData
    categoryContext := some retained }
  let input ← retainCallableEndpoints input endpointWire endpointWire retained
  let reject (label : String) (action : TermElabM Unit) : TermElabM Unit := do
    let rejected ← try
      action
      pure false
    catch error =>
      if Exception.interpretationKind error == .invalid then pure true else throw error
    unless rejected do
      throwError "{label} replaced a complete retained category dictionary"
  let trace ← Trace.new
  harness.results.modify (·.insert endpoint endpointWire)
  let framed ← presentMorphism input endpointWire endpointWire (some retained)
  for wire in #[input, framed] do
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
    discard <| realizeCallableEndpoint harness trace pending endpoint true (some retained)
  let retainedEndpoint ← realizeCallableEndpoint harness trace input endpoint true (some retained)
  unless sameCompleteWireContext retainedEndpoint endpointWire do
    throwError "a later cache entry replaced the completed callable's original endpoint occurrence"
  let unknown ← mkFreshExprMVar (← inferType retained.bundle)
  reject "incomplete selected context" do
    discard <| presentMorphism input endpointWire endpointWire
      (some { retained with bundle := unknown })
  unless (← instantiateMVars unknown).isMVar do
    throwError "framing inferred missing category data from a retained context"
  checkFramingOwnership harness input.fragment

end
