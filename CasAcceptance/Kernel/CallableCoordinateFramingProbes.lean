/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls of complete callable coordinates. Arbitrary opaque data
below supply no mathematical answer, proof, transfer or live backend result. -/

open Lean Meta Elab Command Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

run_cmd liftTermElabM <| withoutErrToSorry do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the selected set category is absent"
  let source ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let wrong ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 3)) none
  let hom ← mkAppM ``CategoryTheory.CategoryStruct.id #[source]
  let trace ← Trace.new
  discard <| Semantic.recordNamedObject source (some trace)
  let harness ← Harness.empty
  let endpoint ← realizeEndpoint harness trace "the exact whole-map endpoint" source
  let symbolic := Json.mkObj [("ctor", "identity"),
    ("args", Json.arr #[endpoint.json, endpoint.json])]
  let token := Backend.ComputationalValue.encode (.opaque "unchanged whole-map data")
  let ordinary : Wire := { form := .canonicalMorphism sets, payload := .ordinary hom symbolic }
  let owned : Wire := {
    form := .canonicalMorphism sets
    payload := .computed hom (.owned "coordinate-owner" 41 token) }
  for input in #[ordinary, owned] do
    let (data, dependencies) ← frameMorphismFragment harness trace source source input
    unless data.json == input.json do
      throwError "framing replaced the complete symbolic or owned callable data"
    let retained : Wire := { input with
      payload := (← combinedPayload hom data (dependencies.push input)) }
    unless retained.owner? == input.owner? do
      throwError "framing changed the original callable owner"
    for framed in #[false, true] do
      let rejected ← try
        discard <| frameMorphismData harness trace source wrong
          { input with morphismFramed := framed }
        pure false
      catch _ => pure true
      unless rejected do throwError "a callable accepted a changed middle endpoint"
  logInfo "PASS: symbolic and owned whole callables retain complete endpoints and original data"

run_cmd liftTermElabM <| withoutErrToSorry do
  let state ← registryState
  let forms ← categoryNamed state "Bil"
  let zeroForm ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (0 : LinearMap.BilinMap ℤ ℤ ℤ))) none
  let multiplicationForm ← elabTermAndSynthesize (← `(
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
      (LinearMap.mul ℤ ℤ))) none
  let leftModule ← mkAppM
    ``LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.carrierObj #[zeroForm]
  let rightModule ← mkAppM
    ``LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.carrierObj #[multiplicationForm]
  unless ← withTransparency .all <| isDefEq leftModule rightModule do
    throwError "the structure control did not retain a common module carrier"
  if ← withTransparency .all <| isDefEq zeroForm multiplicationForm then
    throwError "the structure control did not select distinct complete forms"
  let context ← CategoryContext.ofNamed forms zeroForm
  let hom ← mkAppM ``CategoryTheory.CategoryStruct.id #[zeroForm]
  let input : Wire := {
    form := .canonicalMorphism forms
    payload := .computed hom (.opaque "coordinate-owner" 41 "original formed map")
    categoryContext := some context }
  for framed in #[false, true] do
    let rejected ← try
      discard <| frameMorphismData (← Harness.empty) (← Trace.new)
        zeroForm multiplicationForm { input with morphismFramed := framed } (some context)
      pure false
    catch error =>
      if Exception.interpretationKind error == .invalid then pure true else throw error
    unless rejected do throwError "callable framing identified distinct same-carrier forms"
  logInfo "PASS: complete selected structures remain distinct despite a shared carrier"

run_cmd liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats do
  let mut scope : Language.Scope := {}
  for (name, text) in #[("S", "ℤ in Rings"), ("M", "RegularModule(S)")] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "the independent coordinate context did not parse"
    scope := scope.insert name.toName parsed
  let trace ← Trace.new
  let .ok selectedSyntax := Parser.runParserCategory (← getEnv) `cas_term "M"
    | throwError "the selected coordinate did not parse"
  let selected ← (eval scope selectedSyntax).run { trace := some trace }
  let coordinate ← (carrierObject selected).run { trace := some trace }
  let selectedObject ← (semanticObject selected).run {}
  let coordinateObject ← (semanticObject coordinate).run {}
  let context ← (objectContext selected).run {}
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the coordinate has no set category"
  let harness ← Harness.empty
  let returned : Wire := {
    form := contextualForm state context (.diagrams sets)
    payload := .computed selectedObject (.opaque "coordinate-owner" 41 "actual module data")
    categoryContext := some context }
  harness.results.modify (·.insert selectedObject returned)
  let target ← realizeEndpoint harness trace "the actual selected coordinate" coordinateObject
  for numeral in #[3, 1] do
    let .element point _ ← (toElement (.nat numeral) coordinate).run { trace := some trace }
      | throwError "the selected coordinate did not admit its existing numeral"
    let raw ← realize harness trace "the original scalar-owned literal" point
    let .ok ("element", #[owner, _]) := ComputationalData.envelope raw.json
      | throwError "the literal lost its independently selected scalar owner"
    unless owner != target.json do
      throwError "the control did not distinguish the scalar owner and selected coordinate"
    let some (domain, _) := homEnds? (← inferType point)
      | throwError "the literal lost its generalized domain"
    let (data, dependencies) ← frameMorphismFragment harness trace domain coordinateObject raw
    let .ok ("typedMap", #[_, actualTarget, actualPoint]) := ComputationalData.envelope data.json
      | throwError "the coordinate point has no full endpoint framing"
    unless actualTarget == target.json && actualPoint == raw.json do
      throwError "the coordinate frame replaced the scalar owner or actual selected module"
    let retained : Wire := { raw with
      payload := (← combinedPayload point data (dependencies.push raw)) }
    unless retained.owner? == returned.owner? &&
        (retained.json.compress.splitOn "actual module data").length > 1 do
      throwError "the literal coordinate lost its actual returned module and owner"
  logInfo "PASS: scalar-owner literals retain the distinct complete coordinate and returned owner"
