/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/-! Engineering controls for the distinct point-data and whole-callable roles.
The arbitrary packets establish no mathematical answer or live session. -/
run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term "23 in ℚ"
    | throwError "the point-interface control did not parse"
  let trace ← CasCatalogue.Trace.new
  let .element formal _ ← (eval {} parsed).run { trace := some trace }
    | throwError "the point-interface control did not retain its original point"
  let some (source, target) := homEnds? (← inferType formal)
    | throwError "the original point has no complete endpoints"
  let some category := (← registryState).categories.find? (·.id == CategoryId.sets)
    | throwError "the point-interface control has no registered data category"
  let owned := fun token session => DataOwnership.Data.capture
    (Backend.ComputationalValue.encode (.opaque token)) ("framing-owner", session)
  let domain ← scopedNode "finiteData"
    #[owned "actual singleton domain" 7, { json := Json.arr #[toJson "supplied key"] }]
  let endpoint := owned "actual point target" 11
  let point := owned "actual returned point" 13
  let selected ← pointDataInterfaceAt source target domain endpoint
  let wire : Wire := {
    form := .canonicalMorphism category, payload := .computed formal (.scoped point)
    morphismFramed := true, callableObserved := true, pointDataInterface := selected }
  let harness ← Harness.empty
  let (argument, _) ← frameMorphismFragment harness trace source target wire
  unless argument == point do
    throwError "an ordinary point invocation changed the actual point data"
  let (framed, _) ← frameMorphismFragment harness trace source target wire (pointAsMap := true)
  let expectedGraph := DataOwnership.Data.array
    #[DataOwnership.Data.array #[{ json := toJson "supplied key" }, point]]
  let expected ← scopedNode "typedMap" #[domain, endpoint,
    ← scopedNode "finiteGraph" #[{ json := Json.arr #[toJson "supplied key"] }, expectedGraph]]
  unless framed == expected do
    throwError "map-position framing lost the supplied key, endpoints, actual point or occurrence owners"
  discard <| checkedFragment framed.validate
  let retained ← checkedFragment (framed.project
    #[.field "args", .index 2, .field "args", .index 1, .index 0, .index 1])
  unless retained == point do
    throwError "the framed map did not retain the original point's exact supplier"
  let opaqueKey := owned "actual returned point" 19
  let opaqueInventory := DataOwnership.Data.array #[opaqueKey]
  let opaqueDomain ← scopedNode "finiteData"
    #[owned "actual singleton domain" 7, opaqueInventory]
  let opaqueWire := { wire with pointDataInterface := (← pointDataInterfaceAt
    source target opaqueDomain endpoint) }
  let (opaqueFramed, _) ← frameMorphismFragment harness trace source target opaqueWire
    (pointAsMap := true)
  let opaqueExpected ← scopedNode "typedMap" #[opaqueDomain, endpoint,
    ← scopedNode "finiteGraph" #[opaqueInventory,
      DataOwnership.Data.array #[DataOwnership.Data.array #[opaqueKey, point]]]]
  unless opaqueKey.json == point.json && opaqueKey.ownership != point.ownership &&
      opaqueFramed == opaqueExpected do
    throwError "identical inventory-key and returned-point bytes conflated their independent suppliers"
  discard <| checkedFragment opaqueFramed.validate
  let graphKey ← checkedFragment (opaqueFramed.project
    #[.field "args", .index 2, .field "args", .index 1, .index 0, .index 0])
  let graphValue ← checkedFragment (opaqueFramed.project
    #[.field "args", .index 2, .field "args", .index 1, .index 0, .index 1])
  unless graphKey == opaqueKey && graphValue == point do
    throwError "the finite graph did not retain each exact key and value occurrence owner"
  let callable := { wire with pointDataInterface := none }
  let (ordinary, _) ← frameMorphismFragment harness trace source target callable (pointAsMap := true)
  unless ordinary == point && !sameActionOperand wire callable do
    throwError "identical callable bytes silently acquired the point-data role"
  let missing := { wire with pointDataInterface := some {
    domain := source, target, domainData := owned "domain without inventory" 7,
    targetData := endpoint } }
  let refused ← try
      discard <| frameMorphismFragment harness trace source target missing (pointAsMap := true)
      pure false
    catch error => pure (Exception.stratum? error == some .noImplementation)
  unless refused do throwError "the point's formal domain fabricated a missing computational inventory"
  let changed := { wire with pointDataInterface := some {
    domain := source, target := source, domainData := domain, targetData := endpoint } }
  let refused ← try
      discard <| frameMorphismFragment harness trace source target changed (pointAsMap := true)
      pure false
    catch _ => pure true
  unless refused do throwError "map-position framing accepted a changed complete point target"
  logInfo "PASS: completed point roles, exact endpoint/key framing, independent equal-byte key/value owners, missing-inventory and changed-target refusals"
