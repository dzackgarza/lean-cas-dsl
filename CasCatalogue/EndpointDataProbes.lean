/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.ComputationalData
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

/-! Engineering framing checks at independently selected result positions.
The deliberately noncanonical endpoint data do not assert the answer, a map law,
or equality with the requested mathematical endpoints. -/

run_elab do
  let state ← registryState
  let some reversal := state.morphisms.find? (·.id.raw == "mor.sets.fin_rev")
    | throwError "the existing public finite-map declaration is absent"
  let formal ← mkAppM reversal.declaration #[mkNatLit 1]
  let some (source, target) := Language.homEnds? (← inferType formal)
    | throwError "the public finite map lost its complete declared endpoints"
  unless ← withTransparency .all <| isDefEq source target do
    throwError "the endpoint-role control requires definitionally equal formal endpoints"
  let node := fun (tag : String) (arguments : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]
  let finite := fun (size : Nat) => node "obj.sets.fin" #[toJson size]
  let first : ComputationalData.DataEndpointSlot := {
    index := 0, formal := source, data := { json := finite 2 } }
  let second : ComputationalData.DataEndpointSlot := {
    index := 1, formal := target, data := { json := finite 3 } }
  let graph := fun (pairs : Array (Nat × Nat)) => Json.arr (pairs.map fun (x, y) =>
    Json.arr #[toJson x, toJson y])
  let check := fun left right data =>
    ComputationalData.validateEndpointSlots formal left right data
  let complete : DataOwnership.Data := { json := graph #[(0, 1), (1, 2)] }
  if let .error message ← check first second complete then
    throwError "distinct returned endpoint roles were collapsed: {message}"
  for bad in #[graph #[(0, 1)], graph #[(0, 1), (1, 3)]] do
    let .error _ ← check first second { json := bad }
      | throwError "the actual endpoint inventory or output codec was bypassed"
  let .error _ ← check first { second with index := first.index } complete
    | throwError "one declared endpoint role accepted two different data occurrences"

  let same : ComputationalData.DataEndpointSlot := {
    second with data := first.data }
  let named : DataOwnership.Data := { json := node reversal.id.raw #[toJson (2 : Nat)] }
  if let .error message ← check first same named then
    throwError "a named callable was checked at the canonical requested endpoints: {message}"
  if let .error message ← check first { same with index := first.index } named then
    throwError "one repeated complete endpoint role was rejected: {message}"
  let .error _ ← check first same { json := node reversal.id.raw #[toJson (3 : Nat)] }
    | throwError "a named callable changed its actual complete endpoint interface"

  let opaque := fun (token : String) (session : Nat) => Id.run do
    let json := node "opaqueData" #[toJson token]
    return ({ json, ownership := DataOwnership.capture json ("endpoint-probe", session) }
      : DataOwnership.Data)
  if let .error message ← check first second (opaque "whole map" 1) then
    throwError "a complete opaque callable was restricted to graph data: {message}"
  let ownedFirst : ComputationalData.DataEndpointSlot := {
    first with data := opaque "same spelling" 2 }
  let ownedSecond : ComputationalData.DataEndpointSlot := {
    second with data := opaque "same spelling" 3 }
  let map := opaque "owned whole map" 4
  let .ok packet := DataOwnership.Data.ctor "typedMap"
      #[ownedFirst.data, ownedSecond.data, map]
    | throwError "the complete owned callable control has malformed ownership"
  if let .error message ← check ownedFirst ownedSecond packet then
    throwError "distinct owned endpoint positions were merged: {message}"
  let .ok swapped := DataOwnership.Data.ctor "typedMap"
      #[ownedSecond.data, ownedFirst.data, map]
    | throwError "the ownership-negative control has malformed coverage"
  let .error _ ← check ownedFirst ownedSecond swapped
    | throwError "equal opaque bytes replaced the exact endpoint suppliers"
  logInfo "PASS: endpoint positions, actual graph/named/opaque interfaces, and exact suppliers"
