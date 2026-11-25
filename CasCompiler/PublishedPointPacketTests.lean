module

import CasContract.Port
public meta import Lean.Elab.Command
meta import CasContract.Port

namespace CasCompiler.PublishedPointPacketTests

open Lean CasCatalogue.Backend

-- Pure packet framing preserves all seven actual fields in both the original action and
-- a later complete-map continuation. It supplies no source or realization authority.
run_cmd do
  let node := fun (tag : String) (arguments : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", .arr arguments)]
  let reference := fun (index : Nat) => node "scopeRef" #[toJson index]
  let functor := "fun.protocol.parameterized"
  let parameters := #[toJson false, node "category" #[toJson "cat.protocol", toJson #[7]]]
  let source := node "object" #[toJson "source"]
  let target := node "object" #[toJson "target"]
  let domain := node "object" #[toJson "domain"]
  let point := reference 8
  let action := node functor parameters
  let original : PointInvocation := {
    operation := functor ++ "#map"
    parameters
    arrow := node "map" #[action, TypedMap.encode {
      source := node "object" #[toJson "before"]
      target := node "object" #[toJson "after"]
      callable := reference 1 }]
    domain
    source
    target
    argument := point }
  let accepted := fun packet => PointInvocation.decodeFunctorMap functor packet
  let .ok decoded := accepted original.encode | throwError "the original map action was rejected"
  unless decoded.encode == original.encode do throwError "the original action changed its fields"
  for data in #[node "finiteGraph" #[toJson #[0, 1], toJson #[#[0, 2], #[1, 3]]],
      node "identity" #[source, target],
      node "compose" #[reference 2, reference 3],
      node "opaqueData" #[toJson "actual-original-owner-token"]] do
    let actual := TypedMap.encode { source, target, callable := data }
    let continued := { original with arrow := actual }
    let decoded ← match accepted continued.encode with
      | .ok value => pure value
      | .error reason => throwError "an actual returned map was rejected by native framing: {reason}"
    unless decoded.encode == continued.encode && decoded.arrow == actual do
      throwError "the actual returned map or one of its seven fields was reconstructed"
    for changed in #[{ continued with operation := "fun.other#map" },
        { continued with arrow := TypedMap.encode { source := target, target := source, callable := data } },
        { continued with arrow := node "typedMap" #[source, target] }] do
      if (accepted changed.encode).isOk then
        throwError "changed map operation, endpoints or missing data passed framing"
  let wrongAction := node functor (parameters.set! 0 (toJson (0 : Nat)))
  let changedOriginal := { original with arrow := node "map" #[wrongAction,
    TypedMap.encode { source, target, callable := point }] }
  if (accepted changedOriginal.encode).isOk then
    throwError "a Boolean action parameter was replaced with numeric data"

-- A recursive action continuation retains the exact nested identity and all actual
-- parameter slots, independently from the opaque or portable representation of its map.
run_cmd do
  let node := fun (tag : String) (arguments : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", .arr arguments)]
  let reference := fun (index : Nat) => node "scopeRef" #[toJson index]
  let identity := Json.mkObj [("constructorMap", .arr #[toJson "ctor.arrow",
    Json.mkObj [("constructorMap", .arr #[toJson "ctor.core",
      Json.mkObj [("classifierForget", toJson "cls.protocol")]])]])]
  let .ok address := actionAddress identity | throwError "the canonical recursive action failed"
  let action := node "constructorMap" #[toJson "ctor.arrow",
    node "constructorMap" #[toJson "ctor.core",
      node "classifierForget" #[toJson "cls.protocol",
        .arr #[toJson false, reference 2]]]]
  let source := reference 3
  let target := reference 4
  let actual := TypedMap.encode {
    source
    target
    callable := node "finiteGraph" #[toJson #[0], toJson #[#[0, 1]]] }
  let continued : PointInvocation := {
    operation := address ++ "#map"
    parameters := #[action]
    arrow := actual
    domain := reference 5
    source
    target
    argument := reference 6 }
  let accepted := fun packet => PointInvocation.decodeActionMap address packet
  let decoded ← match accepted continued.encode with
    | .ok value => pure value
    | .error reason => throwError "the recursive action rejected its actual returned map: {reason}"
  unless decoded.encode == continued.encode do
    throwError "the recursive action changed a native continuation field"
  let original := { continued with arrow := node "map" #[action, TypedMap.encode {
    source := reference 0
    target := reference 1
    callable := reference 7 }] }
  unless (accepted original.encode).isOk do throwError "the recursive original map was rejected"
  let changed := node "constructorMap" #[toJson "ctor.arrow",
    node "constructorMap" #[toJson "ctor.product",
      node "classifierForget" #[toJson "cls.protocol",
        .arr #[toJson false, reference 2]]]]
  for bad in #[{ continued with parameters := #[changed] },
      { continued with parameters := #[] }, { continued with parameters := #[action, action] },
      { continued with arrow := TypedMap.encode { source := target, target := source, callable := .arr #[] } }] do
    if (accepted bad.encode).isOk then
      throwError "a recursive action lost its exact identity, parameters or endpoints"

-- The already released creation envelope keeps each original source diagram and target
-- packet unchanged. Framing introduces no alternative owner, proof, or operation selector.
run_cmd do
  let node := fun (tag : String) (arguments : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", .arr arguments)]
  let reference := fun (index : Nat) => node "scopeRef" #[toJson index]
  let target := node "cone" #[reference 1, TypedMap.encode {
    source := reference 1, target := reference 2, callable := reference 3 }]
  let source := node "cospan" #[reference 4, reference 5]
  let created : CreatedCone := { lift := "lift.protocol", diagram := source, targetCone := target }
  let nested : CreatedCone := {
    lift := "lift.protocol.outer"
    diagram := node "cospan" #[reference 6, reference 7]
    targetCone := created.encode }
  for original in #[created, nested] do
    let .ok decoded := CreatedCone.decode original.encode
      | throwError "the complete original creation packet was rejected"
    unless decoded.encode == original.encode && decoded.diagram == original.diagram &&
        decoded.targetCone == original.targetCone do
      throwError "creation framing changed an original source diagram or target result"
  for packet in #[node "createdCone" #[toJson "", source, target],
      node "createdCone" #[toJson false, source, target],
      node "createdCone" #[toJson created.lift, target],
      node "createdCone" #[toJson created.lift, source, target, target],
      Json.mkObj [("ctor", toJson "createdCone"),
        ("args", .arr #[toJson created.lift, source, target]), ("owner", toJson "invented")],
      Json.mkObj [("ctor", toJson "createdCone"),
        ("args", .arr #[toJson created.lift, source, target]), ("proof", toJson true)]] do
    if (CreatedCone.decode packet).isOk then
      throwError "creation framing admitted missing data or new owner/proof authority"

end CasCompiler.PublishedPointPacketTests

