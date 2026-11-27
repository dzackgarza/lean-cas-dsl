module

import CasRuntime.CallablePacket
public meta import Lean.Elab.Command
meta import CasRuntime.CallablePacket

open Lean CasRuntime

-- Complete released callable framing is checked independently of mathematical correctness.
-- No callable is applied, and no native function is reconstructed from a graph.
run_cmd Lean.Elab.Command.liftTermElabM do
  let domain := #[toJson (0 : Nat), toJson (1 : Nat)]
  let target := #[toJson (3 : Nat), toJson (4 : Nat)]
  let graph := Json.arr #[Json.arr #[domain[1]!, target[0]!],
    Json.arr #[domain[0]!, target[1]!]]
  let explicit := Json.mkObj [("ctor", toJson "finiteGraph"),
    ("args", Json.arr #[Json.arr domain.reverse, graph])]
  for packet in #[graph, explicit] do
    let .ok admitted := CallablePacket.finite packet (some domain) (some target)
      | throwError "complete original-domain callable data were rejected"
    unless admitted.value == packet do
      throwError "callable admission rewrote the original graph or inventory order"
  let .ok admitted := CallablePacket.finite explicit none none
    | throwError "an explicit complete actual inventory was discarded"
  unless admitted.value == explicit do
    throwError "explicit callable framing replaced the supplied map"
  let incomplete := Json.arr #[Json.arr #[domain[0]!, target[0]!]]
  let repeated := Json.arr #[Json.arr #[domain[0]!, target[0]!],
    Json.arr #[domain[0]!, target[1]!]]
  let foreign := Json.arr #[Json.arr #[domain[0]!, target[0]!],
    Json.arr #[toJson (2 : Nat), target[1]!]]
  let outOfRange := Json.arr #[Json.arr #[domain[0]!, target[0]!],
    Json.arr #[domain[1]!, toJson (5 : Nat)]]
  let wrongInventory := Json.mkObj [("ctor", toJson "finiteGraph"),
    ("args", Json.arr #[Json.arr #[domain[0]!], incomplete])]
  let duplicateInventory := Json.mkObj [("ctor", toJson "finiteGraph"),
    ("args", Json.arr #[Json.arr #[domain[0]!, domain[0]!], repeated])]
  for packet in #[incomplete, repeated, foreign, outOfRange, wrongInventory,
      duplicateInventory, Json.arr #[Json.arr #[domain[0]!]], toJson (7 : Nat)] do
    if (CallablePacket.finite packet (some domain) (some target)).isOk then
      throwError "an incomplete or malformed callable acquired a function interface"
  if (CallablePacket.finite graph none none).isOk then
    throwError "an unframed graph invented its complete computational domain"
  let object := Json.mkObj [("ctor", toJson "finiteData"),
    ("args", Json.arr #[Json.mkObj [("ctor", toJson "retainedEndpoint"),
      ("args", Json.arr #[])], Json.arr domain])]
  unless callableEndpointInventory object == .ok (some domain) do
    throwError "an original finiteData inventory was not retained"
  let duplicateObject := Json.mkObj [("ctor", toJson "finiteData"),
    ("args", Json.arr #[toJson "actual endpoint", Json.arr #[domain[0]!, domain[0]!]])]
  if (callableEndpointInventory duplicateObject).isOk then
    throwError "a repeated object inventory was admitted"

  let node := fun (tag : String) (args : Array Json) =>
    Json.mkObj [("ctor", toJson tag), ("args", .arr args)]
  let endpoint := node "retainedEndpoint" #[]
  let retained := (ScopedReference.scope 0).encode
  let symbolic := #[
    node "identity" #[endpoint, endpoint],
    node "zero" #[endpoint, endpoint],
    node "compose" #[retained, retained],
    node "map" #[node "functor.actual" #[], retained],
    node "morphism.actual" #[retained],
    node "cellComponent" #["cell.actual", .arr #[retained], retained, toJson false],
    node "constructedCellComponent" #[.arr #["constructor.actual"],
      node "cellComponent" #["cell.actual", .arr #[], retained, toJson true]],
    node "cartesianMap" #["functor.reindex", .arr #[retained], retained],
    node "presentation" #["comparison.actual", .arr #[retained], toJson false],
    node "constructionLeg" #["limit.actual", retained, retained, toJson (0 : Nat)]]
  for packet in symbolic do
    let .ok admitted := CallablePacket.symbolic packet
      | throwError "a complete symbolic callable lost its released framing"
    unless admitted.value == packet do
      throwError "symbolic framing rewrote the supplied descriptor or original references"
  for packet in #[
      node "identity" #[endpoint],
      node "compose" #[retained, retained, retained],
      node "cartesianMap" #["", .arr #[], retained],
      node "presentation" #["comparison.actual", retained, toJson false],
      node "constructionLeg" #["limit.actual", retained, retained],
      retained, node "opaqueData" #["not-an-admitted-export"]] do
    if (CallablePacket.symbolic packet).isOk then
      throwError "malformed symbolic framing acquired a callable packet"
  let owned := node "opaqueData" #["original-token"]
  for value in #[retained, (ScopedReference.input #[.index 2]).encode,
      (ScopedReference.result 0).encode, owned] do
    let .ok framed := CallablePacket.retained value
      | throwError "released retained callable framing was rejected"
    let complete := node "typedMap" #[endpoint, endpoint, value]
    let .ok mapped := framed.withMap complete
      | throwError "complete typedMap lost its original retained callable field"
    unless mapped.value == complete do
      throwError "retained callable framing rewrote the complete original map"
    let wrapped := node "valueData" #[complete]
    let .ok framed := mapped.inline wrapped
      | throwError "an original complete inline wrapper was discarded"
    unless framed.value == wrapped do
      throwError "inline framing rewrote the original complete packet"
  for value in #[node "scopeRef" #[toJson (-1 : Int)], node "resultRef" #[],
      node "opaqueData" #[""], node "identity" #[endpoint, endpoint],
      node "valueData" #[owned]] do
    if (CallablePacket.retained value).isOk then
      throwError "malformed retained framing acquired a callable packet"
