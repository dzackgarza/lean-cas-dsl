module

import CasTools.JsonGraph
public meta import Lean.Elab.Command
meta import CasTools.JsonGraph

open Lean Elab Command CasTools

run_cmd liftTermElabM do
  let lines := (← IO.FS.readFile "timing/logs/20261125T211917Z-slow.ayTPJv/application/32da0237-51a5-4e62-bca5-5a7ef3547a86.jsonl").splitOn "\n"
  let some line := lines[12]?
    | throwError "the recorded original request event is absent"
  let .ok event := Json.parse line | throwError "the recorded event is not JSON"
  let .ok original := event.getObjVal? "data" | throwError "the recorded event lost its data"
  let .ok restored := JsonGraph.decode original | throwError "the recorded event graph is invalid"
  let start ← IO.getNumHeartbeats
  let encoded := JsonGraph.encode restored
  let .ok nodes := encoded.getObjValAs? (Array Json) "nodes"
    | throwError "the reencoded event lost its node table"
  let finish ← IO.getNumHeartbeats
  IO.println s!"JSON_GRAPH_EVENT rawTicks={finish - start} nodes={nodes.size}"
  (← IO.getStdout).flush
  unless encoded.compress == original.compress do
    throwError "the codec changed the exact original graph on reencoding"
