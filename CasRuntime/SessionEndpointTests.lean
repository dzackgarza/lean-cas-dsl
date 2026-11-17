module

import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneFactorization

open Lean Elab Command Term CasRuntime

-- The original RX-LIFT cone followed by its public functor action. Its endpoint must refer
-- to that selected arrow occurrence. The peer checks references, not mathematical laws.
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← liftM (m := IO) IO.currentDir
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let log := root / ".tmp" / "kernel-endpoint-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operation := "fun.bilin_module.forget#map"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", toJson #[ (root / "scripts/probes/kernel_lift_peer.py").toString,
          log.toString, operation])]]),
      ("registrations", .arr #[Json.mkObj [("operation", toJson operation),
        ("input", "fun.bilin_module.forget#input"), ("backend", "peer")]])]
    let path := root / ".tmp" / "kernel-endpoint-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      for text in #["let cone := degenerate_plane_cone()",
          "let underlyingCone := map cone along «fun.bilin_module.forget»(ℚ, ℚ)"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      let some cone := session.source.context.entries.find? (·.userName == `cone)
        | throwError "the selected cone was not declared"
      let some mapped := session.source.context.entries.find? (·.userName == `underlyingCone)
        | throwError "the mapped cone was not declared"
      let some coneValue := session.value? cone.id
        | throwError "the cone has no retained occurrence"
      let some mappedValue := session.value? mapped.id
        | throwError "the mapped cone has no retained occurrence"
      let graph := (← SessionSnapshot.current).graph
      let .ok (some application) := graph.applicationOrigin mappedValue
        | throwError "the mapped cone lost its actual application"
      let #[some domain, some _, some arrow] := application.arguments
        | throwError "the map changed its argument interface"
      unless arrow.value == coneValue.value do
        throwError "the map replaced its selected arrow"
      let some node := graph.find domain.value
        | throwError "the endpoint is outside the retained graph"
      let .container endpoint := node.payload.data
        | throwError "the endpoint lost its selected arrow interface"
      let #[slot] := endpoint.slots
        | throwError "the endpoint does not retain its defining arrow"
      unless slot.binding.value == coneValue.value do
        throwError "the endpoint refers to a different arrow occurrence"
    finally liftM (m := IO) session.close
  finally setEnv environment
