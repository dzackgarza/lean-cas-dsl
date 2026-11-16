module

import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Elab Command Term CasRuntime

/- RX-LIFT's first selected lift (tests/acceptance/proposals/independent-extension-reconstruction-
20261024/completion/rx-lift-prescribed-stages.cas) through the public path with no leaf. The lift
is a record of delayed fields: defining it dispatches nothing, and its fields are then projected
from that same retained record. A computation that needs a leaf is a gap, and so is a
projection whose dependent type needs such a value; reading holds. Functional work may use the
heartbeats it needs (constitution C21). -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let mut session ← KernelSession.start none
    try
      for (text, kind) in #[
          ("let Q := ℚ in CommutativeRings", "holds"),
          ("let Qring := view Q along «fun.commutative_rings.ring»()", "gap"),
          ("let scalarModule := RegularModule(Qring)", "gap"),
          ("let X := DegeneratePlane()", "holds"),
          ("let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)", "gap"),
          ("let i0(t) := (2*t, -2*t) in scalarModule → sourceModule", "holds"),
          ("let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)", "holds"),
          -- The lift's fields depend on the module scalarModule, whose computation has no
          -- leaf here: projecting them is that gap.
          ("let X1 := first.obj()", "gap"),
          ("let i1 := first.hom()", "gap")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
    finally liftM (m := IO) session.close
  finally setEnv environment

/- The same lift with leaves. A field of a selected lift is the lift's published computation
(LiftEntry.computation), so `first.obj()` is resolved to the leaf registered at the contract's
`<lift>#obj` port (api/wire-examples.md, "Prescribed subobject lifts") and is not reduced in Lean
(constitution C22). The request carries the lift's evidence parameters (ℚ, ℚ). A real
protocol-v2 process answers; its log records each request. -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let prepared ← liftM (m := IO) <| IO.Process.output {
      cmd := "/home/dzack/.local/bin/uv", args := #["sync", "--frozen", "--project", contract.toString] }
    unless prepared.exitCode == 0 do
      throwError "the pinned native SDK dependencies could not be provisioned: {prepared.stderr}"
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let log := root / ".tmp" / "kernel-lift-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operations : Array String := #["fun.commutative_rings.ring", "fun.bilin_module.forget",
      "lift.bilin_module.restrict#obj", "lift.bilin_module.restrict#hom",
      "lift.bilin_module.restrict#forward", "lift.bilin_module.restrict#backward"]
    let input := fun (operation : String) => s!"{(operation.splitOn "#").head!}#input"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr (#[toJson (root / "scripts/probes/kernel_lift_peer.py").toString,
          toJson log.toString] ++ operations.map toJson))]]),
      ("registrations", .arr (operations.map fun (operation : String) => Json.mkObj [
        ("operation", toJson operation), ("input", toJson (input operation)),
        ("backend", "peer")]))]
    let path := root / ".tmp" / "kernel-lift-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      unless session.kernel.rejected.isEmpty do
        throwError "a lift port registration was rejected: {session.kernel.rejected}"
      for text in #[
          "let Q := ℚ in CommutativeRings",
          "let Qring := view Q along «fun.commutative_rings.ring»()",
          "let scalarModule := RegularModule(Qring)",
          "let X := DegeneratePlane()",
          "let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)",
          "let i0(t) := (2*t, -2*t) in scalarModule → sourceModule",
          "let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)",
          "let X1 := first.obj()"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not holds"
        session := run.session
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched.contains "lift.bilin_module.restrict#obj" do
        throwError "the lift's object was not dispatched to its port: {dispatched}"
      let requests := ((← liftM (m := IO) <| IO.FS.readFile log).splitOn "\n").filter (!·.isEmpty)
      let some line := requests.find? (·.startsWith "{\"op\": \"lift.bilin_module.restrict#obj\"")
        | throwError "the peer received no lift request: {requests}"
      let .ok request := Json.parse line | throwError "the peer log is malformed: {line}"
      let .ok parameters := (request.getObjValD "context").getObjValAs? (Array Json) "parameters"
        | throwError "the lift request has no parameters: {line}"
      -- Every non-proof argument of the evidence `forgetMonoLift (R) [CommRing R] (W)
      -- [AddCommGroup W] [Module R W]`, in order, as for every published family: ℚ at R and W.
      let rationals := Json.mkObj [("args", .arr #[]), ("ctor", "obj.sets.rationals")]
      unless parameters.size == 5 && parameters[0]! == rationals && parameters[2]! == rationals do
        throwError "the lift request does not carry the evidence parameters (ℚ, ℚ): {line}"
    finally liftM (m := IO) session.close
  finally setEnv environment
