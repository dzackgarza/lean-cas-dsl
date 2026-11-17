module

import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Elab Command Term CasRuntime

/- Two source selections of the same lift family are distinct computational occurrences.
The protocol peer returns distinct exports for actual calls. This checks that KernelSession
preserves those occurrences; the peer does not establish mathematical lift acceptance. -/
set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let root ← liftM (m := IO) IO.currentDir
    let contract ← liftM (m := IO) <| CasCatalogue.Backend.packageDir
      CasCatalogue.Backend.contractPackage
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let log := root / ".tmp" / "kernel-occurrence-peer.log"
    liftM (m := IO) <| IO.FS.writeFile log ""
    let operations : Array String := #["fun.commutative_rings.ring", "fun.bilin_module.forget",
      "lift.bilin_module.restrict#obj"]
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr (#[toJson (root / "scripts/probes/kernel_lift_peer.py").toString,
          toJson log.toString] ++ operations.map toJson))]]),
      ("registrations", .arr (operations.map fun operation => Json.mkObj [
        ("operation", toJson operation),
        ("input", toJson s!"{(operation.splitOn "#").head!}#input"), ("backend", "peer")]))]
    let path := root / ".tmp" / "kernel-occurrence-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      for (text, kind) in #[
          ("let Q := ℚ in CommutativeRings", "holds"),
          ("let Qring := view Q along «fun.commutative_rings.ring»()", "holds"),
          ("let scalarModule := RegularModule(Qring)", "holds"),
          ("let X := DegeneratePlane()", "holds"),
          ("let sourceModule := view X along «fun.bilin_module.forget»(ℚ, ℚ)", "holds"),
          ("let i0(t) := (2*t, -2*t) in scalarModule → sourceModule", "holds"),
          ("let first := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)", "holds"),
          ("let second := lift(X) along «lift.bilin_module.restrict»(ℚ, ℚ) with i0 using proof(CasCatalogue.Modules.Bilinear.Valued.DegeneratePlaneLifts.kernelInclusion_mono)", "holds"),
          ("let X1 := first.obj()", "holds"),
          ("let X2 := second.obj()", "holds"),
          ("let Xalias := X1", "holds"),
          ("let again := first.obj()", "holds")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
      let some first := session.source.context.entries.find? (·.userName == `X1)
        | throwError "the first selection was not declared"
      let some second := session.source.context.entries.find? (·.userName == `X2)
        | throwError "the second selection was not declared"
      let some firstValue := session.value? first.id
        | throwError "the first selection has no retained occurrence"
      let some secondValue := session.value? second.id
        | throwError "the second selection has no retained occurrence"
      unless firstValue.value != secondValue.value do
        throwError "independent selected lift declarations share one computational occurrence"
      for name in #[`Xalias, `again] do
        let some declaration := session.source.context.entries.find? (·.userName == name)
          | throwError "the repeated selected use was not declared"
        let some value := session.value? declaration.id
          | throwError "the repeated selected use has no retained occurrence"
        unless value.value == firstValue.value do
          throwError "a repeated use changed the selected lift's returned occurrence"
    finally liftM (m := IO) session.close
  finally setEnv environment
