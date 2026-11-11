module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality

open Lean Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

/- Public statements run from source text through the reader, the lowerer and the kernel
executor to a real protocol-v2 process. The provider supplies integer-ring traffic only; the
catalogue fixes every question. Reuse: the pinned SDK project and KernelSession. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let prepared ← liftM (m := IO) <| IO.Process.output {
      cmd := "/home/dzack/.local/bin/uv", args := #["sync", "--frozen", "--project", contract.toString] }
    unless prepared.exitCode == 0 do
      throwError "the pinned native SDK dependencies could not be provisioned: {prepared.stderr}"
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_session_peer.py"
    let registration := fun (operation : String) => Json.mkObj [("operation", operation),
      ("input", s!"{operation}#input"), ("backend", "peer")]
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul", "meth.cardinality"].map
        registration ++ #[Json.mkObj [("operation", "op.unpublished"),
          ("input", "op.unpublished#input"), ("backend", "peer")]]))]
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "kernel-session-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      unless session.kernel.rejected.size == 1 do
        throwError "an unpublished operation address was admitted as a registration"
      let expected : Array (String × String) := #[
        ("let a := 17 + 29 in ℤ", "holds"),
        ("assert a = 46 in ℤ", "holds"),
        ("assert a = 47 in ℤ", "wrong"),
        ("let b := a · a in ℤ", "holds"),
        ("assert b = 2116 in ℤ", "holds"),
        ("let d := a · 2 in ℤ", "holds"),
        ("assert d = 92 in ℤ", "holds"),
        ("let c := |Fin(3)|", "holds"),
        ("assert c = 3", "holds"),
        ("assert c = 4", "wrong"),
        ("assert implemented |Fin(2)|", "holds"),
        ("assert 2 + 2 = 4 in ℤ", "holds")]
      for (text, kind) in expected do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
      -- The retained sum is sent again as data. The deferred addition is a real dispatch.
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["op.rings.add", "op.rings.mul", "op.rings.mul", "op.rings.add",
          "meth.cardinality", "meth.cardinality"] do
        throwError "the session dispatched {dispatched}"
    finally liftM (m := IO) session.close
    -- With no manifest the same source has the same reading and no realization.
    setEnv environment
    let bare ← KernelSession.start none
    try
      let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt "let a := 17 + 29 in ℤ" with
        | .ok statement => pure statement
        | .error error => throwError "the statement did not parse: {error}"
      let run ← withoutErrToSorry <| bare.run ⟨statement⟩
      unless run.outcome.kind == "gap" do
        throwError "a statement with no installed leaf is {run.outcome.kind}, not a gap"
    finally liftM (m := IO) bare.close
  finally setEnv environment
