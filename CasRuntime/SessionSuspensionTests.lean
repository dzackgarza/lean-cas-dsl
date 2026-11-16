module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients

open Lean Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

/- A leaf that suspends asks the kernel to resolve a published operation it uses
(constitution C22, execution contract §6). The provider computes `a · 2` by suspending on the
addition `a + a`; the kernel dispatches that child, resumes the generator on the same
connection, and the resumed reply completes the original multiplication. -/
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
    let peer := root / "scripts/probes/kernel_suspension_peer.py"
    let registration := fun (operation : String) => Json.mkObj [("operation", operation),
      ("input", s!"{operation}#input"), ("backend", "peer")]
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul"].map registration))]
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "kernel-suspension-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path)
    try
      for (text, kind) in #[
          ("let a := 17 + 29 in ℤ", "holds"),
          ("let d := a · 2 in ℤ", "holds"),
          ("assert d = 92 in ℤ", "holds")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["op.rings.add", "op.rings.mul", "op.rings.add"] do
        throwError "the session dispatched {dispatched}"
    finally liftM (m := IO) session.close
  finally setEnv environment
