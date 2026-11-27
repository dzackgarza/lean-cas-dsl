module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.Semirings
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.Semirings
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
meta import LeanCategories.Catalogue.Semantics.Foundation.PowerSets

open Lean Elab Command Term CasRuntime CasCompiler CasCatalogue.Backend

/- A question that is a predicate is computed by the leaf that implements the predicate
(constitution C22). The provider answers primality of a natural number; the kernel decides
membership in the subset of primes, and its negation, from that Boolean answer. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_predicate_peer.py"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString])]]),
      ("registrations", .arr #[Json.mkObj [("operation", "mor.sets.nat_is_prime"),
        ("input", "mor.sets.nat_is_prime"), ("backend", "peer")]])]
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "kernel-predicate-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let mut session ← KernelSession.start (some path) (computationOnly := true)
    try
      for (text, kind) in #[
          ("let primes := {n ∈ ℕ | n.is_prime()}", "holds"),
          ("assert 7 ∈ primes", "holds"),
          ("assert 9 ∉ primes", "holds"),
          ("assert 9 ∈ primes", "wrong"),
          ("assert (9 ∈ primes) = false", "holds"),
          ("assert (7 ∈ primes) = true", "holds")] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the statement did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == kind do
          throwError "`{text}` is {run.outcome.kind} ({run.outcome.detail}), not {kind}"
        session := run.session
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless dispatched == #["mor.sets.nat_is_prime", "mor.sets.nat_is_prime",
          "mor.sets.nat_is_prime", "mor.sets.nat_is_prime", "mor.sets.nat_is_prime"] do
        throwError "the session dispatched {dispatched}"
    finally liftM (m := IO) session.close
  finally setEnv environment
