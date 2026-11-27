module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations

open Lean Meta Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

-- The independently checked ring-multiplication plan must reach one of its exact
-- published prerequisites. The existing protocol peer implements neither operation:
-- it supplies no mathematical answer and must return its ordinary unsupported outcome.
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← packageDir contractPackage
    let root ← IO.currentDir
    let python := (← IO.FS.realPath contract) / ".venv/bin/python"
    let operations := #[FunctorId.ringsMultiplicative.raw, "op.monoids.mul"]
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "prerequisite-peer"),
        ("command", toJson python.toString),
        ("args", .arr #[toJson (root / "scripts/probes/protocol_v2_peer.py").toString])]]),
      ("registrations", .arr (operations.map fun operation => Json.mkObj [
        ("operation", toJson operation), ("input", toJson s!"{operation}#input"),
        ("backend", "prerequisite-peer")]))]
    let profile := Json.mkObj [("format", "cas-realization-profile/1"),
      ("id", "selected-source-prerequisites"), ("default", "all"),
      ("rules", .arr #[Json.mkObj [
        ("target", Json.mkObj [("kind", "operation"), ("id", "op.rings.mul")]),
        ("primitive_registrations", Json.mkObj [("mode", "only"), ("entries", .arr #[])]),
        ("derivations", Json.mkObj [("mode", "only"),
          ("ids", .arr #["derive.rings.mul.monoid"])])]])]
    IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp/checked-derivation-prerequisites.json"
    IO.FS.writeFile path manifest.compress
    let session ← KernelSession.start (some path) (computationOnly := true)
      (profile := some profile)
    try
      unless session.kernel.rejected.isEmpty do
        throwError "the checked derivation lost its published prerequisite registrations"
      let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt
          "let product := 17 · 2 in ℤ"
        | throwError "the original multiplication statement did not parse"
      let run ← withoutErrToSorry <| session.run ⟨statement⟩
      let dispatched := (← session.kernel.dispatches.get).map (·.operation)
      unless !dispatched.isEmpty && dispatched.all operations.contains do
        throwError "the source program did not reach its exact prerequisite: {dispatched}; \
          {run.outcome.detail}"
      unless run.outcome.stratum? == some "noImplementation" do
        throwError "the absent prerequisite changed failure stratum: {run.outcome.kind}; \
          {run.outcome.detail}"
      let some result := run.session.source.context.entries.back?
        | throwError "the source program lost its original result declaration"
      unless (run.session.value? result.id).isNone do
        throwError "the kernel computed a result for the unsupported prerequisite"
    finally session.close
  finally setEnv environment
