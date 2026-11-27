module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations

open Lean Meta Elab Command Term CasRuntime CasCompiler CasCatalogue.Backend

-- Start from an ordinary source operation. Every fault belongs to the original complete
-- control frame, so no first child, resume, result or receipt may escape its rejection.
-- The framing peer supplies no mathematical result and is not a mathematical oracle.
run_cmd liftTermElabM do
  let contract ← liftM (m := IO) <| packageDir contractPackage
  let root ← liftM (m := IO) IO.currentDir
  let peer := root / "scripts/probes/kernel_control_admission_peer.py"
  let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
  for mode in #["duplicate_capture", "bad_export_capture", "bad_later_call",
      "bad_later_graph", "bad_template_scope", "undeclared_opaque"] do
    let environment ← getEnv
    try
      let traffic := root / ".tmp" / s!"control-admission-{mode}.jsonl"
      let manifestPath := root / ".tmp" / s!"control-admission-{mode}.json"
      let registration := fun (operation : String) => Json.mkObj [
        ("operation", toJson operation), ("input", toJson s!"{operation}#input"),
        ("backend", "control-admission-peer")]
      let manifest := Json.mkObj [
        ("backends", .arr #[Json.mkObj [("name", "control-admission-peer"),
          ("command", toJson python.toString), ("args", .arr #[toJson peer.toString,
            toJson mode, toJson traffic.toString])]]),
        ("registrations", .arr (#["op.rings.mul", "op.rings.add"].map registration))]
      liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
      liftM (m := IO) <| IO.FS.writeFile traffic ""
      liftM (m := IO) <| IO.FS.writeFile manifestPath manifest.compress
      let session ← KernelSession.start (some manifestPath)
      try
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt
            "let d := 17 · 2 in ℤ" with
          | .ok statement => pure statement
          | .error error => throwError "the control-admission statement did not parse: {error}"
        let before ← SessionSnapshot.current
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "malformed" do
          throwError "{mode}: the complete control was {run.outcome.kind}: {run.outcome.detail}"
        let after ← SessionSnapshot.current
        unless before.id == after.id && before.graph.sameRevision after.graph &&
            before.outputBatches.size == after.outputBatches.size do
          throwError "a malformed whole control published a result or output batch"
        let dispatched := (← session.kernel.dispatches.get).map (·.operation)
        unless dispatched == #["op.rings.mul"] do
          throwError "a child was dispatched before whole-control admission: {dispatched}"
        let lines := (← liftM (m := IO) <| IO.FS.readFile traffic).splitOn "\n"
        let mut operations : Array String := #[]
        for line in lines do
          if line.isEmpty then continue
          let .ok frame := Json.parse line
            | throwError "the independent traffic log contains a malformed frame"
          let .ok operation := frame.getObjValAs? String "op"
            | throwError "the independent traffic log omitted its operation"
          if operation != "$cas.discard" then operations := operations.push operation
        unless operations == #["op.rings.mul"] do
          throwError "a malformed control sent a child or resume frame: {operations}"
      finally liftM (m := IO) session.close
    finally setEnv environment

-- Distinct original addresses may carry the same node and must remain distinct captures.
-- A nonempty valid export table is accepted; nothing is materialized by control admission.
run_cmd liftTermElabM <| liftM (m := MetaM) do
  let environment ← getEnv
  try
    let contract ← packageDir contractPackage
    let root ← IO.currentDir
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    discard <| SessionSnapshot.initialize owners
    let traffic := root / ".tmp" / "control-admission-valid.jsonl"
    IO.FS.createDirAll (root / ".tmp")
    IO.FS.writeFile traffic ""
    let .ok wire ← FramedConnection.start owners "control-admission-peer" {
        cmd := ((← IO.FS.realPath contract) / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/kernel_control_admission_peer.py").toString,
          "valid", traffic.toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the valid control peer did not negotiate"
    try
      let transaction ← CellTransaction.begin ledger
      try
        let program ← owners.identities.fresh .program
        let occurrence ← ledger.allocate
        let context ← ContextTelescope.capture #[]
        let source ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
        let role ← SourceLayout.ofTerm (← context.close source)
        let original ← transaction.stage
          { program, occurrence, role, parameters := #[] } (.closure program #[])
        let graph ← transaction.view
        let identity : DispatchIdentity := {
          manifestDigest := "control-admission", profileDigest := "control-admission"
          registration := { operation := "op.rings.mul", input := "op.rings.mul#input",
            backend := "control-admission-peer" } }
        let .ok reservation ← transaction.reserve occurrence identity wire.connection #[original]
          | throwError "the valid control could not reserve"
        let positions : Array InputPosition := #[
          { path := #[.field "first"], binding := original },
          { path := #[.field "second"], binding := original }]
        let scope ← RequestScope.issue ledger reservation graph #[] positions #[]
        let .ok (.suspended _ _ captures calls exports) ← wire.invokeControlBefore ledger
            transaction reservation scope (Json.mkObj [("first", .null), ("second", .null)]) 5000
          | throwError "the valid original captures or nonempty export table were rejected"
        unless captures == #[(ScopedReference.input #[.field "first"]).encode,
            (ScopedReference.input #[.field "second"]).encode] && calls.size == 1 do
          throwError "the control changed its ordered original capture addresses"
        let declared ← ReplyExport.parseControl scope reservation graph scope.wireId exports
        let #[exported] := declared
          | throwError "the valid control lost its original export"
        unless exported.owner == wire.connection.generation && exported.captures.size == 2 &&
            exported.captures.all (fun value => value.value == original.value &&
              value.associationIds == original.associationIds) do
          throwError "export capture admission merged or replaced original reference roles"
        unless graph.sameRevision (← transaction.view) &&
            ((← SessionSnapshot.current).receipt occurrence).isNone do
          throwError "control admission staged or published a joint result"
        scope.retire
      finally discard <| transaction.abort
    finally wire.close
  finally setEnv environment
