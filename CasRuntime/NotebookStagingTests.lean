module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems

namespace CasRuntime.NotebookStagingTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue CasCatalogue.Backend

private def statement (text : String) : TermElabM (TSyntax `cas_stmt) := do
  match Parser.runParserCategory (← getEnv) `cas_stmt text with
  | .ok parsed => pure ⟨parsed⟩
  | .error message => throwError "the original notebook statement did not parse: {message}"

-- A deferred result can share the child's actual node. The consuming
-- application's occurrence is nevertheless a separate committed receipt.
private def checkRoutineReceipts (snapshot : SessionSnapshot)
    (binding : ValueBinding) (expected : Array (String × String)) : TermElabM Unit := do
  let some node := snapshot.graph.find binding.value
    | throwError "routine test lost the retained node"
  let occurrences := (#[node.origin.occurrence] ++
    binding.applications.map (·.association.occurrence) ++
    binding.instantiations.map (·.association.occurrence)).toList.eraseDups
  let mut observed : Array (String × String) := #[]
  for occurrence in occurrences do
    let some receipt := snapshot.receipt occurrence | continue
    match receipt.association.producer with
    | .kernel => unless receipt.association.routines.isEmpty do
        throwError "kernel computation fabricated an engine routine"
    | .invocation dispatch _ requestId =>
      let .primitive identity := dispatch.selected
        | throwError "the arithmetic peer used an unexpected native export"
      let #[frame] := receipt.association.routines
        | throwError "an ordinary peer invocation lost its one actual received frame"
      unless frame.connection == dispatch.connection &&
          frame.occurrence == occurrence && frame.requestId == requestId do
        throwError "routine observation lost its actual request identity"
      let some #[routine] := frame.observations
        | throwError "the negotiated SDK invocation lost its actual entrypoint"
      let .ok role := routine.getObjValAs? String "role"
        | throwError "routine observation lost its role"
      let .ok name := routine.getObjValAs? String "qualified_name"
        | throwError "routine observation lost its callable identity"
      unless role == "entrypoint" do
        throwError "the arithmetic peer's actual entrypoint was replaced"
      observed := observed.push (identity.registration.operation, name)
  unless observed.size == expected.size &&
      expected.all (fun item => observed.contains item) do
    throwError "the committed binding lost an actual routine: {repr observed}"

-- The notebook stages separately parsed statements in one actual transaction.
-- Exercise that exact public runtime entrance in addition to the context-block
-- and actual worker controls. No alternate executor or host arithmetic is used.
run_cmd liftTermElabM do
  let env ← getEnv
  try
    let root ← IO.currentDir
    let contract ← packageDir contractPackage
    let python := (← IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_session_peer.py"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul"].map fun operation =>
        Json.mkObj [("operation", toJson operation), ("input", toJson (s!"{operation}#input")), ("backend", "peer")]))]
    IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp/notebook-staging-leaves.json"
    IO.FS.writeFile path manifest.compress
    let initial ← KernelSession.start (some path)
    try
      let parent ← initial.run (← statement "let outer := 17 + 29 in ℤ")
      unless parent.outcome.kind == "holds" && parent.published do
        throwError "the notebook parent failed: {parent.outcome.detail}"
      let before ← SessionSnapshot.current
      let callsBefore ← initial.kernel.dispatches.get
      let transaction ← CellTransaction.begin initial.kernel.ledger
      try
        let mut session := parent.session
        for text in #["let localSum := outer + 1 in ℤ",
            "let localProduct := localSum · 2 in ℤ",
            "assert localProduct = 94 in ℤ"] do
          let run ← session.run (← statement text) (some transaction)
          unless run.outcome.kind == "holds" && !run.published do
            throwError "the notebook staging failed at {text}: {run.outcome.kind}: {run.outcome.detail}"
          session := run.session
        unless (← SessionSnapshot.current).outputBatches.size == before.outputBatches.size do
          throwError "a staged statement independently published its cell"
        let calls ← initial.kernel.dispatches.get
        unless (calls.drop callsBefore.size).map (·.operation) ==
            #["op.rings.add", "op.rings.mul", "op.rings.add"] do
          throwError "the notebook replayed or lost an actual deferred arithmetic occurrence"
        let .ok snapshot ← transaction.commit
          | throwError "the staged notebook cell failed to commit"
        unless snapshot.outputBatches.size == before.outputBatches.size + 1 do
          throwError "the staged notebook did not publish exactly one output batch"
        let some entry := session.source.context.entries.back?
          | throwError "the notebook lost its product binding"
        let some value := session.value? entry.id
          | throwError "the notebook lost its retained product"
        let packet ← IO.ofExcept <| (snapshot.graph.packet? value).mapError IO.userError
        unless packet == some (toJson (94 : Int)) do
          throwError "the committed product changed its actual value"
        checkRoutineReceipts snapshot value
          #[("op.rings.mul", "multiply"), ("op.rings.add", "add")]
      finally discard <| transaction.abort
    finally initial.close
  finally setEnv env

end CasRuntime.NotebookStagingTests
