module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration

open Lean Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

/- The existing public integer statements and protocol peer now share an explicit cell.
No caller supplies an executor, runtime result or prepared request. This tests the session
seam; it does not replace the complete worker/Jupyter lifecycle or mathematical acceptance. -/
run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let python := (← liftM (m := IO) <| IO.FS.realPath contract) / ".venv/bin/python"
    let peer := root / "scripts/probes/kernel_session_peer.py"
    let manifest := Json.mkObj [
      ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
        ("args", .arr #[toJson peer.toString])]]),
      ("registrations", .arr (#["op.rings.add", "op.rings.mul"].map fun (operation : String) =>
        Json.mkObj [("operation", toJson operation), ("input", s!"{operation}#input"),
          ("backend", "peer")]))]
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let path := root / ".tmp" / "kernel-session-cell-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile path manifest.compress
    let initial ← KernelSession.start (some path) (computationOnly := false)
    try
      let parse : String → TermElabM (TSyntax `cas_stmt) := fun text => do
        match Parser.runParserCategory (← getEnv) `cas_stmt text with
        | .ok statement => pure ⟨statement⟩
        | .error error => throwError "the public cell statement did not parse: {error}"
      let run : KernelSession → CellTransaction → String → TermElabM StatementRun :=
        fun session transaction text => do
          withoutErrToSorry <| session.runIn transaction (← parse text)
      let holds : KernelSession → CellTransaction → String → TermElabM KernelSession :=
        fun session transaction text => do
          let step ← run session transaction text
          unless step.outcome.kind == "holds" do
            throwError "`{text}` is {step.outcome.kind}: {step.outcome.detail}"
          return step.session
      let unchanged : SessionSnapshot → TermElabM Unit := fun parent => do
        let current ← SessionSnapshot.current
        unless current.id == parent.id && current.graph.sameRevision parent.graph &&
            current.outputBatches.size == parent.outputBatches.size do
          throwError "a tentative source statement changed the committed runtime snapshot"

      let parent ← SessionSnapshot.current
      let aborted ← CellTransaction.begin initial.kernel.ledger
      let first ← holds initial aborted "let a := 17 + 29 in ℤ"
      let some firstEntry := first.source.context.entries.back?
        | throwError "the staged definition lost its source binding"
      let some firstValue := first.value? firstEntry.id
        | throwError "the staged definition lost its actual provider result"
      let staged ← aborted.view
      let some firstNode := staged.find firstValue.value
        | throwError "the actual provider result is absent from the active graph"
      unless (parent.graph.find firstValue.value).isNone &&
          (parent.receipt firstNode.origin.occurrence).isNone do
        throwError "the active provider result was published before cell commit"
      unchanged parent
      let copied ← holds first aborted "let copy := a"
      let some copyEntry := copied.source.context.entries.back?
        | throwError "the staged alias lost its source binding"
      let some copyValue := copied.value? copyEntry.id
        | throwError "the staged alias discarded its actual computed value"
      unless copyValue.value == firstValue.value &&
          copyValue.associationIds == firstValue.associationIds do
        throwError "the staged alias replaced its actual computed reference"
      -- This local hypothesis cannot discharge an assertion about observed data. Without
      -- staged producing provenance the native proof branch would incorrectly accept it.
      let assumed ← holds copied aborted "let h : copy = 47 in ℤ"
      let rejected ← run assumed aborted "assert copy = 47 in ℤ"
      unless rejected.outcome.kind == "wrong" do
        throwError "a staged computed value was discharged from source: \
          {rejected.outcome.kind} ({rejected.outcome.detail})"
      unless (← aborted.activeGraph).isNone do
        throwError "a wrong statement left its earlier cell results publishable"
      match ← aborted.commit with
      | .error .settled => pure ()
      | _ => throwError "an aborted public cell could commit its successful prefix"
      unchanged parent
      unless initial.source.context.entries.isEmpty &&
          (← initial.kernel.dispatches.get).map (·.operation) == #["op.rings.add"] do
        throwError "the aborted cell changed its parent source or repeated the computation"

      -- A deliberate new cell makes a new occurrence, then consumes that exact staged
      -- result in the original multiplication and question before one final commit.
      let transaction ← CellTransaction.begin initial.kernel.ledger
      let sum ← holds initial transaction "let a := 17 + 29 in ℤ"
      let some sumEntry := sum.source.context.entries.back?
        | throwError "the new cell lost its original sum binding"
      let some sumValue := sum.value? sumEntry.id
        | throwError "the new cell discarded its original sum value"
      unless sumValue.value != firstValue.value do
        throwError "a new execution recovered the aborted cell's value"
      let squared ← holds sum transaction "let b := a · a in ℤ"
      let some squareEntry := squared.source.context.entries.back?
        | throwError "the dependent definition lost its source binding"
      let some squareValue := squared.value? squareEntry.id
        | throwError "the dependent definition discarded its actual result"
      let candidate ← holds squared transaction "assert b = 2116 in ℤ"
      unchanged parent
      let graph ← transaction.view
      let some sumNode := graph.find sumValue.value
        | throwError "the completed cell lost its staged sum"
      let some squareNode := graph.find squareValue.value
        | throwError "the completed cell lost its staged square"
      let published ← match ← transaction.commit with
        | .ok snapshot => pure snapshot
        | .error failure => Execute.completionFailure failure
      unless published.id != parent.id &&
          published.outputBatches.size == parent.outputBatches.size + 1 &&
          (← SessionSnapshot.current).id == published.id do
        throwError "the complete public cell was not published as one runtime snapshot"
      let some batch := published.outputBatches.back?
        | throwError "the complete public cell lost its output batch"
      unless batch.transaction == transaction.id do
        throwError "the output batch belongs to another cell"
      for node in #[sumNode, squareNode] do
        let some receipt := published.receipt node.origin.occurrence
          | throwError "a committed public value lost its original completion receipt"
        unless receipt.snapshot == published.id && receipt.outputBatch == batch.id &&
            receipt.commit == batch.commit &&
            receipt.association.request.observation.sourceSnapshot.isSome do
          throwError "the cell published incomplete receipt or source observation data"
      unless (published.receipt firstNode.origin.occurrence).isNone &&
          (published.graph.find firstValue.value).isNone do
        throwError "a later commit resurrected an aborted result or receipt"
      unless (← initial.kernel.dispatches.get).map (·.operation) ==
          #["op.rings.add", "op.rings.add", "op.rings.mul"] do
        throwError "the shared cell repeated a staged computation"

      -- Existing standalone source-only statements retain their original snapshot behavior.
      let mut session := candidate
      for text in #["let RCell ∈ Rings", "let xCell ∈ RCell", "let hCell : xCell = xCell",
          "assert RCell ∈ Rings", "assert xCell ∈ RCell"] do
        let before ← SessionSnapshot.current
        let step ← withoutErrToSorry <| session.run (← parse text)
        unless step.outcome.kind == "holds" do
          throwError "the standalone source statement failed: {step.outcome.detail}"
        session := step.session
        unchanged before
      let continued ← withoutErrToSorry <| session.run (← parse "assert b = 2116 in ℤ")
      unless continued.outcome.kind == "holds" do
        throwError "the committed candidate lost its retained result: {continued.outcome.detail}"
      -- The original #cas_tests harness starts an independent source scope for every file.
      -- That scope must not start another kernel or discard the preceding committed receipts.
      let beforeScope ← SessionSnapshot.current
      let calls ← initial.kernel.dispatches.get
      let fresh ← continued.session.freshScope
      unless fresh.source.context.entries.isEmpty &&
          (fresh.value? sumEntry.id).isNone && (fresh.value? squareEntry.id).isNone &&
          fresh.kernel.ledger.owners.worker == initial.kernel.ledger.owners.worker &&
          fresh.kernel.manifestDigest == initial.kernel.manifestDigest &&
          fresh.kernel.profile.sha256 == initial.kernel.profile.sha256 &&
          fresh.computationOnly == continued.session.computationOnly do
        throwError "a fresh file scope copied names or replaced the startup kernel policy"
      let absent ← withoutErrToSorry <| fresh.run (← parse "assert b = 2116 in ℤ")
      unless absent.outcome.kind == "invalid" && absent.session.source.context.entries.isEmpty do
        throwError "a declaration escaped from its original file scope"
      let computing ← fresh.freshScope (computationOnly := true)
      unless computing.computationOnly &&
          computing.kernel.ledger.owners.worker == fresh.kernel.ledger.owners.worker &&
          computing.kernel.manifestDigest == fresh.kernel.manifestDigest &&
          computing.kernel.profile.sha256 == fresh.kernel.profile.sha256 &&
          (← initial.kernel.dispatches.get).size == calls.size do
        throwError "the explicit computing mode changed the frozen realization configuration"
      unchanged beforeScope
      unless (beforeScope.receipt sumNode.origin.occurrence).isSome &&
          (beforeScope.receipt squareNode.origin.occurrence).isSome do
        throwError "an independent file scope discarded the earlier committed results"
    finally liftM (m := IO) initial.close
  finally setEnv environment
