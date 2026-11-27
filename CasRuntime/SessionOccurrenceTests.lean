module

import CasRuntime.BindingIdentityTests
import CasCompiler.SourceTestSupport
import CasRuntime.Session
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts
public meta import Lean.Elab.Command
meta import CasRuntime.BindingIdentityTests
meta import CasCompiler.SourceTestSupport
meta import CasRuntime.Session
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.DegeneratePlaneLifts

open Lean Elab Command Term CasRuntime




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

namespace CasRuntime.SessionOccurrenceTests

open Lean Meta Elab Command Term CasCatalogue.Backend




run_cmd liftTermElabM do
  let root ← IO.currentDir
  let contract ← packageDir contractPackage
  let python := (← IO.FS.realPath contract) / ".venv/bin/python"
  let logDirectory : System.FilePath :=
    (← IO.getEnv "CAS_APPLICATION_LOG_DIR").getD "timing/application"
  let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
  let evidence := logDirectory / "controls" / nonce
  IO.FS.createDirAll evidence
  let registration := Json.mkObj [
    ("operation", "meth.cardinality"), ("input", "obj.sets.fin"), ("backend", "peer")]
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
      ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString])]]),
    ("registrations", .arr #[registration])]
  let path := evidence / "leaves.json"
  IO.FS.writeFile path manifest.compress
  let selected := ("meth.cardinality", "obj.sets.fin", "peer")


  BindingIdentityTests.observePublicOccurrences path "|Fin(7)|" #[selected, selected]
    "CategoryTheory.Discrete Cardinal.{0}"




run_cmd liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let logDirectory : System.FilePath :=
      (← IO.getEnv "CAS_APPLICATION_LOG_DIR").getD "timing/application"
    let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
    let evidence := logDirectory / "controls" / nonce
    IO.FS.createDirAll evidence
    let path := evidence / "empty-leaves.json"
    IO.FS.writeFile path
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let initial ← KernelSession.start (some path) (computationOnly := true)
    try
      let .ok definition := Parser.runParserCategory (← getEnv) `cas_stmt
          "let original := rev(3, 0)"
        | throwError "the original registered application did not parse"
      let produced ← withoutErrToSorry <| initial.run ⟨definition⟩
      unless produced.outcome matches .noImplementation _ do
        throwError "the original public application changed its unavailable implementation: {produced.outcome.detail}"
      unless produced.attempted && !produced.published &&
          (← initial.kernel.dispatches.get).isEmpty do
        throwError "the unavailable original application published or dispatched a runtime value"
      let session := produced.session
      let #[conclusion] := produced.conclusions
        | throwError "the original public application lost its retained conclusion"
      let #[application] := conclusion.terms
        | throwError "the original public conclusion changed its retained application"
      let selected := application.selections.toArray.filter fun (_, selection) =>
        match selection.reference with
        | some (.named (.registered (.inr entry) _)) =>
          entry.id.raw == "mor.sets.fin_rev" && selection.originalApplication.isSome
        | _ => false
      unless !selected.isEmpty do
        throwError "the public application lost its original selected map row"
      let #[entry] ← CasCompiler.SourceTest.authoredEntries
          session.source.context session.source.selections
        | throwError "the original public application changed its authored declaration"
      unless entry.userName == `original && entry.value.isSome &&
          (session.value? entry.id).isNone do
        throwError "the unavailable original application lost its source meaning or gained a value"
      let .ok continuation := Parser.runParserCategory (← getEnv) `cas_stmt
          "assert implemented original"
        | throwError "the original public application continuation did not parse"
      let .implemented reused ← session.source.readStatement ⟨continuation⟩
        | throwError "the public continuation changed its original statement"
      session.source.withTerm reused fun context selections expression => do
        let some binding := context.bindings.find? (·.id == entry.id)
          | throwError "the public continuation lost the original authored binding"
        unless expression.equal binding.expression do
          throwError "the public continuation reread a different application"
        let some body := (← binding.expression.fvarId!.getDecl).value?
          | throwError "the public continuation lost the original native definition"
        unless body.equal (← application.source.inContext context) do
          throwError "the public continuation changed the retained original application"
        unless CasCompiler.SourceSelectionScope.exactlyMatches Expr.equal selections
            (← session.source.selections.inContext context) do
          throwError "the public continuation replaced the original selection table"
        for (identity, originalSelection) in selected do
          let some retained := selections[identity]?
            | throwError "the public continuation lost an original application selection"
          let originalSelection ← originalSelection.mapM (fun source => source.inContext context)
          unless originalSelection.exactlyMatches Expr.equal retained do
            throwError "the public continuation changed the complete original selected application"
      let continued ← withoutErrToSorry <| session.run ⟨continuation⟩
      unless continued.outcome matches .noImplementation _ do
        throwError "the intact public continuation lost the original unavailable outcome"
      unless continued.attempted && !continued.published &&
          continued.session.source.context.exactlyMatches session.source.context &&
          (← session.kernel.dispatches.get).isEmpty do
        throwError "the intact public continuation changed or dispatched its original definition"
      for (identity, _) in selected do
        let brokenSource := { session.source with
          selections := session.source.selections.erase identity }
        let broken := { session with source := brokenSource }
        let before ← SessionSnapshot.current
        let codeCount := (← session.kernel.codes.get).size
        let dispatchCount := (← session.kernel.dispatches.get).size
        let failure : Option Exception ← withoutModifyingState do
          try
            discard <| broken.source.readStatement ⟨continuation⟩
            pure none
          catch error => pure (some error)
        let some failure := failure
          | throwError "the reader accepted the original application without its selected row"
        unless failure.toMessageData.hasTag (· == `CasCompiler.SourceReadM.missingSelection) do
          throw failure
        let failed ← withoutErrToSorry <| broken.run ⟨continuation⟩
        let .internal message := failed.outcome
          | throwError "the public continuation changed the original missing-selection reader error"
        unless message.endsWith "the source lost its retained typed selection" &&
            !failed.attempted && !failed.published && failed.conclusions.isEmpty &&
            failed.session.source.context.exactlyMatches brokenSource.context &&
            !failed.session.source.selections.contains identity &&
            failed.session.source.selections.size + 1 == session.source.selections.size &&
            (failed.session.value? entry.id).isNone do
          throwError "the missing original application selection entered execution or changed its scope"
        brokenSource.context.withOpen fun bindings => do
          let context ← CasCompiler.ContextTelescope.capture bindings
          unless CasCompiler.SourceSelectionScope.exactlyMatches Expr.equal
              (← brokenSource.selections.inContext context)
              (← failed.session.source.selections.inContext context) do
            throwError "reader rejection changed another original application selection"
        let after ← SessionSnapshot.current
        unless after.id == before.id && after.graph.sameRevision before.graph &&
            after.outputBatches.size == before.outputBatches.size &&
            (← session.kernel.codes.get).size == codeCount &&
            (← session.kernel.dispatches.get).size == dispatchCount do
          throwError "the reader-rejected original application changed graph, code, output or dispatch state"
    finally initial.close
  finally setEnv originalEnvironment


end CasRuntime.SessionOccurrenceTests
