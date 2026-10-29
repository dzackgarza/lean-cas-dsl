module

import CasCatalogue.Realize
meta import CasCatalogue.Realize
import CasCatalogue.FileItems
meta import CasCatalogue.FileItems
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
meta import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
meta import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
meta import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests

open Lean Elab Command Term CasCatalogue CasCatalogue.Language

/- Maintained invocation of the original ten-question first-stage diagnostic.
All preceding binding syntax comes from the original file. One loaded harness
is shared across the selected questions in original order. CAS_READER_THROUGH
selects an inclusive prefix: "first" or an exact ID; absent means all ten.
A later question therefore retains the earlier selected execution history.

Each question has one unchanged 200000-heartbeat budget shared by production
prepare and evaluatePrepared. Audit export is omitted. Phase timing includes
failed phases; execution timing is absent when preparation did not finish.
Report serialization and writing are measured separately after each question,
with completed write durations emitted as rx_lift_report_write JSON events on
stderr. Recording that duration inside the same write would require a rewrite.
This driver makes no acceptance claim and changes no assertion. -/
run_cmd do
  let some input := (← IO.getEnv "CAS_READER_INPUT")
    | throwError "CAS_READER_INPUT is required"
  let some report := (← IO.getEnv "CAS_READER_REPORT")
    | throwError "CAS_READER_REPORT is required"
  let some manifest := (← IO.getEnv "CAS_LEAVES")
    | throwError "CAS_LEAVES must name the actual independent diagnostic manifest"
  unless ← (System.FilePath.mk manifest).pathExists do
    throwError "the actual independent diagnostic manifest does not exist: {manifest}"
  if ← (System.FilePath.mk report).pathExists then
    throwError "refuse to overwrite an earlier runtime report"
  let allSelected := #[
    "reconstructed_extensions_20261024.complete.lift.first_inverse_on_carrier",
    "reconstructed_extensions_20261024.complete.lift.first_inverse_on_scalar",
    "reconstructed_extensions_20261024.complete.lift.first_defining_map",
    "reconstructed_extensions_20261024.complete.lift.first_backward_action",
    "reconstructed_extensions_20261024.complete.lift.first_nonidentity_coordinate",
    "reconstructed_extensions_20261024.complete.lift.first_full_pairing",
    "reconstructed_extensions_20261024.complete.lift.first_whole_factorization",
    "reconstructed_extensions_20261024.complete.lift.first_factor_comparison",
    "reconstructed_extensions_20261024.complete.lift.first_factor_sample_one",
    "reconstructed_extensions_20261024.complete.lift.first_factor_sample_two"]
  let through? ← IO.getEnv "CAS_READER_THROUGH"
  let selected ← match through? with
    | none => pure allSelected
    | some "first" => pure (allSelected.extract 0 1)
    | some identity =>
        let some index := allSelected.findIdx? (· == identity)
          | throwError "CAS_READER_THROUGH is not an original first-stage question: {identity}"
        pure (allSelected.extract 0 (index + 1))
  let dispatches ← IO.mkRef (#[] : Array Json)
  let loaded ← liftCoreM (Realize.Harness.load (some (System.FilePath.mk manifest)))
  let harness : Realize.Harness :=
    { loaded with computationOnly := true, dispatches := some dispatches }
  let writeReport (rows : Array Json) : CommandElabM Unit := do
    let started ← IO.monoMsNow
    IO.FS.writeFile report (Json.mkObj [
      ("purpose", toJson "first-stage execution diagnostic; not acceptance"),
      ("acceptanceClaim", toJson false), ("auditExport", toJson "omitted"),
      ("source", toJson input), ("manifest", toJson manifest),
      ("bindingHandling", toJson "original preceding syntax retained; read at each use"),
      ("computationOnly", toJson true),
      ("session", toJson "one shared harness across the original selected execution prefix"),
      ("requestedThrough", toJson through?),
      ("reportWritingTiming", toJson "rx_lift_report_write events on stderr; serialization and file write"),
      ("rejectedRegistrations", toJson loaded.rejected),
      ("selected", toJson selected), ("observations", Json.arr rows)]).pretty
    let elapsed := (← IO.monoMsNow) - started
    IO.eprintln (Json.mkObj [
      ("event", toJson "rx_lift_report_write"), ("report", toJson report),
      ("observations", toJson rows.size), ("milliseconds", toJson elapsed)]).compress
  let mut scope : Language.Scope := {}
  let mut bindingCount := 0
  let mut observations : Array Json := #[]
  try
    writeReport #[]
    for item in itemsWithLocations (← IO.FS.readFile input) do
      let .ok parsed := Parser.runParserCategory (← getEnv) `cas_item item.text input
        | throwError "the original input could not be parsed at line {item.line}"
      let (identity, statement) := match parsed with
        | `(cas_item| test $id:ident $_:str : $s:cas_stmt) =>
            (id.getId.toString, s.raw)
        | `(cas_item| $s:cas_stmt) => ("", s.raw)
        | _ => ("", parsed)
      if selected.contains identity then
        unless selected[observations.size]? == some identity do
          throwError "the selected original first-stage questions changed order"
        if observations.isEmpty && bindingCount != 22 then
          throwError "the first original first-stage question requires all 22 preceding bindings"
        IO.eprintln s!"first-stage runtime {input}:{item.line}: {identity}"
        let stages ← IO.mkRef (#[] : Array (String × Nat))
        let dispatchStart := (← dispatches.get).size
        let observation ← liftTermElabM <| withoutErrToSorry do
          unless maxHeartbeats.get (← getOptions) == 200000 do
            throwError "the original question budget changed"
          let phase ← IO.mkRef "preparation"
          let preparationHeartbeats ← IO.mkRef (none : Option Nat)
          let executionHeartbeats ← IO.mkRef (none : Option Nat)
          let preparationMilliseconds ← IO.mkRef (none : Option Nat)
          let executionMilliseconds ← IO.mkRef (none : Option Nat)
          let traceNodes ← IO.mkRef (none : Option Nat)
          let start ← IO.monoMsNow
          let heartbeats ← IO.getNumHeartbeats
          let outcome ← tryCatchRuntimeEx (withCurrHeartbeats do
            let preparationStart ← IO.monoMsNow
            let preparationTicks ← IO.getNumHeartbeats
            let question ← try
                Realize.prepare scope statement (some stages)
              finally
                preparationMilliseconds.set (some ((← IO.monoMsNow) - preparationStart))
                preparationHeartbeats.set (some ((← IO.getNumHeartbeats) - preparationTicks))
            traceNodes.set (some question.trace.size)
            phase.set "evaluation"
            let executionStart ← IO.monoMsNow
            let executionTicks ← IO.getNumHeartbeats
            try
              return (← Realize.evaluatePrepared harness question).toOutcome
            finally
              executionMilliseconds.set (some ((← IO.monoMsNow) - executionStart))
              executionHeartbeats.set (some ((← IO.getNumHeartbeats) - executionTicks)))
            (fun error => do
              if (← phase.get) == "evaluation" then
                return (← Realize.executionFailure error).toOutcome
              Outcome.ofException error)
          let totalHeartbeats := (← IO.getNumHeartbeats) - heartbeats
          let elapsed := (← IO.monoMsNow) - start
          let calls ← dispatches.get
          return Json.mkObj [
            ("mode", toJson "first-stage-runtime-diagnostic"),
            ("acceptanceClaim", toJson false), ("auditExport", toJson "omitted"),
            ("input", toJson input), ("manifest", toJson manifest),
            ("id", toJson identity), ("line", toJson item.line),
            ("source", toJson item.text), ("precedingBindings", toJson bindingCount),
            ("phase", toJson (← phase.get)), ("traceNodes", toJson (← traceNodes.get)),
            ("milliseconds", toJson elapsed),
            ("preparationMilliseconds", toJson (← preparationMilliseconds.get)),
            ("executionMilliseconds", toJson (← executionMilliseconds.get)),
            ("preparationHeartbeatTicks", toJson (← preparationHeartbeats.get)),
            ("executionHeartbeatTicks", toJson (← executionHeartbeats.get)),
            ("totalHeartbeatTicks", toJson totalHeartbeats),
            ("maxHeartbeats", toJson (maxHeartbeats.get (← getOptions))),
            ("completedStages", toJson (← stages.get)),
            ("kind", toJson outcome.kind), ("detail", toJson outcome.detail),
            ("fails", toJson outcome.fails),
            ("dispatches", toJson (calls.extract dispatchStart calls.size))]
        observations := observations.push observation
        writeReport observations
        IO.eprintln s!"completed first-stage runtime: {identity}"
        if observations.size == selected.size then break
      if let some (name, body) ← liftTermElabM (letBinding? statement) then
        scope := scope.insert name body
        bindingCount := bindingCount + 1
    unless observations.size == selected.size do
      throwError "not every selected original first-stage assertion was read"
  finally
    harness.stop
