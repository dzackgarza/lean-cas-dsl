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

/- The archived FullContextInterpretProduction diagnostic supplies the parser,
   complete preceding syntactic scope, six imports, and per-question budget.
   This invocation retains the full production identity and then evaluates the
   same prepared question without a leaf or proof discharge. It is a reader
   preflight, not the required complete structured-computation acceptance run. -/
run_cmd do
  let some input := (← IO.getEnv "CAS_READER_INPUT")
    | throwError "CAS_READER_INPUT is required"
  let some report := (← IO.getEnv "CAS_READER_REPORT")
    | throwError "CAS_READER_REPORT is required"
  if ← (System.FilePath.mk report).pathExists then
    throwError "refuse to overwrite an earlier reader report"
  let selected := #[
    "reconstructed_extensions_20261024.complete.lift.first_factor_sample_one",
    "reconstructed_extensions_20261024.complete.lift.first_factor_sample_two"]
  let mut scope : Language.Scope := {}
  let mut bindingCount := 0
  let mut observations : Array Json := #[]
  for item in itemsWithLocations (← IO.FS.readFile input) do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_item item.text input
      | throwError "the original input could not be parsed at line {item.line}"
    let (identity, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) =>
          (id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => ("", s.raw)
      | _ => ("", parsed)
    if selected.contains identity then
      IO.eprintln s!"production reader {input}:{item.line}: {identity}"
      let stages ← IO.mkRef (#[] : Array (String × Nat))
      let observation ← liftTermElabM <| withoutErrToSorry do
        let dispatches ← IO.mkRef (#[] : Array Json)
        let empty ← Realize.Harness.empty
        let harness : Realize.Harness :=
          { empty with computationOnly := true, dispatches := some dispatches }
        let questionIdentity ← IO.mkRef (none : Option (String × String))
        let phase ← IO.mkRef "interpretation"
        let interpretedHeartbeats ← IO.mkRef (none : Option Nat)
        let start ← IO.monoMsNow
        let heartbeats ← IO.getNumHeartbeats
        let outcome ← tryCatchRuntimeEx (withCurrHeartbeats do
          let question ← Realize.interpret scope statement (some stages)
          interpretedHeartbeats.set (some ((← IO.getNumHeartbeats) - heartbeats))
          questionIdentity.set (some question.identity)
          phase.set "evaluation"
          return (← Realize.evaluate harness question).toOutcome)
          (fun error => do
            if (← phase.get) == "evaluation" then
              return (← Realize.executionFailure error).toOutcome
            Outcome.ofException error)
        let totalHeartbeats := (← IO.getNumHeartbeats) - heartbeats
        harness.stop
        let question := (← questionIdentity.get).getD ("", "")
        return Json.mkObj [
          ("id", toJson identity), ("line", toJson item.line),
          ("source", toJson item.text), ("precedingBindings", toJson bindingCount),
          ("question", toJson question.1), ("proposition", toJson question.2),
          ("phase", toJson (← phase.get)),
          ("milliseconds", toJson ((← IO.monoMsNow) - start)),
          ("interpretationHeartbeatTicks", toJson (← interpretedHeartbeats.get)),
          ("totalHeartbeatTicks", toJson totalHeartbeats),
          ("maxHeartbeats", toJson ((← getOptions).getNat `maxHeartbeats 200000)),
          ("completedStages", toJson (← stages.get)),
          ("kind", toJson outcome.kind), ("detail", toJson outcome.detail),
          ("fails", toJson outcome.fails), ("dispatches", toJson (← dispatches.get))]
      observations := observations.push observation
      IO.FS.writeFile report (toJson observations).pretty
      IO.eprintln s!"completed production reader: {identity}"
    if let some (name, body) ← liftTermElabM (letBinding? statement) then
      scope := scope.insert name body
      bindingCount := bindingCount + 1
  unless observations.size == selected.size do
    throwError "not every selected original assertion was read"
