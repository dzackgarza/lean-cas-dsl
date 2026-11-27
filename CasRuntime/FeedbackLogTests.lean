module

import CasRuntime.Session
import CasCatalogue.TestSuite
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCatalogue.TestSuite
meta import LeanCategories.Catalogue

open Lean Meta Elab Command Term CasRuntime CasCompiler CasCatalogue CasCatalogue.Backend

run_cmd do
  let root ← IO.currentDir
  let contract ← packageDir contractPackage
  let python := (← IO.FS.realPath contract) / ".venv/bin/python"
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "peer"), ("command", python.toString),
      ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString])]]),
    ("registrations", .arr #[Json.mkObj [("operation", "meth.cardinality"),
      ("input", "obj.sets.fin"), ("backend", "peer")]])]
  IO.FS.createDirAll (root / ".tmp")
  let manifestPath := root / ".tmp" / "feedback-log-leaves.json"
  IO.FS.writeFile manifestPath manifest.compress
  CasCatalogue.Language.withSession (some manifestPath) true fun initial => do
    unless initial.kernel.rejected.isEmpty do
      throwError "the existing cardinality registration was rejected"
    let seeded ← CasCatalogue.Language.runStatement initial "let timingPrepared := Fin(3)"
    unless seeded.outcome.kind == "holds" && seeded.attempted && seeded.published &&
        seeded.session.source.context.entries.size > initial.source.context.entries.size &&
        seeded.session.setupMilliseconds > 0 do
      throwError "the continuation seed did not retain its measured definition: {seeded.outcome.detail}"
    let input := root / "tests/runtime/feedback_log.cas"
    let (rows, continuedSession) ← CasCatalogue.Language.runFile seeded.session input
    unless rows.map (·.id) == #["logging.direct", "logging.nested"] &&
        rows.all (fun row => row.kind == "holds" && row.attempted && row.published) do
      throwError "the complete finite-object log fixture failed: {toJson rows}"
    let events ← CasTools.ApplicationLog.readEvents initial.kernel.log.path
    let dataOf (event : Json) : Json := (event.getObjVal? "data").toOption.getD .null
    let isEvent (name : String) (event : Json) : Bool :=
      (event.getObjValAs? String "event").toOption == some name
    let starts := (events.filter (isEvent "computation.started")).map dataOf
    let timings := (events.filter (isEvent "computation.timing")).map dataOf
    let children := events.filter (isEvent "statement.child.started")
    let childFinishes := events.filter (isEvent "statement.child.finished")
    unless starts.size == 6 && timings.size == 6 && children.size == 2 && childFinishes.size == 2 do
      throwError "the complete fixture did not produce six roots and two executed children"
    for event in childFinishes do
      unless ((dataOf event).getObjValAs? String "kind").toOption == some "holds" &&
          ((dataOf event).getObjValAs? String "publication").toOption == some "pending enclosing cell" do
        throwError "the nested computation did not retain its pending enclosing publication"
    let #[fileStarted] := (events.filter (isEvent "file.started")).map dataOf
      | throwError "the continued file did not have exactly one native start"
    let .ok fileSetup := fileStarted.getObjValAs? Nat "sharedFileSetupMilliseconds"
      | throwError "the file did not retain its separate setup measurement"
    let mut expectedSetup := seeded.session.setupMilliseconds + fileSetup
    for start in starts, timing in timings, index in [:timings.size] do
      unless (start.getObjValAs? Nat "cumulativeSetupMilliseconds").toOption == some expectedSetup &&
          (timing.getObjValAs? Nat "setupMilliseconds").toOption == some expectedSetup &&
          (timing.getObjValAs? Nat "sharedFileSetupMilliseconds").toOption == some fileSetup do
        throwError "the seed/file continuation changed accumulated setup at root {index}"
      if index < 4 then
        let .ok elapsed := timing.getObjValAs? Nat "executionMilliseconds"
          | throwError "a retained file definition lost its measured interval"
        expectedSetup := expectedSetup + elapsed
    unless continuedSession.setupMilliseconds == expectedSetup do
      throwError "the returned session changed its accumulated setup"
    let .ok firstPreceding := (dataOf children[0]!).getObjValAs? Nat "precedingSetupMilliseconds"
      | throwError "the first child lost its preceding setup"
    let .ok secondPreceding := (dataOf children[1]!).getObjValAs? Nat "precedingSetupMilliseconds"
      | throwError "the later child lost its preceding setup"
    let .ok firstElapsed := (dataOf childFinishes[0]!).getObjValAs? Nat "milliseconds"
      | throwError "the child definition lost its measured duration"
    unless firstPreceding == 0 && secondPreceding >= firstElapsed do
      throwError "the later child did not inherit its retained definition cost"
    let later ← CasCatalogue.Language.runStatement continuedSession "assert implemented |timingPrepared|"
    unless later.outcome.kind == "holds" && later.attempted && later.published &&
        later.session.setupMilliseconds == expectedSetup do
      throwError "the later public use changed its retained result or setup: {later.outcome.detail}"
    let rejectedText := "let timingRejected :="
    let rejected ← try
        discard <| CasCatalogue.Language.runStatement later.session rejectedText
        pure false
      catch error =>
        unless (← error.toMessageData.toString).startsWith "not a statement of the language:" do
          throw error
        pure true
    unless rejected do
      throwError "the exact malformed public definition was accepted"
    let events ← CasTools.ApplicationLog.readEvents initial.kernel.log.path
    let #[failure] := (events.filter (isEvent "statement.parseFailed")).map dataOf
      | throwError "the exact parse rejection did not produce one completed native event"
    unless (failure.getObjValAs? String "source").toOption == some rejectedText &&
        (failure.getObjValAs? String "kind").toOption == some "invalid" &&
        (failure.getObjValAs? String "stratum").toOption == some "invalid" &&
        (failure.getObjValAs? Bool "fails").toOption == some true &&
        (failure.getObjValAs? Bool "attempted").toOption == some false &&
        (failure.getObjValAs? Bool "published").toOption == some false &&
        (failure.getObjValAs? Bool "retainsSetup").toOption == some false &&
        (failure.getObjValAs? Nat "cumulativeSetupMilliseconds").toOption == some expectedSetup do
      throwError "the public parse rejection changed its exact outcome or inherited setup"
