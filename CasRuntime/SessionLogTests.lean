module

import CasRuntime.Session
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

namespace CasRuntime.SessionLogTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue CasCatalogue.Backend

run_cmd do
  let environment ← getEnv
  try
    for peer in #[true, false] do
      setEnv environment
      let preparationStarted ← IO.monoMsNow
      let input : System.FilePath := "tests/acceptance/sets.cas"
      let contents ← IO.FS.readFile input
      let original ← liftCoreM <| SourceFile.parse input.toString contents
      let selected : Array (TSyntax `cas_stmt) := original.items.filterMap fun item =>
        match item with
        | `(cas_item| test $id:ident $_:str : $statement:cas_stmt) =>
          if id.getId == `sets.implemented.card_fin then some statement else none
        | _ => none
      let #[statement] := selected
        | throwError "the original sets file lost its one sets.implemented.card_fin assertion"
      unless (statement.raw.reprint.getD "").trimAscii.toString ==
          "assert implemented |Fin(3)|" do
        throwError "the phase control changed the original cardinality assertion"
      let root ← IO.currentDir
      let registration := Json.mkObj [
        ("operation", "meth.cardinality"), ("input", "obj.sets.fin"), ("backend", "peer")]
      let backends : Array Json ← if peer then do
          let contract ← packageDir contractPackage
          let python := (← IO.FS.realPath contract) / ".venv/bin/python"
          pure #[Json.mkObj [("name", "peer"), ("command", python.toString),
            ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString])]]
        else pure #[]
      let manifest := Json.mkObj [("backends", .arr backends),
        ("registrations", .arr (if peer then #[registration] else #[]))]
      let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
      let path := root / ".tmp" / s!"session-phases-{nonce}.json"
      IO.FS.createDirAll (root / ".tmp")
      IO.FS.writeFile path manifest.compress
      let session ← liftTermElabM <| KernelSession.start (some path)
        (computationOnly := true) (preparationStarted? := some preparationStarted)
      try
        unless session.kernel.rejected.isEmpty do
          throwError "the phase control rejected its original cardinality registration"
        let run ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
          original.withContext (session.run statement)
        unless run.attempted && (if peer then run.outcome.kind == "holds"
            else run.outcome.stratum? == some "noImplementation") do
          throwError "the original cardinality phase control is {run.outcome.kind}: {run.outcome.detail}"
        let calls ← session.kernel.dispatches.get
        if peer then
          let #[actual] := calls
            | throwError "the original cardinality assertion lost its one dispatch"
          unless actual.operation == "meth.cardinality" && actual.input == "obj.sets.fin" &&
              actual.backend == "peer" do
            throwError "the original cardinality assertion changed its actual registration"
        else
          unless calls.isEmpty do
            throwError "the empty manifest dispatched an implementation"
        unless (← IO.FS.readFile input) == contents do
          throwError "the original acceptance source changed during the phase control"
        let events ← CasTools.ApplicationLog.readEvents session.kernel.log.path
        let dataOf (event : Json) : Json := (event.getObjVal? "data").toOption.getD .null
        let isEvent (name : String) (event : Json) : Bool :=
          (event.getObjValAs? String "event").toOption == some name
        let sequenceOf (event : Json) : Nat :=
          (event.getObjValAs? Nat "sequence").toOption.getD 0
        let timeOf (event : Json) : Nat :=
          (event.getObjValAs? Nat "monotonicMilliseconds").toOption.getD 0
        let hasParent (sequence : Nat) (event : Json) : Bool :=
          ((event.getObjValAs? (Array Nat) "parents").toOption.getD #[]).contains sequence
        let mut previousTime := 0
        for event in events, sequence in [:events.size] do
          unless (event.getObjValAs? Nat "schema").toOption == some 2 &&
              (event.getObjValAs? String "session").toOption == some session.kernel.log.session &&
              (event.getObjValAs? Nat "sequence").toOption == some sequence do
            throwError "the phase log changed its stream schema, session or event identity"
          let .ok parents := event.getObjValAs? (Array Nat) "parents"
            | throwError "a phase event lost its causal parents"
          let .ok timestamp := event.getObjValAs? Nat "monotonicMilliseconds"
            | throwError "a phase event lost its measured monotonic timestamp"
          unless parents.all (· < sequence) && timestamp ≥ previousTime do
            throwError "the phase log references a later parent or moves its clock backwards"
          previousTime := timestamp
        let #[started] := events.filter (isEvent "statement.started")
          | throwError "the phase control did not enter exactly one original statement"
        let statementSequence := sequenceOf started
        let entered := events.filter (hasParent statementSequence)
        let #[terminal] := entered.filter (isEvent "statement.finished")
          | throwError "the original statement lost its one completed outcome"
        unless (events.filter (isEvent "statement.interrupted")).isEmpty &&
            (dataOf started).getObjVal? "source" == .ok (toJson (statement.raw.reprint.getD "")) &&
            (dataOf started).getObjVal? "position" == .ok (SourceSnapshot.spanJson
              ⟨input.toString, statement.raw.getPos?, statement.raw.getTailPos?⟩) do
          throwError "the phase control interrupted or changed its original source and position"
        let #[setup] := events.filter (isEvent "session.prepared")
          | throwError "the phase control lost its actual session preparation"
        let .ok setupMilliseconds := (dataOf setup).getObjValAs? Nat "milliseconds"
          | throwError "the session preparation lost its measured duration"
        unless ((dataOf setup).getObjValAs? Nat "startedMonotonicMilliseconds").toOption ==
              some preparationStarted &&
            preparationStarted + setupMilliseconds ≤ timeOf setup &&
            sequenceOf setup < statementSequence &&
            ((dataOf started).getObjValAs? Nat "cumulativeSetupMilliseconds").toOption ==
              some session.setupMilliseconds do
          throwError "the statement lost its actual setup and retained fixture timing"
        for (field, expected) in #[
            ("kind", toJson run.outcome.kind), ("stratum", toJson run.outcome.stratum?),
            ("detail", toJson run.outcome.detail), ("attempted", toJson run.attempted),
            ("published", toJson run.published)] do
          unless (dataOf terminal).getObjVal? field == .ok expected do
            throwError "the terminal phase changed its actual outcome field {field}"
        unless ((dataOf terminal).getObjValAs? Nat "milliseconds").isOk do
          throwError "the terminal phase lost its measured statement duration"
        let #[reading] := entered.filter (isEvent "statement.read")
          | throwError "the original statement lost its one selected reading"
        let .ok conclusions := (dataOf reading).getObjValAs? (Array Json) "conclusions"
          | throwError "the original statement lost its typed source conclusions"
        unless ((dataOf reading).getObjValAs? String "kind").toOption == some "implementation" &&
            !conclusions.isEmpty do
          throwError "the phase log changed the original implementation assertion's reading"
        for event in events do
          let .ok name := event.getObjValAs? String "event"
            | throwError "a phase row lost its event name"
          if #["statement.read", "statement.finished", "lower.phase.started", "lower.phase.finished",
              "request.prepared", "request.execute", "request.dispatched", "dispatch",
              "reply.admission.started", "reply.admitted", "realization.missing"].contains name ||
              name.startsWith "request.prepare." || name.startsWith "execution.response." then
            unless hasParent statementSequence event do
              throwError "the phase {name} is detached from its original statement"
        let mut lowerStack : Array Json := #[]
        let mut lowerPairs : Array (Json × Json) := #[]
        for event in entered do
          if isEvent "lower.phase.started" event then
            lowerStack := lowerStack.push event
          else if isEvent "lower.phase.finished" event then
            let some before := lowerStack.back?
              | throwError "a lower phase completed without entering its original work"
            for field in #["phase", "program", "transaction", "start"] do
              let .ok expected := (dataOf before).getObjVal? field
                | throwError "a lower phase lost its original {field}"
              unless (dataOf event).getObjVal? field == .ok expected do
                throwError "a nested lower phase changed its original {field}"
            unless sequenceOf before < sequenceOf event && timeOf before ≤ timeOf event do
              throwError "a lower phase completed before its actual start"
            lowerStack := lowerStack.pop
            lowerPairs := lowerPairs.push (before, event)
        unless lowerStack.isEmpty && !lowerPairs.isEmpty do
          throwError "the original statement lost a complete lower phase"
        let anchorName := if peer then "request.dispatched" else "realization.missing"
        let #[anchor] := entered.filter (isEvent anchorName)
          | throwError "the original statement lost its one actual {anchorName} event"
        unless ((dataOf anchor).getObjValAs? String "operation").toOption ==
            some "meth.cardinality" do
          throwError "the actual dispatch or gap changed its registered operation address"
        let causes := entered.filter fun event =>
          isEvent "request.execute" event && hasParent (sequenceOf event) anchor
        let some execution := causes.back?
          | throwError "the dispatch or missing realization lost its causal prepared request"
        let .ok native := (dataOf execution).getObjVal? "native"
          | throwError "the actual execution lost its native request"
        let .ok request := native.getObjVal? "request"
          | throwError "the actual execution lost its complete prepared request"
        let .ok program := request.getObjVal? "program"
          | throwError "the actual request lost its program identity"
        let .ok occurrence := request.getObjVal? "occurrence"
          | throwError "the actual request lost its occurrence identity"
        let prepared := entered.filter fun event =>
          let request := ((dataOf event).getObjVal? "native").bind (·.getObjVal? "request")
          isEvent "request.prepared" event &&
            (request.bind (·.getObjVal? "program")).toOption == some program &&
            (request.bind (·.getObjVal? "occurrence")).toOption == some occurrence
        let #[prepared] := prepared
          | throwError "the executed occurrence lost its one original preparation"
        let .ok originalNative := (dataOf prepared).getObjVal? "native"
          | throwError "the prepared occurrence lost its complete native descriptor"
        unless CasTools.JsonGraph.encode originalNative == CasTools.JsonGraph.encode native do
          throwError "the execution changed its original prepared descriptor"
        let selectedPhase (name : String) : CommandElabM Json := do
          let #[event] := entered.filter fun event => isEvent name event &&
              (dataOf event).getObjVal? "occurrence" == .ok occurrence
            | throwError "the actual request lost its one {name} boundary"
          return event
        let preparation ← selectedPhase "request.prepare.source.started"
        unless (dataOf preparation).getObjVal? "program" == .ok program &&
            sequenceOf prepared < sequenceOf execution && sequenceOf execution < sequenceOf anchor do
          throwError "the original request changed its preparation or execution order"
        let some lower := lowerPairs.find? fun (before, after) =>
            (dataOf before).getObjVal? "program" == .ok program &&
              sequenceOf reading < sequenceOf before && sequenceOf after < sequenceOf preparation
          | throwError "the actual request lost its completed lowering before preparation"
        let mut phases := #[(started, reading), lower, (preparation, prepared)]
        if peer then
          unless (dataOf anchor).getObjVal? "registration" == .ok registration &&
              (dataOf anchor).getObjVal? "program" == .ok program &&
              (dataOf anchor).getObjVal? "occurrence" == .ok occurrence do
            throwError "the dispatch phase changed its actual registration or request identity"
          let dispatched ← selectedPhase "dispatch"
          let reply ← selectedPhase "reply.admission.started"
          let admitted ← selectedPhase "reply.admitted"
          let admitStart ← selectedPhase "execution.response.admit.started"
          let admitFinish ← selectedPhase "execution.response.admit.completed"
          let bindStart ← selectedPhase "execution.response.retain.started"
          let bindFinish ← selectedPhase "execution.response.retain.completed"
          unless sequenceOf anchor < sequenceOf dispatched && sequenceOf dispatched < sequenceOf reply &&
              sequenceOf reply < sequenceOf admitted && sequenceOf admitted < sequenceOf admitStart &&
              (entered.filter (isEvent "realization.missing")).isEmpty do
            throwError "the supported dispatch lost its actual reply and admission order"
          let .ok transaction := (dataOf anchor).getObjVal? "transaction"
            | throwError "the actual dispatch lost its transaction identity"
          for event in #[admitStart, admitFinish, bindStart, bindFinish] do
            unless (dataOf event).getObjVal? "program" == .ok program &&
                (dataOf event).getObjVal? "transaction" == .ok transaction do
              throwError "the actual reply changed its request program or transaction"
          phases := phases ++ #[(anchor, reply), (admitStart, admitFinish), (bindStart, bindFinish)]
        else
          let .ok forms := (dataOf anchor).getObjValAs? (Array String) "forms"
            | throwError "the missing realization lost its exact input address"
          unless forms.contains "obj.sets.fin" &&
              (run.outcome.detail.splitOn "meth.cardinality").length > 1 do
            throwError "the terminal no-implementation outcome lost its registered address"
          for name in #["request.dispatched", "dispatch", "reply.admission.started", "reply.admitted",
              "execution.response.admit.started", "execution.response.admit.completed",
              "execution.response.retain.started", "execution.response.retain.completed"] do
            unless (entered.filter fun event => isEvent name event &&
                (dataOf event).getObjVal? "occurrence" == .ok occurrence).isEmpty do
              throwError "the missing occurrence fabricated a {name} phase"
        let mut previous := statementSequence
        for (before, after) in phases do
          unless previous ≤ sequenceOf before && sequenceOf before < sequenceOf after &&
              sequenceOf after < sequenceOf terminal && timeOf before ≤ timeOf after &&
              timeOf after - timeOf before ≤ timeOf terminal - timeOf started do
            throwError "the actual read/lower/prepare/dispatch/admit/bind phases lost their measured order"
          previous := sequenceOf after
      finally
        session.close
  finally
    setEnv environment

end CasRuntime.SessionLogTests
