module

public import CasRuntime.Session
public import CasCompiler.Parse
public import CasCatalogue.TestSuite
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCatalogue.TestSuite
meta import LeanCategories.Catalogue

namespace CasRuntime.ApplicationLogTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue CasCatalogue.Backend

public meta def runOriginalFile (peer : Bool)
    (observe : KernelSession → SourceFile → Array CasCatalogue.Language.TestResult →
      Array Json → Json → CommandElabM Unit := fun _ _ _ _ _ => pure ()) :
    CommandElabM Unit := do
  let preparationStarted ← IO.monoMsNow
  let environment ← getEnv
  try
    let root ← IO.currentDir
    let input : System.FilePath := "tests/acceptance/sets.cas"
    let contents ← IO.FS.readFile input
    let sourceSha256 ← sha256Hex contents
    let original ← liftCoreM <| SourceFile.parse input.toString contents
    let contract ← packageDir contractPackage
    let python := (← IO.FS.realPath contract) / ".venv/bin/python"
    let logDirectory : System.FilePath :=
      (← IO.getEnv "CAS_APPLICATION_LOG_DIR").getD "timing/application"
    let nonce := (← IO.FS.readFile "/proc/sys/kernel/random/uuid").trimAscii.toString
    let evidence := logDirectory / "original-acceptance" / nonce
    IO.FS.createDirAll evidence
    let registration := Json.mkObj [
      ("operation", "meth.cardinality"), ("input", "obj.sets.fin"), ("backend", "peer")]
    let backends := if peer then
        #[Json.mkObj [("name", "peer"), ("command", python.toString),
          ("args", toJson #[(root / "scripts/probes/kernel_session_peer.py").toString])]]
      else #[]
    let registrations := if peer then #[registration] else #[]
    let manifest := Json.mkObj [
      ("backends", .arr backends), ("registrations", .arr registrations)]
    let manifestPath := evidence / "leaves.json"
    IO.FS.writeFile manifestPath manifest.compress
    let initial ← liftTermElabM <| KernelSession.start (some manifestPath)
      (computationOnly := true) (preparationStarted? := some preparationStarted)
    try
      unless initial.kernel.rejected.isEmpty do
        throwError "the original-file control lost its one legitimate peer registration"
      let (rows, completed) ← CasCatalogue.Language.runFile initial input

      IO.FS.writeFile (evidence / "results.json") <| (Json.mkObj [
        ("file", toJson input.toString), ("sourceSha256", toJson sourceSha256),
        ("manifest", manifest), ("peer", toJson peer),
        ("applicationLog", toJson initial.kernel.log.path.toString),
        ("results", toJson rows)]).pretty
      unless (← IO.FS.readFile input) == contents do
        throwError "the original acceptance file changed during its public execution"
      let events ← CasTools.ApplicationLog.readEvents initial.kernel.log.path
      let dataOf (event : Json) : Json := (event.getObjVal? "data").toOption.getD .null
      let isEvent (name : String) (event : Json) : Bool :=
        (event.getObjValAs? String "event").toOption == some name
      let hasParent (sequence : Nat) (event : Json) : Bool :=
        ((event.getObjValAs? (Array Nat) "parents").toOption.getD #[]).contains sequence
      for event in events, sequence in [:events.size] do
        unless (event.getObjValAs? Nat "sequence").toOption == some sequence &&
            (event.getObjValAs? String "session").toOption == some initial.kernel.log.session do
          throwError "the original file log changed its event order or session"
        let .ok parents := event.getObjValAs? (Array Nat) "parents"
          | throwError "the original file log lost its causal event parents"
        unless parents.all (· < sequence) do
          throwError "the original file log references a missing or later event"
      let #[started] := (events.filter (isEvent "file.started")).map dataOf
        | throwError "the original file lost its one parsed-file event"
      let #[finished] := (events.filter (isEvent "file.finished")).map dataOf
        | throwError "the original file lost its complete file outcome"
      for fileEvent in #[started, finished] do
        unless (fileEvent.getObjValAs? String "file").toOption == some input.toString &&
            (fileEvent.getObjValAs? String "sourceSha256").toOption == some sourceSha256 do
          throwError "the file log replaced its original path or exact source"
      unless (started.getObjValAs? Nat "statements").toOption == some original.items.size &&
          (finished.getObjValAs? Nat "executed").toOption == some original.items.size do
        throwError "the public runner omitted an original acceptance-file item"
      let computations := events.filter (isEvent "computation.started")
      let timings := events.filter (isEvent "computation.timing")
      unless computations.size == original.items.size && timings.size == original.items.size do
        throwError "the public file lost an original computation or timing record"
      let originalIds := original.items.filterMap fun item =>
        match item with
        | `(cas_item| test $id:ident $_:str : $_:cas_stmt) => some id.getId.toString
        | _ => none
      unless (rows.filter (!·.id.startsWith "(statement)")).map (·.id) == originalIds do
        throwError "the public report changed the complete original assertion inventory"
      for item in original.items, ordinal in [:original.items.size] do
        let (id, statement) : String × TSyntax `cas_stmt := match item with
          | `(cas_item| test $id:ident $_:str : $statement:cas_stmt) =>
            (id.getId.toString, statement)
          | `(cas_item| $statement:cas_stmt) =>
            (s!"(statement) {item.raw.reprint.getD ""}", statement)
          | _ => (s!"(statement) {item.raw.reprint.getD ""}", ⟨item.raw⟩)
        let some computation := computations[ordinal]?
          | throwError "the original statement lost its entered computation"
        let .ok computationSequence := computation.getObjValAs? Nat "sequence"
          | throwError "the original computation lost its log identity"
        let data := dataOf computation
        unless (data.getObjValAs? String "id").toOption == some id &&
            (data.getObjValAs? Nat "ordinal").toOption == some ordinal &&
            (data.getObjValAs? String "source").toOption ==
              some (statement.raw.reprint.getD "") &&
            (data.getObjValAs? String "sourceSha256").toOption == some sourceSha256 &&
            (data.getObjVal? "position").toOption ==
              some (SourceSnapshot.spanJson ⟨input.toString,
                statement.raw.getPos?, statement.raw.getTailPos?⟩) do
          throwError "the entered computation changed its original statement or position"
        let descendants := events.filter (hasParent computationSequence)
        let #[statementStarted] := descendants.filter (isEvent "statement.started")
          | throwError "an original file item lost its public statement entrance"
        let .ok statementSequence := statementStarted.getObjValAs? Nat "sequence"
          | throwError "the original statement lost its causal identity"
        unless ((dataOf statementStarted).getObjVal? "source").toOption ==
            (data.getObjVal? "source").toOption &&
            ((dataOf statementStarted).getObjVal? "position").toOption ==
              (data.getObjVal? "position").toOption do
          throwError "the public statement replaced its parsed source or position"
        let entered := descendants.filter (hasParent statementSequence)
        let #[timing] := (descendants.filter (isEvent "computation.timing")).map dataOf
          | throwError "an original statement lost its own complete timing"
        let .ok result := timing.getObjVal? "result"
          | throwError "an original statement timing lost its actual root result"
        unless (result.getObjValAs? String "id").toOption == some id &&
            (timing.getObjValAs? Nat "ordinal").toOption == some ordinal &&
            (timing.getObjValAs? Nat "executionMilliseconds").isOk &&
            (timing.getObjValAs? Nat "cumulativeSetupMilliseconds").isOk do
          throwError "the original statement timing changed its identity or measured work"
        let terminal := entered.filter fun event =>
          isEvent "statement.finished" event || isEvent "statement.interrupted" event
        let #[terminal] := terminal
          | throwError "an entered original statement lost its one terminal event"
        if isEvent "statement.finished" terminal then
          for field in #["kind", "stratum", "detail", "fails", "attempted", "published"] do
            unless ((dataOf terminal).getObjVal? field).toOption ==
                (result.getObjVal? field).toOption do
              throwError "the log changed the original root outcome field {field}"
          if ((dataOf terminal).getObjValAs? Bool "attempted").toOption == some true then
            unless entered.any (isEvent "statement.read") do
              throwError "an executed original statement lost its selected reading"
        else
          unless (result.getObjValAs? String "kind").toOption == some "internal" do
            throwError "an interrupted statement was relabeled as another outcome"
        for reading in entered.filter (isEvent "statement.read") do
          let .ok scope := (dataOf reading).getObjVal? "scope"
            | throwError "the original selected reading lost its source scope"
          unless (scope.getObjVal? "context").isOk &&
              (scope.getObjVal? "selections").isOk &&
              (scope.getObjVal? "nativeExpressions").isOk do
            throwError "the original selected reading lost its complete typed interpretation"
      for row in rows do
        let matching := timings.filter fun event =>
          ((dataOf event).getObjValAs? String "id").toOption == some row.id
        let #[timing] := matching
          | throwError "an original report row lost its one measured computation"
        unless ((dataOf timing).getObjVal? "result").toOption == some (toJson row) do
          throwError "the diagnostic report changed an original public result"
      let required := #[
        ("sets.implemented.card_fin", if peer then "holds" else "gap"),
        ("sets.apply.rev", "gap")]
      for (id, kind) in required do
        let #[row] := rows.filter (·.id == id)
          | throwError "the original file lost a required public log control"
        unless row.kind == kind && row.attempted && !row.question.isEmpty &&
            !row.conclusions.isEmpty do
          throwError "the required original statement did not reach its typed execution boundary: {id}: {toJson row}"
        let #[computation] := computations.filter fun event =>
            ((dataOf event).getObjValAs? String "id").toOption == some id
          | throwError "the required original statement lost its computation"
        let .ok sequence := computation.getObjValAs? Nat "sequence"
          | throwError "the required computation lost its causal identity"
        let entered := events.filter (hasParent sequence)
        let #[terminal] := entered.filter (isEvent "statement.finished")
          | throwError "the required original statement lost its completed public outcome"
        unless (entered.filter (isEvent "statement.interrupted")).isEmpty do
          throwError "a required original execution was interrupted"
        if peer && id == "sets.implemented.card_fin" then
          unless row.published && row.dispatches == #[registration] do
            throwError "the original cardinality statement lost its actual peer dispatch"
          let #[dispatch] := entered.filter (isEvent "dispatch")
            | throwError "the original cardinality statement lost its one actual dispatch event"
          let .ok selected := (dataOf dispatch).getObjVal? "selected"
            | throwError "the actual dispatch lost its selected registration"
          for (field, expected) in #[
              ("operation", "meth.cardinality"), ("input", "obj.sets.fin"), ("backend", "peer")] do
            unless (selected.getObjValAs? String field).toOption == some expected do
              throwError "the actual dispatch changed its original registration field {field}"
          let .ok request := (dataOf dispatch).getObjVal? "request"
            | throwError "the actual dispatch lost its prepared request"
          let .ok native := request.getObjVal? "native"
            | throwError "the actual dispatch lost its complete native request"
          unless ((dataOf dispatch).getObjVal? "operands").isOk do
            throwError "the actual dispatch lost its original operands"
          unless entered.any (fun event => isEvent "request.prepared" event &&
              ((dataOf event).getObjVal? "native").toOption == some native) do
            throwError "the dispatch lost its original prepared request event"
          let .ok occurrence := (dataOf dispatch).getObjVal? "occurrence"
            | throwError "the actual dispatch lost its original occurrence"
          for phase in #["reply.admission.started", "reply.admitted"] do
            unless entered.any (fun event => isEvent phase event &&
                ((dataOf event).getObjVal? "occurrence").toOption == some occurrence) do
              throwError "the actual peer reply lost its admission phase {phase}"
        else
          unless !row.published && row.dispatches.isEmpty &&
              ((dataOf terminal).getObjValAs? String "stratum").toOption ==
                some "noImplementation" do
            throwError "the original missing implementation lost its classified terminal outcome"
          let #[missing] := entered.filter (isEvent "realization.missing")
            | throwError "the original missing implementation lost its exact realization request"
          let .ok forms := (dataOf missing).getObjValAs? (Array String) "forms"
            | throwError "the missing implementation lost its complete original input forms"
          let (operation, inputForm) := if id == "sets.implemented.card_fin" then
              ("meth.cardinality", "obj.sets.fin")
            else ("mor.sets.fin_rev", "mor.sets.fin_rev")
          unless ((dataOf missing).getObjValAs? String "operation").toOption ==
              some operation && forms[0]? == some inputForm do
            throwError "the missing implementation changed its original operation or input address"
          unless (entered.filter (isEvent "dispatch")).isEmpty &&
              entered.any (isEvent "request.prepared") do
            throwError "the unregistered original request dispatched or lost its preparation"
      observe completed original rows events manifest
    finally initial.close
  finally setEnv environment

run_cmd runOriginalFile true

end CasRuntime.ApplicationLogTests
