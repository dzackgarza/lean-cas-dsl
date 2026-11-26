

module

public import CasRuntime.Session
import CasRuntime.Inspect
public import CasCompiler.Parse
public import CasTools.QuestionObservation
import Worker.Cell
import Worker.Output
public meta import CasRuntime.Session
public meta import CasRuntime.Inspect
public meta import CasCompiler.Parse
public meta import CasTools.QuestionObservation
public meta import Worker.Cell
public meta import Worker.Output

public section

open Lean Elab Command Term CasRuntime CasCompiler

namespace CasCatalogue.Language

meta section

structure TestResult where
  file : String
  id : String

  kind : String

  stratum : Option String := none
  detail : String := ""

  fails : Bool := false

  attempted : Bool := true

  published : Bool := false

  blockedBy : Option String := none

  question : String := ""
  proposition : String := ""

  conclusions : Array Json := #[]

  dispatches : Array Json := #[]

  milliseconds : Nat := 0

  setupMilliseconds : Nat := 0
  deriving ToJson, FromJson, Inhabited

attribute [-instance] instFromJsonTestResult

instance instFromJsonTestResultCompatible : FromJson TestResult where
  fromJson? json :=
    let normalized := match json with
      | .obj fields =>
        let fields := if (fields.get? "conclusions").isSome then fields
          else fields.insert "conclusions" (.arr #[])
        let fields := if (fields.get? "stratum").isSome then fields
          else fields.insert "stratum" .null
        .obj fields
      | _ => json
    @fromJson? TestResult instFromJsonTestResult normalized

private def TestResult.writeProgress (result : TestResult)
    (position : Option Position := none) : CommandElabM Unit := do
  let output ← if Core.stderrAsMessages.get (← getOptions) then IO.getStdout else IO.getStderr
  let detail := if result.detail.isEmpty then "" else s!": {result.detail}"
  let location := match position with
    | some position => s!"{result.file}:{position.line}:{position.column + 1}"
    | none => result.file
  output.putStrLn s!"{location}: {result.id}: {result.kind} \
    ({result.milliseconds} ms){detail}"
  output.flush

private def dispatchJson (registration : Registration) : Json :=
  Json.mkObj [("operation", toJson registration.operation), ("input", toJson registration.input),
    ("backend", toJson registration.backend)]

private def runOne (session : KernelSession) (statement : TSyntax `cas_stmt)
    (source : Option SourceFile := none) (owningCell : Option CellTransaction := none)
    (diagnostics : Option CasTools.Diagnostics.Scope := none) (started? : Option Nat := none) :
    CommandElabM (StatementRun × Array Json) := do
  let start := (← session.kernel.dispatches.get).size
  let computation : TermElabM StatementRun := withoutErrToSorry <| withCurrHeartbeats <|
    match source with
    | some file => file.withContext (session.run statement owningCell started?)
    | none => session.run statement owningCell started?
  let result ← liftTermElabM <| match diagnostics with
    | some scope => CasTools.Diagnostics.withScope scope computation
    | none => computation
  let calls ← session.kernel.dispatches.get
  return (result, (calls.extract start calls.size).map dispatchJson)

private partial def unexecutedScope (statement : TSyntax `cas_stmt) :
    Array StatementObservation := Id.run do
  let some items := sourceContextItems? statement | return #[]
  return items.flatMap unreadSourceItems

def runFile (session : KernelSession) (path : System.FilePath) :
    CommandElabM (Array TestResult × KernelSession) := do
  let file := path.toString
  let log := session.kernel.log
  let fileBegan ← IO.monoMsNow
  let fileEntry ← log.write #[] "file.begin" (Json.mkObj [("file", toJson file)])
  let fileRun := s!"{log.session}/{fileEntry}"
  let contents ← try IO.FS.readFile path
    catch error =>
      discard <| log.write #[fileEntry] "file.failed" <| Json.mkObj [
        ("fileRun", toJson fileRun), ("file", toJson file), ("stage", toJson "read"),
        ("detail", toJson (← error.toMessageData.toString))]
      return (#[{ file, id := "(statement) infrastructure", kind := "internal"
                  detail := s!"cannot read selected input: {← error.toMessageData.toString}"
                  fails := true }], session)
  let sourceSha256 ← sha256Hex contents
  let source ← try liftCoreM <| SourceFile.parse file contents
    catch error =>
      discard <| log.write #[fileEntry] "file.failed" <| Json.mkObj [
        ("fileRun", toJson fileRun), ("file", toJson file), ("stage", toJson "parse"),
        ("sourceSha256", toJson sourceSha256),
        ("detail", toJson (← error.toMessageData.toString))]

      return (#[{ file, id := "(statement) parse", kind := "invalid", stratum := some "invalid"
                  detail := s!"reader parser failure: {← error.toMessageData.toString}"
                  fails := true }], session)
  let sharedFileSetupMilliseconds := (← IO.monoMsNow) - fileBegan
  discard <| log.write #[fileEntry] "file.started" <| Json.mkObj [
    ("fileRun", toJson fileRun), ("file", toJson file),
    ("sourceSha256", toJson sourceSha256), ("statements", toJson source.items.size),
    ("sharedFileSetupMilliseconds", toJson sharedFileSetupMilliseconds)]
  let mut session := session
  let mut results : Array TestResult := #[]
  let mut setupMilliseconds := 0
  let mut cumulativeSetupMilliseconds := sharedFileSetupMilliseconds
  let mut executed := 0
  for item in source.items, ordinal in [:source.items.size] do
    let (id?, statement) : Option String × TSyntax `cas_stmt := match item with
      | `(cas_item| test $id:ident $_:str : $statement:cas_stmt) =>
        (some id.getId.toString, statement)
      | `(cas_item| $statement:cas_stmt) => (none, statement)
      | _ => (none, ⟨item.raw⟩)
    let id := id?.getD s!"(statement) {item.raw.reprint.getD ""}"
    let position := statement.raw.getPos?.map source.context.fileMap.toPosition
    let computation := s!"{fileRun}/{ordinal}"
    let computationSetupMilliseconds := cumulativeSetupMilliseconds
    let start ← IO.monoMsNow
    let computationEntry ← log.write #[fileEntry] "computation.started" <| Json.mkObj [
      ("computation", toJson computation), ("fileRun", toJson fileRun),
      ("startedMonotonicMilliseconds", toJson start),
      ("file", toJson file), ("sourceSha256", toJson sourceSha256),
      ("ordinal", toJson ordinal), ("id", toJson id),
      ("source", toJson (statement.raw.reprint.getD "")),
      ("cumulativeSetupMilliseconds", toJson computationSetupMilliseconds),
      ("position", SourceSnapshot.spanJson ⟨file, statement.raw.getPos?, statement.raw.getTailPos?⟩)]
    let recordTiming (result : TestResult) (children : Array Json) : IO Unit := do
      discard <| log.write #[fileEntry, computationEntry] "computation.timing" <| Json.mkObj [
        ("computation", toJson computation), ("fileRun", toJson fileRun),
        ("file", toJson file), ("sourceSha256", toJson sourceSha256),
        ("ordinal", toJson ordinal), ("id", toJson id),
        ("milliseconds", toJson (result.milliseconds + computationSetupMilliseconds)),
        ("executionMilliseconds", toJson result.milliseconds),
        ("setupMilliseconds", toJson computationSetupMilliseconds),
        ("cumulativeSetupMilliseconds", toJson computationSetupMilliseconds),
        ("reportSetupMilliseconds", toJson result.setupMilliseconds),
        ("sharedFileSetupMilliseconds", toJson sharedFileSetupMilliseconds),
        ("result", toJson result), ("children", toJson children)]
    executed := executed + 1
    let execution ← try
        let run ← runOne session statement (some source)
          (diagnostics := some { log, parents := #[fileEntry, computationEntry] })
        pure (some run)
      catch error =>
        let result : TestResult := {
          file, id, kind := "internal"
          detail := s!"statement execution failed: {← error.toMessageData.toString}"
          fails := true, milliseconds := (← IO.monoMsNow) - start, setupMilliseconds }
        result.writeProgress position
        recordTiming result #[]
        results := results.push result
        setupMilliseconds := 0
        pure none
    let milliseconds := (← IO.monoMsNow) - start
    let some (run, dispatches) := execution | continue
    let retainsSetup := run.session.source.context.entries.size > session.source.context.entries.size
    session := run.session
    for output in run.inspectionOutput do logInfo output
    let result : TestResult := {
      file, id, kind := run.outcome.kind, detail := run.outcome.detail
      stratum := run.outcome.stratum?
      fails := run.outcome.fails, attempted := run.attempted, published := run.published,
      question := run.proposition, proposition := run.proposition
      conclusions := run.conclusions.map CasTools.QuestionExport.observeConclusion
      dispatches, milliseconds, setupMilliseconds }
    result.writeProgress position
    let scopedObservations :=
      if run.observations.isEmpty && (sourceContextItems? statement).isSome then
        unexecutedScope statement
      else run.observations
    recordTiming result <| scopedObservations.mapIdx fun ordinal child => Json.mkObj [
      ("ordinal", toJson ordinal),
      ("id", toJson (match child.item with
        | `(cas_item| test $name:ident $_:str : $_:cas_stmt) => name.getId.toString (escape := false)
        | _ => s!"(statement) {child.item.raw.reprint.getD ""}")),
      ("source", toJson (child.item.raw.reprint.getD "")),
      ("position", SourceSnapshot.spanJson ⟨file, child.item.raw.getPos?, child.item.raw.getTailPos?⟩),
      ("attempted", toJson child.attempted),
      ("kind", toJson (child.outcome.map (·.kind))),
      ("stratum", toJson (child.outcome.bind (·.stratum?))),
      ("detail", toJson (child.outcome.map (·.detail))),
      ("milliseconds", toJson child.milliseconds),
      ("conclusions", toJson (child.conclusions.map CasTools.QuestionExport.observeConclusion)),
      ("dispatches", toJson (child.dispatches.map dispatchJson))]
    if retainsSetup then
      cumulativeSetupMilliseconds := cumulativeSetupMilliseconds + milliseconds
    if !scopedObservations.isEmpty then

      let elapsed := scopedObservations.foldl (fun total child => total + child.milliseconds) 0
      setupMilliseconds := setupMilliseconds + (milliseconds - elapsed)
      let beforeRows := results.size
      let failedChild := scopedObservations.find? fun child =>
        child.outcome.any (fun outcome => !(outcome matches .holds))
      let cause := match failedChild with
        | some child => match child.item with
          | `(cas_item| test $name:ident $_:str : $_:cas_stmt) =>
            name.getId.toString (escape := false)
          | _ => s!"(statement) {child.item.raw.reprint.getD ""}"
        | none => id
      for child in scopedObservations do
        let childId := match child.item with
          | `(cas_item| test $name:ident $_:str : $_:cas_stmt) =>
            some (name.getId.toString (escape := false))
          | _ => none
        if childId.isNone && child.outcome.any (fun outcome => outcome matches .holds) then
          setupMilliseconds := setupMilliseconds + child.milliseconds
          continue
        if childId.isNone && child.outcome.isNone then
          setupMilliseconds := setupMilliseconds + child.milliseconds
          continue
        let availability :=
          if child.attempted then "attempted but not published" else "not executed"
        let outcome := child.outcome.getD (.unavailable
          s!"{availability}; stopped at {cause}: {run.outcome.kind}: {run.outcome.detail}")
        let row : TestResult := {
          file, id := childId.getD s!"(statement) {child.item.raw.reprint.getD ""}",
          kind := outcome.kind, detail := outcome.detail, fails := outcome.fails,
          stratum := outcome.stratum?,
          attempted := child.attempted, published := run.published,
          blockedBy := if child.outcome.isNone then some cause else none,
          question := child.proposition, proposition := child.proposition,
          conclusions := child.conclusions.map CasTools.QuestionExport.observeConclusion,
          dispatches := child.dispatches.map dispatchJson,
          milliseconds := child.milliseconds, setupMilliseconds }
        row.writeProgress (child.item.raw.getPos?.map source.context.fileMap.toPosition)
        results := results.push row
        setupMilliseconds := 0

      if id?.isSome || (results.size == beforeRows && !(run.outcome matches .holds)) ||
          (failedChild.isNone && !(run.outcome matches .holds)) then
        results := results.push result
      continue
    if id?.isNone && run.outcome matches .holds then
      setupMilliseconds := setupMilliseconds + milliseconds
      continue
    results := results.push result
    setupMilliseconds := 0
  discard <| log.write #[fileEntry] "file.finished" <| Json.mkObj [
    ("fileRun", toJson fileRun), ("file", toJson file),
    ("sourceSha256", toJson sourceSha256), ("executed", toJson executed),
    ("milliseconds", toJson ((← IO.monoMsNow) - fileBegan))]
  return (results, session)

def report (file : String) (results : Array TestResult) : String :=
  let tests := results.filter (!·.id.startsWith "(statement)")
  let passing := (tests.filter (·.kind == "holds")).size
  let lines := results.filter (·.kind != "holds") |>.map fun r => s!"  {r.id}: {r.kind}: {r.detail}"
  s!"{file}: {passing} of {tests.size} hold\n{"\n".intercalate lines.toList}"

def withSession (manifest? : Option System.FilePath) (computationOnly : Bool)
    (action : KernelSession → CommandElabM α) : CommandElabM α := do
  let environment ← getEnv
  try
    liftCoreM KernelSession.clear
    let session ← liftTermElabM <| KernelSession.start manifest? computationOnly
    for rejected in session.kernel.rejected do
      logWarning m!"registration not admitted: {rejected}"
    try action session finally (session.close : IO Unit)
  finally setEnv environment

def runSuite (manifest? : Option System.FilePath) (computationOnly : Bool)
    (path : System.FilePath) (inventory? : Option System.FilePath := none) :
    CommandElabM (Array TestResult) := do
  let mut results : Array TestResult := #[]
  let files ← try
      if ← path.isDir then
        pure ((← path.readDir).filter (·.path.extension == some "cas") |>.map (·.path))
      else pure #[path]
    catch error =>
      results := results.push {
        file := path.toString
        id := "(statement) infrastructure"
        kind := "internal"
        detail := ← error.toMessageData.toString
        fails := true }
      pure #[]
  if files.isEmpty && results.isEmpty then
    results := results.push {
      file := path.toString
      id := "(statement) infrastructure"
      kind := "internal"
      detail := "the selected suite contains no .cas files"
      fails := true }
  for file in files.qsort (·.toString < ·.toString) do
    try
      results := results ++
        (← withSession manifest? computationOnly fun session => do
          return (← runFile session file).1)
    catch error =>
      results := results.push {
        file := file.toString
        id := "(statement) infrastructure"
        kind := "internal"
        detail := ← error.toMessageData.toString
        fails := true }
  let mut identities : Array String := #[]
  for result in results do
    if result.id.startsWith "(statement)" then continue
    if identities.contains result.id then
      results := results.push {
        file := result.file
        id := s!"(statement) duplicate {result.id}"
        kind := "internal"
        detail := s!"duplicate named assertion identity: {result.id}"
        fails := true }
    else
      identities := identities.push result.id
  if let some inventory := inventory? then
    try
      let .ok document := Json.parse (← IO.FS.readFile inventory)
        | throwError "cannot read the fixed assertion inventory {inventory}"
      let .ok (.obj assertions) := document.getObjVal? "assertions"
        | throwError "missing assertion inventory in {inventory}"
      for (identity, _) in assertions.toList do
        unless results.any (·.id == identity) do
          results := results.push {
            file := path.toString
            id := identity
            kind := "internal"
            detail := "required assertion produced no result"
            fails := true }
    catch error =>

      results := results.push {
        file := inventory.toString
        id := "(statement) inventory infrastructure"
        kind := "internal"
        detail := ← error.toMessageData.toString
        fails := true }
  return results

def runStatement (session : KernelSession) (text : String)
    (owningCell : Option CellTransaction := none) : CommandElabM StatementRun := do
  let started ← IO.monoMsNow
  let parsed ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
    | .ok statement => pure statement
    | .error error => do
      let reference ← getRef
      let log := session.kernel.log
      let parents := match ← liftCoreM CasTools.Diagnostics.current? with
        | some active => if active.log.session == log.session then active.parents else #[]
        | none => #[]
      discard <| log.write parents "statement.parseFailed" <| Json.mkObj [
        ("source", toJson text), ("kind", toJson "invalid"),
        ("startedMonotonicMilliseconds", toJson started),
        ("milliseconds", toJson ((← IO.monoMsNow) - started)),
        ("cumulativeSetupMilliseconds", toJson session.setupMilliseconds),
        ("fails", toJson true), ("attempted", toJson false),
        ("published", toJson false), ("retainsSetup", toJson false),
        ("stratum", toJson (some "invalid")), ("detail", toJson error),
        ("position", SourceSnapshot.spanJson ⟨← getFileName,
          reference.getPos?, reference.getTailPos?⟩)]
      throwError "not a statement of the language: {error}\n{text}"
  return (← runOne session ⟨parsed⟩ none owningCell (started? := some started)).1

syntax (name := casTestsCommand)
  "#cas_tests " str (&" manifest " str)? (&" reporting " str)? (&" inventory " str)?
  (&" computing")? : command

@[command_elab casTestsCommand] def elabCasTests : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let manifest? := stx[2][1].isStrLit?.map fun s => (s : System.FilePath)
  let computationOnly := stx[5].getNumArgs > 0
  let inventory? := stx[4][1].isStrLit?.map fun s => (s : System.FilePath)
  let results ← runSuite manifest? computationOnly path inventory?
  let files := results.foldl (fun fs r => if fs.contains r.file then fs else fs.push r.file) #[]
  for file in files do logInfo (report file (results.filter (·.file == file)))
  if let some out := stx[3][1].isStrLit? then
    IO.FS.writeFile out (toJson results).pretty
  let failures := results.filter (·.fails)
  unless failures.isEmpty do
    throwError "the suite fails:\n{"\n".intercalate (failures.toList.map fun r =>
      s!"  {r.file}: {r.id}: {r.kind}: {r.detail}")}"

syntax (name := casStatementCommand) "#cas " str (&" manifest " str)? : command

@[command_elab casStatementCommand] def elabCasStatement : CommandElab := fun stx => do
  let some text := stx[1].isStrLit? | throwUnsupportedSyntax
  let manifest? := stx[2][1].isStrLit?.map fun s => (s : System.FilePath)
  let owningCell ← liftCoreM KernelSession.active?
  let session ← match ← liftCoreM KernelSession.current? with
    | some session =>
      if manifest?.isSome then
        throwError "the session manifest is frozen at startup"
      if owningCell.isSome then pure session else session.fork
    | none => liftTermElabM <| KernelSession.start manifest?
  let run ← runStatement session text owningCell
  let outcome := run.outcome
  let shown := if outcome matches .holds then outcome.kind else s!"{outcome.kind}: {outcome.detail}"
  if outcome.fails || (owningCell.isSome && !(outcome matches .holds)) then
    if owningCell.isSome then
      Worker.Cell.reportFailure { stratum := outcome.stratum?, reason := outcome.detail }
    throwError shown
  else
    liftCoreM (KernelSession.install run.session)
    if let some transaction := owningCell then
      let definitions ← liftTermElabM (CasRuntime.Inspect.newBindings session run.session transaction)
      let rendered := if run.proposition.isEmpty then shown else s!"{shown}: {run.proposition}"
      let rendered := "\n".intercalate (rendered :: run.inspectionOutput.toList)
      let metadata := Json.mkObj [
        ("cas_source", toJson text),
        ("cas_definitions", toJson definitions),
        ("conclusions", toJson (run.conclusions.map CasTools.QuestionExport.observeConclusion))]
      let bundle : Worker.Output :=
        { data := [("text/plain", toJson rendered)], metadata }
      Worker.emitOutput bundle
    else
      logInfo shown
      for output in run.inspectionOutput do logInfo output

end

end CasCatalogue.Language
