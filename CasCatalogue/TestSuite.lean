/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasRuntime.Session
public import CasCompiler.Parse
public meta import CasRuntime.Session
public meta import CasCompiler.Parse

public section

/-!
# The acceptance suite: files of statements in the language

`#cas_tests "tests/acceptance/f.cas"` runs a file of the language, and `#cas_tests "dir"` every
`.cas` file of `dir`. An item is `test id "source": statement`, a statement admitted permanently
(`scripts/check_acceptance_permanent.py`), whose expected value comes from `source`; or a bare
`let`. The file's `let`s scope over the items after them, and each retains its computed value.

Each statement runs through `CasRuntime.KernelSession.run`: the source reader, the lowerer and
the kernel executor, over the registrations of the installed leaves' manifest
(`CasRuntime.installedManifest`; `#cas_tests "dir" manifest "path"` names another). The
registrations not admitted are reported. A statement that holds, a gap (no registration, an
ambiguous one, an unfinished source form) and an unavailable backend are recorded; every other
outcome (`Outcome.fails`) fails the build. A leaf never sees the suite.
`#cas_tests "dir" reporting "out.json"` also writes every result as JSON (`cas-harness` runs it
over a given manifest).

The optional `computing` suffix computes every question through the kernel, with no discharge
in Lean. Each result records the registrations actually dispatched during that statement.

`#cas "statement"` runs one statement of the language the same way (a notebook cell): its outcome
is reported, and an outcome that fails the suite is an error.
-/

open Lean Elab Command Term CasRuntime CasCompiler

namespace CasCatalogue.Language

meta section

/-- The outcome of one test of the suite. -/
structure TestResult where
  file : String
  id : String
  /-- The outcome's kind (`Outcome.kind`). -/
  kind : String
  detail : String := ""
  /-- Whether the outcome fails the suite (`Outcome.fails`). -/
  fails : Bool := false
  /-- Whether this original item entered execution; false for an unexecuted continuation. -/
  attempted : Bool := true
  /-- Whether the item's owning runtime cell committed. Pure source observations have no cell. -/
  published : Bool := false
  /-- Original failing item in this file when an enclosing scope withheld this result. -/
  blockedBy : Option String := none
  /-- The proposition that the reader formed; empty when the statement was not read. -/
  question : String := ""
  proposition : String := ""
  /-- Registrations actually dispatched during this statement; not mathematical evidence. -/
  dispatches : Array Json := #[]
  /-- Wall time of this statement, in milliseconds (constitution C24, timing history). -/
  milliseconds : Nat := 0
  /-- Wall time of the definitions before this statement that are not reported themselves: the
  setup that this statement uses, in milliseconds. -/
  setupMilliseconds : Nat := 0
  deriving ToJson, FromJson, Inhabited

/-- Report a completed statement. `-DstderrAsMessages=false` enables live stderr output. -/
private def TestResult.writeProgress (result : TestResult) : CommandElabM Unit := do
  let output ← if Core.stderrAsMessages.get (← getOptions) then IO.getStdout else IO.getStderr
  let detail := if result.detail.isEmpty then "" else s!": {result.detail}"
  output.putStrLn s!"{result.file}: {result.id}: {result.kind} \
    ({result.milliseconds} ms){detail}"
  output.flush

private def dispatchJson (registration : Registration) : Json :=
  Json.mkObj [("operation", toJson registration.operation), ("input", toJson registration.input),
    ("backend", toJson registration.backend)]

/-- Run one parsed statement in its own heartbeat budget and report its dispatches.
A statement of a file is read against that file's original positions. -/
private def runOne (session : KernelSession) (statement : TSyntax `cas_stmt)
    (source : Option SourceFile := none) : CommandElabM (StatementRun × Array Json) := do
  let start := (← session.kernel.dispatches.get).size
  let result ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
    match source with
    | some file => file.withContext (session.run statement)
    | none => session.run statement
  let calls ← session.kernel.dispatches.get
  return (result, (calls.extract start calls.size).map dispatchJson)

private partial def unexecutedScope (statement : TSyntax `cas_stmt) :
    Array StatementObservation := Id.run do
  let some items := sourceContextItems? statement | return #[]
  return items.flatMap fun item =>
    let child : TSyntax `cas_stmt := match item with
      | `(cas_item| test $_:ident $_:str : $statement:cas_stmt)
      | `(cas_item| $statement:cas_stmt) => statement
      | _ => ⟨item.raw⟩
    if (sourceContextItems? child).isSome then unexecutedScope child
    else #[{ item, attempted := false }]

/-- Runs the file `path` of the suite in `session`: the outcome of each test, and the session
after the file. A `let` or statement that does not hold is reported as a statement of the file.
An exception outside a statement's own outcome is that statement's internal error. -/
def runFile (session : KernelSession) (path : System.FilePath) :
    CommandElabM (Array TestResult × KernelSession) := do
  let file := path.toString
  let contents ← try IO.FS.readFile path
    catch error =>
      return (#[{ file, id := "(statement) infrastructure", kind := "internal"
                  detail := s!"cannot read selected input: {← error.toMessageData.toString}"
                  fails := true }], session)
  let source ← try liftCoreM <| SourceFile.parse file contents
    catch error =>
      -- A syntactically unreadable file is invalid input, not an interpreter crash.
      return (#[{ file, id := "(statement) parse", kind := "invalid"
                  detail := s!"reader parser failure: {← error.toMessageData.toString}"
                  fails := true }], session)
  let mut session := session
  let mut results : Array TestResult := #[]
  let mut setupMilliseconds := 0
  for item in source.items do
    let (id?, statement) : Option String × TSyntax `cas_stmt := match item with
      | `(cas_item| test $id:ident $_:str : $statement:cas_stmt) =>
        (some id.getId.toString, statement)
      | `(cas_item| $statement:cas_stmt) => (none, statement)
      | _ => (none, ⟨item.raw⟩)
    let id := id?.getD s!"(statement) {item.raw.reprint.getD ""}"
    let start ← IO.monoMsNow
    let execution ← try
        pure (some (← runOne session statement (some source)))
      catch error =>
        let result : TestResult := {
          file, id, kind := "internal"
          detail := s!"statement execution failed: {← error.toMessageData.toString}"
          fails := true, milliseconds := (← IO.monoMsNow) - start, setupMilliseconds }
        result.writeProgress
        results := results.push result
        setupMilliseconds := 0
        pure none
    let milliseconds := (← IO.monoMsNow) - start
    let some (run, dispatches) := execution | continue
    session := run.session
    for output in run.inspectionOutput do logInfo output
    let result : TestResult := {
      file, id, kind := run.outcome.kind, detail := run.outcome.detail
      fails := run.outcome.fails, published := run.published,
      question := run.proposition, proposition := run.proposition
      dispatches, milliseconds, setupMilliseconds }
    result.writeProgress
    let scopedObservations := if run.observations.isEmpty && (sourceContextItems? statement).isSome then
        unexecutedScope statement
      else run.observations
    if !scopedObservations.isEmpty then
      -- Child time/calls are measured by the same shared execution cell. Source preflight
      -- and block overhead are charged once as setup, never invented per-question timings.
      let elapsed := scopedObservations.foldl (fun total child => total + child.milliseconds) 0
      setupMilliseconds := setupMilliseconds + (milliseconds - elapsed)
      let beforeRows := results.size
      let cause := match scopedObservations.find? (fun child =>
          child.outcome.any (fun outcome => !(outcome matches .holds))) with
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
        let availability := if child.attempted then "attempted but not published" else "not executed"
        let outcome := child.outcome.getD (.unavailable
          s!"{availability}; stopped at {cause}: {run.outcome.kind}: {run.outcome.detail}")
        let row : TestResult := {
          file, id := childId.getD s!"(statement) {child.item.raw.reprint.getD ""}",
          kind := outcome.kind, detail := outcome.detail, fails := outcome.fails,
          attempted := child.attempted, published := run.published,
          blockedBy := if child.outcome.isNone then some cause else none,
          question := child.proposition, proposition := child.proposition,
          dispatches := child.dispatches.map dispatchJson,
          milliseconds := child.milliseconds, setupMilliseconds }
        row.writeProgress
        results := results.push row
        setupMilliseconds := 0
      if id?.isSome || (results.size == beforeRows && !(run.outcome matches .holds)) ||
          (run.observations.isEmpty && !(run.outcome matches .holds)) then
        results := results.push result
      continue
    if id?.isNone && run.outcome matches .holds then
      setupMilliseconds := setupMilliseconds + milliseconds
      continue
    results := results.push result
    setupMilliseconds := 0
  return (results, session)

/-- The report of a file's results. -/
def report (file : String) (results : Array TestResult) : String :=
  let tests := results.filter (!·.id.startsWith "(statement)")
  let passing := (tests.filter (·.kind == "holds")).size
  let lines := results.filter (·.kind != "holds") |>.map fun r => s!"  {r.id}: {r.kind}: {r.detail}"
  s!"{file}: {passing} of {tests.size} hold\n{"\n".intercalate lines.toList}"

/-- Start a kernel session in a scratch runtime Environment, run `action`, close every started
backend and restore the Environment. Registrations not admitted are reported. -/
def withSession (manifest? : Option System.FilePath) (computationOnly : Bool)
    (action : KernelSession → CommandElabM α) : CommandElabM α := do
  let environment ← getEnv
  try
    let session ← liftTermElabM <| KernelSession.start manifest? computationOnly
    for rejected in session.kernel.rejected do
      logWarning m!"registration not admitted: {rejected}"
    try action session finally (session.close : IO Unit)
  finally setEnv environment

/-- Runs `path`, a file of the suite or a directory of `.cas` files. Each file is one session:
its `let`s do not scope over another file. -/
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
      -- Preserve the outcomes already executed even when inventory I/O fails.
      -- This is an infrastructure failure, not a verdict on those assertions.
      results := results.push {
        file := inventory.toString
        id := "(statement) inventory infrastructure"
        kind := "internal"
        detail := ← error.toMessageData.toString
        fails := true }
  return results

/-- Runs one statement of the language, given as text, in `session`. -/
def runStatement (session : KernelSession) (text : String) : CommandElabM StatementRun := do
  let parsed ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
    | .ok statement => pure statement
    | .error error => throwError "not a statement of the language: {error}\n{text}"
  return (← runOne session ⟨parsed⟩).1

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
  let run ← withSession manifest? false fun session => runStatement session text
  let outcome := run.outcome
  let shown := if outcome matches .holds then outcome.kind else s!"{outcome.kind}: {outcome.detail}"
  if outcome.fails then throwError shown
  else
    logInfo shown
    for output in run.inspectionOutput do logInfo output

end

end CasCatalogue.Language
