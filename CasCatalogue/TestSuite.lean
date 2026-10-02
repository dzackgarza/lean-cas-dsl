/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Realize
public meta import CasCatalogue.Realize

public section

/-!
# The acceptance suite: files of statements in the language

`#cas_tests "tests/acceptance/f.cas"` runs a file of the language, and `#cas_tests "dir"` every
`.cas` file of `dir`. Items are separated by blank
lines; lines beginning with `--` are comments. An item is `test id "source": statement`, a
statement admitted permanently (`scripts/check_acceptance_permanent.py`), whose expected value comes
from `source`; or a bare `let`. The file's `let`s scope over the items after them.

Each statement is decided by `CasCatalogue.Realize.run`: Lean discharge first, then the realized
reading through the registrations of the installed leaves' manifest (`leaves.json` of the leaves
package, found by `CasCatalogue.Realize.leavesManifest`; `#cas_tests "dir" manifest "path"` names
another). The registrations not admitted are reported. Each test's outcome is reported. A
statement that holds, a gap (no registration, an ambiguous one) and an unavailable backend are
recorded; every other outcome (`Outcome.fails`: a wrong or malformed answer, an invalid or
ambiguous statement, an internal error) fails the build. The report
of gaps is the list of implementations the suite derives. A leaf never sees the suite.
`#cas_tests "dir" reporting "out.json"` also writes every result as JSON (`cas-harness` runs it
over a given manifest).

`#cas "statement"` runs one statement of the language the same way (a notebook cell): its outcome
is reported, and an outcome that fails the suite is an error.
-/

open Lean Elab Command Term

namespace CasCatalogue.Language

open Realize (Harness)

/-- The items of a file: its blank-line-separated paragraphs, without comment lines. -/
meta def items (text : String) : Array String := Id.run do
  let mut out := #[]
  let mut current := ""
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "--" then continue
    if t.isEmpty then
      unless current.isEmpty do out := out.push current
      current := ""
    else current := if current.isEmpty then line else current ++ "\n" ++ line
  unless current.isEmpty do out := out.push current
  return out

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
  /-- The semantic question the statement asks (`Realize.claimQuestion`); empty when it was not read. -/
  question : String := ""
  /-- The proposition the question fingerprints, as the acceptance author reads it. -/
  proposition : String := ""
  deriving ToJson, FromJson, Inhabited

end

/-- Runs the file `path` of the suite through `harness`: the outcome of each test. A `let` or
statement that does not hold is reported as a statement of the file, with its outcome. Each test
has its own heartbeat budget; exhausting it is that test's internal error, not the run's. -/
meta def runFile (harness : Harness) (path : System.FilePath) :
    CommandElabM (Array TestResult) := do
  let path := path.toString
  let text ← IO.FS.readFile path
  let mut scope : Scope := {}
  let mut results : Array TestResult := #[]
  for item in items text do
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item path with
      | .ok s => pure s
      | .error e =>
          -- A parser failure belongs to this item. Keep its admitted identity in the report
          -- and continue, so unread assertions cannot shrink the execution denominator.
          let identity := if item.startsWith "test " then
              ((item.drop 5).toString.splitOn " ").head!
            else s!"(statement) {item}"
          results := results.push {
            file := path
            id := identity
            kind := "internal"
            detail := s!"reader parser failure: {e}"
            fails := true }
          continue
    let (id?, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) => (some id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => (none, s.raw)
      | _ => (none, parsed)
    let id := id?.getD s!"(statement) {item}"
    let (outcome, scope', question) ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
      Realize.runAsking harness scope statement
    scope := scope'
    if id?.isNone && outcome matches .holds then continue
    results := results.push
      { file := path, id, kind := outcome.kind, detail := outcome.detail, fails := outcome.fails,
        question := (question.map (·.1)).getD "", proposition := (question.map (·.2)).getD "" }
  return results

/-- The report of a file's results. -/
meta def report (file : String) (results : Array TestResult) : String :=
  let tests := results.filter (!·.id.startsWith "(statement)")
  let passing := (tests.filter (·.kind == "holds")).size
  let lines := results.filter (·.kind != "holds") |>.map fun r => s!"  {r.id}: {r.kind}: {r.detail}"
  s!"{file}: {passing} of {tests.size} hold\n{"\n".intercalate lines.toList}"

/-- Runs `path`, a file of the suite or a directory of `.cas` files, through `harness`. -/
meta def runSuite (harness : Harness) (path : System.FilePath)
    (inventory? : Option System.FilePath := none) : CommandElabM (Array TestResult) := do
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
  for file in files.qsort (·.toString < ·.toString) do
    try results := results ++ (← runFile harness file)
    catch error =>
      results := results.push {
        file := file.toString
        id := "(statement) infrastructure"
        kind := "internal"
        detail := ← error.toMessageData.toString
        fails := true }
  if let some inventory := inventory? then
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
  return results

/-- Runs one statement of the language, given as text, through `harness` within `scope`: its
outcome and the scope after it. -/
meta def runStatement (harness : Harness) (scope : Scope) (text : String) :
    CommandElabM (Outcome × Scope) := do
  let parsed ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
    | .ok s => pure s
    | .error e => throwError "not a statement of the language: {e}\n{text}"
  liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <| Realize.run harness scope parsed

/-- The harness of the manifest at `manifest?`, or of the installed leaves, with the
registrations it does not admit reported. -/
meta def loadHarness (manifest? : Option System.FilePath) : CommandElabM Harness := do
  let harness ← liftCoreM (Harness.load manifest?)
  for rejected in harness.rejected do
    logWarning m!"registration not admitted: {rejected}"
  return harness

syntax (name := casTestsCommand)
  "#cas_tests " str (&" manifest " str)? (&" reporting " str)? (&" inventory " str)? : command

@[command_elab casTestsCommand] meta def elabCasTests : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let manifest? := stx[2][1].isStrLit?.map fun s => (s : System.FilePath)
  let harness ← loadHarness manifest?
  let inventory? := stx[4][1].isStrLit?.map fun s => (s : System.FilePath)
  let results ← try runSuite harness path inventory? finally (harness.stop : IO Unit)
  let files := results.foldl (fun fs r => if fs.contains r.file then fs else fs.push r.file) #[]
  for file in files do logInfo (report file (results.filter (·.file == file)))
  if let some out := stx[3][1].isStrLit? then
    IO.FS.writeFile out (toJson results).pretty
  let failures := results.filter (·.fails)
  unless failures.isEmpty do
    throwError "the suite fails:\n{"\n".intercalate (failures.toList.map fun r =>
      s!"  {r.file}: {r.id}: {r.kind}: {r.detail}")}"

syntax (name := casStatementCommand) "#cas " str (&" manifest " str)? : command

@[command_elab casStatementCommand] meta def elabCasStatement : CommandElab := fun stx => do
  let some text := stx[1].isStrLit? | throwUnsupportedSyntax
  let manifest? := stx[2][1].isStrLit?.map fun s => (s : System.FilePath)
  let harness ← loadHarness manifest?
  let (outcome, _) ← try runStatement harness {} text finally (harness.stop : IO Unit)
  let shown := if outcome matches .holds then outcome.kind else s!"{outcome.kind}: {outcome.detail}"
  if outcome.fails then throwError shown else logInfo shown

end CasCatalogue.Language
