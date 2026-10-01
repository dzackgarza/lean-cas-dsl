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
recorded; a wrong answer, a malformed answer and an invalid statement fail the build. The report
of gaps is the list of implementations the suite derives. A leaf never sees the suite.
`#cas_tests "dir" reporting "out.json"` also writes every result as JSON (`cas-harness` runs it
over a given manifest).

`#cas "statement"` runs one statement of the language the same way (a notebook cell): its outcome
is reported, and a wrong answer, a malformed answer or an invalid statement is an error.
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
  /-- `holds`, `gap`, `unavailable`, `wrong`, `malformed` or `invalid`. -/
  kind : String
  detail : String := ""
  deriving ToJson, FromJson, Inhabited

/-- Whether a result fails the suite: a wrong or malformed answer, or an invalid statement. -/
def TestResult.fails (r : TestResult) : Bool :=
  r.kind == "wrong" || r.kind == "malformed" || r.kind == "invalid"

end

/-- Runs the file `path` of the suite through `harness`: the outcome of each test. An invalid
`let` is reported as an invalid statement of the file. -/
meta def runFile (harness : Harness) (path : System.FilePath) :
    CommandElabM (Array TestResult) := do
  let path := path.toString
  let text ← IO.FS.readFile path
  let mut scope : Scope := {}
  let mut results : Array TestResult := #[]
  for item in items text do
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item path with
      | .ok s => pure s
      | .error e => throwError "{path}: not an item of the language: {e}\n{item}"
    let (id?, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) => (some id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => (none, s.raw)
      | _ => (none, parsed)
    let id := id?.getD s!"(statement) {item}"
    let attempt ← liftTermElabM <| withoutErrToSorry <|
      -- Each test has its own heartbeat budget; a timeout fails that test, not the run.
      tryCatchRuntimeEx
        (do return Except.ok (← withCurrHeartbeats (Realize.run harness scope statement)))
        fun e => do return Except.error (← e.toMessageData.toString)
    match attempt with
    | .error message =>
        results := results.push { file := path, id, kind := "invalid", detail := message }
    | .ok (outcome, scope') =>
        scope := scope'
        if id?.isNone then continue
        let (kind, detail) := match outcome with
          | .holds => ("holds", "")
          | .gap reason => ("gap", reason)
          | .unavailable reason => ("unavailable", reason)
          | .wrong message => ("wrong", message)
          | .malformed reason => ("malformed", reason)
        results := results.push { file := path, id, kind, detail }
  return results

/-- The report of a file's results. -/
meta def report (file : String) (results : Array TestResult) : String :=
  let tests := results.filter (!·.id.startsWith "(statement)")
  let passing := (tests.filter (·.kind == "holds")).size
  let lines := results.filter (·.kind != "holds") |>.map fun r => s!"  {r.id}: {r.kind}: {r.detail}"
  s!"{file}: {passing} of {tests.size} hold\n{"\n".intercalate lines.toList}"

/-- Runs `path`, a file of the suite or a directory of `.cas` files, through `harness`. -/
meta def runSuite (harness : Harness) (path : System.FilePath) :
    CommandElabM (Array TestResult) := do
  unless ← path.isDir do return ← runFile harness path
  let files := (← path.readDir).filter (·.path.extension == some "cas") |>.map (·.path)
  let mut results := #[]
  for file in files.qsort (·.toString < ·.toString) do
    results := results ++ (← runFile harness file)
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
  "#cas_tests " str (&" manifest " str)? (&" reporting " str)? : command

@[command_elab casTestsCommand] meta def elabCasTests : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let manifest? := stx[2][1].isStrLit?.map fun s => (s : System.FilePath)
  let harness ← loadHarness manifest?
  let results ← try runSuite harness path finally (harness.stop : IO Unit)
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
  let attempt : CommandElabM (Except String Outcome) := do
    try return .ok (← runStatement harness {} text).1
    -- not a reading fallback: an invalid statement is reported as such, by its message
    catch e => return .error (← e.toMessageData.toString)
  let outcome ← try attempt finally (harness.stop : IO Unit)
  match outcome with
  | .error message => throwError "invalid: {message}"
  | .ok .holds => logInfo m!"holds"
  | .ok (.gap reason) => logInfo m!"gap: {reason}"
  | .ok (.unavailable reason) => logInfo m!"unavailable: {reason}"
  | .ok (.wrong message) => throwError "wrong: {message}"
  | .ok (.malformed reason) => throwError "malformed: {reason}"

end CasCatalogue.Language
