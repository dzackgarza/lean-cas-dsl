/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Language
public meta import CasCatalogue.Language

public section

/-!
# The acceptance suite: files of statements in the language

`#cas_tests "tests/acceptance/f.cas"` runs a file of the language, and `#cas_tests "dir"` every
`.cas` file of `dir`. Items are separated by blank
lines; lines beginning with `--` are comments. An item is `test id "source": statement`, a
statement admitted permanently (`scripts/check_acceptance_permanent.py`), whose expected value comes
from `source`; or a bare `let`. The file's `let`s scope over the items after them.

Each test's outcome is reported. A statement that holds, a gap (`NoImplementation`, an ambiguous
realization) and an unavailable backend are recorded; a wrong answer, a malformed answer and an
invalid statement fail the build. The report of gaps is the list of implementations the suite
derives. The suite is run over the installed realizations; a leaf never imports it. `#cas_tests "dir"
reporting "out.json"` also writes every result as JSON (`cas-harness` runs it over given leaves).
-/

open Lean Elab Command Term

namespace CasCatalogue.Language

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

/-- Runs the file `path` of the suite: the outcome of each test. An invalid `let` is reported as
an invalid statement of the file. -/
meta def runFile (path : System.FilePath) : CommandElabM (Array TestResult) := do
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
      try return Except.ok (← run scope statement)
      catch e => return Except.error (← e.toMessageData.toString)
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

/-- Runs `path`, a file of the suite or a directory of `.cas` files. -/
meta def runSuite (path : System.FilePath) : CommandElabM (Array TestResult) := do
  unless ← path.isDir do return ← runFile path
  let files := (← path.readDir).filter (·.path.extension == some "cas") |>.map (·.path)
  let mut results := #[]
  for file in files.qsort (·.toString < ·.toString) do results := results ++ (← runFile file)
  return results

syntax (name := casTestsCommand) "#cas_tests " str (&" reporting " str)? : command

@[command_elab casTestsCommand] meta def elabCasTests : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let results ← runSuite path
  let files := results.foldl (fun fs r => if fs.contains r.file then fs else fs.push r.file) #[]
  for file in files do logInfo (report file (results.filter (·.file == file)))
  if let some out := stx[2][1].isStrLit? then
    IO.FS.writeFile out (toJson results).pretty
  let failures := results.filter (·.fails)
  unless failures.isEmpty do
    throwError "the suite fails:\n{"\n".intercalate (failures.toList.map fun r =>
      s!"  {r.file}: {r.id}: {r.kind}: {r.detail}")}"

end CasCatalogue.Language
