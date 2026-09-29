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
derives. The suite is run over the installed realizations; a leaf never imports it.
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

syntax (name := casTestsCommand) "#cas_tests " str : command

/-- Runs the file `path` of the suite. -/
meta def runFile (path : System.FilePath) : CommandElabM Unit := do
  let path := path.toString
  let text ← IO.FS.readFile path
  let mut scope : Scope := {}
  let mut passing := 0
  let mut tests := 0
  let mut lines : Array String := #[]
  for item in items text do
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item path with
      | .ok s => pure s
      | .error e => throwError "{path}: not an item of the language: {e}\n{item}"
    let (id?, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) => (some id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => (none, s.raw)
      | _ => (none, parsed)
    let (outcome, scope') ← liftTermElabM <| withoutErrToSorry <|
      try run scope statement
      catch e => throwError "{path}: {id?.getD "statement"} is not a valid statement: \
        {e.toMessageData}\n{item}"
    scope := scope'
    let some id := id? | continue
    tests := tests + 1
    match outcome with
    | .holds => passing := passing + 1
    | .gap reason => lines := lines.push s!"  {id}: gap: {reason}"
    | .unavailable reason => lines := lines.push s!"  {id}: not exercised: {reason}"
    | .wrong message => throwError "{path}: {id} is wrong: {message}"
    | .malformed reason => throwError "{path}: {id}: malformed answer: {reason}"
  logInfo m!"{path}: {passing} of {tests} hold\n{"\n".intercalate lines.toList}"

@[command_elab casTestsCommand] meta def elabCasTests : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let path : System.FilePath := path
  unless ← path.isDir do return ← runFile path
  let files := (← path.readDir).filter (·.path.extension == some "cas") |>.map (·.path)
  for file in files.qsort (·.toString < ·.toString) do runFile file

end CasCatalogue.Language
