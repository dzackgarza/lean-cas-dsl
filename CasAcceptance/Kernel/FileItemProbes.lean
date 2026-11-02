/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.FileItems
meta import CasCatalogue.FileItems
public meta import Lean.Elab.Term.TermElabM

/-! Mechanical file-boundary checks; these strings state no mathematical assertions. -/

open Lean Elab Term CasCatalogue.Language

run_elab do
  let source := "-- heading\nlet A := first\nlet B := second\n\n" ++
    "test boundary \"source\":\n  assert B\nlet C := third\n"
  let actual := itemsWithLocations source
  unless actual.map (·.text) == #["let A := first", "let B := second",
      "test boundary \"source\":\n  assert B", "let C := third"] &&
      actual.map (·.line) == #[2, 3, 5, 7] do
    throwError "consecutive declarations changed an item or its original source line"
  let unindented := "test boundary \"source\":\nassert retained\nassert separate"
  unless items unindented == #["test boundary \"source\":\nassert retained",
      "assert separate"] do
    throwError "an unindented test body was separated from its assertion identity"
  let trailing := "let A := first  \nlet B := second\t\nassert retained  "
  unless items trailing == #["let A := first  ", "let B := second\t", "assert retained  "] do
    throwError "trailing whitespace was mistaken for statement indentation"
  let proof := "let A := supplied(proof {by\n\nlet retained := \"{\"\n" ++
    "exact retained\n})\nlet B := next"
  unless items proof == #["let A := supplied(proof {by\n\nlet retained := \"{\"\n" ++
      "exact retained\n})", "let B := next"] do
    throwError "a proof block or quoted delimiter was split into independent statements"
  let comments := "let A := supplied( /- outer /- nested -/\nlet ignored := }\n-/ first)\n" ++
    "let B := «name{» -- an unmatched comment delimiter }\nlet C := next"
  unless (items comments).size == 3 do
    throwError "a nested comment or quoted identifier changed item boundaries"
  let character := "let A := supplied(proof {by\nlet retained := '}'\n" ++
    "let escaped := '\\''\nexact retained\n})\nlet B := next"
  unless (items character).size == 2 do
    throwError "a character literal changed a proof block's delimiter depth"

run_elab do
  let directory : System.FilePath := "tests/acceptance/proposals/" ++
    "independent-extension-reconstruction-20261024/completion"
  let negative ← IO.FS.readFile (directory / "rx09-constant-one-rejection.cas")
  let fixedQuestion ← IO.FS.readFile (directory / "rx10-fixed-execution-question.cas")
  let negativeItems := itemsWithLocations negative
  unless negativeItems.size == 5 && (items fixedQuestion).size == 9 do
    throwError "an unchanged extension input did not retain its individual top-level statements"
  let some rejected := negativeItems.back? | unreachable!
  unless rejected.text == "let impossibleAdmission := constantOne in Summable(Y, indices)" &&
      (negative.splitOn "\n")[rejected.line - 1]? == some rejected.text do
    throwError "the unchanged negative admission lost its actual source location"
