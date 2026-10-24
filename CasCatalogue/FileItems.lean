/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean

@[expose] public section

namespace CasCatalogue.Language

/-- A file item keeps its original one-based source line even when comments and
blank separators are omitted from the text passed to the statement parser. -/
structure SourceItem where
  text : String
  line : Nat
  deriving Inhabited, Repr

private structure ItemNesting where
  delimiters : Nat := 0
  comments : Nat := 0
  string : Bool := false
  quotedName : Bool := false
  escaped : Bool := false
  deriving Inhabited

private meta def ItemNesting.atTop (state : ItemNesting) : Bool :=
  state.delimiters == 0 && state.comments == 0 && !state.string && !state.quotedName

private meta partial def scanItemLine (state : ItemNesting) : List Char → ItemNesting
  | [] => state
  | c :: rest =>
    if state.string then
      if state.escaped then scanItemLine { state with escaped := false } rest
      else if c == '\\' then scanItemLine { state with escaped := true } rest
      else scanItemLine { state with string := c != '"' } rest
    else if state.quotedName then
      scanItemLine { state with quotedName := c != '»' } rest
    else match c, rest with
      | '/', '-' :: tail => scanItemLine { state with comments := state.comments + 1 } tail
      | '-', '/' :: tail => scanItemLine { state with comments := state.comments - 1 } tail
      | _, _ =>
        if state.comments > 0 then scanItemLine state rest
        else match c, rest with
          | '-', '-' :: _ => state
          | '"', _ => scanItemLine { state with string := true } rest
          | '«', _ => scanItemLine { state with quotedName := true } rest
          | '\'', '\\' :: _ :: '\'' :: tail => scanItemLine state tail
          | '\'', _ :: '\'' :: tail => scanItemLine state tail
          | '(', _ | '[', _ | '{', _ =>
              scanItemLine { state with delimiters := state.delimiters + 1 } rest
          | ')', _ | ']', _ | '}', _ =>
              scanItemLine { state with delimiters := state.delimiters - 1 } rest
          | _, _ => scanItemLine state rest

/-- Blank lines or new unindented statements separate file items. Delimited
terms, quoted text, proof blocks and an assertion following its test header stay
intact. Consecutive top-level bindings therefore require no empty separator. -/
meta def itemsWithLocations (text : String) : Array SourceItem := Id.run do
  let mut out := #[]
  let mut current := ""
  let mut firstLine := 1
  let mut nesting : ItemNesting := {}
  for (line, index) in (text.splitOn "\n").zipIdx do
    let t := line.trimAscii.toString
    if nesting.atTop && t.startsWith "--" then continue
    if nesting.atTop && t.isEmpty then
      unless current.isEmpty do out := out.push { text := current, line := firstLine }
      current := ""
    else
      let starts := line.startsWith "let " || line.startsWith "test " ||
        line.startsWith "assert "
      let awaitingAssertion := current.startsWith "test " &&
        current.trimAscii.toString.endsWith ":" && t.startsWith "assert "
      if nesting.atTop && starts && !awaitingAssertion && !current.isEmpty then
        out := out.push { text := current, line := firstLine }
        current := ""
      if current.isEmpty then firstLine := index + 1
      current := if current.isEmpty then line else current ++ "\n" ++ line
      nesting := scanItemLine nesting line.toList
  unless current.isEmpty do out := out.push { text := current, line := firstLine }
  return out

/-- The statement text of every complete file item, in original source order. -/
meta def items (text : String) : Array String :=
  (itemsWithLocations text).map (·.text)

end CasCatalogue.Language
