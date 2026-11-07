module

import CasCompiler.Parse
public meta import Lean.Elab.Command
meta import CasCompiler.Parse

open Lean Elab Command CasCompiler CasCatalogue.Language

private def jsonFile (path : String) : CommandElabM Json := do
  let .ok document := Json.parse (← IO.FS.readFile path)
    | throwError "the retained source inventory is not valid JSON"
  return document

private def sourceIdentities (entries : Array Json) : CommandElabM (Std.HashSet String) := do
  let mut identities : Std.HashSet String := {}
  for entry in entries do
    let .ok path := entry.getObjValAs? String "source"
      | throwError "the retained input has no original source path"
    let text ← IO.FS.readFile path
    let source ← SourceFile.parse path text
    unless source.context.input == text && source.context.fileName == path do
      throwError "parsing changed the original source bytes or file identity"
    for item in source.items do
      unless item.raw.getPos?.isSome && item.raw.getTailPos?.isSome do
        throwError "a parsed original item lost its byte positions"
      match item with
      | `(cas_item| test $identity:ident $_:str : $_:cas_stmt) =>
        let identity := identity.getId.toString
        if identities.contains identity then throwError "a retained source identity occurs twice"
        identities := identities.insert identity
      | `(cas_item| $_:cas_stmt) => pure ()
      | _ => throwError "an original item changed its public syntax category"
  return identities

run_cmd do
  let fixture ← jsonFile "scripts/probes/fixed_question_export_inputs.json"
  let permanent ← jsonFile "CasAcceptance/Permanent/admitted.json"
  for (selection, inventory) in #[
      ("permanentSources", permanent), ("extensionSources", fixture)] do
    let .ok entries := fixture.getObjValAs? (Array Json) selection
      | throwError "the complete retained source selection is absent"
    let .ok expected := (inventory.getObjVal? "assertions").bind Json.getObj?
      | throwError "the original identity inventory is absent"
    let observed ← sourceIdentities entries
    unless observed.size == expected.size && expected.toList.all (observed.contains ·.1) do
      throwError "the source parser changed the original complete identity inventory"

run_cmd do
  let prefix := "-- α\r\n\r\n"
  let binding := "let width := 3"
  let middle := "\r\nlet point((a, b)) := (a, b) in X → X\r\n\r\n"
  let question := "test parser.scope \"source\":\r\n  assert width = 3"
  let text := prefix ++ binding ++ middle ++ question
  let source ← SourceFile.parse "source-positions.cas" text
  unless source.items.size == 3 && source.context.input == text do
    throwError "file parsing changed consecutive declarations or source line endings"
  let some first := source.items[0]? | throwError "the source binding is absent"
  let some last := source.items[2]? | throwError "the source question is absent"
  unless first.raw.getPos?.map (·.byteIdx) == some prefix.utf8ByteSize &&
      last.raw.getPos?.map (·.byteIdx) ==
        some (prefix ++ binding ++ middle).utf8ByteSize do
    throwError "Unicode or carriage returns changed original byte positions"
  let some position := last.raw.getPos? | throwError "the source question has no location"
  unless (source.context.fileMap.toPosition position).line == 6 do
    throwError "the source question lost its original line"
  let empty ← SourceFile.parse "empty.cas" "-- source comment\n"
  unless empty.items.isEmpty do throwError "a comment-only source acquired a statement"
  let rejected ← try
    discard <| SourceFile.parse "malformed.cas" "let width := 3\nassert ("
    pure false
  catch _ => pure true
  unless rejected do throwError "malformed trailing source was accepted as a complete file"
