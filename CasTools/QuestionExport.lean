/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Realize
public import CasCatalogue.FileItems
public import Lean.Elab.Frontend
public import CasTools.QuestionExportData
public meta import CasCatalogue.Realize
public meta import CasCatalogue.FileItems
public meta import CasTools.QuestionExportData

@[expose] public section

/-!
# Read-only export of the fixed questions

`cas-question-export --readings FILE --failures FILE [--suite DIR] [--inventory FILE]
[--import Qualified.Module]` reads the suite with the production parser and
`Realize.interpret`. It never constructs a harness, discharges a claim, loads a leaf
manifest or evaluates a prepared question. Each reading carries the unmodified complete
typed question/operation snapshot and its display from `TypedQuestion.identity`.

Unread questions have empty snapshots and separate stage-tagged diagnostics. The fixed
inventory is checked without changing it. A failed binding remains in the original
syntactic scope; it cannot become a fresh free variable in a later assertion. A binding
that cannot even be parsed blocks the rest of that file's scope explicitly.

The failure report also records the selected imports and their resolved module paths.
These are environment observations, not revision authentication. In particular, the
historical revision label read by `interpret` is not evidence for the sources used to
build the loaded modules. Keep independent source/build provenance with the export.
Neither exit success nor readable coverage accepts a mathematical reading or migration.
-/

open Lean Elab Command Term
open CasCatalogue.Language

namespace CasCatalogue.Tools.QuestionExport

meta def failure (file id stage : String) (error : Exception)
    (completedStages : Array (String × Nat) := #[]) : TermElabM Failure := do
  let outcome ← Outcome.ofException error
  return { file, id, stage, kind := outcome.kind, detail := outcome.detail, completedStages }

/-- Read one file with the same item/parser/scope APIs as the production runner. -/
meta def readFile (path : System.FilePath) : CommandElabM Export := do
  let file := path.toString
  let text ← IO.FS.readFile path
  let mut result : Export := {}
  let mut scope : Language.Scope := {}
  let mut blockedScope := false
  let sourceItems := items text
  for index in [:sourceItems.size] do
    let item := sourceItems[index]!
    let fallback := s!"(statement) item {index + 1}"
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item file with
      | .ok parsed => pure parsed
      | .error detail =>
          result := { result with failures := result.failures.push {
            file, id := fallback, stage := "parse", kind := "invalid", detail } }
          -- No guessed identifier is inserted into the scope. The inventory below
          -- retains every omitted admitted ID even when its syntax is unreadable.
          if !item.startsWith "test " then blockedScope := true
          continue
    let (id?, statement) := match parsed with
      | `(cas_item| test $id:ident $_:str : $s:cas_stmt) => (some id.getId.toString, s.raw)
      | `(cas_item| $s:cas_stmt) => (none, s.raw)
      | _ => (none, parsed)
    let id := id?.getD fallback
    IO.eprintln s!"reading {file}: {id}"
    let binding ← liftTermElabM <| tryCatchRuntimeEx
      (Except.ok <$> letBinding? statement)
      (fun error => return .error (← failure file id "binding" error))
    let .ok binding := binding | do
      if let .error problem := binding then
        result := { result with failures := result.failures.push problem }
      if id?.isSome then
        result := { result with readings := result.readings.push { file, id } }
      blockedScope := true
      continue
    if let some (name, value) := binding then
      if id?.isNone then
        let problem ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
          tryCatchRuntimeEx (do
            let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
            discard <| (Language.claim scope statement).run { closedTerms := some closedTerms }
            pure none)
            (fun error => return some (← failure file name.toString "binding" error))
        -- Preserve even a failing fixed binding; dependent questions must read its
        -- original term, never reinterpret its name as an unbound variable.
        scope := scope.insert name value
        if let some problem := problem then
          result := { result with failures := result.failures.push problem }
        continue
    if blockedScope then
      result := { result with
        readings := result.readings.push { file, id },
        failures := result.failures.push {
          file, id, stage := "scope", kind := "internal",
          detail := "a preceding binding could not be parsed; the original scope is unavailable" } }
      continue
    let stages ← IO.mkRef (#[] : Array (String × Nat))
    let interpreted : Except Failure Reading ←
      liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
      tryCatchRuntimeEx (do
        let question ← Realize.interpret scope statement (some stages)
        pure (.ok ({
          file, id, question := question.identity.1,
          proposition := question.identity.2 } : Reading)))
        (fun error => return .error (← failure file id "interpretation" error (← stages.get)))
    match interpreted with
    | .ok reading => result := { result with readings := result.readings.push reading }
    | .error problem => result := { result with
        readings := result.readings.push { file, id },
        failures := result.failures.push problem }
  return result

meta def readSuite (suite : String) (required : Array String) : CommandElabM Export := do
  let path : System.FilePath := suite
  let files ← if ← path.isDir then
      pure ((← path.readDir).filter (·.path.extension == some "cas") |>.map (·.path))
    else pure #[path]
  let mut result : Export := {}
  for file in files.qsort (·.toString < ·.toString) do
    try
      let next ← readFile file
      result := { readings := result.readings ++ next.readings,
                  failures := result.failures ++ next.failures }
    catch error =>
      result := { result with failures := result.failures.push {
          file := file.toString, id := "(statement) file", stage := "file", kind := "internal",
          detail := ← error.toMessageData.toString } }
  return checkInventory suite required result

syntax (name := exportQuestionsCommand)
  "#cas_export_questions " str &" inventory " str &" readings " str &" failures " str : command

@[command_elab exportQuestionsCommand] meta def elabExportQuestions : CommandElab := fun stx => do
  let some suite := stx[1].isStrLit? | throwUnsupportedSyntax
  let some inventory := stx[3].isStrLit? | throwUnsupportedSyntax
  let some readings := stx[5].isStrLit? | throwUnsupportedSyntax
  let some failures := stx[7].isStrLit? | throwUnsupportedSyntax
  let o : Options := { suite, inventory, readings, failures }
  let required ← inventoryIds inventory
  let result ← readSuite suite required
  let imports := (← getEnv).imports.map (·.module)
  let observed := (#[`CasCatalogue.Realize, `LeanCategories.Catalogue, `CasContract.Port] ++ imports)
  let moduleFiles ← observed.mapM fun name => do
    return Json.mkObj [("module", toJson name.toString),
      ("olean", toJson (← findOLean name).toString)]
  let provenance := Json.mkObj [
    ("leanVersion", toJson Lean.versionString),
    ("imports", toJson (imports.map Name.toString)), ("moduleFiles", Json.arr moduleFiles)]
  writeExport o required result provenance
  logInfo m!"question export: {required.size} required; {result.failures.size} interpretation/infrastructure diagnostics"
  unless result.failures.isEmpty do
    throwError "some questions or their fixed contexts could not be read; see {failures}"

def main (args : List String) : IO UInt32 := do
  let mut o : Options := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--suite" :: value :: more => o := { o with suite := value }; rest := more
    | "--inventory" :: value :: more => o := { o with inventory := value }; rest := more
    | "--readings" :: value :: more => o := { o with readings := value }; rest := more
    | "--failures" :: value :: more => o := { o with failures := value }; rest := more
    | "--import" :: value :: more =>
        o := { o with imports := o.imports.push value.toName }; rest := more
    | _ =>
        IO.eprintln "usage: cas-question-export --readings FILE --failures FILE [--suite DIR] [--inventory FILE] [--import Qualified.Module]"
        return 2
  if o.readings.isEmpty || o.failures.isEmpty || o.readings == o.failures then
    IO.eprintln "cas-question-export requires distinct --readings and --failures output files"
    return 2
  let mut required := #[]
  try
    required ← inventoryIds o.inventory
    IO.FS.writeFile o.readings ""
    IO.FS.writeFile o.failures ""
    initSearchPath (← findSysroot)
    unsafe Lean.enableInitializersExecution
    let modules := #[`CasTools.QuestionExport] ++ o.imports
    let env ← importModules (modules.map fun module => { module }) {} (loadExts := true)
    let quote (s : String) := (toJson s).compress
    let command := s!"#cas_export_questions {quote o.suite} inventory {quote o.inventory} readings {quote o.readings} failures {quote o.failures}\n"
    let state ← IO.processCommands (Parser.mkInputContext command "<cas-question-export>") {}
      (Command.mkState env {} {})
    for message in state.commandState.messages.toList do IO.eprintln (← message.toString)
    if (← IO.FS.readFile o.readings).isEmpty || (← IO.FS.readFile o.failures).isEmpty then
      throw <| IO.userError "export failed before producing the reading files"
    return if state.commandState.messages.hasErrors then 1 else 0
  catch error =>
    let detail := s!"question export infrastructure failure: {error}"
    IO.eprintln detail
    let result := checkInventory o.suite required { failures := #[
      { file := o.suite, id := "(statement) infrastructure", stage := "infrastructure", kind := "internal", detail }] }
    writeExport o required result (Json.mkObj [("requestedImports", toJson (o.imports.map Name.toString))])
    return 1

end CasCatalogue.Tools.QuestionExport
