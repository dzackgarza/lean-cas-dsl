module

public import CasTools.QuestionObservation
public meta import CasTools.QuestionObservation
public import LeanCategories.Catalogue
public import CasContract.Port
public import Lean.Elab.Command

@[expose] public section

namespace CasTools.QuestionExport

open Lean Meta Elab Term Command CasCompiler

private meta def sourceFiles (suite : System.FilePath) : IO (Array System.FilePath) := do
  if ← suite.isDir then
    let files := (← suite.readDir).filterMap fun entry =>
      if entry.path.extension == some "cas" then some entry.path else none
    return files.qsort (fun left right => left.toString < right.toString)
  unless suite.extension == some "cas" do
    throw <| IO.userError "question export requires a source file or a directory of .cas files"
  return #[suite]

private meta def provenance : CommandElabM Json := do
  let env ← getEnv
  let imports := env.header.imports.map (·.module)
  let observed := #[`CasCompiler.Context, `CasCompiler.Elaborate, `CasCompiler.Surface,
    `CasCompiler.Resolve, `CasCompiler.SourceCarrier, `CasCompiler.SourcePattern,
    `CasCompiler.SourceNumeral, `CasCompiler.SourceTuple, `CasCompiler.SourceOperation,
    `CasCompiler.SourceLimit,
    `CasCompiler.ReadExpression,
    `CasCompiler.Read,
    `LeanCategories.Catalogue, `CasContract.Port,
    `CasTools.QuestionObservation, `CasCatalogue.QuestionIdentity] ++ imports
  let modules ← observed.mapM fun name => do
    unless env.header.modules.any (·.module == name) do
      throwError "the question observer did not load required module {name}"
    let path ← IO.FS.realPath (← findOLean name)
    return Json.mkObj [("module", toJson (name.toString (escape := false))),
      ("olean", toJson path.toString)]
  return Json.mkObj [("leanVersion", toJson Lean.versionString),
    ("imports", toJson (imports.map (·.toString (escape := false)))),
    ("moduleFiles", toJson modules),
    ("reader", toJson "CasCompiler.SourceSession.readStatement")]

syntax (name := exportQuestions) "#cas_export_questions " str &"inventory " str
  &"readings " str &"failures " str : command

/-- Export each fixed original ID through the native observer, with full failures and actual
loaded module provenance. Inventory checks establish completeness only; independent assessment
owns mathematical meaning. Reuse: native Json, FilePath, exclusive FS.writeNew and environment
import metadata. Source: T029 and scripts/ci_kernel_candidate.py's complete-reading protocol. -/
@[command_elab exportQuestions] meta def elabExportQuestions : CommandElab := fun stx => do
  let `(command| #cas_export_questions $suite:str inventory $inventoryFile:str
      readings $readingsFile:str failures $failuresFile:str) := stx
    | throwUnsupportedSyntax
  let readingsPath : System.FilePath := readingsFile.getString
  let failuresPath : System.FilePath := failuresFile.getString
  if readingsPath == failuresPath || (← readingsPath.pathExists) ||
      (← failuresPath.pathExists) then
    throwError "question export requires distinct new output files"
  let .ok inventoryJson := Json.parse (← IO.FS.readFile inventoryFile.getString)
    | throwError "the original question inventory is not valid JSON"
  let .ok expected := (inventoryJson.getObjVal? "assertions").bind Json.getObj?
    | throwError "the original question inventory has no assertion map"
  let files ← sourceFiles suite.getString
  let mut observation : Observation := {}
  for path in files do
    let text ← IO.FS.readFile path
    let next ← liftTermElabM do
      let file ← SourceFile.parse path.toString text
      let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
      observeFile file (← SourceSession.empty identities)
    observation := {
      «readings» := observation.readings ++ next.readings,
      «failures» := observation.failures ++ next.failures }
  let mut actual : Std.HashSet String := {}
  for row in observation.readings do
    if actual.contains row.id then throwError "duplicate original question identity: {row.id}"
    actual := actual.insert row.id
  unless actual.size == expected.size && expected.toList.all (actual.contains ·.1) do
    throwError "the original question inventory differs from the complete selected source IDs"
  let unreadable := (observation.readings.filter fun row =>
    row.question.isEmpty || row.proposition.isEmpty).map (·.id)
  let document := Json.mkObj [("requiredCount", toJson expected.size),
    ("readableCount", toJson (observation.readings.size - unreadable.size)),
    ("unreadableIds", toJson (unreadable.qsort (· < ·))),
    ("failures", toJson observation.failures), ("provenance", ← provenance)]
  -- writeNew is the native O_EXCL boundary; existing evidence cannot be overwritten.
  IO.FS.withFile readingsPath .writeNew fun output =>
    IO.FS.withFile failuresPath .writeNew fun diagnostic => do
      output.putStrLn (toJson observation.readings).compress
      diagnostic.putStrLn document.compress
  unless observation.failures.isEmpty do
    logError "question export contains source failures; inspect its structured failure document"

end CasTools.QuestionExport
