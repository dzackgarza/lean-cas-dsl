module

import CasTools.QuestionExport
meta import CasTools.QuestionExport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
meta import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
meta import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
meta import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests

open Lean Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Reconstructed diagnostic, not recovery of the missing historical driver.
   It reads unchanged fixed bindings through the production file-item, binding,
   claim and scope APIs. Each statement has a fresh production term scope and
   ordinary heartbeat budget. It stops at the first failed binding in each file.
   Questions are not interpreted or executed by this binding-only diagnostic.
   Exit zero means the report was written; reported failures remain failures. -/

structure FixedBindingFailure where
  binding : String
  line : Nat
  source : String
  stage : String
  kind : String
  detail : String
  deriving ToJson

structure FixedBindingFileReport where
  file : String
  bindingsChecked : Nat
  bindingsSucceeded : Nat
  failure : Option FixedBindingFailure
  deriving ToJson

meta def bindingFailure (binding stage : String) (item : SourceItem)
    (error : Exception) : TermElabM FixedBindingFailure := do
  let outcome ← Outcome.ofException error
  return { binding, line := item.line, source := item.text,
           stage, kind := outcome.kind, detail := outcome.detail }

meta def readFixedBindings (path : System.FilePath) : CommandElabM FixedBindingFileReport := do
  let file := path.toString
  let text ← IO.FS.readFile path
  let mut scope : Language.Scope := {}
  let mut checked := 0
  let mut succeeded := 0
  let mut firstFailure : Option FixedBindingFailure := none
  for item in itemsWithLocations text do
    let parsed ← match Parser.runParserCategory (← getEnv) `cas_item item.text file with
      | .ok parsed => pure parsed
      | .error detail =>
          firstFailure := some {
            binding := "(unparsed item)", line := item.line, source := item.text,
            stage := "parse", kind := "invalid", detail }
          break
    let (isTest, statement) := match parsed with
      | `(cas_item| test $_:ident $_:str : $s:cas_stmt) => (true, s.raw)
      | `(cas_item| $s:cas_stmt) => (false, s.raw)
      | _ => (false, parsed)
    if isTest then continue
    let extracted ← liftTermElabM <| tryCatchRuntimeEx
      (Except.ok <$> letBinding? statement)
      (fun error => return .error (← bindingFailure "(binding syntax)" "binding" item error))
    let .ok binding := extracted | do
      if let .error problem := extracted then firstFailure := some problem
      break
    let some (name, value) := binding | continue
    checked := checked + 1
    IO.eprintln s!"binding {file}:{item.line}: {name}"
    let problem ← liftTermElabM <| withoutErrToSorry <| withCurrHeartbeats <|
      tryCatchRuntimeEx (do
        let closedTerms ← IO.mkRef ({} : Std.HashMap String Value)
        discard <| (Language.claim scope statement).run { closedTerms := some closedTerms }
        pure none)
        (fun error => return some (← bindingFailure name.toString "binding" item error))
    if let some problem := problem then
      firstFailure := some problem
      break
    succeeded := succeeded + 1
    scope := scope.insert name value
  return { file, bindingsChecked := checked, bindingsSucceeded := succeeded,
           failure := firstFailure }

run_cmd do
  let inputs := (← IO.getEnv "CAS_FIXED_BINDING_INPUTS").getD "/workspace/scratch/08e8d69f9eb1/kernel-mvp-frozen-trials-20261025/positive-clarified-inputs.json"
  let output := (← IO.getEnv "CAS_FIXED_BINDING_REPORT").getD "/workspace/scratch/08e8d69f9eb1/kernel-verification-20261025/fixed-bindings-reconstructed-20261025.json"
  if ← (System.FilePath.mk output).pathExists then
    throwError "refuse to overwrite an earlier binding report: {output}"
  let .ok (.obj records) := Json.parse (← IO.FS.readFile inputs)
    | throwError "the fixed input manifest is not a JSON object: {inputs}"
  let mut paths : Array String := #[]
  for (_, record) in records.toList do
    let .ok path := record.getObjValAs? String "selectedPath"
      | throwError "a fixed input record has no selectedPath"
    if paths.contains path then throwError "duplicate fixed input path: {path}"
    paths := paths.push path
  let mut reports : Array FixedBindingFileReport := #[]
  for path in paths.qsort (· < ·) do
    reports := reports.push (← readFixedBindings path)
  IO.FS.writeFile output (toJson reports).pretty
  let failed := (reports.filter (·.failure.isSome)).size
  let checked := reports.foldl (fun total report => total + report.bindingsChecked) 0
  logInfo m!"fixed-binding diagnostic: {reports.size} files; {checked} bindings attempted; \
    {failed} files with a first failure. Exit success records diagnostic completion only."
