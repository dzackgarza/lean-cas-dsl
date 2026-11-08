module

import CasTools.QuestionExport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra

open Lean Meta Elab Term CasCompiler CasTools.QuestionExport

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the observer context did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `n (← nativeTerm "Nat")
  let hypotheses ← parameters.assume `h (← nativeTerm "n = n")
  let initial ← hypotheses.assume `chosen (← nativeTerm "Inhabited Nat") .instImplicit
  let file ← SourceFile.parse "observer-original.cas"
    "-- α\r\nlet X := Fin(n)\r\n\
     test observer.first \"scope\": assert X = X\r\n\
     test observer.unsupported \"source\": assert n + n = n\r\n\
     test observer.later \"scope\": assert X = X\r\n\
     let bad := n + n\r\n\
     test observer.blocked \"scope\": assert X = X\r\n"
  let observation ← observeFile file initial
  unless observation.readings.map (·.id) == #["observer.first", "observer.unsupported",
      "observer.later", "observer.blocked"] do
    throwError "the observer changed original question identities or source order"
  let first := observation.readings[0]!
  unless first.file == "observer-original.cas" && first.sourceLine == 3 &&
      first.source == "test observer.first \"scope\": assert X = X" do
    throwError "the observer lost original source bytes or line positions"
  let question := first.sourceContext
  let .ok context := question.getObjValAs? (Array Json) "context"
    | throwError "the observer omitted the question telescope"
  unless context.size == 4 && (context[1]!.getObjValAs? String "role") == .ok "hypothesis" &&
      (context[3]!.getObjValAs? String "name") == .ok "X" do
    throwError "the observer shortened or changed the actual preceding source context"
  let .ok instances := question.getObjValAs? (Array Json) "instances"
    | throwError "the observer omitted selected local dictionaries"
  unless instances.size == 1 && !first.proposition.isEmpty &&
      !observation.readings[2]!.question.isEmpty &&
      observation.readings[1]!.question.isEmpty &&
      observation.readings[3]!.question.isEmpty do
    throwError "the observer lost complete readings or manufactured a reading after failure"
  unless observation.failures.size == 3 &&
      observation.failures[0]!.kind == "unsupported" &&
      observation.failures[0]!.stage == "interpretation" &&
      observation.failures[1]!.id == "bad" && observation.failures[1]!.stage == "binding" &&
      observation.failures[2]!.cause.map (·.id) == some "bad" do
    throwError "the observer lost a stage-specific error or the actual blocking definition"
  unless initial.context.entries.size == 3 do
    throwError "source observation mutated its input session"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let initial ← empty.assume `n (← nativeTerm "Nat")
  let file ← SourceFile.parse "observer-identifiers.cas"
    "let inventory := Fin(n)\nlet readings := inventory\nlet failures := readings\n\
     test observer.names \"scope\": assert failures = inventory\n"
  let observation ← observeFile file initial
  unless observation.failures.isEmpty && observation.readings.size == 1 &&
      !observation.readings[0]!.question.isEmpty do
    throwError "the public observer changed ordinary source binding names"

run_cmd Lean.Elab.Command.liftTermElabM do
  let observe (fileName label leading : String) : TermElabM Reading := do
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let empty ← SourceSession.empty identities
    let initial ← empty.assume `n (← nativeTerm "Nat")
    let file ← SourceFile.parse fileName <| leading ++ "let X := Fin(n)\n" ++
      "test observer.stable \"" ++ label ++ "\": assert X = X\n"
    let result ← observeFile file initial
    unless result.failures.isEmpty && result.readings.size == 1 do
      throwError "the source identity control did not produce its complete reading"
    return result.readings[0]!
  let first ← observe "first-location.cas" "first source" ""
  let second ← observe "second-location.cas" "second source" "-- diagnostic location\n"
  unless first.question == second.question do
    throwError "source provenance or fresh worker bindings changed the native question identity"
  unless first.file != second.file && first.provenance != second.provenance &&
      first.sourceLine != second.sourceLine && first.sourceContext != second.sourceContext do
    throwError "the observer discarded original source provenance"

run_cmd Lean.Elab.Command.liftTermElabM do
  let observe (fileName label leading : String) : TermElabM Reading := do
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let empty ← SourceSession.empty identities
    let initial ← empty.assume `n (← nativeTerm "Nat")
    let file ← SourceFile.parse fileName <| leading ++
      "let X := Fin(n)\nlet V := Vec(X, 2)\n" ++
      "let diagonal(i) := (i, i) in X → V\n" ++
      "test observer.tuple \"" ++ label ++ "\": assert diagonal = diagonal\n"
    let result ← observeFile file initial
    unless result.failures.isEmpty && result.readings.size == 1 &&
        !result.readings[0]!.proposition.isEmpty do
      throwError "the tuple observer did not retain the complete native proposition"
    return result.readings[0]!
  let first ← observe "first-tuple.cas" "first tuple source" ""
  let second ← observe "second-tuple.cas" "second tuple source" "-- tuple provenance\n"
  unless first.question == second.question && first.sourceContext != second.sourceContext do
    throwError "tuple observation changed its native question or discarded source provenance"
