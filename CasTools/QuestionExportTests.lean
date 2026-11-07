module

import CasTools.QuestionExport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects

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
  let .ok question := Json.parse first.question
    | throwError "the observer did not export the complete checked source question"
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
