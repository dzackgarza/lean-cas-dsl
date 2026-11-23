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

/- Public hypotheses are source declarations, not injected native test parameters. The
ordinary question exporter must retain them as the original question's visible provenance. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let file ← SourceFile.parse "observer-scoped-declarations.cas"
    "let X ∈ Sets\nlet x ∈ X\nlet h : x = x\n\
     test observer.hypothesis \"scope\": assert x = x\n"
  let observation ← observeFile file empty
  unless observation.failures.isEmpty && observation.readings.size == 1 &&
      !observation.readings[0]!.question.isEmpty do
    throwError "the ordinary exporter did not read the public hypothetical source scope"
  let .ok context := observation.readings[0]!.sourceContext.getObjValAs? (Array Json) "context"
    | throwError "the public hypothesis lost its prepared original context"
  unless context.map (fun row => row.getObjValAs? String "name") ==
      #[.ok "X", .ok "x", .ok "h"] &&
      context.map (fun row => row.getObjValAs? String "role") ==
        #[.ok "parameter", .ok "parameter", .ok "hypothesis"] &&
      context.all (fun row => row.getObjValD "value" == Json.null) &&
      empty.context.entries.isEmpty do
    throwError "a hypothetical scope was defined, omitted, reordered or leaked"

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
  let .ok graph := question.getObjVal? "nativeExpressions"
    | throwError "the observer omitted its exact native graph"
  let .ok nodes := CasTools.NativeExpression.decodeNodes graph
    | throwError "the observer's native graph did not decode"
  let .ok index := context[3]!.getObjValAs? Nat "value"
    | throwError "the observer omitted the original definition value"
  let some value := nodes[index]? | throwError "the definition value is outside its native graph"
  unless (value.find? fun expression => match expression with
      | .mdata data _ => !(data.getString `CasCompiler.source.id).isEmpty
      | _ => false).isSome do
    throwError "the native snapshot lost its actual source identity metadata"
  let .ok instances := question.getObjValAs? (Array Json) "instances"
    | throwError "the observer omitted selected local dictionaries"
  unless instances.size == 1 && !first.proposition.isEmpty &&
      !observation.readings[2]!.question.isEmpty &&
      observation.readings[1]!.question.isEmpty &&
      observation.readings[3]!.question.isEmpty do
    throwError "the observer lost complete readings or manufactured a reading after failure"
  unless first.question == observation.readings[2]!.question do
    throwError "a failed question changed the later identity of the same original question"
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

/- SourceStatement.settled retains every conjunct. The public observer must retain those
ordered terms, their original scopes and spans, under one original assertion identity. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let firstParameter ← empty.assume `n (← nativeTerm "Nat")
  let initial ← firstParameter.assume `m (← nativeTerm "Nat")
  let file ← SourceFile.parse "observer-conjunction.cas"
    "let X := Fin(n)\n\
     test observer.first_settled \"typing\": assert n ∈ ℕ\n\
     test observer.second_settled \"typing\": assert m ∈ ℕ\n\
     test observer.conjunction \"typing\": assert n ∈ ℕ and m ∈ ℕ\n\
     test observer.reversed \"typing\": assert m ∈ ℕ and n ∈ ℕ\n"
  let observation ← observeFile file initial
  unless observation.failures.isEmpty && observation.readings.map (·.id) ==
      #["observer.first_settled", "observer.second_settled", "observer.conjunction",
        "observer.reversed"] do
    throwError "compound typing observation lost an original assertion or failed to read it"
  let nativeRoots (row : Reading) : TermElabM (Array Expr) := do
    let .ok graph := Json.parse row.proposition
      | throwError "a typing observation lost its native graph document"
    let .ok roots := CasTools.NativeExpression.decode graph
      | throwError "a typing observation's native graph did not decode"
    return roots
  let #[first] ← nativeRoots observation.readings[0]!
    | throwError "an individual typing judgement changed its singleton native graph"
  let #[second] ← nativeRoots observation.readings[1]!
    | throwError "an individual typing judgement changed its singleton native graph"
  if ← isDefEq first second then
    throwError "the two source parameters no longer distinguish conjunct order"
  for row in observation.readings.extract 0 2 do
    let .ok question := Json.parse row.question | throwError "a singleton identity did not parse"
    let .ok roots := question.getObjVal? "roots" | throwError "a singleton identity lost its root"
    let .ok _ := roots.getObjValAs? Nat "proposition"
      | throwError "a singleton typing identity changed its existing proposition shape"
    let .error _ := roots.getObjVal? "conjuncts"
      | throwError "a singleton typing identity acquired an aggregate wrapper"
  for (row, expected) in #[(observation.readings[2]!, #[first, second]),
      (observation.readings[3]!, #[second, first])] do
    let actual ← nativeRoots row
    unless actual.size == expected.size do
      throwError "a typing conjunction lost a native term"
    for index in [:expected.size] do
      checkWithKernel actual[index]!
      unless ← isDefEq actual[index]! expected[index]! do
        throwError "a typing conjunction changed or reordered its original terms"
    let .ok question := Json.parse row.question | throwError "a compound identity did not parse"
    let .ok roots := question.getObjVal? "roots" | throwError "a compound identity lost its roots"
    let .ok conjuncts := roots.getObjValAs? (Array Json) "conjuncts"
      | throwError "a compound identity lost its ordered judgements"
    let .ok snapshots := row.sourceContext.getObjValAs? (Array Json) "conjuncts"
      | throwError "a compound observation lost its source snapshots"
    unless conjuncts.size == 2 && snapshots.size == 2 do
      throwError "a compound identity or source snapshot lost a conjunct"
    let mut previousStop := 0
    for snapshot in snapshots do
      let .ok context := snapshot.getObjValAs? (Array Json) "context"
        | throwError "a typing conjunct lost its complete source context"
      unless context.size == 3 && (context[2]!.getObjValAs? String "name") == .ok "X" do
        throwError "a typing conjunct discarded the unused original let binding"
      let .ok graph := snapshot.getObjVal? "nativeExpressions"
        | throwError "a typing conjunct lost its exact source graph"
      let .ok #[_, _] := CasTools.NativeExpression.decode graph
        | throwError "a typing conjunct lost its source expression or type"
      let .ok start := snapshot.getObjValAs? Nat "startByte"
        | throwError "a typing conjunct lost its original start position"
      let .ok stop := snapshot.getObjValAs? Nat "stopByte"
        | throwError "a typing conjunct lost its original end position"
      unless previousStop ≤ start && start < stop do
        throwError "a typing conjunction changed its ordered original source spans"
      previousStop := stop
  unless observation.readings[2]!.question != observation.readings[3]!.question do
    throwError "reversing distinct typing judgements did not change their ordered identity"

/- Typed identity keeps binder annotations. Encoding the same accepted native terms in one
table or in separate tables must yield the same documents, including under a dependent binder. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let writtenExplicit ← withSynthesize <| elabTerm
    (← nativeTerm "fun (n : Nat) => fun (x : Fin n) => x") none
  let writtenImplicit ← withSynthesize <| elabTerm
    (← nativeTerm "fun (n : Nat) => fun {x : Fin n} => x") none
  let writtenExplicit ← instantiateMVars writtenExplicit
  let writtenImplicit ← instantiateMVars writtenImplicit
  checkWithKernel writtenExplicit
  checkWithKernel writtenImplicit
  unless writtenExplicit == writtenImplicit && !writtenExplicit.equal writtenImplicit do
    throwError "the native control did not preserve its distinct binder annotations"
  let standaloneExplicit ← CasCatalogue.Realize.termIdentity writtenExplicit
  let standaloneImplicit ← CasCatalogue.Realize.termIdentity writtenImplicit
  unless standaloneExplicit != standaloneImplicit do
    throwError "standalone typed identity discarded a native binder annotation"
  let shared ← CasCatalogue.Realize.TermTable.new
  let explicitRoot ← shared.encode writtenExplicit
  let implicitRoot ← shared.encode writtenImplicit
  unless (← shared.rootIdentity explicitRoot) == standaloneExplicit &&
      (← shared.rootIdentity implicitRoot) == standaloneImplicit do
    throwError "shared typed serialization merged distinct native binder annotations"
