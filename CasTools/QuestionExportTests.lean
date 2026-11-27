module

import CasTools.QuestionExport
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

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


-- Public lexical scopes retain the exact inner telescope/categories in the exported
-- question and restore the outer source scope for the next original labeled item.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let file ← SourceFile.parse "scoped-export.cas"
    "let outside := Fin(3)\ncontext do\n  let R ∈ CommutativeRings\n  let x ∈ R\n  \
     let one := 1 in R\n  assume h : x = one\n  \
     test scoped.inside \"local hypothesis\": assert x = one using (proof(h))\nend\n\
     test scoped.after \"outer scope\": assert outside = outside\n"
  let observation ← observeFile file empty
  unless observation.failures.isEmpty &&
      observation.readings.map (·.id) == #["scoped.inside", "scoped.after"] do
    throwError "scoped export changed the original questions or failed their source readings"
  let inside := observation.readings[0]!
  let afterScope := observation.readings[1]!
  unless inside.file == "scoped-export.cas" && inside.sourceLine == 7 &&
      inside.source ==
        "test scoped.inside \"local hypothesis\": assert x = one using (proof(h))" &&
      inside.provenance == "local hypothesis" do
    throwError "scoped export changed the original local assertion's source provenance"
  let .ok entries := inside.sourceContext.getObjValAs? (Array Json) "context"
    | throwError "the scoped question omitted its original telescope"
  let names := #["outside", "R", "x", "one", "h"]
  let roles := #["definition", "parameter", "parameter", "definition", "hypothesis"]
  unless entries.size == names.size do
    throwError "scoped export shortened the original conditional context"
  for entry in entries, name in names, role in roles do
    unless entry.getObjValAs? String "name" == .ok name &&
        entry.getObjValAs? String "role" == .ok role do
      throwError "scoped export changed an original declaration or assumption role"
  let .ok categories := inside.sourceContext.getObjValAs? (Array Json) "categories"
    | throwError "the scoped question omitted its original category selections"
  let category ← selectCategory (← CasCatalogue.semanticState) "CommutativeRings"
  unless categories.size == entries.size &&
      categories[1]!.getObjValAs? String "expression" == .ok (reprStr category.expression) do
    throwError "scope exit replaced the abstract ring's actual selected category"
  let .ok afterEntries := afterScope.sourceContext.getObjValAs? (Array Json) "context"
    | throwError "the following outer question omitted its source telescope"
  unless afterEntries.size == 1 &&
      afterEntries[0]!.getObjValAs? String "name" == .ok "outside" &&
      empty.context.entries.isEmpty do
    throwError "scoped export leaked a child binding or mutated its input session"
  let .ok document := Json.parse inside.proposition
    | throwError "the complete scoped proposition is not a native graph"
  let .ok #[proposition] := CasTools.NativeExpression.decode document
    | throwError "the complete scoped proposition did not decode"
  unless !proposition.hasFVar && !proposition.hasLooseBVars do
    throwError "the scoped proposition escaped its original local hypotheses"
  checkWithKernel proposition
  let .ok graph := inside.sourceContext.getObjVal? "nativeExpressions"
    | throwError "the scoped snapshot omitted its exact native graph"
  let .ok nodes := CasTools.NativeExpression.decodeNodes graph
    | throwError "the scoped source graph did not decode"
  let .ok native := inside.sourceContext.getObjVal? "native"
    | throwError "the scoped snapshot omitted the original source term"
  let .ok index := native.getObjValAs? Nat "expression"
    | throwError "the scoped snapshot omitted its original expression reference"
  let some body := nodes[index]? | throwError "the scoped expression is outside its graph"
  let mut closed := body
  for entry in entries.reverse do
    let .ok nameJson := entry.getObjVal? "nativeName"
      | throwError "a scoped native binder lost its name"
    let .ok name := CasTools.NativeExpression.nameFromJson nameJson
      | throwError "a scoped native binder name did not decode"
    let .ok typeIndex := entry.getObjValAs? Nat "type"
      | throwError "a scoped native binder lost its type"
    let some type := nodes[typeIndex]? | throwError "a scoped binder type is outside its graph"
    let .ok valueIndex := entry.getObjValAs? (Option Nat) "value"
      | throwError "a scoped native binder lost its declaration kind"
    let .ok nondep := entry.getObjValAs? Bool "nondep"
      | throwError "a scoped native let lost its dependency information"
    let .ok info := entry.getObjValAs? BinderInfo "nativeBinderInfo"
      | throwError "a scoped native binder lost its annotation"
    match valueIndex with
    | none => closed := .forallE name type closed info
    | some valueIndex =>
      let some value := nodes[valueIndex]? | throwError "a scoped definition is outside its graph"
      closed := .letE name type value closed nondep
  unless closed.equal proposition do
    throwError "the exported proposition discarded or changed its actual local assumptions"
  checkWithKernel closed

-- A source error blocks its actual local continuation without poisoning the parent
-- scope or dropping the original identity of the blocked question.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let file ← SourceFile.parse "scoped-export-failure.cas"
    "let outside := Fin(3)\ncontext do\n  let X ∈ Sets\n  \
     let bad := t030_unregistered_input\n  \
     test scoped.blocked \"local failure\": assert X = X\nend\n\
     test scoped.recovered \"outer scope\": assert outside = outside\n"
  let observation ← observeFile file empty
  unless observation.readings.map (·.id) == #["scoped.blocked", "scoped.recovered"] &&
      observation.readings[0]!.question.isEmpty &&
      !observation.readings[1]!.question.isEmpty do
    throwError "a local source failure changed or falsely established an original question"
  unless observation.failures.size == 2 && observation.failures[0]!.id == "bad" &&
      observation.failures[0]!.kind == "invalid" && observation.failures[0]!.stage == "binding" &&
      observation.failures[1]!.id == "scoped.blocked" &&
      observation.failures[1]!.cause.map (·.id) == some "bad" do
    throwError "scoped export lost the exact failed declaration and its local blocking cause"

private def exportedDocument (text : String) : TermElabM Json := do
  let .ok document := Json.parse text
    | throwError "an exported native or canonical document did not parse"
  return document

private def exportedNativeRoots (reading : Reading) : TermElabM (Array Expr) := do
  let .ok roots := CasTools.NativeExpression.decode (← exportedDocument reading.proposition)
    | throwError "an exported typed reading did not decode"
  return roots

-- These controls deliberately have empty native scopes, so a ClosedTerm descriptor's
-- body is closed and can be compared directly with the canonical lambda closure.
private def exportedClosedBody (nodes : Array Expr) (descriptor : Json) : TermElabM Expr := do
  let .ok context := descriptor.getObjValAs? (Array Json) "context"
    | throwError "an exported selected term lost its original context"
  unless context.isEmpty do
    throwError "the closed-selection control unexpectedly acquired local assumptions"
  let .ok index := descriptor.getObjValAs? Nat "expression"
    | throwError "an exported selected term lost its exact expression reference"
  let some expression := nodes[index]?
    | throwError "an exported selected expression is outside its native graph"
  checkWithKernel expression
  return expression

private def checkCanonicalRoot (table : CasCatalogue.Realize.TermTable)
    (fields : Json) (field : String) (expression : Expr) : TermElabM Unit := do
  let .ok index := fields.getObjValAs? Nat field
    | throwError "an exported canonical selection lost its {field} root"
  unless (← table.rootIdentity index) == (← CasCatalogue.Realize.termIdentity expression) do
    throwError "the canonical {field} changed its original native term"

-- An implementation request retains its non-propositional value and its own judgement.
-- The neighboring ordinary proposition keeps its existing singleton identity shape.
run_cmd Lean.Elab.Command.liftTermElabM <| withCurrHeartbeats do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let file ← SourceFile.parse "implemented-export.cas"
    "test observer.implemented_value \"typed value\": assert implemented Fin(2)\n\
     test observer.ordinary_proposition \"ordinary question\": assert true\n"
  let observation ← observeFile file empty
  unless observation.failures.isEmpty && observation.readings.map (·.id) ==
      #["observer.implemented_value", "observer.ordinary_proposition"] do
    throwError "implementation observation rejected a typed value or changed original identities"
  let implementation := observation.readings[0]!
  let #[value] ← exportedNativeRoots implementation
    | throwError "an implementation request lost its original singleton typed value"
  unless !(← isProp value) do
    throwError "an implementation request was replaced by a fabricated proposition"
  let expected ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 2]
  unless ← isDefEq value expected do
    throwError "the implementation request changed its original finite object"
  checkWithKernel value
  let document ← exportedDocument implementation.question
  let .ok roots := document.getObjVal? "roots"
    | throwError "an implementation identity lost its roots"
  unless roots.getObjValAs? String "judgement" == .ok "implemented" do
    throwError "the implementation request changed its distinct judgement kind"
  let .error _ := roots.getObjVal? "conjuncts"
    | throwError "a singleton implementation request acquired a conjunction wrapper"
  let .ok category := roots.getObjVal? "category"
    | throwError "the implementation identity lost its selected category"
  let .error _ := category.getObjVal? "limit"
    | throwError "a category without a chosen limit acquired a canonical limit field"
  let .ok nativeCategory := implementation.sourceContext.getObjVal? "category"
    | throwError "the implementation snapshot lost its selected category"
  let .error _ := nativeCategory.getObjVal? "limit"
    | throwError "a category without a chosen limit acquired a native limit field"
  let .ok encodedNodes := document.getObjValAs? (Array Json) "terms"
    | throwError "the implementation identity lost its canonical node table"
  let canonical ← CasCatalogue.Realize.TermTable.new
  canonical.nodes.set encodedNodes
  checkCanonicalRoot canonical roots "proposition" value
  let ordinary := observation.readings[1]!
  let #[proposition] ← exportedNativeRoots ordinary
    | throwError "an ordinary question changed its singleton native root"
  unless ← isProp proposition do
    throwError "an ordinary proposition acquired implementation-value semantics"
  let ordinaryDocument ← exportedDocument ordinary.question
  let .ok ordinaryRoots := ordinaryDocument.getObjVal? "roots"
    | throwError "the ordinary proposition lost its canonical roots"
  let .ok _ := ordinaryRoots.getObjValAs? Nat "proposition"
    | throwError "the ordinary proposition changed its original root shape"
  for field in #["judgement", "conjuncts"] do
    let .error _ := ordinaryRoots.getObjVal? field
      | throwError "an ordinary proposition acquired a new {field} wrapper"

-- Selected presentations survive all three actual consumers: fresh typing
-- values, categories of original definitions, and inert post-scope conclusions.
run_cmd Lean.Elab.Command.liftTermElabM <| withCurrHeartbeats do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let file ← SourceFile.parse "selected-cone-export.cas"
    "test observer.fresh_product \"selected cone\": assert (Fin(2) × Fin(3)) in Sets\n\
     let P := Fin(2) × Fin(3)\n\
     test observer.stored_product \"selected scope\": assert P = P\n"
  let observation ← observeFile file empty
  unless observation.failures.isEmpty && observation.readings.map (·.id) ==
      #["observer.fresh_product", "observer.stored_product"] do
    throwError "selected-cone observation rejected or omitted an original assertion"
  let fresh := observation.readings[0]!
  let stored := observation.readings[1]!
  let state ← CasCatalogue.semanticState
  let sets ← selectCategory state "Sets"
  let left ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 2]
  let right ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 3]
  let presentation ← mkAppM ``CasCatalogue.Limits.Registration.setsProduct #[left, right]
  let expectedCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let expectedApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[expectedCone]
  let inspectSelection := fun (sourceContext category : Json)
      (canonical? : Option (CasCatalogue.Realize.TermTable × Json)) => do
    let .ok graph := sourceContext.getObjVal? "nativeExpressions"
      | throwError "the selected-cone snapshot lost its native graph"
    let .ok nodes := CasTools.NativeExpression.decodeNodes graph
      | throwError "the selected-cone native graph did not decode"
    let .ok limit := category.getObjVal? "limit"
      | throwError "an exported category discarded its chosen cone"
    let .ok rowId := limit.getObjValAs? String "row"
      | throwError "an exported chosen cone lost its original row"
    let #[row] := state.limits.filter (·.id.raw == rowId)
      | throwError "the exported chosen cone no longer identifies one original presentation"
    let .ok declarationJson := limit.getObjVal? "declaration"
      | throwError "the chosen cone lost its native declaration name"
    let .ok declaration := CasTools.NativeExpression.nameFromJson declarationJson
      | throwError "the chosen cone's native declaration name did not decode"
    unless row.category == sets.id && row.shape == "product" && !row.colimit &&
        declaration == ``CasCatalogue.Limits.Registration.setsProduct &&
        row.declaration == declaration && limit.getObjValAs? Bool "colimit" == .ok false &&
        category.getObjValAs? String "role" == .ok "object" &&
        category.getObjValAs? String "expression" == .ok (reprStr sets.expression) &&
        limit.getObjValAs? String "category" == .ok (reprStr sets.expression) do
      throwError "the exported cone changed its original row, category or presentation kind"
    let .ok bundleJson := category.getObjVal? "bundle"
      | throwError "the exported category lost its complete native bundle"
    let bundle ← exportedClosedBody nodes bundleJson
    let .ok chosenBundleJson := limit.getObjVal? "bundle"
      | throwError "the exported cone lost its complete native category bundle"
    let chosenBundle ← exportedClosedBody nodes chosenBundleJson
    let .ok coneJson := limit.getObjVal? "cone"
      | throwError "the exported cone lost its native term"
    let cone ← exportedClosedBody nodes coneJson
    unless bundle == chosenBundle && cone.containsConst (· == declaration) &&
        (← isDefEq cone expectedCone) do
      throwError "the exported cone changed its complete bundle or original finite operands"
    if let some (canonical, fields) := canonical? then
      let .ok chosen := fields.getObjVal? "limit"
        | throwError "the canonical category discarded its chosen cone"
      let .ok chosenDeclarationJson := chosen.getObjVal? "declaration"
        | throwError "the canonical cone lost its native declaration name"
      let .ok chosenDeclaration := CasTools.NativeExpression.nameFromJson chosenDeclarationJson
        | throwError "the canonical cone's declaration name did not decode"
      unless chosen.getObjValAs? String "row" == .ok rowId &&
          chosenDeclaration == declaration &&
          chosen.getObjValAs? Bool "colimit" == .ok false &&
          chosen.getObjValAs? String "category" == .ok (reprStr sets.expression) do
        throwError "the canonical cone changed its selected presentation fields"
      checkCanonicalRoot canonical fields "bundle" bundle
      checkCanonicalRoot canonical chosen "bundle" chosenBundle
      checkCanonicalRoot canonical chosen "cone" cone
  for (reading, isFresh) in #[(fresh, true), (stored, false)] do
    let document ← exportedDocument reading.question
    let .ok roots := document.getObjVal? "roots"
      | throwError "a selected-cone identity lost its canonical roots"
    if isFresh then
      unless roots.getObjValAs? String "judgement" == .ok "settled" do
        throwError "the fresh product typing changed its original settled judgement"
    let .ok encodedNodes := document.getObjValAs? (Array Json) "terms"
      | throwError "a selected-cone identity lost its canonical node table"
    let canonical ← CasCatalogue.Realize.TermTable.new
    canonical.nodes.set encodedNodes
    let category ← if isFresh then do
        let .ok category := reading.sourceContext.getObjVal? "category"
          | throwError "the fresh product lost its selected category snapshot"
        pure category
      else do
        let .ok #[category] := reading.sourceContext.getObjValAs? (Array Json) "categories"
          | throwError "the stored product lost its original declaration's selected category"
        pure category
    let canonicalCategory ← if isFresh then do
        let .ok category := roots.getObjVal? "category"
          | throwError "the fresh product lost its canonical selected category"
        pure category
      else do
        let .ok #[category] := roots.getObjValAs? (Array Json) "categories"
          | throwError "the stored product lost its original canonical declaration selection"
        pure category
    inspectSelection reading.sourceContext category (some (canonical, canonicalCategory))
  let #[value] ← exportedNativeRoots fresh
    | throwError "the fresh product lost its original native typing value"
  unless ← isDefEq value expectedApex do
    throwError "the fresh product typing changed its original apex"
  -- Construct one conclusion through the public source boundary, then inspect the
  -- frozen result through observeConclusion without any current session or evaluation.
  let `(cas_item| test $_:ident $_:str : $statement:cas_stmt) := file.items[0]!
    | throwError "the selected-conclusion control lost its original source item"
  let .settled #[term] ← file.withContext (empty.readStatement statement)
    | throwError "the selected-conclusion control changed its typed statement kind"
  let conclusion ← empty.conclusion #[term]
  let observed := observeConclusion conclusion
  let .ok #[snapshot] := observed.getObjValAs? (Array Json) "terms"
    | throwError "the inert conclusion observer lost its original selected term"
  let .ok proof := observed.getObjVal? "proof"
    | throwError "the inert conclusion observer changed its proof field"
  unless proof.isNull do throwError "a typing conclusion fabricated proof evidence"
  let .ok category := snapshot.getObjVal? "category"
    | throwError "the inert conclusion observer lost its selected category"
  inspectSelection snapshot category none
