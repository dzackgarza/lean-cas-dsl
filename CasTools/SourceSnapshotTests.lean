module

import CasTools.QuestionExport
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
meta import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
meta import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
meta import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
meta import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
meta import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests

open Lean Meta Elab Term CasCompiler CasCatalogue.Language CasTools.QuestionExport

run_cmd Lean.Elab.Command.liftTermElabM do
  let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/" ++
    "completion/rx-lift-prescribed-stages.cas"
  let input ← liftM (m := IO) (IO.FS.readFile path)
  let file ← SourceFile.parse path input
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let observation ← observeFile file (← SourceSession.empty identities)
  let expected := file.items.filterMap fun item => match item with
    | `(cas_item| test $id:ident $_:str : $_:cas_stmt) =>
      some (id.getId.toString (escape := false))
    | _ => none
  unless observation.readings.map (·.id) == expected &&
      observation.failures.all (·.kind != "interrupted") do
    throwError "native snapshot export did not retain the original inventory within its shared budget"
  let some row := observation.readings.find?
    (·.id == "reconstructed_extensions_20261024.complete.lift.whole_formed_equation")
    | throwError "the original whole-pairing question is absent"
  let .ok document := Json.parse row.proposition
    | throwError "the whole native proposition is not a graph document"
  let .ok #[proposition] := CasTools.NativeExpression.decode document
    | throwError "the whole native proposition did not decode"
  checkWithKernel proposition
  unless ← isProp proposition do throwError "the decoded whole question is not a proposition"
  let .ok graph := row.sourceContext.getObjVal? "nativeExpressions"
    | throwError "the source snapshot has no exact native graph"
  let .ok nodes := CasTools.NativeExpression.decodeNodes graph
    | throwError "the complete native source graph did not decode"
  let .ok native := row.sourceContext.getObjVal? "native"
    | throwError "the native snapshot omitted its original term"
  let .ok root := native.getObjValAs? Nat "expression"
    | throwError "the native snapshot omitted its term reference"
  let some body := nodes[root]? | throwError "the native term is outside its graph"
  let .ok entries := native.getObjValAs? (Array Json) "context"
    | throwError "the native snapshot omitted its complete telescope"
  let mut closed := body
  for entry in entries.reverse do
    let .ok nameJson := entry.getObjVal? "nativeName"
      | throwError "the native context omitted a binder name"
    let .ok name := CasTools.NativeExpression.nameFromJson nameJson
      | throwError "a native binder name did not decode"
    let .ok typeIndex := entry.getObjValAs? Nat "type"
      | throwError "the native context omitted a binding type"
    let some type := nodes[typeIndex]? | throwError "a binding type is outside its graph"
    let .ok valueIndex := entry.getObjValAs? (Option Nat) "value"
      | throwError "the native context changed its declaration kind"
    let .ok nondep := entry.getObjValAs? Bool "nondep"
      | throwError "the native context omitted let dependency information"
    let .ok info := entry.getObjValAs? BinderInfo "nativeBinderInfo"
      | throwError "the native context omitted its binder annotation"
    match valueIndex with
    | none => closed := .forallE name type closed info
    | some index =>
      let some value := nodes[index]? | throwError "a binding value is outside its graph"
      closed := .letE name type value closed nondep
  unless closed.equal proposition do
    throwError "the complete native snapshot differs from its original closed proposition"
  checkWithKernel closed
