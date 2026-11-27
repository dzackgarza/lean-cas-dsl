module

import CasTools.QuestionExport
import CasTools.Diagnostics
import CasCompiler.Resolve
import all CasTools.NativeExpression
import all CasCompiler.ContextSnapshot
import all CasCompiler.SourceSnapshot
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets
import LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients
import LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions
import LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
public meta import Lean.Elab.Command
meta import CasTools.QuestionExport
meta import CasTools.Diagnostics
meta import CasCompiler.Resolve
meta import CasTools.NativeExpression
meta import CasCompiler.ContextSnapshot
meta import CasCompiler.SourceSnapshot
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
  let log ← liftM (m := IO) <| CasTools.ApplicationLog.new identities.worker
    (Json.mkObj [("file", toJson path)])
  let observation ← CasTools.Diagnostics.withScope { log } do
    let observation ← observeFile file (← SourceSession.empty identities)
    try
      CasTools.Diagnostics.emit "source.observation.finished" (Json.mkObj [
        ("file", toJson path), ("readings", toJson observation.readings.size),
        ("failures", toJson observation.failures.size)])
    catch _ => pure ()
    pure observation
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
    | throwError "the whole native proposition is not a graph document; first source failure: {toJson observation.failures[0]?}"
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

private def snapshotKindsReference (context : ContextTelescope) :
    StateM CasTools.NativeExpression.Builder (Array Json) := do
  let first ← ContextSnapshot.contextJsonReference context
  let second := ContextSnapshot.instancesJson context
  let third ← ContextSnapshot.contextJsonReference context
  return #[first, second, third, ContextSnapshot.instancesJson context]

private unsafe def snapshotKindsCached (context : ContextTelescope) :
    StateM CasTools.NativeExpression.Builder (Array Json) :=
  letI : TypeName ContextTelescope := TypeName.mk ContextTelescope ``ContextTelescope
  do
    let first ← ContextSnapshot.contextJson context
    let second ← CasTools.NativeExpression.Builder.memoSnapshot ``ContextSnapshot.instancesJson context
      (pure (ContextSnapshot.instancesJson context))
    let third ← ContextSnapshot.contextJson context
    let fourth ← CasTools.NativeExpression.Builder.memoSnapshot ``ContextSnapshot.instancesJson context
      (pure (ContextSnapshot.instancesJson context))
    return #[first, second, third, fourth]

@[implemented_by snapshotKindsCached]
private def snapshotKinds (context : ContextTelescope) :
    StateM CasTools.NativeExpression.Builder (Array Json) :=
  snapshotKindsReference context

run_cmd Lean.Elab.Command.liftTermElabM do
  withLCtx {} #[] do
    withLocalDeclD `snapshotInput (mkConst ``Nat) fun localExpression => do
      let binding : LocalBinding := {
        id := ⟨"snapshot-owner-control", 1⟩, role := .parameter, expression := localExpression }
      let context ← ContextTelescope.capture #[binding]
      let metadata : MData := { entries := [(`first, .ofNat 1), (`second, .ofNat 2)] }
      let term ← context.close (.mdata metadata localExpression)
      let other ← context.close (.mdata { entries := metadata.entries.reverse } localExpression)
      let selection : SourceSelection ClosedTerm := {
        value := term, originalApplication := some other,
        presentationEndpoints := some (term, other) }
      let selections := ({} : SourceSelectionScope ClosedTerm).insert binding.id selection
      let build
          (encodeContext : ContextTelescope → StateM CasTools.NativeExpression.Builder Json)
          (encodeTerm : ClosedTerm → StateM CasTools.NativeExpression.Builder Json)
          (encodeSelection : SourceSelection ClosedTerm → StateM CasTools.NativeExpression.Builder Json)
          (encodeSelections : SourceSelectionScope ClosedTerm → StateM CasTools.NativeExpression.Builder Json)
          (withPrefix : Bool) : StateM CasTools.NativeExpression.Builder (Array Json × Array Nat) := do
        if withPrefix then
          discard <| CasTools.NativeExpression.Builder.add (mkStrLit "independent-build-prefix")
        let firstContext ← encodeContext context.telescope
        let firstTerm ← encodeTerm term
        let firstSelection ← encodeSelection selection
        let firstSelections ← encodeSelections selections
        let inserted ← CasTools.NativeExpression.Builder.add
          (.mdata metadata (mkApp (mkConst ``Nat.succ) (mkNatLit 7)))
        let otherTerm ← encodeTerm other
        let repeatedSelections ← encodeSelections selections
        let repeatedSelection ← encodeSelection selection
        let repeatedTerm ← encodeTerm term
        let repeatedContext ← encodeContext context.telescope
        let expression ← CasTools.NativeExpression.Builder.add term.expression
        let otherExpression ← CasTools.NativeExpression.Builder.add other.expression
        return (#[firstContext, firstTerm, firstSelection, firstSelections, otherTerm,
          repeatedSelections, repeatedSelection, repeatedTerm, repeatedContext],
          #[expression, otherExpression, inserted])
      for withPrefix in #[false, true] do
        let (expected, expectedBuilder) := (build ContextSnapshot.contextJsonReference
          ContextSnapshot.closedTermJsonReference SourceSnapshot.selectionJsonReference
          SourceSnapshot.selectionsJsonReference withPrefix).run {}
        let (actual, actualBuilder) := (build ContextSnapshot.contextJson ContextSnapshot.closedTermJson
          SourceSnapshot.selectionJson SourceSnapshot.selectionsJson withPrefix).run {}
        unless (Json.arr actual.1).compress == (Json.arr expected.1).compress &&
            (actualBuilder.finish actual.2).compress == (expectedBuilder.finish expected.2).compress &&
            actualBuilder.indices.size == expectedBuilder.indices.size &&
            expectedBuilder.indices.toArray.all (fun (expression, index) =>
              actualBuilder.indices[expression]? == some index) do
          throwError "snapshot memoization changed complete JSON or native node order across a build"
        unless actual.1[0]! == actual.1[8]! && actual.1[1]! == actual.1[7]! &&
            actual.1[2]! == actual.1[6]! && actual.1[3]! == actual.1[5]! do
          throwError "snapshot memoization changed a repeated owner after intervening native nodes"
        if actual.2[0]! == actual.2[1]! then
          throwError "snapshot memoization identified different complete native metadata"
      let (expectedKinds, expectedBuilder) := (snapshotKindsReference context.telescope).run {}
      let (actualKinds, actualBuilder) := (snapshotKinds context.telescope).run {}
      unless (Json.arr actualKinds).compress == (Json.arr expectedKinds).compress &&
          (actualBuilder.finish #[]).compress == (expectedBuilder.finish #[]).compress &&
          actualKinds[0]! != actualKinds[1]! do
        throwError "snapshot memoization mixed independent serializer kinds for the same owner"

      let referenceBuild := build ContextSnapshot.contextJsonReference
        ContextSnapshot.closedTermJsonReference SourceSnapshot.selectionJsonReference
        SourceSnapshot.selectionsJsonReference false
      let cachedBuild := build ContextSnapshot.contextJson ContextSnapshot.closedTermJson
        SourceSnapshot.selectionJson SourceSnapshot.selectionsJson false
      let (_, cachedBuilder) := cachedBuild.run {}
      let (_, prefixedBuilder) := (CasTools.NativeExpression.Builder.add
        (mkStrLit "transplanted-builder-prefix")).run {}
      let resetBuilder := { cachedBuilder with indices := {}, nodes := #[] }
      let transplantedBuilder := { prefixedBuilder with
        snapshotDocuments := cachedBuilder.snapshotDocuments }
      let resetIndicesBuilder := { cachedBuilder with indices := {} }
      let resetNodesBuilder := { cachedBuilder with nodes := #[] }
      let runFrom
          (encode : StateM CasTools.NativeExpression.Builder (Array Json × Array Nat))
          (initial : CasTools.NativeExpression.Builder) (appendFirst : Bool) :=
        let action : StateM CasTools.NativeExpression.Builder (Array Json × Array Nat) := do
          if appendFirst then
            discard <| CasTools.NativeExpression.Builder.add (mkStrLit "changed-state-prefix")
          encode
        action.run initial
      for (stateKind, initial) in #[
          ("reset", resetBuilder), ("transplanted", transplantedBuilder),
          ("reset-indices", resetIndicesBuilder), ("reset-nodes", resetNodesBuilder)] do
        for appendFirst in #[false, true] do
          let (expected, expectedBuilder) := runFrom referenceBuild initial appendFirst
          let (actual, actualBuilder) := runFrom cachedBuild initial appendFirst
          unless (Json.arr actual.1).compress == (Json.arr expected.1).compress &&
              (actualBuilder.finish actual.2).compress == (expectedBuilder.finish expected.2).compress &&
              actualBuilder.indices.size == expectedBuilder.indices.size &&
              expectedBuilder.indices.toArray.all (fun (expression, index) =>
                actualBuilder.indices[expression]? == some index) do
            throwError "snapshot memoization changed complete JSON or native tables after {stateKind} (append first: {appendFirst})"
