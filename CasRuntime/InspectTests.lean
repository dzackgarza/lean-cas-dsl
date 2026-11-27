module

import CasRuntime.Inspect
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import Lean.Elab.Command
meta import CasRuntime.Inspect
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

namespace CasRuntime.InspectTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue




run_cmd liftTermElabM do
  let env ← getEnv
  try
    let root ← IO.currentDir
    IO.FS.createDirAll (root / ".tmp")
    let manifest := root / ".tmp" / "inspect-empty-leaves.json"
    IO.FS.writeFile manifest (Json.mkObj
      [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let initial ← KernelSession.start (some manifest)
    try
      let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt "let S := Fin(3)"
        | throwError "the finite object observation did not parse"
      let run ← initial.run ⟨statement⟩
      unless run.outcome.kind == "holds" do
        throwError "the original finite object did not bind: {run.outcome.detail}"
      let session := run.session
      let transaction ← CellTransaction.begin session.kernel.ledger
      try
        let before ← session.kernel.dispatches.get
        let #[observed] ← Inspect.prepare session transaction
          | throwError "discovery did not observe exactly the retained source binding"
        unless observed.name == "S" && observed.members.contains "is_finite" do
          throwError "the selected finite object's applicable property was not discovered"
        let source := observed.details.getObjValD "source"
        let .ok sourceContext := source.getObjValAs? (Array Json) "context"
          | throwError "inspection omitted the complete original source telescope"
        let .ok sourceSelections := source.getObjValAs? (Array Json) "selections"
          | throwError "inspection omitted the complete typed source selection table"
        unless sourceContext.map (·.getObjValD "id") ==
              session.source.context.entries.map
                (fun entry => ContextSnapshot.bindingJson entry.id) &&
            sourceSelections.size == session.source.selections.size &&
            !sourceSelections.isEmpty do
          throwError "inspection dropped original source bindings or selections"
        for (id, _) in session.source.selections.toArray do
          unless (sourceSelections.filter fun row =>
              row.getObjValD "binding" == ContextSnapshot.bindingJson id).size == 1 do
            throwError "inspection changed an exact source selection identity"
        let .ok candidates := observed.details.getObjValAs? (Array Json) "candidates"
          | throwError "the observation has no source candidate inventory"
        let some property := candidates.find? fun row =>
            (row.getObjValAs? String "kind").toOption == some "member" &&
            (row.getObjValAs? String "name").toOption == some "is_finite"
          | throwError "the original finiteness classifier was not retained"
        unless (property.getObjValAs? String "status").toOption == some "applicable" do
          throwError "the original classifier did not survive ordinary member competition: {property}"
        let .ok #[alternative] := property.getObjValAs? (Array Json) "alternatives"
          | throwError "the classifier lost its unique original candidate"
        unless (alternative.getObjValAs? String "kind").toOption == some "property" &&
            (alternative.getObjValAs? (Array Json) "permittedRegistrationForms").toOption == some #[] do
          throwError "mathematical applicability was identified with provider availability"
        let .ok selected := property.getObjVal? "selected"
          | throwError "discovery did not retain the actual checked selection"
        unless (selected.getObjVal? "native").isOk &&
            (selected.getObjVal? "nativeExpressions").isOk do
          throwError "the selected property lost its original native term"
        let .ok selectedScopes := selected.getObjValAs? (Array Json) "selections"
          | throwError "the completed property lost its original typed source scope"
        let .ok propertyId := alternative.getObjValAs? String "id"
          | throwError "the property candidate lost its original registry identity"
        let some propertyRow := (← semanticState).properties.find? (·.id.raw == propertyId)
          | throwError "the property observation does not name its original registry row"
        unless selectedScopes.any (fun row =>
            let application := (row.getObjValD "selection").getObjValD "application"
            let selectedFamily := (application.getObjValD "family").getObjValD "property"
            (selectedFamily.getObjValD "family").getObjValD "entry" == toJson propertyRow) do
          throwError "the completed property discarded its complete original registry row"
        unless (← session.kernel.dispatches.get).size == before.size do
          throwError "mathematical discovery dispatched a computation"
      finally
        discard <| transaction.abort
    finally initial.close
  finally setEnv env



run_cmd liftTermElabM do
  let env ← getEnv
  try
    let root ← IO.currentDir
    IO.FS.createDirAll (root / ".tmp")
    let manifest := root / ".tmp" / "inspect-operation-empty-leaves.json"
    IO.FS.writeFile manifest (Json.mkObj
      [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let initial ← KernelSession.start (some manifest)
    try
      let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt "let R := ℤ"
        | throwError "the original ring object observation did not parse"
      let run ← initial.run ⟨statement⟩
      unless run.outcome.kind == "holds" do
        throwError "the original ring object did not bind: {run.outcome.detail}"
      let session := run.session
      let transaction ← CellTransaction.begin session.kernel.ledger
      try
        let before ← session.kernel.dispatches.get
        let #[observed] ← Inspect.prepare session transaction
          | throwError "operation discovery lost the retained ring binding"
        let .ok candidates := observed.details.getObjValAs? (Array Json) "candidates"
          | throwError "the ring observation has no source candidate inventory"
        let some power := candidates.find? fun row =>
            (row.getObjValAs? String "kind").toOption == some "operation" &&
            (row.getObjValAs? String "id").toOption == some "op.rings.pow"
          | throwError "the selected ring lost its independently declared power family"
        unless (power.getObjValAs? String "status").toOption == some "typed_candidate" &&
            (power.getObjValAs? Nat "arity").toOption == some 1 &&
            (power.getObjValAs? (Array Json) "permittedRegistrationForms").toOption == some #[] do
          throwError "the power family's dependent interface or availability changed"
        let some powerRow := (← semanticState).operations.find? (·.id.raw == "op.rings.pow")
          | throwError "the power observation lost its independent source row"
        unless power.getObjValD "reference" ==
            toJson (some (.operation powerRow : SelectedSourceReference)) &&
            (power.getObjVal? "nativeRoute").isOk &&
            (power.getObjVal? "selections").isOk do
          throwError "the power family lost its complete original row, route or source scope"
        let .ok native := power.getObjVal? "nativeExpressions"
          | throwError "the discovered power family lost its complete native expression graph"
        let .ok #[expression, type] := NativeExpression.decode native
          | throwError "the discovered power family lost its exact expression and type"
        unless expression.containsConst (· == ``CasCatalogue.Algebra.NamedRings.pow) &&
            type.containsConst (· == ``Nat) && !expression.hasMVar && !type.hasMVar do
          throwError "the power family lost its declared operation or remaining exponent"
        unless (← session.kernel.dispatches.get).size == before.size do
          throwError "operation discovery dispatched a computation"
      finally
        discard <| transaction.abort
    finally initial.close
  finally setEnv env

end CasRuntime.InspectTests
