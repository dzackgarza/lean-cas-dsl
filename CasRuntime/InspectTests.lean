module

import CasRuntime.Inspect
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import Lean.Elab.Command
meta import CasRuntime.Inspect
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality

namespace CasRuntime.InspectTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue

-- Use the public source statement entrance, with an explicitly empty provider
-- manifest. A registered property remains mathematically applicable even
-- when there is no provider for its computation.
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
        unless (← session.kernel.dispatches.get).size == before.size do
          throwError "mathematical discovery dispatched a computation"
      finally
        discard <| transaction.abort
    finally initial.close
  finally setEnv env

end CasRuntime.InspectTests
