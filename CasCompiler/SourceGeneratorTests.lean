module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations

open Lean Meta Elab Term CasCompiler CasCatalogue

-- The first two objects and generator applications come from the unchanged public F9
-- questions. The alias control checks source identity only: equal native carriers cannot
-- replace the actual named object. No comparison action or generator value is evaluated.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let file ← SourceFile.parse "source-explicit-generators.cas"
      "let X := F9x\nlet Y := F9y\nlet Xalias := X\n\
       let GX := generator(X)\nlet GY := generator(Y)\nlet GA := generator(Xalias)\n"
    let mut session ← SourceSession.empty identities
    let expected := #[
      (`X, "obj.sets.f9_x", ``CasCatalogue.Algebra.PolynomialPresentations.firstGenerator),
      (`Y, "obj.sets.f9_y", ``CasCatalogue.Algebra.PolynomialPresentations.secondGenerator),
      (`Xalias, "obj.sets.f9_x", ``CasCatalogue.Algebra.PolynomialPresentations.firstGenerator)]
    for item in file.items, index in [:file.items.size] do
      let `(cas_item| $statement:cas_stmt) := item
        | throwError "the explicit generator control changed its parsed category"
      let .definition next value ← file.withContext (session.readStatement statement)
        | throwError "the explicit generator control is not a source definition"
      session := next
      if index < 3 then continue
      let some (name, objectId, declaration) := expected[index - 3]?
        | throwError "the generator control acquired an unexpected source statement"
      value.source.withOpen fun bindings expression => do
        let some selected ← bindings.findM? fun binding =>
            return (← binding.expression.fvarId!.getUserName) == name
          | throwError "the explicit generator lost its original source object"
        unless (← inferType expression) == selected.expression do
          throwError "the generator replaced its exact source object by another carrier"
        let some (.mdata data body) := expression.find? fun expression =>
            match expression with
            | .mdata data _ => data.getName `CasCompiler.source.kind == ``ObjectEntry.generator
            | _ => false
          | throwError "the explicit generator lost its selected catalogue reference"
        unless data.getString `CasCompiler.source.id == objectId &&
            data.getName `CasCompiler.source.declaration == declaration &&
            body.containsConst (· == declaration) do
          throwError "the explicit generator changed its original registered declaration"
        let some ordinal := bindings.findIdx? (·.id == selected.id)
          | throwError "the generator's source object is outside its complete telescope"
        unless (← contextDependencies bindings (← inferType expression)).contains ordinal do
          throwError "the generator dropped its actual source-binding dependency"
  finally setEnv original
