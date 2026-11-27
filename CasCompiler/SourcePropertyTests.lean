module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness

open Lean Meta Elab Term CasCompiler CasCatalogue CasCompiler.SourceTest

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the property source did not parse"
  return ⟨source⟩




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  for (text, object) in #[("Fin(3).is_finite()", ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 3]),
      ("ℤ.is_finite()", Expr.const ``CasCatalogue.Foundation.Objects.integers [])] do
    let result ← session.read (← sourceTerm text)
    let #[classifier] := (← semanticState).classifiers.filter (·.id == ClassifierId.setsFinite)
      | throwError "the finiteness classifier is not uniquely registered"
    checkSelected result fun value => do
      let some selected ← SourceReadM.selection? value
        | liftM (m := TermElabM) <| throwError "the property lost its original selected source"
      let some application := selected.application
        | liftM (m := TermElabM) <| throwError "the property lost its original complete application"
      let .property family := application.family
        | liftM (m := TermElabM) <| throwError "the property changed its original family"
      unless (SelectedSourceReference.classifier family.classifier).exactlyMatches
          (.classifier classifier) do
        liftM (m := TermElabM) <| throwError "the property reading has a different classifier"
      let expectedClassifier ← classifierInstance classifier
      checkOriginal #[value, object, expectedClassifier] fun native => do
        let value ← zetaReduce native[0]!
        unless (← whnf (← inferType value)).isProp do
          throwError "the property did not read as a proposition"
        let holds := value.consumeMData
        unless holds.isAppOfArity ``CasCatalogue.Classifier.Holds 3 do
          throwError "the property reading is not a classifier proposition: {value}"
        unless ← isDefEq holds.appFn!.appArg! native[2]! do
          throwError "the property reading has a different classifier: {value}"
        unless ← isDefEq holds.appArg! native[1]! do
          throwError "`{text}` is not the property at its receiver: {value}"
