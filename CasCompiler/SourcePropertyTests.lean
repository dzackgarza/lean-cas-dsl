module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness

open Lean Meta Elab Term CasCompiler CasCatalogue

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the property source did not parse"
  return ⟨source⟩

/- A registered property of an object reads as the proposition that its classifier's fibre over
the object is inhabited (CC-PROP): `Fin(3).is_finite()` is `Classifier.Holds` of the finiteness
classifier at `Fin(3)`. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let result ← session.read (← sourceTerm "Fin(3).is_finite()")
  result.source.withOpen fun _ value => do
    unless (← whnf (← inferType value)).isProp do
      throwError "the property did not read as a proposition"
    let state ← semanticState
    let some classifier := state.classifiers.find? (·.id == ClassifierId.setsFinite)
      | throwError "the finiteness classifier is not registered"
    let object ← mkAppM ``CasCatalogue.Foundation.Objects.fin #[mkNatLit 3]
    let holds := value.consumeMData
    unless holds.isAppOfArity ``CasCatalogue.Classifier.Holds 3 do
      throwError "the property reading is not a classifier proposition: {value}"
    unless ← isDefEq holds.appFn!.appArg! (← classifierInstance classifier) do
      throwError "the property reading has a different classifier: {value}"
    unless ← isDefEq holds.appArg! object do
      throwError "the property reading is not at Fin(3): {value}"
