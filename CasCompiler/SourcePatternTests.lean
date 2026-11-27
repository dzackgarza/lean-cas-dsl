module

import CasCompiler.Read
import CasCompiler.Parse
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native pattern parameter did not parse"
  return ⟨stx⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source pattern did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let first ← empty.assume `A (← nativeTerm "Type")
  let types ← first.assume `B (← nativeTerm "Type")
  let hypotheses ← types.assume `h (← nativeTerm "A = A")
  let session ← hypotheses.assume `b (← nativeTerm "B")
  let type ← session.term (← nativeTerm "A × (B × A) → A")
  let term ← session.read (← sourceTerm "(a, (b, c)) ↦ c") (some type.source) type.selections
  let expected ← session.term (← nativeTerm "fun (p : A × (B × A)) => p.2.2")
  unless (← authoredEntries term.source.context term.selections).size == 4 do
    throwError "a destructured function shortened its complete preceding scope"
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm term
    let expected ← session.readTerm expected
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "nested source patterns changed the actual native projections"
      unless native[0]!.getUsedConstants.contains ``Prod.fst &&
          native[0]!.getUsedConstants.contains ``Prod.snd do
        throwError "a source pattern discarded its actual component declarations"
    return expression
  let retained ← session.read (← sourceTerm "b")
  checkSelected retained fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    unless ← originatesAt scope.context scope.selections expression bindings[3]!.expression false do
      throwError "a destructured binder escaped into the enclosing source session"
  for pattern in #["(a, a) ↦ a", "(a, 0) ↦ a", "(a, b, c) ↦ a"] do
    let failure : Option Exception ← try
      discard <| session.read (← sourceTerm pattern) (some type.source) type.selections
      pure none
    catch error => pure (some error)
    unless failure.isSome do
      throwError "a source pattern accepted duplicate names, a nonbinder or the wrong arity"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Type")
  let type ← session.term
    (← nativeTerm "CasCatalogue.Algebra.LinearAlgebra.vectors X 3 → X")
  let term ← session.read (← sourceTerm "(a, b, c) ↦ b") (some type.source) type.selections
  checkSelected term fun expression => do
    let bindings ← authoredBindings
    checkOriginal #[expression, bindings[0]!.expression] fun native => do
      let expression := native[0]!
      unless expression.getUsedConstants.contains
          ``CasCatalogue.Algebra.LinearAlgebra.vectorComponent do
        throwError "a vector pattern replaced its independently declared coordinate maps"
      unless expression.containsFVar native[1]!.fvarId! do
        throwError "a vector pattern lost its actual coefficient type"
      lambdaTelescope expression fun _ body => do
        let .letE `a _ _ (.letE `b _ selected (.letE `c _ _ (.bvar 1) _) _) _ := body
          | throwError "a vector pattern did not return its actual bound second coordinate"
        unless selected.getUsedConstants.contains
            ``CasCatalogue.Algebra.LinearAlgebra.vectorComponent do
          throwError "the bound vector coordinate is not its declared projection"
  let file ← SourceFile.parse "component-functions.cas"
    "let pick((a, b, c)) := b in Vec(X, 3) → X\n"
  let `(cas_item| $statement:cas_stmt) := file.items[0]!
    | throwError "the component function statement did not parse"
  let .definition next term ← file.withContext (session.readStatement statement)
    | throwError "the component function did not define its retained value"
  unless (← authoredEntries next.context next.selections).size == 2 && term.span.fileName == "component-functions.cas" &&
      term.span.start == statement.raw.getPos? && term.span.stop == statement.raw.getTailPos? do
    throwError "a component function lost its complete context or original statement range"
  checkSelected term fun expression => do
    let bindings ← authoredBindings
    checkOriginal #[expression, bindings[0]!.expression] fun native => do
      unless native[0]!.getUsedConstants.contains
          ``CasCatalogue.Algebra.LinearAlgebra.vectorComponent &&
          native[0]!.containsFVar native[1]!.fvarId! do
        throwError "a component function replaced its selected projections or coefficient type"
  let type ← session.term
    (← nativeTerm "CasCatalogue.Algebra.LinearAlgebra.vectors X 2 → X")
  let rejected ← try
    discard <| session.read (← sourceTerm "(a, b, c) ↦ b") (some type.source) type.selections
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a source pattern ignored its object's declared finite arity"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  for pair in #["Sigma", "PSigma"] do
    let type ← session.term
      (← nativeTerm s!"(p : {pair} (fun n : Nat => Fin n)) → Fin p.1")
    let expected ← session.term
      (← nativeTerm s!"fun (p : {pair} (fun n : Nat => Fin n)) => p.2")
    let term ← session.read (← sourceTerm "(n, i) ↦ i") (some type.source) type.selections
    discard <| session.elaborateScoped Syntax.missing do
      let expression ← session.readTerm term
      let expected ← session.readTerm expected
      checkOriginal #[expression, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a dependent pattern changed its actual second projection or dependent type"
      return expression

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Fin 3 → Type")
  let type ← session.term (← nativeTerm "((i : Fin 3) → X i) → X 1")
  let expected ← session.term (← nativeTerm "fun (v : (i : Fin 3) → X i) => v 1")
  let term ← session.read (← sourceTerm "(a, b, c) ↦ b") (some type.source) type.selections
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm term
    let expected ← session.readTerm expected
    let bindings ← authoredBindings
    checkOriginal #[expression, expected, bindings[0]!.expression] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a finite function pattern changed its actual indexed component"
      unless native[0]!.containsFVar native[2]!.fvarId! do
        throwError "a finite function pattern lost its original dependent value family"
    return expression
  let rejected ← try
    discard <| session.read (← sourceTerm "(a, b) ↦ b") (some type.source) type.selections
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a finite function pattern accepted a different native index arity"
