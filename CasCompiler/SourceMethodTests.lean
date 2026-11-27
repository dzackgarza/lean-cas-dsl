module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok source := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native method source did not parse"
  return ⟨source⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original method expression did not parse"
  return ⟨source⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← empty.read (← sourceTerm "Fin(3)")
  let session ← empty.defineTerm `X object
  let session ← session.assume `unused (← nativeTerm "Nat")
  let expected ← session.term (← nativeTerm
    "CasCatalogue.Foundation.Cardinality.setsCardinality.obj (CategoryTheory.Core.mk X)")
  let method ← session.read (← sourceTerm "X.cardinality()")
  unless method.category.any (fun category => category.role == .object &&
      category.expression.syntacticEq (.atom ⟨"cat.cardinals"⟩)) do
    throwError "the method result lost its declared object role or target category"
  for expression in #["X.cardinality()", "(X).cardinality()", "|X|", "|Fin(3)|"] do
    let result ← session.read (← sourceTerm expression)
    unless (← authoredEntries result.source.context result.selections).size == 2 do
      throwError "method formation discarded the complete preceding source context"
    discard <| session.elaborateScoped Syntax.missing do
      let value ← session.readTerm result
      let expected ← session.readTerm expected
      checkOriginal #[value, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "source method formation changed the actual registered functor application"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      return value

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let category ← session.namedCategory Syntax.missing "Rings" [.zero] #[]
  let object ← session.term (← nativeTerm "R")
  let object ← object.inCategory category.expression category.value
  let session ← session.defineTerm `S object
  let expected ← session.term (← nativeTerm
    "CasCatalogue.Foundation.Cardinality.setsCardinality.obj (CategoryTheory.Core.mk (S : Type))")
  let result ← session.read (← sourceTerm "S.cardinality()")
  discard <| session.elaborateScoped Syntax.missing do
    let value ← session.readTerm result
    let expected ← session.readTerm expected
    let scope ← get
    let bindings ← authoredBindings
    unless (← visitNativeData (fun term => originatesAt scope.context scope.selections term
        bindings[1]!.expression false) value false) > 0 do
      throwError "whole method-family agreement changed its original rigid ring receiver"
    checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "whole method-family agreement changed its original rigid ring receiver"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
    return value

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← empty.read (← sourceTerm "Fin(3)")
  let session ← empty.defineTerm `X object
  let session ← session.assume `unused (← nativeTerm "Nat")
  let method ← session.read (← sourceTerm "X.cardinality()")
  let resultType ← session.elaborateScoped Syntax.missing do
    inferType (← session.readTerm method)
  let lexical ← session.assumeTerm `X.cardinality resultType
  let localValue ← lexical.read (← sourceTerm "X.cardinality()")
  checkSelected localValue fun value => do
    let bindings ← authoredBindings
    unless value == bindings[2]!.expression do
      throwError "a method call displaced an exact qualified lexical binding"
  let session ← session.defineTerm `answer method
  let session ← session.assume `X (← nativeTerm "Type")
  let retained ← session.read (← sourceTerm "answer")
  checkSelected retained fun value => do
    let bindings ← authoredBindings
    unless value == bindings[2]!.expression do
      throwError "a method result was reconstructed after its receiver name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Type")
  let selected ← session.namedCategory Syntax.missing "Sets" [.zero] #[]
  let object ← session.term (← nativeTerm "X")
  let object ← object.inCategory selected.expression selected.value
  let session ← session.defineTerm `A object
  let expected ← session.term (← nativeTerm
    "CasCatalogue.Foundation.Cardinality.setsCardinality.obj (CategoryTheory.Core.mk A)")
  let result ← session.read (← sourceTerm "A.cardinality()")
  discard <| session.elaborateScoped Syntax.missing do
    let value ← session.readTerm result
    let expected ← session.readTerm expected
    let scope ← get
    let bindings ← authoredBindings
    unless (← visitNativeData (fun term => originatesAt scope.context scope.selections term
        bindings[1]!.expression false) value false) > 0 do
      throwError "a method specialized or replaced its arbitrary original receiver"
    checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a method specialized or replaced its arbitrary original receiver"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
    return value

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeTerm "Nat")
  let object ← session.read (← sourceTerm "Fin(n) in FiniteSets")
  let session ← session.defineTerm `X object
  let expected ← session.term (← nativeTerm
    "CasCatalogue.Foundation.Cardinality.setsCardinality.obj (CategoryTheory.Core.mk (LeanCategories.Foundation.Mathlib.finite.forget.toFunctor.obj X))")
  for expression in #["X.cardinality()", "|X|", "|Fin(n) in FiniteSets|"] do
    let result ← session.read (← sourceTerm expression)
    unless (← authoredEntries result.source.context result.selections).size == 2 do
      throwError "inherited method formation lost its original parameter or object binding"
    discard <| session.elaborateScoped Syntax.missing do
      let value ← session.readTerm result
      let expected ← session.readTerm expected
      checkOriginal #[value, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "inherited method formation changed its actual classifier forgetful action"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      return value

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let object ← empty.read (← sourceTerm "Fin(3)")
  let session ← empty.defineTerm `X object
  let session ← session.assume `unused (← nativeTerm "Nat")
  for expression in #["|X| = 3", "|X| = (3)", "3 = |X|"] do
    let question ← session.readQuestion (← sourceTerm expression)
    unless (← authoredEntries question.source.context question.selections).size == 2 do
      throwError "literal formation lost the original mathematical context"
    checkSelected question fun value => do
      let type ← inferType value
      unless type.isSort && type.sortLevel! == .zero do
        throwError "literal comparison did not form a proposition"
      let literal ← mkAppM ``CasCatalogue.Foundation.Cardinality.CardinalLiteral.denote
        #[← mkAppM ``CasCatalogue.Foundation.Cardinality.CardinalLiteral.finite #[mkNatLit 3]]
      checkOriginal #[value, literal] fun native => do
        let value := native[0]!
        unless value.isAppOfArity ``Eq 3 do
          throwError "literal comparison changed the source equality"
        let right := value.getAppArgs[if expression == "3 = |X|" then 1 else 2]!
        unless ← isDefEq right native[1]! do
          throwError "the literal did not retain its registered denotation"
      unless (← authoredBindings).size == 2 do
        throwError "literal comparison lost its unused binding"
  let question ← session.readQuestion (← sourceTerm "|X| = ℵ₀")
  checkSelected question fun value => do
    let literal ← mkAppM ``CasCatalogue.Foundation.Cardinality.CardinalLiteral.denote
      #[mkConst ``CasCatalogue.Foundation.Cardinality.CardinalLiteral.aleph0]
    checkOriginal #[value, literal] fun native => do
      unless native[0]!.isAppOfArity ``Eq 3 do
        throwError "the named literal comparison changed the source equality"
      unless ← isDefEq native[0]!.getAppArgs[2]! native[1]! do
        throwError "the named literal lost its independently registered denotation"
