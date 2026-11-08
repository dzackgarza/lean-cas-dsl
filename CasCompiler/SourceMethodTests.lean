module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality

open Lean Meta Elab Term CasCompiler CasCatalogue

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
  for expression in #["X.cardinality()", "(X).cardinality()", "|X|", "|Fin(3)|"] do
    let result ← session.read (← sourceTerm expression)
    unless result.source.context.entries.size == 2 do
      throwError "method formation discarded the complete preceding source context"
    result.source.withOpen fun bindings value => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless ← isDefEq value expected do
        throwError "source method formation changed the actual registered functor application"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let resultType ← session.elaborate Syntax.missing fun context => do
    inferType (← expected.source.inContext context)
  let lexical ← session.assumeTerm `X.cardinality resultType
  let localValue ← lexical.read (← sourceTerm "X.cardinality()")
  localValue.source.withOpen fun bindings value => do
    unless value == bindings[2]!.expression do
      throwError "a method call displaced an exact qualified lexical binding"
  let session ← session.defineTerm `answer method
  let session ← session.assume `X (← nativeTerm "Type")
  let retained ← session.read (← sourceTerm "answer")
  retained.source.withOpen fun bindings value => do
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
  result.source.withOpen fun bindings value => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    unless value.containsFVar bindings[1]!.expression.fvarId! && (← isDefEq value expected) do
      throwError "a method specialized or replaced its arbitrary original receiver"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))

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
    unless result.source.context.entries.size == 2 do
      throwError "inherited method formation lost its original parameter or object binding"
    result.source.withOpen fun bindings value => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless ← isDefEq value expected do
        throwError "inherited method formation changed its actual classifier forgetful action"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
