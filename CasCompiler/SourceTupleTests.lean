module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra

open Lean Meta Elab Term CasCompiler

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native tuple parameter did not parse"
  return ⟨stx⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source tuple did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `A (← nativeTerm "Type")
  let session ← session.assume `B (← nativeTerm "Type")
  let session ← session.assume `a (← nativeTerm "A")
  let session ← session.assume `b (← nativeTerm "B")
  let type ← session.term (← nativeTerm "A × B")
  let term ← session.read (← sourceTerm "(a, b)") (some type.source)
  let expected ← session.term (← nativeTerm "(a, b)")
  term.source.withOpen fun bindings expression => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq expression expected do
      throwError "a source pair changed its actual native constructor arguments"
    unless expression.containsFVar bindings[2]!.expression.fvarId! &&
        expression.containsFVar bindings[3]!.expression.fvarId! do
      throwError "a source pair replaced its original component bindings"
  let session ← session.defineTerm `pair term
  let session ← session.assume `a (← nativeTerm "B")
  let retained ← session.read (← sourceTerm "pair")
  retained.source.withOpen fun bindings expression => do
    unless expression == bindings[4]!.expression do
      throwError "a source pair was rebuilt after a component name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeTerm "Nat")
  let session ← session.assume `i (← nativeTerm "Fin n")
  for pair in #["Sigma", "PSigma"] do
    let type ← session.term (← nativeTerm s!"{pair} (fun n : Nat => Fin n)")
    let expected ← session.term (← nativeTerm s!"{pair}.mk n i")
    let term ← session.read (← sourceTerm "(n, i)") (some type.source)
    term.source.withOpen fun bindings expression => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless ← isDefEq expression expected do
        throwError "a source dependent pair changed its constructor or dependent component"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Fin 2 → Type")
  let session ← session.assume `a (← nativeTerm "X 0")
  let session ← session.assume `b (← nativeTerm "X 1")
  let type ← session.term (← nativeTerm "(i : Fin 2) → X i")
  let term ← session.read (← sourceTerm "(a, b)") (some type.source)
  unless term.source.context.entries.size == session.context.entries.size do
    throwError "a finite tuple shortened its complete dependent context"
  term.source.withOpen fun bindings expression => do
    let indices ← sourceFiniteIndices (mkNatLit 2) 2
    for index in indices, binding in bindings.extract 1 3 do
      unless ← isDefEq (mkApp expression index) binding.expression do
        throwError "a finite dependent tuple changed its actual indexed component"
      unless expression.containsFVar binding.expression.fvarId! do
        throwError "a finite dependent tuple discarded an original component binding"
  let rejected ← try
    discard <| session.read (← sourceTerm "(a, b, a)") (some type.source)
    pure false
  catch _ => pure true
  unless rejected do
    throwError "a finite tuple accepted a different declared native arity"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Type")
  let session ← session.assume `a (← nativeTerm "X")
  let session ← session.assume `b (← nativeTerm "X")
  let type ← session.read (← sourceTerm "Vec(X, 3)")
  let term ← session.read (← sourceTerm "(b, a, b)") (some type.source)
  let expected ← session.term (← nativeTerm "![b, a, b]")
  term.source.withOpen fun bindings expression => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq expression expected do
      throwError "a source vector tuple changed its original ordered components"
