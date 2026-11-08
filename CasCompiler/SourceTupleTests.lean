module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra

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

-- A matrix literal is checked at the actual declared finite row and column domains.
-- Its native data are ordered finite functions; this control supplies arbitrary cells.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "CommRingCat.{0}")
  let rings ← session.namedCategory Syntax.missing "CommutativeRings" [.zero] #[]
  let ring ← session.term (← nativeTerm "R")
  let ring ← ring.inCategory rings.expression rings.value
  let session ← session.defineTerm `S ring
  let session ← session.assume `a (← nativeTerm "(S : Type)")
  let session ← session.assume `b (← nativeTerm "(S : Type)")
  for (rows, columns, source, native) in #[
      (1, 2, "[a, b]", "![![a, b]]"),
      (2, 2, "[a, b; b, a]", "![![a, b], ![b, a]]"),
      (3, 2, "[a, b; b, a; a, a]", "![![a, b], ![b, a], ![a, a]]")] do
    let type ← session.read (← sourceTerm s!"RectangularMatrices({rows}, {columns}, S)")
    let value ← session.read (← sourceTerm source) (some type.source)
    let expected ← session.term (← nativeTerm native)
    value.source.withOpen fun bindings expression => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      unless ← isDefEq expression expected do
        throwError "a source finite matrix changed its declared dimensions or ordered cells"
      unless (← inferType expression).containsFVar bindings[1]!.expression.fvarId! &&
          expression.containsFVar bindings[2]!.expression.fvarId! &&
          expression.containsFVar bindings[3]!.expression.fvarId! do
        throwError "a source matrix discarded its selected coefficient object or cell bindings"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
  let type ← session.read (← sourceTerm "RectangularMatrices(2, 2, S)")
  for source in #["[a, b]", "[a; b]", "[a, b; b]"] do
    let rejected ← withoutModifyingState do
      try
        discard <| session.read (← sourceTerm source) (some type.source)
        pure false
      catch error =>
        let detail ← error.toMessageData.toString
        unless (detail.splitOn "finite arit").length > 1 do throw error
        pure true
    unless rejected do throwError "a finite matrix accepted a different declared shape"
