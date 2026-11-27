module

import CasCompiler.Read
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest

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
  let term ← session.read (← sourceTerm "(a, b)") (some type.source) type.selections
  let expected ← session.term (← nativeTerm "(a, b)")
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm term
    let expected ← session.readTerm expected
    let scope ← get
    let bindings ← authoredBindings
    for binding in bindings.extract 2 4 do
      unless (← visitNativeData (fun term =>
          originatesAt scope.context scope.selections term binding.expression false)
          expression false) > 0 do
        liftM (m := TermElabM) <| throwError "a source pair replaced its original component bindings"
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a source pair changed its actual native constructor arguments"
    return expression
  let session ← session.defineTerm `pair term
  let session ← session.assume `a (← nativeTerm "B")
  let retained ← session.read (← sourceTerm "pair")
  checkSelected retained fun expression => do
    let scope ← get
    let bindings ← authoredBindings
    unless ← originatesAt scope.context scope.selections expression bindings[4]!.expression false do
      liftM (m := TermElabM) <| throwError "a source pair was rebuilt after a component name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `n (← nativeTerm "Nat")
  let session ← session.assume `i (← nativeTerm "Fin n")
  for pair in #["Sigma", "PSigma"] do
    let type ← session.term (← nativeTerm s!"{pair} (fun n : Nat => Fin n)")
    let expected ← session.term (← nativeTerm s!"{pair}.mk n i")
    let term ← session.read (← sourceTerm "(n, i)") (some type.source) type.selections
    discard <| session.elaborateScoped Syntax.missing do
      let expression ← session.readTerm term
      let expected ← session.readTerm expected
      checkOriginal #[expression, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a source dependent pair changed its constructor or dependent component"
      return expression

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Fin 2 → Type")
  let session ← session.assume `a (← nativeTerm "X 0")
  let session ← session.assume `b (← nativeTerm "X 1")
  let type ← session.term (← nativeTerm "(i : Fin 2) → X i")
  let term ← session.read (← sourceTerm "(a, b)") (some type.source) type.selections
  unless (← authoredEntries term.source.context term.selections).map (·.id) ==
      (← authoredEntries session.context session.selections).map (·.id) do
    throwError "a finite tuple shortened its complete dependent context"
  checkSelected term fun expression => do
    let bindings ← authoredBindings
    checkOriginal #[expression, bindings[1]!.expression, bindings[2]!.expression] fun native => do
      let expression := native[0]!
      let indices ← sourceFiniteIndices (mkNatLit 2) 2
      for index in indices, binding in native.extract 1 3 do
        unless ← isDefEq (mkApp expression index) binding do
          throwError "a finite dependent tuple changed its actual indexed component"
        unless expression.containsFVar binding.fvarId! do
          throwError "a finite dependent tuple discarded an original component binding"
  let rejected ← try
    discard <| session.read (← sourceTerm "(a, b, a)") (some type.source) type.selections
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
  let term ← session.read (← sourceTerm "(b, a, b)") (some type.source) type.selections
  let expected ← session.term (← nativeTerm "![b, a, b]")
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm term
    let expected ← session.readTerm expected
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "a source vector tuple changed its original ordered components"
    return expression



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
  for (source, native) in #[
      ("Mat₂(S)", "CasCatalogue.Algebra.LinearAlgebra.matrices 2 S"),
      ("Mat₂(S) in Rings", "CasCatalogue.Algebra.LinearAlgebra.matrixRing 2 S")] do
    let value ← session.read (← sourceTerm source)
    let expected ← session.term (← nativeTerm native)
    discard <| session.elaborateScoped Syntax.missing do
      let expression ← session.readTerm value
      let expected ← session.readTerm expected
      let scope ← get
      let bindings ← authoredBindings
      unless (← visitNativeData (fun term =>
          originatesAt scope.context scope.selections term bindings[1]!.expression false)
          expression false) > 0 do
        liftM (m := TermElabM) <| throwError "a subscripted family discarded its actual coefficient binding"
      checkOriginal #[expression, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a subscripted family changed its selected declaration or coefficient object"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      return expression
  for (domain, source, native) in #[
      ("RectangularMatrices(1, 2, S)", "[a, b]", "![![a, b]]"),
      ("RectangularMatrices(2, 2, S)", "[a, b; b, a]", "![![a, b], ![b, a]]"),
      ("RectangularMatrices(3, 2, S)", "[a, b; b, a; a, a]",
        "![![a, b], ![b, a], ![a, a]]"),
      ("Mat₂(S)", "[a, b; b, a]", "![![a, b], ![b, a]]")] do
    let type ← session.read (← sourceTerm domain)
    let value ← session.read (← sourceTerm source) (some type.source) type.selections
    let expected ← session.term (← nativeTerm native)
    discard <| session.elaborateScoped Syntax.missing do
      let expression ← session.readTerm value
      let expected ← session.readTerm expected
      let scope ← get
      let bindings ← authoredBindings
      unless (← visitNativeData (fun term =>
          originatesAt scope.context scope.selections term bindings[1]!.expression false)
          (← inferType expression) false) > 0 do
        liftM (m := TermElabM) <| throwError "a source matrix discarded its selected coefficient object"
      checkOriginal #[expression, expected, bindings[2]!.expression, bindings[3]!.expression] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "a source finite matrix changed its declared dimensions or ordered cells"
        unless native[0]!.containsFVar native[2]!.fvarId! &&
            native[0]!.containsFVar native[3]!.fvarId! do
          throwError "a source matrix discarded its original cell bindings"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))
      return expression
  let type ← session.read (← sourceTerm "RectangularMatrices(2, 2, S)")
  for source in #["[a, b]", "[a; b]", "[a, b; b]"] do
    let rejected ← withoutModifyingState do
      try
        discard <| session.read (← sourceTerm source) (some type.source) type.selections
        pure false
      catch error =>
        let detail ← error.toMessageData.toString
        unless (detail.splitOn "finite arit").length > 1 do throw error
        pure true
    unless rejected do throwError "a finite matrix accepted a different declared shape"
  let session ← session.assume `ambientZero (← nativeTerm "OfNat (S : Type) 0") .instImplicit
  let session ← session.assume `ambientOne (← nativeTerm "OfNat (S : Type) 1") .instImplicit
  let type ← session.read (← sourceTerm "RectangularMatrices(1, 2, S)")
  let value ← session.read (← sourceTerm "[1, 0]") (some type.source) type.selections
  let expected ← session.term (← nativeTerm
    "![![TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Algebra.NamedRings.ringNumeral (CasCatalogue.Algebra.Algebras.commutativeRingsRings.toFunctor.obj S) 1)) default, TypeCat.Fun.toFun (TypeCat.Hom.hom (CasCatalogue.Algebra.NamedRings.ringNumeral (CasCatalogue.Algebra.Algebras.commutativeRingsRings.toFunctor.obj S) 0)) default]]")
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm value
    let expected ← session.readTerm expected
    let bindings ← authoredBindings
    checkOriginal #[expression, expected, bindings[4]!.expression, bindings[5]!.expression] fun native => do
      unless (← isDefEq native[0]! native[1]!) &&
          !native[0]!.containsFVar native[2]!.fvarId! &&
          !native[0]!.containsFVar native[3]!.fvarId! do
        throwError "matrix cells changed their selected coefficient or declared point maps"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
    return expression
