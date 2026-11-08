module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native operation parameter did not parse"
  return ⟨stx⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source operation did not parse"
  return ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `a (← nativeTerm "Rat")
  let session ← session.assume `b (← nativeTerm "Rat")
  let type ← session.term (← nativeTerm "Rat")
  for (source, declaration) in #[
      ("a + b", ``CasCatalogue.Algebra.NamedRings.add),
      ("a · b", ``CasCatalogue.Algebra.NamedRings.mul),
      ("-a", ``CasCatalogue.Algebra.NamedRings.neg),
      ("a ^ 2", ``CasCatalogue.Algebra.NamedRings.pow)] do
    let term ← session.read (← sourceTerm source) (some type.source)
    term.source.withOpen fun bindings expression => do
      unless expression.containsConst (· == declaration) &&
          expression.containsFVar bindings[0]!.expression.fvarId! do
        throwError "a source scalar operation changed its declared operation or first operand"
      if source == "a + b" || source == "a · b" then
        unless expression.containsFVar bindings[1]!.expression.fvarId! do
          throwError "a binary source operation lost its second original operand"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let rings ← parameters.namedCategory Syntax.missing "Rings" [.zero] #[]
  let ring ← parameters.term (← nativeTerm "R")
  let selected ← ring.inCategory rings.expression rings.value
  let session ← parameters.defineTerm `S selected
  let session ← session.assume `x (← nativeTerm "S")
  let session ← session.assume `y (← nativeTerm "S")
  let session ← session.assume `customAddition (← nativeTerm "Add S") .instImplicit
  let term ← session.read (← sourceTerm "x + y")
  term.source.withOpen fun bindings expression => do
    let pair ← mkAppM ``Prod.mk #[bindings[2]!.expression, bindings[3]!.expression]
    let addition ← mkAppM ``CasCatalogue.Algebra.NamedRings.add #[bindings[1]!.expression]
    let function ← mkAppM ``TypeCat.Hom.hom #[addition]
    let function ← mkAppM ``TypeCat.Fun.toFun #[function]
    let expected := mkApp function pair
    unless ← isDefEq expression expected do
      throwError "source addition differs from its complete selected native map"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl expression) (← mkEq expression expected))
    unless expression.containsConst (· == ``CasCatalogue.Algebra.NamedRings.add) &&
        expression.containsFVar bindings[1]!.expression.fvarId! &&
        expression.containsFVar bindings[2]!.expression.fvarId! &&
        expression.containsFVar bindings[3]!.expression.fvarId! &&
        !expression.containsFVar bindings[4]!.expression.fvarId! do
      throwError "a source operation changed its selected ring, operands or dictionary"
  let session ← session.defineTerm `sum term
  let session ← session.assume `S (← nativeTerm "RingCat.{0}")
  let retained ← session.read (← sourceTerm "sum")
  retained.source.withOpen fun bindings expression => do
    unless expression == bindings[5]!.expression do
      throwError "a source operation was reconstructed after its structure name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let parameters ← empty.assume `A (← nativeTerm "Type")
  let parameters ← parameters.assume `first (← nativeTerm "Ring A")
  let parameters ← parameters.assume `second (← nativeTerm "Ring A")
  let rings ← parameters.namedCategory Syntax.missing "Rings" [.zero] #[]
  let first ← parameters.term (← nativeTerm "@RingCat.of A first")
  let first ← first.inCategory rings.expression rings.value
  let parameters ← parameters.defineTerm `R first
  let second ← parameters.term (← nativeTerm "@RingCat.of A second")
  let second ← second.inCategory rings.expression rings.value
  let session ← parameters.defineTerm `S second
  let session ← session.assume `x (← nativeTerm "R")
  let session ← session.assume `y (← nativeTerm "S")
  let rejected ← withoutModifyingState do
    try
      discard <| session.read (← sourceTerm "x + y")
      pure false
    catch error =>
      let message ← error.toMessageData.toString
      return (message.splitOn "selected common refinement").length > 1
  unless rejected do
    throwError "equal carriers selected one of two independently supplied ring structures"
