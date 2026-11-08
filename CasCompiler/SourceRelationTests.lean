module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok source := Parser.runParserCategory (← getEnv) `term text
    | throwError "the retained native relation source did not parse"
  return ⟨source⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original relation source did not parse"
  return ⟨source⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  for name in #["FinOrder", "ReverseFinOrder"] do
    let object ← empty.read (← sourceTerm s!"{name}(5)")
    let session ← empty.defineTerm `X object
    let session ← session.assume `unused (← `(Nat))
    for (text, declaration) in #[
        ("0 ≤ 1 in X", ``CasCatalogue.Foundation.PowerSets.le),
        ("0 < 1 in X", ``CasCatalogue.Foundation.PowerSets.lt)] do
      let expected ← session.elaborate Syntax.missing fun context => do
        let object ← object.source.inContext context
        let operation ← mkAppM declaration #[object]
        let function ← sourceSetFunction operation
        let pair : Term ← `((0, 1))
        let value ← elabTermEnsuringType pair
          (some (← inferType function).bindingDomain!)
        elabAppArgs function #[] #[Arg.expr value] (some (mkSort .zero)) false false
      let question ← session.readQuestion (← sourceTerm text)
      question.source.withOpen fun bindings value => do
        let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
        unless bindings.size == 2 && (← isDefEq value expected) do
          throwError "the source relation changed its actual selected structure or context"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `L (← `(LinOrd.{0}))
  let category ← session.namedCategory Syntax.missing "LinearOrders" [.zero] #[]
  let object ← session.term (← nativeTerm "L")
  let object ← object.inCategory category.expression category.value
  let session ← session.defineTerm `A object
  let session ← session.assume `x (← nativeTerm "CasCatalogue.Foundation.PowerSets.orderCarrier A")
  let session ← session.assume `y (← nativeTerm "CasCatalogue.Foundation.PowerSets.orderCarrier A")
  let session ← session.assume `unused (← `(Nat))
  let expected ← session.term (← nativeTerm "CasCatalogue.Foundation.PowerSets.le A (x, y)")
  for (text, truth) in #[
      ("x ≤ y", none), ("(x ≤ y) = false", some ``False),
      ("(x ≤ y) = true", some ``True)] do
    let question ← session.readQuestion (← sourceTerm text)
    question.source.withOpen fun bindings value => do
      let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
      let expected ← match truth with
        | none => pure expected
        | some declaration => mkEq expected (mkConst declaration)
      unless bindings.size == 5 && (← isDefEq value expected) do
        throwError "the relation or truth constant changed its arbitrary selected order"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let session ← session.assume `false (← `(Prop))
  let question ← session.readQuestion (← sourceTerm "(x ≤ y) = false")
  question.source.withOpen fun bindings value => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    let expected ← mkEq expected bindings[5]!.expression
    unless ← isDefEq value expected do
      throwError "a logical spelling displaced its exact lexical binding"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let expected ← session.term (← nativeTerm
    "CasCatalogue.Foundation.PowerSets.le CasCatalogue.Foundation.PowerSets.orderIntegers (0, 1)")
  let question ← session.readQuestion (← sourceTerm "0 ≤ 1")
  question.source.withOpen fun bindings value => do
    let expected ← expected.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq value expected do
      throwError "the relation's truth-value result replaced its declared integral literal domain"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
