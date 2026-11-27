module

import CasCompiler.Read
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

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
      let question ← session.readQuestion (← sourceTerm text)
      discard <| session.elaborateScoped Syntax.missing do
        let value ← session.readTerm question
        let object ← session.readTerm object
        unless (← authoredBindings).size == 2 do
          throwError "the source relation changed its complete preceding context"
        let scope ← get
        liftM (m := TermElabM) <| controlAt MetaM fun run =>
          scope.context.withOriginalSources #[value, object] fun native => run do
            let operation ← mkAppM declaration #[native[1]!]
            let function ← sourceSetFunction operation
            let pair : Term ← `((0, 1))
            let argument ← elabTermEnsuringType pair
              (some (← inferType function).bindingDomain!)
            let expected ← elabAppArgs function #[] #[Arg.expr argument]
              (some (mkSort .zero)) false false
            unless ← isDefEq native[0]! expected do
              throwError "the source relation changed its actual selected structure"
            checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
              (← mkEq native[0]! expected))
        return value

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
    discard <| session.elaborateScoped Syntax.missing do
      let value ← session.readTerm question
      let expected ← session.readTerm expected
      unless (← authoredBindings).size == 5 do
        throwError "the relation or truth constant changed its complete preceding context"
      checkOriginal #[value, expected] fun native => do
        let expected ← match truth with
          | none => pure native[1]!
          | some declaration => mkEq native[1]! (mkConst declaration)
        unless ← isDefEq native[0]! expected do
          throwError "the relation or truth constant changed its arbitrary selected order"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! expected))
      return value
  let session ← session.assume `false (← `(Prop))
  let question ← session.readQuestion (← sourceTerm "(x ≤ y) = false")
  discard <| session.elaborateScoped Syntax.missing do
    let value ← session.readTerm question
    let expected ← session.readTerm expected
    let bindings ← authoredBindings
    checkOriginal #[value, expected, bindings[5]!.expression] fun native => do
      let expected ← mkEq native[1]! native[2]!
      unless ← isDefEq native[0]! expected do
        throwError "a logical spelling displaced its exact lexical binding"
    return value

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let expected ← session.term (← nativeTerm
    "CasCatalogue.Foundation.PowerSets.le CasCatalogue.Foundation.PowerSets.orderIntegers (0, 1)")
  let question ← session.readQuestion (← sourceTerm "0 ≤ 1")
  discard <| session.elaborateScoped Syntax.missing do
    let value ← session.readTerm question
    let expected ← session.readTerm expected
    checkOriginal #[value, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "the relation's truth-value result replaced its declared integral literal domain"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
    return value
