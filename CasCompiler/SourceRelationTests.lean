module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders

open Lean Meta Elab Term CasCompiler CasCatalogue

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
