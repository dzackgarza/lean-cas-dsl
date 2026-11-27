module

import CasCompiler.RecordAction
public meta import Lean.Elab.Command
meta import CasCompiler.RecordAction

open Lean Meta CasCompiler



run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let pair ← mkAppM ``Prod.mk #[mkNatLit 8, mkNatLit 8]
  let pairLayout ← SourceLayout.ofTerm (← context.close pair)
  let some second := pairLayout.fields[1]?
    | throwError "the original pair lost its second source field"
  unless (← pairLayout.actionInputs context pair #[second]).isEmpty do
    throwError "an independent record field acquired an unrelated earlier input"

  let family ← withLocalDeclD `n (mkConst ``Nat) fun n =>
    mkLambdaFVars #[n] (mkApp (mkConst ``Fin) (mkApp2 (mkConst ``Nat.add) n (mkNatLit 1)))
  let point := mkApp (mkConst ``Fin.last) (mkNatLit 5)
  let source ← mkAppOptM ``Sigma.mk #[some (mkConst ``Nat), some family,
    some (mkNatLit 5), some point]
  let layout ← SourceLayout.ofTerm (← context.close source)
  let some dependent := layout.fields[1]?
    | throwError "the original dependent pair lost its second source field"
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  SourceSelectionScope.withBinding identities {} context { value := source }
      fun context _ retained => do
    let #[input] ← layout.actionInputs context retained #[dependent]
      | throwError "the dependent field did not retain exactly its declared earlier slot"
    unless input.sourceIndex == 0 && input.projection == ``Sigma.fst do
      throwError "the dependent field changed its original source slot"
    let term ← input.source.inContext context
    let some projection ← SourceProjection.ofExpr? term
      | throwError "the prepared input lost its original native projection"
    unless projection.parent == retained && projection.declaration == ``Sigma.fst do
      throwError "a prepared dependency replaced its selected original record parent"

  let proofFamily ← withLocalDeclD `h (mkConst ``True) fun h =>
    mkLambdaFVars #[h] (mkConst ``Nat) (usedOnly := false)
  let proofFirst ← mkAppOptM ``PSigma.mk #[some (mkConst ``True), some proofFamily,
    some (mkConst ``True.intro), some (mkNatLit 8)]
  let proofLayout ← SourceLayout.ofTerm (← context.close proofFirst)
  let some data := proofLayout.fields[1]?
    | throwError "proof erasure changed a native source field position"
  unless data.sourceIndex == 1 && data.wireIndex == some 0 &&
      (← proofLayout.actionInputs context proofFirst #[data]).isEmpty do
    throwError "a formal proof became a computational preceding input"

  let changed ← mkAppM ``Prod.mk #[mkNatLit 9, mkNatLit 8]
  let rejected ← try
      discard <| pairLayout.actionInputs context changed #[second]
      pure false
    catch _ => pure true
  unless rejected do
    throwError "record dependency preparation admitted another native parent"
