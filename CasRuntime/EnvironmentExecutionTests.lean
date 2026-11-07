module

import CasRuntime.Execute
public meta import Lean.Elab.Command
meta import CasRuntime.Execute

open Lean Meta CasCompiler CasRuntime

private def noExternalRegistration (request : PreparedRequest) (_ : CellTransaction) :
    MetaM (CandidateResponse request.source × CellTransaction) :=
  throwError "unavailable: no external registration in this source-context control"

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
    let callableRole ← SourceLayout.ofTerm (← empty.close (mkConst ``Nat.succ))
    let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let pairRole ← SourceLayout.ofTerm (← empty.close pair)
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let produced ← liftM (m := BaseIO) ledger.allocate
    let producer ← CellTransaction.begin ledger
    let scalar ← liftM (m := IO) <| producer.stage
      { program, occurrence := produced, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
    let pair ← liftM (m := IO) <| producer.stage
      { program, occurrence := produced, role := pairRole, parameters := #[] } (.product #[scalar, scalar])
    let .ok base ← producer.commit | throwError "the source-context inputs could not commit"
    let pending ← CellTransaction.begin ledger
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let token ← liftM (m := IO) do
        child.child.stdin.putStr "retained context callable\n"
        child.child.stdin.flush
        return (← child.child.stdout.getLine).trimAscii.toString
      let callable ← liftM (m := IO) <| pending.stage
        { program, occurrence := produced, role := callableRole, parameters := #[] } (.ownedExport child token #[])
      withLocalDeclD `unused (← inferType (mkConst ``Nat.succ)) fun unused => do
        let id : BindingId := ⟨"execution-context", 0⟩
        let context ← ContextTelescope.capture #[{ id, role := .parameter, expression := unused }]
        let graph ← liftM (m := IO) pending.view
        let .ok parameter := RuntimeParameter.ofValue graph id callable
          | throwError "the actual staged context value is missing"
        let parameters := #[parameter]
        let occurrence ← liftM (m := BaseIO) ledger.allocate
        let request ← PreparedRequest.forProjection program occurrence context graph pair 0 parameters
        let older ← CellTransaction.begin ledger
        let rejected ← do
          try
            discard <| Execute.run noExternalRegistration
              (PFunctor.FreeM.lift (P := OperationalSignature) request) older
            pure false
          catch error => do
            let message ← error.toMessageData.toString
            pure (message.endsWith "the value reference is outside the visible graph")
        unless rejected do
          throwError "a source/runtime table recovered a value absent from the transaction graph"
        unless (← liftM (m := BaseIO) older.activeGraph).isNone &&
            (← liftM (m := BaseIO) pending.activeGraph).isSome do
          throwError "source-context rejection settled the wrong transaction"
        unless (← SessionSnapshot.current).id == base.id do
          throwError "a rejected source context published a staged value"
        let .ok _ ← pending.commit | throwError "the actual context value could not commit"
        liftM (m := IO) <| owners.close child.generation
        let consumer ← CellTransaction.begin ledger
        let next ← liftM (m := BaseIO) ledger.allocate
        let request ← PreparedRequest.forProjection program next context graph pair 0 parameters
        let .ok (some retained) := request.environment.lookup id
          | throwError "the complete context lost its unused actual callable"
        unless retained.value == callable.value do
          throwError "source context capture replaced an existing runtime value"
        let response ← Execute.run noExternalRegistration
          (PFunctor.FreeM.lift (P := OperationalSignature) request) consumer
        unless response.root.value == scalar.value do
          throwError "an unused dead context owner changed the selected portable field"
        let .ok _ ← consumer.commit
          | throwError "an unused dead source-context value blocked independent publication"
    finally
      discard <| liftM (m := BaseIO) pending.abort
      liftM (m := IO) <| owners.close child.generation
  finally setEnv original
