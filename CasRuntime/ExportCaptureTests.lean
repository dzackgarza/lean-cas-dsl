module

import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- Real SDK traffic must transfer original input positions into fresh capture slots.
run_cmd Lean.Elab.Command.liftTermElabM <| liftM (m := MetaM) do
  let original ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "capture-peer" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the export capture peer did not negotiate"
    try
      let transaction ← CellTransaction.begin ledger
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let context ← ContextTelescope.capture #[]
      let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      let first ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
      let second ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
      let selected : DispatchIdentity := {
        manifestDigest := "capture-control", profileDigest := "capture-control"
        registration := { operation := "captured", input := "capture#input", backend := wire.backend } }
      let .ok reserved ← liftM (m := BaseIO) <|
          transaction.reserve occurrence selected wire.connection #[first, second]
        | throwError "the capture producer could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let scope ← liftM (m := IO) <| RequestScope.issue ledger reserved graph #[]
        #[{ path := #[.field "first"], binding := first },
          { path := #[.field "second"], binding := second }] #[]
      let .ok produced ← liftM (m := IO) <| wire.invokeBefore ledger transaction reserved scope
          (Json.mkObj [("first", toJson (7 : Nat)), ("second", toJson (7 : Nat))]) 5000
        | throwError "the SDK did not produce its captured callable"
      let some exported := produced.exports[0]?
        | throwError "the captured callable has no export declaration"
      unless exported.captures.map (·.value) == #[first.value, second.value] do
        throwError "capture admission changed its ordered original input positions"
      let function ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
      let callable ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := function, parameters := #[] }
        (.ownedExport wire.connection exported.token exported.captures)
      liftM (m := BaseIO) scope.retire
      for _ in [:2] do
        let invocation ← liftM (m := BaseIO) ledger.allocate
        let .ok reserved ← liftM (m := BaseIO) <|
            transaction.reserveExport invocation callable wire.connection #[]
          | throwError "a retained capture invocation could not reserve"
        let graph ← liftM (m := IO) transaction.view
        let scope ← liftM (m := IO) <| RequestScope.issue ledger reserved graph #[] #[] #[]
        let arguments := Json.mkObj [
          ("kind", .str "dependent"), ("prepared_role", .str "capture-control"),
          ("parameters", .arr #[]), ("bindings", .arr #[]), ("arguments", .arr #[]),
          ("argument_layouts", .arr #[]), ("result_layout", Json.mkObj [("kind", .str "data")])]
        let .ok reply ← liftM (m := IO) <|
            wire.invokeBefore ledger transaction reserved scope arguments 5000
          | throwError "the captured SDK callable did not run in its fresh capture frame"
        unless reply.references.map (·.binding.value) == #[second.value, first.value] do
          throwError "the capture frame changed the original proxy correspondence"
        liftM (m := BaseIO) scope.retire
      discard <| liftM (m := BaseIO) transaction.abort
    finally liftM (m := IO) wire.close
  finally setEnv original
