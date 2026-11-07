module

import CasRuntime.Materialize
import CasRuntime.Transport
public meta import Lean.Elab.Command
meta import CasRuntime.Materialize
meta import CasRuntime.Transport

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- The public SDK echoes packets and exports a stored diagnostic callable; it computes no mathematics.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "materialization-peer" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the materialization control peer did not negotiate"
    try
      let context ← ContextTelescope.capture #[]
      let transaction ← CellTransaction.begin ledger
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let prepare (term : Expr) (occurrence : RuntimeId .occurrence) :
          MetaM PreparedRequest := do
        let type ← inferType term
        let identity ← context.close (mkConst ``id [← getLevel type])
        let layout ← SourceLayout.ofTerm identity
        let callable ← liftM (m := IO) <| transaction.stage
          { program, occurrence, role := layout, parameters := #[] } (.closure program #[])
        PreparedRequest.forApplication program occurrence context callable
          #[← context.close type, ← context.close term] #[] #[]
      let nativeOccurrence ← liftM (m := BaseIO) ledger.allocate
      let nativeRequest ← prepare (mkConst ``Nat.succ) nativeOccurrence
      let selected : DispatchIdentity := {
        manifestDigest := "materialization-manifest", profileDigest := "materialization-profile"
        registration := {
          operation := "stored", input := "materialization#input", backend := wire.backend } }
      let .ok reservation ← liftM (m := BaseIO) <|
        transaction.reserve nativeOccurrence selected wire.connection #[]
        | throwError "the native result control could not reserve"
      let before ← liftM (m := IO) transaction.view
      let scope ← liftM (m := IO) <| RequestScope.issue ledger reservation before #[] #[] #[]
      let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger transaction reservation scope
        (.str "retained diagnostic callable") 5000
        | throwError "the native result control did not return"
      let (draft, native) ← reply.materialize nativeRequest transaction scope wire.connection
      let some node := draft.view.find native.root.value
        | throwError "materialization lost the returned native node"
      let .ownedToken owner token captures := node.payload.data
        | throwError "materialization replaced the actual native export"
      unless owner == wire.connection.generation && captures.isEmpty &&
          reply.exports.any (·.token == token) do
        throwError "materialization changed the actual native owner, token or capture table"
      if ((← liftM (m := IO) transaction.view).find native.root.value).isSome then
        throwError "materialization installed a tentative native reply"
      let .ok () ← liftM (m := BaseIO) <| transaction.installDraft draft
        | throwError "the complete native draft could not enter the active graph"
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
      let request ← prepare pair occurrence
      let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      let scalar ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
      let selected := { selected with registration := { selected.registration with operation := "echo" } }
      let .ok reservation ← liftM (m := BaseIO) <|
        transaction.reserve occurrence selected wire.connection #[scalar, native.root]
        | throwError "the joint result control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let scope ← liftM (m := IO) <|
        RequestScope.issue ledger reservation graph #[scalar, native.root] #[] #[]
      let packet := Json.arr #[(ScopedReference.scope 0).encode, (ScopedReference.scope 1).encode]
      let .ok reply ← liftM (m := IO) <|
        wire.invokeBefore ledger transaction reservation scope packet 5000
        | throwError "the joint result control did not return"
      let (draft, response) ← reply.materialize request transaction scope wire.connection
      let .ok first := draft.view.project response.root 0
        | throwError "the materialized record lost its first actual field"
      let .ok second := draft.view.project response.root 1
        | throwError "the materialized record lost its actual callable"
      unless first.value == scalar.value && second.value == native.root.value &&
          second.instantiations.size == native.root.instantiations.size + 1 do
        throwError "joint materialization replaced a retained input or its consuming role"
      if ((← liftM (m := IO) transaction.view).find response.root.value).isSome then
        throwError "joint materialization exposed an uninstalled result"
      let some node := draft.view.find response.root.value
        | throwError "the materialized literal packet is absent"
      let .container stored := node.payload.data
        | throwError "joint materialization discarded the original packet structure"
      let .ok filled := stored.fill #[.str "scalar-slot", .str "callable-slot"]
        | throwError "the materialized packet lost its exact reference positions"
      unless filled == Json.arr #[.str "scalar-slot", .str "callable-slot"] do
        throwError "materialization changed its original packet layout"
      if ((← SessionSnapshot.current).graph.find response.root.value).isSome then
        throwError "materialization published a tentative reply"
      let aliasOccurrence ← liftM (m := BaseIO) ledger.allocate
      let aliasRequest ← prepare (mkNatLit 7) aliasOccurrence
      let .ok aliasReservation ← liftM (m := BaseIO) <|
        transaction.reserve aliasOccurrence selected wire.connection #[scalar]
        | throwError "the returned-reference control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let aliasScope ← liftM (m := IO) <|
        RequestScope.issue ledger aliasReservation graph #[scalar] #[] #[]
      let .ok aliasReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        aliasReservation aliasScope (ScopedReference.scope 0).encode 5000
        | throwError "the returned-reference control did not return"
      let (aliasDraft, aliasValue) ←
        aliasReply.materialize aliasRequest transaction aliasScope wire.connection
      unless aliasValue.root.value == scalar.value && aliasDraft.view.sameRevision graph do
        throwError "returning a reference allocated a replacement value"
      let .ok () ← liftM (m := BaseIO) <| transaction.installDraft aliasDraft
        | throwError "a complete reply containing only an existing reference could not install"
      match ← liftM (m := BaseIO) <| transaction.installDraft aliasDraft with
      | .error .staleDraft => pure ()
      | _ => throwError "a reference-only reply draft installed twice"
      let badOccurrence ← liftM (m := BaseIO) ledger.allocate
      let badRequest ← prepare pair badOccurrence
      let boolRole ← SourceLayout.ofTerm (← context.close (mkConst ``Bool.true))
      let wrong ← liftM (m := IO) <| transaction.stage
        { program, occurrence := badOccurrence, role := boolRole, parameters := #[] }
        (.portable "true".toUTF8)
      let .ok badReservation ← liftM (m := BaseIO) <|
        transaction.reserve badOccurrence selected wire.connection #[wrong]
        | throwError "the joint rejection control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let badScope ← liftM (m := IO) <|
        RequestScope.issue ledger badReservation graph #[wrong] #[] #[]
      let .ok badReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        badReservation badScope (.arr #[toJson (7 : Nat), (ScopedReference.scope 0).encode]) 5000
        | throwError "the joint rejection control did not return"
      let failure : Option Exception ← try
        discard <| badReply.materialize badRequest transaction badScope wire.connection
        pure none
      catch error => pure (some error)
      let some failure := failure | throwError "joint materialization accepted a mistyped later field"
      unless (← failure.toMessageData.toString).startsWith
          "the runtime value has an incompatible complete source type" do throw failure
      unless (← liftM (m := IO) transaction.view).sameRevision graph do
        throwError "a rejected later field installed an earlier tentative reply prefix"
      discard <| liftM (m := BaseIO) transaction.abort
    finally liftM (m := IO) wire.close
  finally setEnv original
