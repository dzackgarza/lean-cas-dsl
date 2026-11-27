module

import CasRuntime.CallableView
public meta import Lean.Elab.Command
meta import CasRuntime.CallableView

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- The real scope parser supplies every input/result reference. Literal inventories and
-- reference-held portable points have one computational framing, while opaque points
-- keep their exact original identities. The cat process supplies no mathematical answer.
run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    let program ← owners.identities.fresh .program
    let produced ← ledger.allocate
    let origin := { program, occurrence := produced, role, parameters := #[] : ValueOrigin }
    let (graph, zero) ← (ValueGraph.empty owners.identities).stage owners.identities origin
      (.portable "0".toUTF8)
    let (graph, one) ← graph.stage owners.identities origin (.portable "1".toUTF8)
    let (graph, three) ← graph.stage owners.identities origin (.portable "3".toUTF8)
    let (graph, four) ← graph.stage owners.identities origin (.portable "4".toUTF8)
    let owner ← owners.spawn { cmd := "/bin/cat" }
    try
      owner.child.stdin.putStr "original-point\n"
      owner.child.stdin.flush
      let token := (← owner.child.stdout.getLine).trimAscii.toString
      let (graph, opaquePoint) ← graph.stage owners.identities origin
        (.ownedExport owner token #[])
      let (graph, otherOpaquePoint) ← graph.stage owners.identities origin
        (.ownedExport owner (token ++ "-other") #[])
      let occurrence ← ledger.allocate
      let transaction ← owners.identities.fresh .transaction
      let selected : DispatchIdentity := {
        manifestDigest := "callable-framing", profileDigest := "callable-framing"
        registration := { operation := "callable-framing", input := "callable-framing",
          backend := "cat" } }
      let values := #[zero, zero, one, three, four, opaquePoint, opaquePoint, otherOpaquePoint]
      let .ok reservation ← ledger.reserve occurrence transaction selected owner graph values
        | throw <| IO.userError "the callable framing scope could not reserve"
      let inputPath := #[InputPathStep.field "original", .index 0]
      let scope ← RequestScope.issue ledger reservation graph values
        #[{ path := inputPath, binding := zero }] #[one]
      let frame := fun value => Json.mkObj [("request_id", toJson (73 : Nat)),
        ("status", toJson "ok"), ("value", value), ("exports", Json.arr #[])]
      let domain := some (#[toJson (0 : Nat), toJson (1 : Nat)].map CallableDatum.literal)
      let target := some (#[toJson (3 : Nat), toJson (4 : Nat)].map CallableDatum.literal)
      let referenceGraph := Json.arr #[
        Json.arr #[(ScopedReference.input inputPath).encode, (ScopedReference.scope 3).encode],
        Json.arr #[(ScopedReference.result 0).encode, (ScopedReference.scope 4).encode]]
      let mixedGraph := Json.arr #[
        Json.arr #[(ScopedReference.scope 1).encode, toJson (3 : Nat)],
        Json.arr #[toJson (1 : Nat), (ScopedReference.scope 4).encode]]
      for packet in #[referenceGraph, mixedGraph] do
        let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 73 (frame packet)
        let original := reply.references.map fun reference =>
          (reference.path, reference.binding.value, reference.binding.associationIds)
        let .ok admitted := CallablePacket.finiteWith packet domain target
            (fun value path => reply.callableDatum graph value path)
          | throw <| IO.userError "original reference points did not match their literal inventory"
        unless admitted.value == packet && original == reply.references.map (fun reference =>
            (reference.path, reference.binding.value, reference.binding.associationIds)) do
          throw <| IO.userError "graph framing changed original packet references"
      let duplicate := Json.arr #[
        Json.arr #[(ScopedReference.scope 0).encode, toJson (3 : Nat)],
        Json.arr #[(ScopedReference.scope 1).encode, toJson (4 : Nat)]]
      let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 73 (frame duplicate)
      if (CallablePacket.finiteWith duplicate domain target
          (fun value path => reply.callableDatum graph value path)).isOk then
        throw <| IO.userError "different wire aliases concealed a repeated actual graph key"
      for key in #[6, 7] do
        let packet := Json.mkObj [("ctor", toJson "finiteGraph"),
          ("args", Json.arr #[Json.arr #[(ScopedReference.scope 5).encode],
            Json.arr #[Json.arr #[(ScopedReference.scope key).encode, toJson (3 : Nat)]]])]
        let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 73 (frame packet)
        let admitted := CallablePacket.finiteWith packet none target
          (fun value path => reply.callableDatum graph value path)
        unless admitted.isOk == (key == 6) do
          throw <| IO.userError "opaque graph keys lost their exact original reference identity"
      scope.retire
      discard <| ledger.retire reservation
    finally owners.close owner.generation
