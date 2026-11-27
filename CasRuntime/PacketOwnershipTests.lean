module

import CasRuntime.CallableView
import CasRuntime.FixedValue
import CasRuntime.Encode
public meta import Lean.Elab.Command
meta import CasRuntime.CallableView
meta import CasRuntime.FixedValue
meta import CasRuntime.Encode

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- An actual supplying process returns a diagnostic token. Repeated packet positions retain
-- that handle and its exact captures; they do not acquire native point identities.
run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
  let callable ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    let supplier ← owners.spawn { cmd := "/bin/cat" }
    let receiver ← owners.spawn { cmd := "/bin/cat" }
    try
      supplier.child.stdin.putStr "inert-point-handle\n"
      supplier.child.stdin.flush
      let token := (← supplier.child.stdout.getLine).trimAscii.toString
      let program ← owners.identities.fresh .program
      let occurrence ← ledger.allocate
      let origin := { program, occurrence, role := scalar, parameters := #[] : ValueOrigin }
      let (graph, first) ← (ValueGraph.empty owners.identities).stage owners.identities origin
        (.portable "0".toUTF8)
      let (graph, second) ← graph.stage owners.identities origin (.portable "0".toUTF8)
      let (graph, image) ← graph.stage owners.identities origin (.portable "3".toUTF8)
      let values := #[first, second, image]
      let selected : DispatchIdentity := {
        manifestDigest := "packet-ownership", profileDigest := "packet-ownership"
        registration := {
          operation := "packet-ownership", input := "packet-ownership", backend := "cat" } }
      let transaction ← owners.identities.fresh .transaction
      let .ok reservation ← ledger.reserve occurrence transaction selected supplier graph values
        | throw <| IO.userError "the original packet scope could not reserve"
      let scope ← RequestScope.issue ledger reservation graph values #[] #[]
      let point := (ComputationalValue.opaque token).encode
      let packet := Json.mkObj [("ctor", toJson "finiteGraph"),
        ("args", .arr #[.arr #[point],
          .arr #[.arr #[point, (ScopedReference.scope 2).encode]]])]
      let encodedPacket := Json.mkObj [("ctor", toJson "finiteGraph"),
        ("args", .arr #[.arr #[point], .arr #[.arr #[point, toJson (3 : Nat)]]])]
      let frame := fun capture => Json.mkObj [
        ("request_id", toJson (91 : Nat)), ("status", toJson "ok"), ("value", packet),
        ("exports", .arr #[Json.mkObj [("token", toJson token),
          ("captures", .arr #[(ScopedReference.scope capture).encode])]])]
      let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 91 (frame 0)
      let .ok admitted := CallablePacket.finiteWith packet none
          (some #[CallableDatum.literal (toJson (3 : Nat))])
          (fun value path => reply.callableDatum graph value path)
        | throw <| IO.userError "the same admitted inert handle lost its finite framing"
      let descriptor ← IO.ofExcept <|
        (reply.packetDescriptor graph supplier #[]).mapError IO.userError
      let #[firstExport, secondExport] := descriptor.exports
        | throw <| IO.userError "inert framing changed the complete original export positions"
      unless
          descriptor.slots.map (·.binding.value) == #[image.value] &&
          firstExport.path != secondExport.path &&
          firstExport.originPath != secondExport.originPath &&
          descriptor.exports.all (fun owned =>
            owned.originScope == reply.scopeId && owned.originPath == owned.path &&
              owned.owner == supplier.generation && owned.token == token &&
              owned.captures.map (·.value) == #[first.value]) do
        throw <| IO.userError "inert framing merged packet positions or changed actual captures"
      let fragment ← IO.ofExcept <|
        (reply.packetDescriptor graph supplier firstExport.path).mapError IO.userError
      let #[fragmentExport] := fragment.exports
        | throw <| IO.userError "an original export fragment changed its complete slot"
      let moved := fragmentExport.prefixed #[.field "nested"]
      unless fragmentExport.path.isEmpty && fragmentExport.originScope == firstExport.originScope &&
          fragmentExport.originPath == firstExport.originPath &&
          moved.path == #[.field "nested"] && moved.originScope == fragmentExport.originScope &&
          moved.originPath == fragmentExport.originPath do
        throw <| IO.userError "packet prefixing changed the original reply export occurrence"
      let (framed, framingBindings, framingExports) ← IO.ofExcept <|
        (ValueContainer.nativeFraming #[descriptor, descriptor, fragment]).mapError IO.userError
      let #[framingFirst, framingSecond] := framingExports
        | throw <| IO.userError "native framing changed the complete original export table"
      unless framed.size == 3 && framingBindings.size == 2 &&
          framingFirst.originPath != framingSecond.originPath do
        throw <| IO.userError "native framing merged equal tokens from distinct original positions"
      let .ok firstGraph := (framed[0]!.getObjVal? "args").bind (·.getArr?)
        | throw <| IO.userError "native framing lost the original complete graph"
      let .ok inventory := firstGraph[0]!.getArr?
        | throw <| IO.userError "native framing lost the original graph inventory"
      unless inventory[0]! == (ScopedReference.scope 2).encode &&
          framed[2]! == (ScopedReference.scope 2).encode do
        throw <| IO.userError "a repeated original export fragment received another native position"
      let conflict ← IO.ofExcept <| (PacketExport.fromConnection receiver
        fragmentExport.originScope fragmentExport.originPath fragmentExport.path
        fragmentExport.token fragmentExport.captures).mapError IO.userError
      let conflictPayload ← IO.ofExcept <|
        (ValuePayload.descriptor fragment.template fragment.slots #[conflict]).mapError IO.userError
      let .container conflictPacket := conflictPayload.data
        | throw <| IO.userError "the conflict control lost its original descriptor"
      if (ValueContainer.nativeFraming #[fragment, conflictPacket]).isOk then
        throw <| IO.userError "one original opaque position accepted another supplying owner"
      let payload ← IO.ofExcept <|
        (ValuePayload.callablePacket admitted descriptor.slots none descriptor.exports
          (some descriptor)).mapError IO.userError
      let (graph, stored) ← graph.stage owners.identities { origin with role := callable } payload
      let some node := graph.find stored.value
        | throw <| IO.userError "the complete inert callable disappeared"
      let .container retained := node.payload.data
        | throw <| IO.userError "inert callable admission replaced its complete packet"
      unless retained.callableData && retained.retainsOriginalPacket descriptor do
        throw <| IO.userError "the completed callable lost its original packet snapshot"
      unless (← IO.ofExcept <| (graph.requiredOwners #[stored]).mapError IO.userError) ==
          #[supplier.generation] &&
          node.references.any (fun value => value.value == first.value) do
        throw <| IO.userError "owner-only packet captures were omitted from graph retention"
      let path := #[InputPathStep.field "actual-map"]
      let ownerInputs ← IO.ofExcept <|
        (graph.encodeInputs supplier.generation #[{ path, binding := stored }]).mapError IO.userError
      unless ownerInputs.values == #[encodedPacket] && ownerInputs.slots.isEmpty do
        throw <| IO.userError "the actual owner lost the complete original callable packet"
      let foreign ← IO.ofExcept <|
        (graph.encodeInputs receiver.generation #[{ path, binding := stored }]).mapError IO.userError
      unless foreign.values == #[(ScopedReference.scope 0).encode] &&
          foreign.slots.map (·.value) == #[stored.value] do
        throw <| IO.userError "a foreign receiver exposed an owned leaf or lost the whole map"
      if (retained.fillForOwner receiver.generation #[toJson (3 : Nat)]).isOk then
        throw <| IO.userError "a foreign owner received an inert token directly"
      let changed ← ImmediateReply.parseControl scope reservation graph scope.wireId 91 (frame 1)
      let changedDescriptor ← IO.ofExcept <|
        (changed.packetDescriptor graph supplier #[]).mapError IO.userError
      if retained.retainsOriginalPacket changedDescriptor then
        throw <| IO.userError "equal captured bytes substituted another original capture"
      let otherOccurrence ← ledger.allocate
      let otherTransaction ← owners.identities.fresh .transaction
      let .ok otherReservation ← ledger.reserve otherOccurrence otherTransaction selected
          supplier graph values
        | throw <| IO.userError "the independent original packet scope could not reserve"
      let otherScope ← RequestScope.issue ledger otherReservation graph values #[] #[]
      let otherReply ← ImmediateReply.parseControl otherScope otherReservation graph
        otherScope.wireId 91 (frame 0)
      let otherDescriptor ← IO.ofExcept <|
        (otherReply.packetDescriptor graph supplier #[]).mapError IO.userError
      if retained.retainsOriginalPacket otherDescriptor then
        throw <| IO.userError "identical export bytes replaced another original reply scope"
      otherScope.retire
      discard <| ledger.retire otherReservation
      if (← IO.ofExcept <|
          (changed.retainsValue graph supplier packet #[] stored).mapError IO.userError) then
        throw <| IO.userError "fixed callable reuse accepted the same token with wrong captures"
      let (graph, dependent) ← graph.stage owners.identities { origin with role := callable }
        (.closure program #[stored])
      scope.retire
      discard <| ledger.retire reservation
      owners.close supplier.generation
      if (← graph.isAvailable owners stored) || (← graph.isAvailable owners dependent) then
        throw <| IO.userError "owner death left an inert callable or dependent continuation live"
    finally
      owners.close supplier.generation
      owners.close receiver.generation
