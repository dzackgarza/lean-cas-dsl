module

import CasRuntime.Reply
public meta import Lean.Elab.Command
meta import CasRuntime.Reply

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    let program ← owners.identities.fresh .program
    let produced ← ledger.allocate
    let transaction ← owners.identities.fresh .transaction
    let (graph, input) ← (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence := produced, role } (.portable "retained input".toUTF8)
    let child ← owners.spawn { cmd := "/bin/cat" }
    try
      child.child.stdin.putStr "returned export token\n"
      child.child.stdin.flush
      let token := (← child.child.stdout.getLine).trimAscii.toString
      let occurrence ← ledger.allocate
      let selected : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := { operation := "resource-test", input := "resource-test", backend := "cat" }
        profileDigest := "resource-test-profile" }
      let .ok reservation ← ledger.reserve occurrence transaction selected child graph #[input]
        | throw <| IO.userError "the reply control could not reserve"
      let scope ← RequestScope.issue ledger reservation graph #[input, input] #[] #[]
      let reference := (ScopedReference.scope 0).encode
      let capture := (ScopedReference.scope 1).encode
      let exported := CasCatalogue.Backend.ComputationalValue.encode (.opaque token)
      let declaration := Json.mkObj [("token", .str token), ("captures", .arr #[reference, capture])]
      let makeFrame := fun (id : Nat) (value : Json) (exports : Array Json) => Json.mkObj [
        ("request_id", toJson id), ("status", .str "ok"), ("value", value), ("exports", .arr exports)]
      let frame := makeFrame (73 : Nat) (.arr #[reference, exported]) #[declaration]
      let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 73 frame
      unless reply.requestId == 73 && reply.scopeId == scope.id && reply.references.size == 1 do
        throw <| IO.userError "reply control validation lost its exact scope association"
      let some returned := reply.references[0]? | throw <| IO.userError "the returned reference is missing"
      unless returned.binding.value == input.value && returned.path == #[.index 0] do
        throw <| IO.userError "reply validation changed an actual retained reference"
      let some native := reply.exports[0]? | throw <| IO.userError "the native export declaration is missing"
      unless native.token == token && native.owner == child.generation && native.captures.size == 2 do
        throw <| IO.userError "reply control validation changed exports or capture authority"
      let malformed := #[
        makeFrame 74 (.arr #[reference, exported]) #[declaration],
        makeFrame 73 exported #[],
        makeFrame 73 exported #[declaration, declaration],
        makeFrame 73 exported #[Json.mkObj [("token", .str token)]],
        makeFrame 73 exported #[Json.mkObj [
          ("token", .str token), ("captures", .arr #[reference, reference])]],
        makeFrame 73 exported #[Json.mkObj [
          ("token", .str token), ("captures", .arr #[]), ("owner", .str "claimed")]],
        Json.mkObj [("request_id", toJson (73 : Nat)), ("status", .str "ok"),
          ("value", exported), ("exports", .arr #[declaration]), ("owner", .str "claimed")],
        makeFrame 73 (Json.mkObj [("ctor", .str "valueData"), ("args", .arr #[.null]),
          ("resultType", .str "claimed")]) #[],
        makeFrame 73 (ScopedReference.result 0).encode #[],
        makeFrame 73 exported #[Json.mkObj [("token", .str token), ("captures", .arr #[.null])]]]
      for bad in malformed do
        let rejected ← try
          discard <| ImmediateReply.parseControl scope reservation graph scope.wireId 73 bad
          pure false
        catch _ => pure true
        unless rejected do throw <| IO.userError "a malformed reply control was admitted"
      let wrongScope ← try
        discard <| ImmediateReply.parseControl scope reservation graph "another scope" 73
          (makeFrame 73 (.str "portable control") #[])
        pure false
      catch _ => pure true
      unless wrongScope do
        throw <| IO.userError "a reference-free reply bypassed scope authority"
      unless (← ledger.pendingFor occurrence transaction).isSome &&
          (graph.find input.value).isSome do
        throw <| IO.userError "control validation changed reservation or retained value state"
      scope.retire
      discard <| ledger.retire reservation
    finally owners.close child.generation
