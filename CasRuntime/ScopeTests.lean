module

import CasRuntime.Scope
public meta import Lean.Elab.Command
meta import CasRuntime.Scope

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
  let record ← SourceLayout.ofTerm (← context.close pair)
  let some field := record.fields[0]? | throwError "the source field control is missing"
  let fieldRole ← field.toLayout
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    let program ← owners.identities.fresh .program
    let transaction ← owners.identities.fresh .transaction
    let occurrence ← ledger.allocate
    let (graph, original) ← (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role } (.portable "scope payload".toUTF8)
    let retained ← IO.ofExcept <| (graph.rebind original fieldRole).mapError IO.userError
    let child ← owners.spawn { cmd := "/bin/cat" }
    try
      let selected : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := { operation := "resource-test", input := "resource-test", backend := "cat" }
        profileDigest := "resource-test-profile" }
      let .ok reservation ← ledger.reserve occurrence transaction selected child graph #[original]
        | throw <| IO.userError "the request scope could not reserve its invocation"
      let scope ← RequestScope.issue ledger reservation graph #[original, retained]
        #[{ path := #[.field "argument"], binding := retained }] #[original]
      let refs := #[ScopedReference.scope 0, .scope 1, .input #[.field "argument"], .result 0]
      for reference in refs do
        let parsed ← IO.ofExcept <| (ScopedReference.parse? reference.encode).mapError IO.userError
        unless parsed == some reference do
          throw <| IO.userError "a public reference changed through wire encoding"
      let values ← scope.resolveMany reservation graph scope.wireId refs
      unless values.size == 4 && values.all (fun value => value.value == original.value) do
        throw <| IO.userError "scope resolution replaced an actual retained value"
      let some first := values[0]? | throw <| IO.userError "the first scope role is missing"
      let some second := values[1]? | throw <| IO.userError "the second scope role is missing"
      unless first.role.address.isEmpty && second.role.address == #[``Prod.fst] do
        throw <| IO.userError "scope resolution merged aliased consuming roles"
      let captures ← scope.capture reservation graph scope.wireId #[.scope 0, .scope 1]
      unless captures.size == 2 do
        throw <| IO.userError "capture validation merged distinct scope addresses"
      let badRefs := #[ScopedReference.scope 2, .input #[.field "argument", .index 0], .result 1]
      for reference in badRefs do
        let rejected ← try
          discard <| scope.resolveMany reservation graph scope.wireId #[reference]
          pure false
        catch _ => pure true
        unless rejected do throw <| IO.userError "scope resolution admitted an unretained position"
      let duplicate ← try
        discard <| scope.capture reservation graph scope.wireId #[.scope 0, .scope 0]
        pure false
      catch _ => pure true
      unless duplicate do throw <| IO.userError "capture validation accepted a repeated address"
      let wrongScope ← try
        discard <| scope.resolveMany reservation graph "different scope" #[.scope 0]
        pure false
      catch _ => pure true
      unless wrongScope do throw <| IO.userError "a reference escaped its issued scope"
      let outside ← try
        discard <| scope.resolveMany reservation (ValueGraph.empty owners.identities)
          scope.wireId #[.scope 0]
        pure false
      catch _ => pure true
      unless outside do throw <| IO.userError "scope metadata recovered an invisible payload"
      let malformed := Json.mkObj [
        ("ctor", .str "scopeRef"), ("args", .arr #[toJson (0 : Nat)]), ("owner", .str "claimed")]
      unless (ScopedReference.parse? malformed).isError do
        throw <| IO.userError "a reserved reference accepted an unknown control field"
      scope.retire
      let expired ← try
        discard <| scope.resolveMany reservation graph scope.wireId #[.scope 0]
        pure false
      catch _ => pure true
      unless expired do throw <| IO.userError "a retired scope retained reference authority"
      let next ← ledger.allocate
      let .ok nextReservation ← ledger.reserve next transaction selected child graph #[original]
        | throw <| IO.userError "the fresh invocation could not reserve"
      let fresh ← RequestScope.issue ledger nextReservation graph captures #[] #[]
      if fresh.id == scope.id then throw <| IO.userError "a fresh invocation reused its scope identity"
      let mismatch ← try
        discard <| fresh.resolveMany reservation graph fresh.wireId #[.scope 0]
        pure false
      catch _ => pure true
      unless mismatch do throw <| IO.userError "a scope accepted another invocation's authority"
      discard <| ledger.retire nextReservation
      let settled ← try
        discard <| fresh.resolveMany nextReservation graph fresh.wireId #[.scope 0]
        pure false
      catch _ => pure true
      unless settled do throw <| IO.userError "a settled invocation retained scope authority"
      discard <| ledger.retire reservation
    finally owners.close child.generation
