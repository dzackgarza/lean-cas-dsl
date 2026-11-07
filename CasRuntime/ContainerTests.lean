module

import CasRuntime.Scope
public meta import Lean.Elab.Command
meta import CasRuntime.Scope

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  let functionRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
  let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
  let recordRole ← SourceLayout.ofTerm (← context.close pair)
  let some firstField := recordRole.fields[0]? | throwError "the first source field is missing"
  let aliasRole ← firstField.toLayout
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    let program ← owners.identities.fresh .program
    let produced ← ledger.allocate
    let child ← owners.spawn { cmd := "/bin/cat" }
    try
      child.child.stdin.putStr "retained container token\n"
      child.child.stdin.flush
      let token := (← child.child.stdout.getLine).trimAscii.toString
      let (base, scalar) ← (ValueGraph.empty owners.identities).stage owners.identities
        { program, occurrence := produced, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
      let (base, callable) ← base.stage owners.identities
        { program, occurrence := produced, role := functionRole, parameters := #[] } (.ownedExport child token #[])
      let firstPath : Array InputPathStep := #[.field "args", .index 0]
      let secondPath : Array InputPathStep := #[.field "args", .index 1, .field "wrapped"]
      let template := Json.mkObj [
        ("ctor", .str "retainedPacket"),
        ("args", .arr #[.null, Json.mkObj [("wrapped", .null)]]),
        ("description", .str "retained literal data")]
      let slots : Array ContainerSlot := #[
        { path := secondPath, binding := callable }, { path := firstPath, binding := scalar }]
      let payload ← IO.ofExcept <|
        (ValuePayload.container template slots #[scalar, callable] none).mapError IO.userError
      let (graph, record) ← base.stage owners.identities
        { program, occurrence := produced, role := recordRole, parameters := #[] } payload
      let .ok recordCandidate := CandidateResponse.ofValue recordRole graph record
        | throw <| IO.userError "the retained container lost its complete record shape"
      unless recordCandidate.root.value == record.value do
        throw <| IO.userError "candidate shape checking replaced its actual root"
      let .ok first := graph.project record 0
        | throw <| IO.userError "the retained first field is missing"
      let .ok second := graph.project record 1
        | throw <| IO.userError "the retained second field is missing"
      unless first.value == scalar.value && second.value == callable.value do
        throw <| IO.userError "container projection used packet traversal order instead of field slots"
      let invocation ← ledger.allocate
      let transaction ← owners.identities.fresh .transaction
      let selected : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := { operation := "resource-test", input := "resource-test", backend := "cat" }
        profileDigest := "resource-test-profile" }
      let .ok reservation ← ledger.reserve invocation transaction selected child graph #[record]
        | throw <| IO.userError "the container request could not reserve"
      let scope ← RequestScope.issue ledger reservation graph #[scalar, callable] #[] #[]
      let some node := graph.find record.value
        | throw <| IO.userError "the retained container root is missing"
      let .container stored := node.payload.data
        | throw <| IO.userError "container storage changed its operational form"
      let replacements := #[(ScopedReference.scope 1).encode, (ScopedReference.scope 0).encode]
      let packet ← IO.ofExcept <| (stored.fill replacements).mapError IO.userError
      let expected := Json.mkObj [
        ("ctor", .str "retainedPacket"),
        ("args", .arr #[replacements[1]!, Json.mkObj [("wrapped", replacements[0]!)]]),
        ("description", .str "retained literal data")]
      unless packet == expected && stored.slots.size == 2 do
        throw <| IO.userError "container substitution lost literal structure or exact reference positions"
      let aliased ← IO.ofExcept <| (graph.rebind scalar aliasRole).mapError IO.userError
      let aliases ← IO.ofExcept <| (ValuePayload.container
        (.arr #[(ScopedReference.scope 0).encode, (ScopedReference.scope 1).encode])
        #[{ path := #[.index 0], binding := scalar }, { path := #[.index 1], binding := aliased }]
        #[scalar, aliased] none).mapError IO.userError
      let .container aliasContainer := aliases.data
        | throw <| IO.userError "the aliased container lost its packet form"
      unless aliasContainer.template == .arr #[.null, .null] &&
          (aliasContainer.slots.map (·.binding.value)) == #[scalar.value, scalar.value] &&
          (aliasContainer.slots.map (·.binding.role.address)) == #[scalarRole.address, aliasRole.address] do
        throw <| IO.userError "container retention merged aliases, changed their roles or retained ambient authority"
      let incompletePayload ← IO.ofExcept <|
        (ValuePayload.container template slots #[scalar] none).mapError IO.userError
      let (incompleteGraph, incomplete) ← graph.stage owners.identities
        { program, occurrence := produced, role := recordRole, parameters := #[] } incompletePayload
      match CandidateResponse.ofValue recordRole incompleteGraph incomplete with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "an incomplete container filled a complete record interface"
      let resolved ← scope.resolveMany reservation graph scope.wireId #[.scope 1, .scope 0]
      unless (resolved.map (·.value)) == (stored.slots.map (·.binding.value)) do
        throw <| IO.userError "rendered container slots changed their retained values"
      let callablePayload ← IO.ofExcept <| (ValuePayload.container
        (Json.mkObj [("description", .str "retained callable interface")])
        #[] #[] (some callable)).mapError IO.userError
      let (wrappedGraph, wrapped) ← graph.stage owners.identities
        { program, occurrence := produced, role := functionRole, parameters := #[] } callablePayload
      let .ok candidate := CandidateResponse.ofValue functionRole wrappedGraph wrapped
        | throw <| IO.userError "a stored callable container lost its accepted action"
      let leaf ← IO.ofExcept <| (wrappedGraph.callable candidate.root).mapError IO.userError
      unless leaf.value == callable.value && candidate.root.value == wrapped.value do
        throw <| IO.userError "callable access replaced the stored arrow or actual callable node"
      let (invalidGraph, dataFunction) ← graph.stage owners.identities
        { program, occurrence := produced, role := functionRole, parameters := #[] } (.portable "7".toUTF8)
      let invalidCallable ← IO.ofExcept <|
        (ValuePayload.container .null #[] #[] (some dataFunction)).mapError IO.userError
      let (invalidGraph, invalidFunction) ← invalidGraph.stage owners.identities
        { program, occurrence := produced, role := functionRole, parameters := #[] } invalidCallable
      match CandidateResponse.ofValue functionRole invalidGraph invalidFunction with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "a data slot became a retained callable"
      let some nativeSlot := slots[0]?
        | throw <| IO.userError "the native reference slot is missing"
      let malformed := #[
        ValuePayload.container template #[nativeSlot, nativeSlot] #[scalar, callable] none,
        ValuePayload.container template #[{ path := #[], binding := scalar }, nativeSlot] #[scalar, callable] none,
        ValuePayload.container template #[{ path := #[.field "missing"], binding := scalar }] #[scalar] none,
        ValuePayload.container template slots #[] (some scalar),
        ValuePayload.container (ScopedReference.scope 0).encode #[] #[] none,
        ValuePayload.container (ComputationalValue.encode (.opaque token)) #[] #[] none]
      for invalid in malformed do
        match invalid with
        | .error _ => pure ()
        | .ok _ => throw <| IO.userError "an invalid container reference layout was retained"
      match stored.fill #[replacements[0]!] with
      | .error _ => pure ()
      | .ok _ => throw <| IO.userError "container substitution changed its required arity"
      let other ← OwnerRegistry.new
      let otherProgram ← other.identities.fresh .program
      let otherOccurrence ← other.identities.fresh .occurrence
      let (_, foreign) ← (ValueGraph.empty other.identities).stage other.identities
        { program := otherProgram, occurrence := otherOccurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
      let foreignPayload ← IO.ofExcept <|
        (ValuePayload.container .null #[] #[foreign] none).mapError IO.userError
      let rejectedForeign ← try
        discard <| graph.stage owners.identities
          { program, occurrence := produced, role := scalarRole, parameters := #[] } foreignPayload
        pure false
      catch _ => pure true
      unless rejectedForeign do
        throw <| IO.userError "a non-wire field recovered a value outside the current graph"
      scope.retire
      discard <| ledger.retire reservation
      owners.close child.generation
      unless ← wrappedGraph.isAvailable owners first do
        throw <| IO.userError "a portable container field died with another field's owner"
      if ← wrappedGraph.isAvailable owners second then
        throw <| IO.userError "a native container field survived its actual owner"
      if ← wrappedGraph.isAvailable owners wrapped then
        throw <| IO.userError "a callable container lost its transitive owner dependency"
    finally owners.close child.generation
