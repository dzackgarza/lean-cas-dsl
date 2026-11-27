module

import CasRuntime.Encode
public meta import Lean.Elab.Command
meta import CasRuntime.Encode

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  let callableRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
  let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
  let recordRole ← SourceLayout.ofTerm (← context.close pair)
  let lifted := mkApp2 (mkConst ``ULift.up [.zero, .zero]) (mkConst ``Nat) (mkNatLit 7)
  let liftedRole ← SourceLayout.ofTerm (← context.close lifted)
  let owners ← liftM (m := IO) OwnerRegistry.new
  let localOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  let foreignOwner ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  try
    let token (connection : Connection) (value : String) : IO String := do
      connection.child.stdin.putStr (value ++ "\n")
      connection.child.stdin.flush
      return (← connection.child.stdout.getLine).trimAscii.toString
    let localToken ← liftM (m := IO) <| token localOwner "local-code"
    let foreignToken ← liftM (m := IO) <| token foreignOwner "foreign-code"
    let program ← liftM (m := BaseIO) <| owners.identities.fresh .program
    let occurrence ← liftM (m := BaseIO) <| owners.identities.fresh .occurrence
    let stage (graph : ValueGraph) (role : SourceLayout) (payload : ValuePayload) :=
      graph.stage owners.identities { program, occurrence, role, parameters := #[] } payload
    let (graph, number) ← liftM (m := IO) <|
      stage (ValueGraph.empty owners.identities) scalarRole (.portable "19".toUTF8)
    let (graph, localCode) ← liftM (m := IO) <|
      stage graph callableRole (.ownedExport localOwner localToken #[])
    let (graph, remoteCode) ← liftM (m := IO) <|
      stage graph callableRole (.ownedExport foreignOwner foreignToken #[])
    let (graph, record) ← liftM (m := IO) <|
      stage graph recordRole (.product #[number, remoteCode])
    let path := #[InputPathStep.field "argument"]
    let .ok encoded := graph.encodeInputs localOwner.generation #[{ path, binding := record }]
      | throwError "the retained record could not encode"
    unless encoded.values == #[Json.arr #[toJson (19 : Nat), (ScopedReference.scope 0).encode]] &&
        encoded.slots.map (·.value) == #[remoteCode.value] &&
        encoded.inputs.map (·.path) == #[path, path.push (.index 0), path.push (.index 1)] &&
        encoded.inputs.map (·.binding.value) == #[record.value, number.value, remoteCode.value] do
      throwError "input encoding changed actual data, foreign ownership or complete typed positions"
    let .ok localPacket := graph.encodeInputs localOwner.generation #[{ path, binding := localCode }]
      | throwError "the local native export could not encode"
    unless localPacket.values == #[(ComputationalValue.opaque localToken).encode] &&
        localPacket.slots.isEmpty && localPacket.inputs.map (·.binding.value) == #[localCode.value] do
      throwError "local native encoding lost its token or exact input authority"
    let .ok payload := ValuePayload.container
      (Json.mkObj [("value", .null), ("label", .str "original packet")])
      #[{ path := #[.field "value"], binding := number, fieldIndex := some 0 }] #[number, remoteCode] none
      | throwError "the retained container could not form"
    let (graph, container) ← liftM (m := IO) <| stage graph recordRole payload
    let .ok encoded := graph.encodeInputs localOwner.generation #[{ path, binding := container }]
      | throwError "the original container packet could not encode"
    unless encoded.values == #[Json.mkObj [("value", toJson (19 : Nat)),
        ("label", .str "original packet")]] &&
        encoded.inputs.map (·.binding.value) == #[container.value, number.value] do
      throwError "input encoding rebuilt a retained packet or lost its whole-value interface"
    let .ok wrapper := ValuePayload.container (.str "callable wrapper") #[] #[] (some localCode)
      | throwError "the callable wrapper could not form"
    let (graph, wrapped) ← liftM (m := IO) <| stage graph callableRole wrapper
    let .ok encoded := graph.encodeInputs localOwner.generation #[{ path, binding := wrapped }]
      | throwError "the hidden callable interface could not encode"
    unless encoded.values == #[(ScopedReference.scope 0).encode] &&
        encoded.slots.map (·.value) == #[wrapped.value] do
      throwError "input encoding replaced a whole hidden callable by its wire template or inner code"
    let (graph, collapsed) ← liftM (m := IO) <| stage graph liftedRole (.product #[number])
    let .ok encoded := graph.encodeInputs localOwner.generation #[{ path, binding := collapsed }]
      | throwError "the single-field public record could not encode"
    unless encoded.values == #[toJson (19 : Nat)] &&
        encoded.inputs.map (·.binding.value) == #[collapsed.value] do
      throwError "single-field wire collapse replaced the complete original input authority"
    let .ok aliases := graph.encodeInputs localOwner.generation #[
        { path := #[.index 0], binding := remoteCode },
        { path := #[.index 1], binding := remoteCode }]
      | throwError "distinct aliased input positions could not encode"
    unless aliases.values == #[(ScopedReference.scope 0).encode, (ScopedReference.scope 1).encode] &&
        aliases.slots.map (·.value) == #[remoteCode.value, remoteCode.value] do
      throwError "input encoding merged distinct scoped occurrences of an aliased value"
    let forbidden := (ComputationalValue.opaque foreignToken).encode.compress
    let (graph, unbound) ← liftM (m := IO) <| stage graph scalarRole (.portable forbidden.toUTF8)
    let (graph, malformed) ← liftM (m := IO) <| stage graph scalarRole (.portable "not JSON".toUTF8)
    for value in #[unbound, malformed] do
      if (graph.encodeInputs localOwner.generation #[{ path, binding := value }]).isOk then
        throwError "input encoding accepted a malformed or unbound portable packet"
    if (graph.encodeInputs localOwner.generation #[
        { path, binding := number }, { path, binding := remoteCode }]).isOk then
      throwError "input encoding accepted overlapping complete root authorities"
  finally
    liftM (m := IO) <| owners.close localOwner.generation
    liftM (m := IO) <| owners.close foreignOwner.generation
