module

import CasRuntime.Value
public meta import Lean.Elab.Command
meta import CasRuntime.Value

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  let proofRole ← SourceLayout.ofTerm (← context.close (mkConst ``True.intro))
  let functionRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
  let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
  let productRole ← SourceLayout.ofTerm (← context.close pair)
  liftM (m := IO) do
    let owners ← OwnerRegistry.new
    let supply := owners.identities
    let program ← supply.fresh .program
    let occurrence ← supply.fresh .occurrence
    let origin : ValueOrigin := { program, occurrence, role }
    let empty := ValueGraph.empty supply
    let bytes := "retained bytes".toUTF8
    let (firstGraph, first) ← empty.stage supply origin (.portable bytes)
    let (graph, second) ← firstGraph.stage supply origin (.portable bytes)
    if first.value == second.value then
      throw <| IO.userError "independent returned values share an identity"
    if (empty.find first.value).isSome || (firstGraph.find second.value).isSome then
      throw <| IO.userError "staging changed an earlier immutable graph"
    let some node := graph.find first.value
      | throw <| IO.userError "the graph lost a staged node"
    unless node.origin.occurrence == occurrence && node.origin.program == program do
      throw <| IO.userError "the node lost its producing occurrence or program"
    let .portable retained := node.payload.data
      | throw <| IO.userError "the node changed its payload form"
    unless retained == bytes && node.owners.isEmpty do
      throw <| IO.userError "portable payload or owner independence changed"
    let rejected ← try
      discard <| graph.stage supply { origin with role := proofRole } (.portable bytes)
      pure false
    catch _ => pure true
    unless rejected do
      throw <| IO.userError "a source proof acquired a computational payload"
    let child ← owners.spawn { cmd := "/bin/cat" }
    try
      child.child.stdin.putStr "native token\n"
      child.child.stdin.flush
      let token := (← child.child.stdout.getLine).trimAscii.toString
      let (ownedGraph, owned) ← graph.stage supply origin
        (.ownedExport child token #[first])
      let (closedGraph, closed) ← ownedGraph.stage supply { origin with role := functionRole }
        (.closure program #[owned])
      let (jointGraph, joint) ← closedGraph.stage supply { origin with role := productRole }
        (.product #[first, closed])
      let projected ← IO.ofExcept <| (jointGraph.project joint 0).mapError IO.userError
      unless projected.value == first.value do
        throw <| IO.userError "projection replaced the retained field node"
      let rebound ← IO.ofExcept <| (jointGraph.rebind owned role).mapError IO.userError
      unless rebound.value == owned.value do
        throw <| IO.userError "an existing input reference acquired a new node"
      unless ← jointGraph.isAvailable owners joint do
        throw <| IO.userError "a live captured owner made the result unavailable"
      owners.close child.generation
      if ← jointGraph.isAvailable owners owned then
        throw <| IO.userError "an owned export survived its supplying connection"
      if ← jointGraph.isAvailable owners closed then
        throw <| IO.userError "a closure lost its captured owner dependency"
      if ← jointGraph.isAvailable owners rebound then
        throw <| IO.userError "rebinding transferred an existing value's owner"
      unless ← jointGraph.isAvailable owners projected do
        throw <| IO.userError "an independent portable field died with another field's owner"
    finally owners.close child.generation
    let other ← OwnerRegistry.new
    let otherProgram ← other.identities.fresh .program
    let otherOccurrence ← other.identities.fresh .occurrence
    let (otherGraph, foreign) ← (ValueGraph.empty other.identities).stage other.identities
      { program := otherProgram, occurrence := otherOccurrence, role } (.portable bytes)
    let rejected ← try
      discard <| graph.stage supply origin (.product #[foreign])
      pure false
    catch _ => pure true
    unless rejected && (otherGraph.find foreign.value).isSome do
      throw <| IO.userError "a value graph admitted a reference outside its visible graph"
