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
    let origin : ValueOrigin := { program, occurrence, role, parameters := #[] }
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
      { program := otherProgram, occurrence := otherOccurrence, role, parameters := #[] } (.portable bytes)
    let rejected ← try
      discard <| graph.stage supply origin (.product #[foreign])
      pure false
    catch _ => pure true
    unless rejected && (otherGraph.find foreign.value).isSome do
      throw <| IO.userError "a value graph admitted a reference outside its visible graph"

-- Shared source-parameter tables remain complete provenance without repeated tree traversal.
-- Every view below is formed through the same public constructor used by native admission.
run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let supply := owners.identities
  let empty ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let program ← supply.fresh .program
  let occurrence ← supply.fresh .occurrence
  let origin : ValueOrigin := { program, occurrence, role, parameters := #[] }
  let (graph, base) ← (ValueGraph.empty supply).stage supply origin
    (.portable "shared visibility base".toUTF8)
  withLocalDeclD `first (mkConst ``Nat) fun first =>
    withLocalDeclD `second (mkConst ``Nat) fun second => do
      let firstId ← supply.fresh .sourceBinding
      let secondId ← supply.fresh .sourceBinding
      let context ← ContextTelescope.capture #[
        { id := ⟨firstId.worker, firstId.serial⟩, role := .parameter, expression := first },
        { id := ⟨secondId.worker, secondId.serial⟩, role := .parameter, expression := second }]
      let completeRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      liftM (m := IO) do
        let child ← owners.spawn { cmd := "/bin/cat" }
        try
          child.child.stdin.putStr "shared visibility owner\n"
          child.child.stdin.flush
          let token := (← child.child.stdout.getLine).trimAscii.toString
          let (graph, owned) ← graph.stage supply origin (.ownedExport child token #[])
          let mut previous := owned
          for _ in [:48] do
            previous ← IO.ofExcept <|
              (base.withRole completeRole #[] (some #[some previous, some previous])).mapError IO.userError
          let retainedOwners ← IO.ofExcept <| (graph.requiredOwners #[previous]).mapError IO.userError
          unless retainedOwners.isEmpty do
            throw <| IO.userError "inert source parameters became owner dependencies"
          let actualOwners ← IO.ofExcept <| (graph.requiredOwners #[owned]).mapError IO.userError
          unless actualOwners == #[child.generation] do
            throw <| IO.userError "a visibility summary changed an actual supplying owner"
          let (extended, absent) ← graph.stage supply origin (.portable "later actual value".toUTF8)
          let changedParameters ← IO.ofExcept <|
            (base.withRole completeRole #[] (some #[some previous, some absent])).mapError IO.userError
          let changedDependencies ← IO.ofExcept <|
            (base.withRole completeRole #[absent] (some #[some previous, some previous])).mapError IO.userError
          -- A previously checked view of this same node cannot certify a changed table.
          unless (match graph.requiredOwners #[previous, changedParameters] with
              | .error _ => true | .ok _ => false) do
            throw <| IO.userError "visibility reuse ignored a changed parameter outside the current graph"
          unless (match graph.requiredOwners #[previous, changedDependencies] with
              | .error _ => true | .ok _ => false) do
            throw <| IO.userError "visibility reuse ignored a changed dependency outside the current graph"
          discard <| IO.ofExcept <|
            (extended.requiredOwners #[previous, changedParameters, changedDependencies]).mapError IO.userError
          owners.close child.generation
          unless ← graph.isAvailable owners previous do
            throw <| IO.userError "an inert source parameter transferred its closed owner"
          if ← graph.isAvailable owners owned then
            throw <| IO.userError "an actual supplying owner was cached as live"
        finally owners.close child.generation

-- Actual public application associations may themselves form a shared DAG. Their original
-- first-visit guards must apply before descending either repeated argument branch.
run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let supply := owners.identities
  let context ← ContextTelescope.capture #[]
  let nativeFunction ← withLocalDeclD `first (mkConst ``Nat) fun first =>
    withLocalDeclD `second (mkConst ``Nat) fun second =>
      mkLambdaFVars #[first, second] first
  let function ← SourceLayout.ofTerm (← context.close nativeFunction)
  let argument ← context.close (mkNatLit 7)
  let (role, application) ← ApplicationLayout.ofSource function context #[argument, argument]
  let program ← supply.fresh .program
  let occurrence ← supply.fresh .occurrence
  let origin : ValueOrigin := { program, occurrence, role, parameters := #[] }
  liftM (m := IO) do
    let (initial, base) ← (ValueGraph.empty supply).stage supply origin
      (.portable "shared application value".toUTF8)
    let mut graph := initial
    let mut previous := base
    for _ in [:48] do
      let application ← IO.ofExcept <|
        (ApplicationOrigin.ofArguments application #[] #[some previous, some previous] none).mapError
          IO.userError
      let occurrence ← supply.fresh .occurrence
      let (next, current) ← graph.bindApplication supply
        { origin with occurrence, application := some application } previous #[]
      graph := next
      previous := current
    unless previous.value == base.value && previous.associationIds.size == 48 do
      throw <| IO.userError "shared application validation changed an original occurrence or association"
    let required ← IO.ofExcept <| (graph.requiredOwners #[previous]).mapError IO.userError
    unless required.isEmpty do
      throw <| IO.userError "shared application provenance introduced a supplying owner"
