module

import all CasRuntime.Value
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



run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let supply := owners.identities
  let empty ← ContextTelescope.capture #[]
  let role ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let intermediateRole ← SourceLayout.ofTerm
    (← empty.close (mkApp (mkConst ``Nat.succ) (mkNatLit 6)))
  if role.source.expression.equal intermediateRole.source.expression then
    throwError "the independent view fixture lost its distinct native source expression"
  unless ← isDefEq role.source.expression intermediateRole.source.expression do
    throwError "the independent view fixture changed its native value"
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
      let otherSourceRole ← SourceLayout.ofTerm (← context.close (mkNatLit 8))
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
          unless previous.exactlyMatches previous do
            throw <| IO.userError "a complete shared source view did not match itself"
          let firstView ← IO.ofExcept <|
            (base.withRole completeRole #[] (some #[some previous, some previous])).mapError IO.userError
          let secondView ← IO.ofExcept <|
            (base.withRole completeRole #[] (some #[some previous, some previous])).mapError IO.userError
          unless firstView.exactlyMatches secondView && secondView.exactlyMatches firstView do
            throw <| IO.userError "separately retained equal views lost their complete shared parameters"
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
          let missingParameter ← IO.ofExcept <|
            (base.withRole completeRole #[] (some #[some previous, none])).mapError IO.userError
          let changedSource ← IO.ofExcept <|
            (base.withRole otherSourceRole #[] (some #[some previous, some previous])).mapError IO.userError
          let originalDependency ← IO.ofExcept <|
            (base.withRole completeRole #[previous] (some #[some previous, some previous])).mapError IO.userError
          unless firstView.value == changedParameters.value &&
              firstView.value == changedSource.value do
            throw <| IO.userError "the exact-view controls changed their original runtime node"
          if firstView.exactlyMatches changedParameters ||
              changedParameters.exactlyMatches firstView then
            throw <| IO.userError "an exact view comparison ignored a changed actual parameter"
          if firstView.exactlyMatches missingParameter ||
              missingParameter.exactlyMatches firstView then
            throw <| IO.userError "an exact view comparison ignored a missing formal parameter"
          if firstView.exactlyMatches changedSource || changedSource.exactlyMatches firstView then
            throw <| IO.userError "an exact view comparison ignored a different complete native source"
          if originalDependency.exactlyMatches changedDependencies ||
              changedDependencies.exactlyMatches originalDependency then
            throw <| IO.userError "an exact view comparison ignored a different actual dependency"


          let originalInterface := firstView.attachNativeInterface firstView
          let changedInterface := firstView.attachNativeInterface changedParameters
          let changedInterfaceSource := firstView.attachNativeInterface changedSource
          if originalInterface.exactlyMatches firstView ||
              firstView.exactlyMatches originalInterface then
            throw <| IO.userError "an exact view comparison ignored a missing native interface"
          if originalInterface.exactlyMatches changedInterface ||
              changedInterface.exactlyMatches originalInterface then
            throw <| IO.userError "an exact view comparison ignored the native interface parameters"
          if originalInterface.exactlyMatches changedInterfaceSource ||
              changedInterfaceSource.exactlyMatches originalInterface then
            throw <| IO.userError "an exact view comparison ignored the complete native interface source"



          let intermediateSeed ← IO.ofExcept <|
            (owned.withRole intermediateRole).mapError IO.userError
          let separateSeed ← IO.ofExcept <| (intermediateSeed.withRole role).mapError IO.userError
          unless separateSeed.sourceRoleFrames.size == owned.sourceRoleFrames.size + 2 do
            throw <| IO.userError "the separate-view control lost its independent retained history"
          unless owned.exactlyMatches separateSeed && separateSeed.exactlyMatches owned do
            throw <| IO.userError "the independent history changed its complete current source view"
          let mut independentLeft ← IO.ofExcept <|
            (base.withRole completeRole #[owned] (some #[some owned, some owned])).mapError IO.userError
          let mut independentRight ← IO.ofExcept <|
            (base.withRole completeRole #[separateSeed]
              (some #[some separateSeed, some separateSeed])).mapError
              IO.userError
          let mut deepParameters ← IO.ofExcept <|
            (base.withRole completeRole #[separateSeed]
              (some #[some separateSeed, some absent])).mapError
              IO.userError
          let mut deepMissing ← IO.ofExcept <|
            (base.withRole completeRole #[separateSeed]
              (some #[some separateSeed, none])).mapError IO.userError
          let mut deepSource ← IO.ofExcept <|
            (base.withRole otherSourceRole #[separateSeed]
              (some #[some separateSeed, some separateSeed])).mapError
              IO.userError


          let mut deepDependencies ← IO.ofExcept <|
            (base.withRole completeRole #[absent]
              (some #[some separateSeed, some separateSeed])).mapError IO.userError
          for _ in [:48] do
            let previousRight := independentRight
            independentLeft ← IO.ofExcept <|
              (base.withRole completeRole #[]
                (some #[some independentLeft, some independentLeft])).mapError IO.userError
            independentRight ← IO.ofExcept <|
              (base.withRole completeRole #[]
                (some #[some previousRight, some previousRight])).mapError IO.userError


            deepParameters ← IO.ofExcept <|
              (base.withRole completeRole #[]
                (some #[some previousRight, some deepParameters])).mapError IO.userError
            deepMissing ← IO.ofExcept <|
              (base.withRole completeRole #[]
                (some #[some previousRight, some deepMissing])).mapError IO.userError
            deepSource ← IO.ofExcept <|
              (base.withRole completeRole #[]
                (some #[some previousRight, some deepSource])).mapError IO.userError
            deepDependencies ← IO.ofExcept <|
              (base.withRole completeRole #[]
                (some #[some previousRight, some deepDependencies])).mapError IO.userError
          unless independentLeft.exactlyMatches independentRight &&
              independentRight.exactlyMatches independentLeft do
            throw <| IO.userError "independently shared complete source views did not agree"
          for (name, changed) in #[
              ("parameter", deepParameters), ("missing parameter", deepMissing),
              ("native source", deepSource), ("dependency", deepDependencies)] do
            unless changed.value == independentLeft.value &&
                changed.associationIds == independentLeft.associationIds do
              throw <| IO.userError "a deep-view control changed its original node or associations"
            if independentLeft.exactlyMatches changed || changed.exactlyMatches independentLeft then
              throw <| IO.userError s!"an exact shared-view comparison ignored a deep {name} change"


          let completeInterface := independentLeft.attachNativeInterface independentLeft
          let equalInterface := independentRight.attachNativeInterface independentRight
          let unequalInterface := independentRight.attachNativeInterface deepParameters
          unless completeInterface.exactlyMatches equalInterface &&
              equalInterface.exactlyMatches completeInterface do
            throw <| IO.userError "independently shared native interfaces did not agree"
          if completeInterface.exactlyMatches unequalInterface ||
              unequalInterface.exactlyMatches completeInterface then
            throw <| IO.userError "an exact shared-view comparison ignored a deep native interface change"

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
