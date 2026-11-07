module

import CasRuntime.Environment
public meta import Lean.Elab.Command
meta import CasRuntime.Environment

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let boolean ← SourceLayout.ofTerm (← empty.close (mkConst ``Bool.true))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, number) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, truthData) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := boolean, parameters := #[] } (.portable "true".toUTF8)
  let .ok relabelled := graph.rebind truthData scalar
    | throwError "the coarse storage role could not be prepared"
  withLocalDeclD `n (mkConst ``Nat) fun n =>
    withLocalDeclD `m (mkConst ``Nat) fun m => do
      withLocalDeclD `h (← mkEq n n) fun h =>
        withLetDecl `k (mkConst ``Nat) n fun k =>
          withLocalDecl `chosen .instImplicit
              (mkApp (mkConst ``Inhabited [Level.zero]) (mkConst ``Nat)) fun chosen => do
            let bindings : Array LocalBinding := #[
              { id := ⟨"runtime-context", 0⟩, role := .parameter, expression := n },
              { id := ⟨"runtime-context", 1⟩, role := .parameter, expression := m },
              { id := ⟨"runtime-context", 2⟩, role := .hypothesis, expression := h },
              { id := ⟨"runtime-context", 3⟩, role := .definition, expression := k },
              { id := ⟨"runtime-context", 4⟩, role := .instance, expression := chosen }]
            let context ← ContextTelescope.capture bindings
            let parameter (source : BindingId) (value : ValueBinding) : MetaM RuntimeParameter := do
              let .ok result := RuntimeParameter.ofValue graph source value
                | throwError "the actual parameter is outside its graph"
              return result
            let supplied : Array RuntimeParameter := #[
              ← parameter bindings[1]!.id number,
              ← parameter bindings[0]!.id number,
              ← parameter bindings[3]!.id number]
            let environment ← RuntimeEnvironment.capture owners.worker context supplied
            let expected := #[number.value, number.value, number.value]
            unless environment.values.size == bindings.size &&
                environment.references.map (·.value) == expected do
              throwError "runtime association changed the full source order or merged source slots"
            for index in #[0, 1, 3] do
              let .ok (some value) := environment.lookup bindings[index]!.id
                | throwError "a captured source binding lost its actual runtime reference"
              unless value.value == number.value do
                throwError "runtime lookup reconstructed a value instead of retaining its node"
            for index in #[2, 4] do
              let .ok none := environment.lookup bindings[index]!.id
                | throwError "a formal-only source binding acquired a runtime payload"
            unless environment.context.entries[3]?.bind (·.value) == some (mkBVar 2) &&
                environment.context.entries[4]?.map (·.binderInfo) == some .instImplicit do
              throwError "runtime association changed a source definition or selected instance"
            match environment.lookup ⟨"absent", 0⟩ with
            | .error _ => pure ()
            | .ok _ => throwError "runtime lookup accepted a source identity outside its telescope"
            let invalid : Array (Array RuntimeParameter) := #[
                #[← parameter bindings[1]!.id number, ← parameter bindings[1]!.id number],
                #[← parameter ⟨"absent", 0⟩ number],
                #[← parameter bindings[2]!.id number],
                #[← parameter bindings[0]!.id truthData],
                #[← parameter bindings[0]!.id relabelled]]
            for parameters in invalid do
              let rejected ← try
                discard <| RuntimeEnvironment.capture owners.worker context parameters
                pure false
              catch _ => pure true
              unless rejected do
                throwError "runtime association accepted duplicate, absent, proof or mistyped input"
            let rejected ← try
              discard <| RuntimeEnvironment.capture "different-worker" context supplied
              pure false
            catch _ => pure true
            unless rejected do throwError "runtime association accepted a foreign worker value"
            let .ok dependencies := graph.requiredOwners environment.references
              | throwError "a captured runtime reference left its actual graph"
            unless dependencies.isEmpty do
              throwError "runtime association added ownership to portable source parameters"

-- Producing contexts retain every actual association; liveness follows the result type.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
  try
    let token ← liftM (m := IO) do
      child.child.stdin.putStr "actual context parameter\n"
      child.child.stdin.flush
      return (← child.child.stdout.getLine).trimAscii.toString
    let older := ValueGraph.empty owners.identities
    let (graph, number) ← liftM (m := IO) <| older.stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] }
      (.ownedExport child token #[])
    withLocalDeclD `n (mkConst ``Nat) fun n =>
      withLocalDeclD `unused (mkConst ``Nat) fun unused =>
        withLetDecl `k (mkConst ``Nat) n fun k =>
          withLocalDeclD `point (mkApp (mkConst ``Fin) k) fun point => do
            let bindings : Array LocalBinding := #[
              { id := ⟨"producing-context", 0⟩, role := .parameter, expression := n },
              { id := ⟨"producing-context", 1⟩, role := .parameter, expression := unused },
              { id := ⟨"producing-context", 2⟩, role := .definition, expression := k },
              { id := ⟨"producing-context", 3⟩, role := .parameter, expression := point }]
            let context ← ContextTelescope.capture bindings
            let .ok parameter := RuntimeParameter.ofValue graph bindings[0]!.id number
              | throwError "the producing parameter is absent from its graph"
            let environment ← RuntimeEnvironment.capture owners.worker context #[parameter]
            let dependent ← SourceLayout.ofTerm (← context.close point)
            let independent ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
            unless dependent.contextDependencies == #[0, 2] &&
                independent.contextDependencies.isEmpty do
              throwError "result-type dependency closure changed a let-bound index or unused binder"
            let origin ← environment.origin program occurrence dependent
            let independentOrigin ← environment.origin program occurrence independent
            unless origin.parameters.size == bindings.size &&
                (origin.parameters[0]?.bind id).map (·.value) == some number.value &&
                (origin.parameters[2]?.bind id).isNone do
              throwError "the producing origin lost its complete separate runtime table"
            let rejected ← liftM (m := IO) do
              try
                discard <| older.stage owners.identities origin (.portable "candidate".toUTF8)
                pure false
              catch _ => pure true
            unless rejected do
              throwError "staging recovered a producing parameter outside the visible graph"
            let (graph, indexed) ← liftM (m := IO) <| graph.stage owners.identities origin
              (.portable "candidate".toUTF8)
            let (graph, anotherIndex) ← liftM (m := IO) <| graph.stage owners.identities
              { program, occurrence, role := scalar, parameters := #[] }
              (.portable "7".toUTF8)
            let .ok indexedParameter := RuntimeParameter.ofValue graph bindings[3]!.id indexed
              | throwError "the actual dependent value is absent"
            let .ok originalIndex := RuntimeParameter.ofValue graph bindings[0]!.id number
              | throwError "the original actual index is absent"
            let .ok changedIndex := RuntimeParameter.ofValue graph bindings[0]!.id anotherIndex
              | throwError "the other actual index is absent"
            let retained ← RuntimeEnvironment.capture owners.worker context
              #[indexedParameter, originalIndex]
            unless ((retained.lookup bindings[3]!.id).toOption.bind id).map (·.value) ==
                some indexed.value do
              throwError "dependent runtime association replaced the original result"
            let reject (parameters : Array RuntimeParameter) (expected : String) : MetaM Unit := do
              let failure : Option Exception ← try
                discard <| RuntimeEnvironment.capture owners.worker context parameters
                pure none
              catch error => pure (some error)
              let some failure := failure
                | throwError "dependent runtime association accepted a changed actual dependency"
              unless (← failure.toMessageData.toString).startsWith expected do throw failure
            reject #[indexedParameter, changedIndex]
              "the runtime value has a different retained dependent reference"
            reject #[indexedParameter]
              "the runtime value is missing a retained dependent reference"
            let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
            let pairLayout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close pair))
            let record ← liftM (m := IO) <|
              RecordPrefix.begin owners.identities program occurrence pairLayout
            let (record, firstRole) ← liftM (m := IO) <| record.bind graph number
            let (_, secondRole) ← liftM (m := IO) <| record.bind graph number
            let .ok firstParameter := RuntimeParameter.ofValue graph bindings[0]!.id firstRole
              | throwError "the original dependent index role is absent"
            let .ok secondParameter := RuntimeParameter.ofValue graph bindings[0]!.id secondRole
              | throwError "the second dependent index role is absent"
            let qualified ← RuntimeEnvironment.capture owners.worker context #[firstParameter]
            let qualifiedOrigin ← qualified.origin program occurrence dependent
            let (graph, qualifiedValue) ← liftM (m := IO) <|
              graph.stage owners.identities qualifiedOrigin (.portable "qualified".toUTF8)
            let .ok qualifiedParameter :=
                RuntimeParameter.ofValue graph bindings[3]!.id qualifiedValue
              | throwError "the result at the original actual index role is absent"
            discard <| RuntimeEnvironment.capture owners.worker context
              #[qualifiedParameter, firstParameter]
            reject #[qualifiedParameter, secondParameter]
              "the runtime value has a different retained dependent reference"
            let (graph, plain) ← liftM (m := IO) <| graph.stage owners.identities independentOrigin
              (.portable "0".toUTF8)
            let .ok plainParameter := RuntimeParameter.ofValue graph bindings[1]!.id plain
              | throwError "the independent source value is absent"
            discard <| RuntimeEnvironment.capture owners.worker context #[plainParameter, changedIndex]
            let some plainNode := graph.find plain.value
              | throwError "the independent node is absent"
            unless plainNode.references.map (·.value) == #[number.value] &&
                plainNode.owners.isEmpty do
              throwError "retaining a full producing context changed independent owner requirements"
            unless ← liftM (m := BaseIO) (graph.isAvailable owners indexed) do
              throwError "a live producing parameter made its dependent result unavailable"
            liftM (m := IO) <| owners.close child.generation
            if ← liftM (m := BaseIO) (graph.isAvailable owners indexed) then
              throwError "a dependent result survived loss of its actual index owner"
            unless ← liftM (m := BaseIO) (graph.isAvailable owners plain) do
              throwError "an unused producing parameter owner blocked an independent result"
  finally liftM (m := IO) <| owners.close child.generation

-- A projected dependent role keeps its actual preceding field through source let bindings.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let family ← withLocalDeclD `n (mkConst ``Nat) fun n =>
    mkLambdaFVars #[n] (mkApp (mkConst ``Fin) n)
  let sigma := mkApp2 (mkConst ``Sigma [.zero, .zero]) (mkConst ``Nat) family
  withLocalDeclD `r sigma fun r => do
    let width ← mkProjection r `fst
    let projected ← mkProjection r `snd
    withLetDecl `n (mkConst ``Nat) width fun n =>
      withLocalDeclD `point (mkApp (mkConst ``Fin) n) fun point => do
        let bindings : Array LocalBinding := #[
          { id := ⟨"consuming-context", 0⟩, role := .result, expression := r },
          { id := ⟨"consuming-context", 1⟩, role := .definition, expression := n },
          { id := ⟨"consuming-context", 2⟩, role := .parameter, expression := point }]
        let context ← ContextTelescope.capture bindings
        let layout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close r))
        let finite ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close projected))
        let owners ← liftM (m := IO) OwnerRegistry.new
        let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
        let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
        let (graph, firstIndex) ← liftM (m := IO) <|
          (ValueGraph.empty owners.identities).stage owners.identities
            { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
        let (graph, secondIndex) ← liftM (m := IO) <| graph.stage owners.identities
          { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
        let record ← liftM (m := IO) <|
          RecordPrefix.begin owners.identities program occurrence finite
        let (record, _) ← liftM (m := IO) <| record.bind graph firstIndex
        let .ok payload := record.finish | throwError "the finite value interface is incomplete"
        let (graph, value) ← liftM (m := IO) <| graph.stage owners.identities
          { program, occurrence, role := finite.source, parameters := #[none, none, none] } payload
        let record ← liftM (m := IO) <|
          RecordPrefix.begin owners.identities program occurrence layout
        let (record, originalIndex) ← liftM (m := IO) <| record.bind graph firstIndex
        let (_, projectedValue) ← liftM (m := IO) <| record.bind graph value
        let record ← liftM (m := IO) <|
          RecordPrefix.begin owners.identities program occurrence layout
        let (_, changedIndex) ← liftM (m := IO) <| record.bind graph secondIndex
        let parameter (id : BindingId) (value : ValueBinding) : MetaM RuntimeParameter := do
          let .ok parameter := RuntimeParameter.ofValue graph id value
            | throwError "the actual consuming field is absent"
          return parameter
        let actual ← parameter bindings[2]!.id projectedValue
        discard <| RuntimeEnvironment.capture owners.worker context
          #[actual, ← parameter bindings[1]!.id originalIndex]
        let invalid := #[
          (#[actual, ← parameter bindings[1]!.id changedIndex],
            "the runtime value has a different consuming dependent reference"),
          (#[actual], "the runtime value is missing a consuming dependent reference")]
        for (parameters, expected) in invalid do
          let failure : Option Exception ← try
            discard <| RuntimeEnvironment.capture owners.worker context parameters
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "runtime association lost the actual preceding field of a dependent role"
          unless (← failure.toMessageData.toString).startsWith expected do throw failure
