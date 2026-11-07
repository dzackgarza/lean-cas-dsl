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
            let failure : Option Exception ← try
              discard <| RuntimeEnvironment.capture owners.worker context
                #[indexedParameter, changedIndex]
              pure none
            catch error => pure (some error)
            let some failure := failure
              | throwError "dependent runtime association accepted another actual index reference"
            unless (← failure.toMessageData.toString).startsWith
                "the runtime value has a different retained dependent reference" do
              throw failure
            let (graph, plain) ← liftM (m := IO) <| graph.stage owners.identities independentOrigin
              (.portable "0".toUTF8)
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
