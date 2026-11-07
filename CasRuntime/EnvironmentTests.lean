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
      { program, occurrence, role := scalar } (.portable "7".toUTF8)
  let (graph, truthData) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := boolean } (.portable "true".toUTF8)
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
            unless environment.values.size == bindings.size &&
                environment.references.map (·.value) == #[number.value, number.value, number.value] do
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
