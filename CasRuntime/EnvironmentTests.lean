module

import CasRuntime.Environment
import LeanCategories.Foundation.Mathlib
public meta import Lean.Elab.Command
meta import CasRuntime.Environment
meta import LeanCategories.Foundation.Mathlib

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
            let (graph, record, firstRole) ← liftM (m := IO) <| record.bind graph number
            let (graph, _, secondRole) ← liftM (m := IO) <| record.bind graph number
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
        let (graph, record, _) ← liftM (m := IO) <| record.bind graph firstIndex
        let .ok payload := record.finish | throwError "the finite value interface is incomplete"
        let (graph, value) ← liftM (m := IO) <| graph.stage owners.identities
          { program, occurrence, role := finite.source, parameters := #[none, none, none] } payload
        let record ← liftM (m := IO) <|
          RecordPrefix.begin owners.identities program occurrence layout
        let (graph, record, originalIndex) ← liftM (m := IO) <| record.bind graph firstIndex
        let (graph, _, projectedValue) ← liftM (m := IO) <| record.bind graph value
        let record ← liftM (m := IO) <|
          RecordPrefix.begin owners.identities program occurrence layout
        let (graph, _, changedIndex) ← liftM (m := IO) <| record.bind graph secondIndex
        let parameter (id : BindingId) (value : ValueBinding) : MetaM RuntimeParameter := do
          let .ok parameter := RuntimeParameter.ofValue graph id value
            | throwError "the actual consuming field is absent"
          return parameter
        let actual ← parameter bindings[2]!.id projectedValue
        let captured ← RuntimeEnvironment.capture owners.worker context
          #[actual, ← parameter bindings[1]!.id originalIndex]
        let .ok argument := RuntimeArgument.ofValue graph 0 projectedValue
          | throwError "the dependent source operand is absent"
        let retained ← captured.checkArgument (← context.close point) argument
        unless retained.value == projectedValue.value &&
            retained.instantiations.map (·.id) == projectedValue.instantiations.map (·.id) &&
            (← retained.role.source.inContext context) == point do
          throwError "source operand preparation changed its node, field roles or native binder"
        let environment ← RuntimeEnvironment.capture owners.worker context
          #[← parameter bindings[1]!.id originalIndex]
        let expected ← SourceLayout.ofTerm (← context.close point)
        let candidate ← environment.checkResult graph expected projectedValue
        unless candidate.root.value == projectedValue.value &&
            candidate.root.instantiations.map (·.id) == projectedValue.instantiations.map (·.id) do
          throwError "prepared result checking changed its actual node or dependent field role"
        let changed ← RuntimeEnvironment.capture owners.worker context
          #[← parameter bindings[1]!.id changedIndex]
        let failure : Option Exception ← try
          discard <| changed.checkResult graph expected projectedValue
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "prepared result checking changed its actual dependent index"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime value has a different consuming dependent reference" do
          throw failure
        let reused ← liftM (m := IO) <|
          RecordPrefix.begin owners.identities program occurrence layout
        let (graph, reused, reusedIndex) ← liftM (m := IO) <| reused.bind graph originalIndex
        let (graph, _, reusedValue) ← liftM (m := IO) <| reused.bind graph projectedValue
        let .ok reusedParameter := RuntimeParameter.ofValue graph bindings[1]!.id reusedIndex
          | throwError "the reused actual index role is absent"
        let reusedEnvironment ← RuntimeEnvironment.capture owners.worker context
          #[reusedParameter]
        let reusedResult ← reusedEnvironment.checkResult graph expected reusedValue
        unless reusedResult.root.value == projectedValue.value &&
            reusedResult.root.instantiations.size == projectedValue.instantiations.size + 1 do
          throwError "dependent record reuse lost its actual value or original consuming roles"
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

-- Distinct equal-valued lets occupy different dependent type positions. A closed formal
-- index also has to retain the actual binding named at that position in the expected type.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, firstIndex) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, secondIndex) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless firstIndex.value != secondIndex.value do
    throwError "the distinct-let control merged its original runtime nodes"
  withLetDecl `n (mkConst ``Nat) (mkNatLit 7) fun n =>
    withLetDecl `m (mkConst ``Nat) (mkNatLit 7) fun m =>
      withLetDecl `alias (mkConst ``Nat) n fun aliasBinding => do
        let indexed := fun index => mkAppM ``Prod
          #[mkApp (mkConst ``Fin) index, mkApp (mkConst ``Fin) m]
        withLocalDeclD `point (← indexed n) fun point => do
          withLocalDeclD `aliasPoint (← indexed aliasBinding) fun aliasPoint => do
            withLocalDeclD `changedPoint (← indexed m) fun changedPoint => do
              let bindings : Array LocalBinding := #[
                { id := ⟨"distinct-consuming-context", 0⟩, role := .definition, expression := n },
                { id := ⟨"distinct-consuming-context", 1⟩, role := .definition, expression := m },
                { id := ⟨"distinct-consuming-context", 2⟩, role := .definition, expression := aliasBinding },
                { id := ⟨"distinct-consuming-context", 3⟩, role := .parameter, expression := point },
                { id := ⟨"distinct-consuming-context", 4⟩, role := .parameter, expression := aliasPoint },
                { id := ⟨"distinct-consuming-context", 5⟩, role := .parameter, expression := changedPoint }]
              let context ← ContextTelescope.capture bindings
              unless ← isDefEq n m do
                throwError "the distinct-let control lost its equal native definitions"
              let family ← withLocalDeclD `width (mkConst ``Nat) fun width => do
                mkLambdaFVars #[width] (← indexed width)
              let pointRole ← SourceLayout.ofTerm (← context.close point)
              let (graph, pointValue) ← liftM (m := IO) <| graph.stage owners.identities
                { program, occurrence, role := pointRole,
                  parameters := Array.replicate bindings.size none } (.closure program #[])
              for formal in #[n, mkNatLit 7] do
                let source := mkApp4 (mkConst ``Sigma.mk [.zero, .zero])
                  (mkConst ``Nat) family formal point
                let layout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close source))
                let record ← liftM (m := IO) <|
                  RecordPrefix.begin owners.identities program occurrence layout
                let (graph, record, originalIndex) ← liftM (m := IO) <| record.bind graph firstIndex
                let (graph, _, consumed) ← liftM (m := IO) <| record.bind graph pointValue
                let parameter (index : Nat) (value : ValueBinding) : MetaM RuntimeParameter := do
                  let .ok parameter := RuntimeParameter.ofValue graph bindings[index]!.id value
                    | throwError "the distinct-let parameter is outside its graph"
                  return parameter
                let actual ← parameter 3 consumed
                let first ← parameter 0 originalIndex
                let second ← parameter 1 secondIndex
                let accepted ← RuntimeEnvironment.capture owners.worker context #[actual, first, second]
                unless ((accepted.lookup bindings[3]!.id).toOption.bind id).map (·.value) ==
                    some consumed.value do
                  throwError "the exact dependent position lost its original value"
                let aliasEnvironment ← RuntimeEnvironment.capture owners.worker context
                  #[first, second, ← parameter 2 originalIndex]
                let aliasRole ← SourceLayout.ofTerm (← context.close aliasPoint)
                let aliased ← aliasEnvironment.checkResult graph aliasRole consumed
                unless aliased.root.value == consumed.value do
                  throwError "a true dependent alias changed its original value"
                let invalid := #[
                  (#[actual, ← parameter 0 secondIndex, second],
                    "the runtime value has a different consuming dependent reference"),
                  (#[actual, second], "the runtime value is missing a consuming dependent reference")]
                for (parameters, expected) in invalid do
                  let failure : Option Exception ← try
                    discard <| RuntimeEnvironment.capture owners.worker context parameters
                    pure none
                  catch error => pure (some error)
                  let some failure := failure
                    | throwError "an equal-valued unrelated binding replaced the required dependent reference"
                  unless (← failure.toMessageData.toString).startsWith expected do throw failure
                let changedRole ← SourceLayout.ofTerm (← context.close changedPoint)
                let failure : Option Exception ← try
                  discard <| accepted.checkResult graph changedRole consumed
                  pure none
                catch error => pure (some error)
                let some failure := failure
                  | throwError "native type conversion changed the retained dependent occurrence"
                unless (← failure.toMessageData.toString).startsWith
                    "the runtime value has a different consuming dependent reference" do throw failure

-- A whole-record alias cannot fill a missing named source root of a dependent type.
-- This differs from the earlier n := r.fst control, which supplies the actual field itself.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, number) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  withLocalDeclD `r pairType fun r =>
    withLetDecl `alias pairType r fun aliasBinding => do
      let width ← mkProjection r `fst
      let aliasWidth ← mkProjection aliasBinding `fst
      let indexed := fun index => mkAppM ``Prod
        #[mkApp (mkConst ``Fin) index, mkApp (mkConst ``Fin) aliasWidth]
      withLocalDeclD `point (← indexed width) fun point => do
        let bindings : Array LocalBinding := #[
          { id := ⟨"projected-alias-context", 0⟩, role := .parameter, expression := r },
          { id := ⟨"projected-alias-context", 1⟩, role := .definition, expression := aliasBinding },
          { id := ⟨"projected-alias-context", 2⟩, role := .parameter, expression := point }]
        let context ← ContextTelescope.capture bindings
        let pair ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close r))
        let record ← liftM (m := IO) <| RecordPrefix.begin owners.identities program occurrence pair
        let (graph, record, index) ← liftM (m := IO) <| record.bind graph number
        let (graph, record, _) ← liftM (m := IO) <| record.bind graph number
        let .ok payload := record.finish | throwError "the alias control lost its source record"
        let (graph, parent) ← liftM (m := IO) <| graph.stage owners.identities
          { program, occurrence, role := pair.source, parameters := #[none, none, none] } payload
        let pointRole ← SourceLayout.ofTerm (← context.close point)
        let (graph, value) ← liftM (m := IO) <| graph.stage owners.identities
          { program, occurrence, role := pointRole, parameters := #[none, none, none] }
          (.closure program #[])
        let family ← withLocalDeclD `bound (mkConst ``Nat) fun bound => do
          mkLambdaFVars #[bound] (← indexed bound)
        let source := mkApp4 (mkConst ``Sigma.mk [.zero, .zero])
          (mkConst ``Nat) family width point
        let layout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close source))
        let record ← liftM (m := IO) <| RecordPrefix.begin owners.identities program occurrence layout
        let (graph, record, _) ← liftM (m := IO) <| record.bind graph index
        let (graph, _, consumed) ← liftM (m := IO) <| record.bind graph value
        let parameter (index : Nat) (value : ValueBinding) : MetaM RuntimeParameter := do
          let .ok parameter := RuntimeParameter.ofValue graph bindings[index]!.id value
            | throwError "the projected alias parameter is outside its graph"
          return parameter
        let actual ← parameter 2 consumed
        let original ← parameter 0 parent
        let aliased ← parameter 1 parent
        discard <| RuntimeEnvironment.capture owners.worker context #[actual, original, aliased]
        for (parameters, missing) in #[(#[actual, aliased], bindings[0]!.id),
            (#[actual, original], bindings[1]!.id)] do
          let failure : Option Exception ← try
            discard <| RuntimeEnvironment.capture owners.worker context parameters
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "a whole-record alias replaced a missing dependent source root"
          unless missingValueOf failure missing do throw failure

-- Typed object provenance keeps the original runtime argument authoritative. These two
-- source objects have equal native definitions but separate actual nodes. The new identity
-- wrapper and a named definition containing it must both retain their exact source binding.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let nativeObject := mkConst ``Nat
  let objectType ← inferType nativeObject
  let sourceRole ← SourceLayout.ofTerm (← empty.close nativeObject)
  let categoryInfo ← getConstInfo ``LeanCategories.Foundation.Mathlib.Sets
  let category : NativeSourceCategory :=
    ⟨.object, .atom CasCatalogue.CategoryId.sets,
      mkConst categoryInfo.name (categoryInfo.levelParams.map fun _ => Level.zero), none, none⟩
  let markedDefinition ← annotateSourceObject category nativeObject
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let .ok payload := ValuePayload.descriptor
      (Json.mkObj [("ctor", "lean:type"), ("args", .arr #[])]) #[]
    | throwError "the object-origin control descriptor is malformed"
  let (graph, firstValue) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := sourceRole, parameters := #[] } payload
  let (graph, secondValue) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := sourceRole, parameters := #[] } payload
  unless firstValue.value != secondValue.value do
    throwError "the object-origin control merged distinct original objects"
  withLetDecl `firstObject objectType markedDefinition fun firstObject =>
    withLetDecl `secondObject objectType markedDefinition fun secondObject => do
      let bindings : Array LocalBinding := #[
        { id := ⟨"object-origin-arguments", 0⟩, role := .definition, expression := firstObject },
        { id := ⟨"object-origin-arguments", 1⟩, role := .definition, expression := secondObject }]
      let context ← ContextTelescope.capture bindings
      unless ← isDefEq firstObject secondObject do
        throwError "the object-origin control lost its equal native definitions"
      let .ok firstParameter := RuntimeParameter.ofValue graph bindings[0]!.id firstValue
        | throwError "the first source object is outside its graph"
      let .ok secondParameter := RuntimeParameter.ofValue graph bindings[1]!.id secondValue
        | throwError "the second source object is outside its graph"
      let environment ← RuntimeEnvironment.capture owners.worker context
        #[firstParameter, secondParameter]
      let .ok originalArgument := RuntimeArgument.ofValue graph 0 firstValue
        | throwError "the original object argument is outside its graph"
      let .ok otherArgument := RuntimeArgument.ofValue graph 0 secondValue
        | throwError "the other object argument is outside its graph"
      let wrapped ← annotateSourceObject category firstObject
      -- Inspect a wrapper only at its own metadata branch. A current named source has its
      -- own actual runtime binding even when its definition also contains such a wrapper.
      for specified in #[firstObject, wrapped] do
        let source ← context.close specified
        let accepted ← environment.checkArgument source originalArgument
        unless accepted.value == firstValue.value &&
            accepted.associationIds == firstValue.associationIds &&
            (← accepted.role.source.inContext context) == specified do
          throwError "object provenance changed the original value, associations or wrapped role"
        let failure : Option Exception ← try
          discard <| environment.checkArgument source otherArgument
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "object provenance admitted another equal-valued source argument"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw failure
        unless ← environment.hasRetainedSource context specified do
          throwError "object provenance hid the original retained source binding"
      -- An outer value mark adds a constraint; it cannot replace the wrapped source binder.
      let marks ← liftM (m := IO) <| IO.mkRef (#[] : Array ValueBinding)
      let relabelled ← markValue marks secondValue wrapped
      let .ok markedOther := RuntimeArgument.ofValue graph 0 secondValue (← marks.get)
        | throwError "the other marked object is outside its graph"
      let failure : Option Exception ← try
        discard <| environment.checkArgument (← context.close relabelled) markedOther
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "an outer occurrence mark bypassed the wrapped source object"
      unless (← failure.toMessageData.toString).startsWith
          "the runtime argument does not retain its specified source value" do throw failure

-- A field family may retain an original ambient source parameter even when the consuming
-- native type spells its closed specialization directly. That validation must not select a
-- different named or marked occurrence, or discard the captured original parameter.
run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let natural := mkConst ``Nat
  let seven := mkNatLit 7
  let pairTerm ← mkAppM ``Prod.mk #[seven, seven]
  let pairType ← inferType pairTerm
  let scalarRole ← SourceLayout.ofTerm (← empty.close seven)
  let pairRole ← SourceLayout.ofTerm (← empty.close pairTerm)
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, firstWidth) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
  let (graph, secondWidth) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
  let (graph, number) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
  let (graph, firstObject) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := pairRole, parameters := #[] }
    (.product #[firstWidth, firstWidth])
  let (graph, secondObject) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := pairRole, parameters := #[] }
    (.product #[secondWidth, secondWidth])
  unless firstObject.value != secondObject.value && firstWidth.value != secondWidth.value do
    throwError "the ambient-parameter control merged its independent original nodes"
  let marks ← liftM (m := IO) <| IO.mkRef (#[] : Array ValueBinding)
  let markedSecond ← markValue marks secondObject pairTerm
  let markedWidth ← mkProjection markedSecond `fst
  unless !markedWidth.hasFVar do
    throwError "the closed marked-parameter control contains an ambient free variable"
  withLetDecl `Qfirst pairType pairTerm fun first =>
    withLetDecl `Qsecond pairType pairTerm fun second =>
      withLetDecl `n natural seven fun n => do
        let firstProjection ← mkProjection first `fst
        let secondProjection ← mkProjection second `fst
        let indexed := fun fixed index => mkAppM ``Prod
          #[mkApp (mkConst ``Fin) fixed, mkApp (mkConst ``Fin) index]
        withLocalDeclD `point (← indexed firstProjection n) fun point =>
          withLocalDeclD `closedPoint (← indexed seven n) fun closedPoint =>
            withLocalDeclD `otherPoint (← indexed secondProjection n) fun otherPoint =>
              withLocalDeclD `markedPoint (← indexed markedWidth n) fun markedPoint => do
                let bindings : Array LocalBinding := #[
                  { id := ⟨"closed-dependent-fragment", 0⟩, role := .definition, expression := first },
                  { id := ⟨"closed-dependent-fragment", 1⟩, role := .definition, expression := second },
                  { id := ⟨"closed-dependent-fragment", 2⟩, role := .definition, expression := n },
                  { id := ⟨"closed-dependent-fragment", 3⟩, role := .parameter, expression := point },
                  { id := ⟨"closed-dependent-fragment", 4⟩, role := .parameter, expression := closedPoint },
                  { id := ⟨"closed-dependent-fragment", 5⟩, role := .parameter, expression := otherPoint },
                  { id := ⟨"closed-dependent-fragment", 6⟩, role := .parameter, expression := markedPoint }]
                let context ← ContextTelescope.capture bindings
                let markedFirst ← markValue marks firstObject first
                let fixedProjection ← mkProjection markedFirst `fst
                let family ← withLocalDeclD `width natural fun width =>
                  mkLambdaFVars #[width] (← indexed fixedProjection width)
                let pointRole ← SourceLayout.ofTerm (← context.close point)
                let (graph, value) ← liftM (m := IO) <| graph.stage owners.identities
                  { program, occurrence, role := pointRole,
                    parameters := #[some firstObject, none, some number, none, none, none, none] }
                  (.closure program #[firstObject, number])
                let source := mkApp4 (mkConst ``Sigma.mk [.zero, .zero]) natural family n point
                let layout ← RecordLayout.ofSource (← SourceLayout.ofTerm (← context.close source))
                let record ← liftM (m := IO) <|
                  RecordPrefix.begin owners.identities program occurrence layout
                let (graph, record, originalIndex) ← liftM (m := IO) <| record.bind graph number
                let (graph, _, consumed) ← liftM (m := IO) <| record.bind graph value
                let parameter (index : Nat) (actual : ValueBinding) : MetaM RuntimeParameter := do
                  let .ok parameter := RuntimeParameter.ofValue graph bindings[index]!.id actual
                    | throwError "the ambient-parameter control lost an original runtime reference"
                  return parameter
                let original ← parameter 0 firstObject
                let unrelated ← parameter 1 secondObject
                let index ← parameter 2 originalIndex
                let environment ← RuntimeEnvironment.capture owners.worker context
                  #[original, unrelated, index]
                let closedRole ← SourceLayout.ofTerm (← context.close closedPoint)
                let accepted ← environment.checkResult graph closedRole consumed
                unless accepted.root.value == consumed.value &&
                    accepted.root.associationIds == consumed.associationIds &&
                    accepted.root.instantiations.map (·.id) == consumed.instantiations.map (·.id) do
                  throwError "closed native specialization changed the actual dependent field"
                for expected in #[otherPoint, markedPoint] do
                  let role ← SourceLayout.ofTerm (← context.close expected)
                  unless ← isDefEq (← inferType point) (← inferType expected) do
                    throwError "the ambient-parameter negative is not natively convertible"
                  let failure : Option Exception ← try
                    discard <| environment.checkResult graph role consumed
                    pure none
                  catch error => pure (some error)
                  let some failure := failure
                    | throwError "closed native conversion substituted a different source occurrence"
                  unless (← failure.toMessageData.toString).startsWith
                      "the runtime value has an unresolved consuming dependent type" do throw failure
                let replacedOriginal ← parameter 0 secondObject
                for (parameters, missing) in #[(#[unrelated, index], true),
                    (#[replacedOriginal, unrelated, index], false)] do
                  let changed ← RuntimeEnvironment.capture owners.worker context parameters
                  let failure : Option Exception ← try
                    discard <| changed.checkResult graph closedRole consumed
                    pure none
                  catch error => pure (some error)
                  let some failure := failure
                    | throwError "closed native specialization discarded its captured original parameter"
                  if missing then
                    unless missingValueOf failure bindings[0]!.id do throw failure
                  else
                    unless (← failure.toMessageData.toString).startsWith
                        "the runtime value has a different retained dependent reference" do throw failure
