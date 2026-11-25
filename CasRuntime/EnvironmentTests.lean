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

-- Conversion of native indexes does not merge their distinct source positions or actual suppliers.
private structure EqualIndexRecord where
  leftIndex : Nat
  rightIndex : Nat
  operation : Fin leftIndex → Fin rightIndex

run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let finite := mkApp (mkConst ``Fin) (mkNatLit 7)
  let identity ← withLocalDeclD `element finite fun element => mkLambdaFVars #[element] element
  let native ← mkAppM ``EqualIndexRecord.mk #[mkNatLit 7, mkNatLit 7, identity]
  withLetDecl `record (mkConst ``EqualIndexRecord) native fun sourceRecord => do
    let leftField ← mkProjection sourceRecord `leftIndex
    let rightField ← mkProjection sourceRecord `rightIndex
    let sourceOperation ← mkProjection sourceRecord `operation
    let leftAlias ← mkAppM ``id #[leftField]
    withLetDecl `left (mkConst ``Nat) leftAlias fun left =>
      withLetDecl `right (mkConst ``Nat) rightField fun right => do
        let operationType ← mkArrow (mkApp (mkConst ``Fin) left) (mkApp (mkConst ``Fin) right)
        withLocalDeclD `operation operationType fun operation => do
          unless ← isDefEq left right do
            throwError "the consuming-position control requires definitionally equal native indexes"
          let bindings : Array LocalBinding := #[
            { id := ⟨"equal-consuming-positions", 0⟩, role := .result, expression := sourceRecord },
            { id := ⟨"equal-consuming-positions", 1⟩, role := .definition, expression := left },
            { id := ⟨"equal-consuming-positions", 2⟩, role := .definition, expression := right },
            { id := ⟨"equal-consuming-positions", 3⟩, role := .parameter, expression := operation }]
          let context ← ContextTelescope.capture bindings
          let recordLayout ← RecordLayout.ofSource
            (← SourceLayout.ofTerm (← context.close sourceRecord))
          let callable ← SourceLayout.ofTerm (← context.close sourceOperation)
          let expected ← SourceLayout.ofTerm (← context.close operation)
          let owners ← liftM (m := IO) OwnerRegistry.new
          let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
          let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
          let (graph, firstIndex) ← liftM (m := IO) <|
            (ValueGraph.empty owners.identities).stage owners.identities
              { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
          let (graph, secondIndex) ← liftM (m := IO) <| graph.stage owners.identities
            { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
          unless firstIndex.value != secondIndex.value do
            throwError "the consuming-position control lost its distinct actual suppliers"
          let (graph, function) ← liftM (m := IO) <| graph.stage owners.identities
            { program, occurrence, role := callable, parameters := #[none, none, none, none] }
            (.closure program #[])
          let record ← liftM (m := IO) <|
            RecordPrefix.begin owners.identities program occurrence recordLayout
          let (graph, record, actualLeft) ← liftM (m := IO) <| record.bind graph firstIndex
          let (graph, record, actualRight) ← liftM (m := IO) <| record.bind graph secondIndex
          let (graph, record, actualOperation) ← liftM (m := IO) <| record.bind graph function
          let .ok _ := record.finish
            | throwError "the consuming-position control did not retain the complete native record"
          let parameter (source : BindingId) (value : ValueBinding) : MetaM RuntimeParameter := do
            let .ok parameter := RuntimeParameter.ofValue graph source value
              | throwError "the consuming-position control lost an actual field"
            return parameter
          let correct := #[
            ← parameter bindings[1]!.id actualLeft,
            ← parameter bindings[2]!.id actualRight]
          let suppliedOperation ← parameter bindings[3]!.id actualOperation
          let captured ← RuntimeEnvironment.capture owners.worker context (correct.push suppliedOperation)
          let .ok argument := RuntimeArgument.ofValue graph 0 actualOperation
            | throwError "the consuming-position control lost its actual callable"
          let retained ← captured.checkArgument (← context.close operation) argument
          let environment ← RuntimeEnvironment.capture owners.worker context correct
          let candidate ← environment.checkResult graph expected actualOperation
          unless retained.value == actualOperation.value &&
              retained.associationIds == actualOperation.associationIds &&
              candidate.root.value == actualOperation.value &&
              candidate.root.associationIds == actualOperation.associationIds do
            throwError "dependent source preparation changed the correctly positioned actual callable"
          let swapped := #[
            ← parameter bindings[1]!.id actualRight,
            ← parameter bindings[2]!.id actualLeft]
          let rejectSwapped (action : MetaM Unit) : MetaM Unit := do
            let failure : Option Exception ← try
              action
              pure none
            catch error => pure (some error)
            let some failure := failure
              | throwError "dependent source preparation accepted swapped actual suppliers"
            unless (← failure.toMessageData.toString).startsWith
                "the runtime value has a different consuming dependent reference" do throw failure
          rejectSwapped do
            discard <| RuntimeEnvironment.capture owners.worker context
              (swapped.push suppliedOperation)
          let changed ← RuntimeEnvironment.capture owners.worker context swapped
          rejectSwapped do
            discard <| changed.checkResult graph expected actualOperation


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
      withLetDecl `alias (mkConst ``Nat) n fun aliasValue => do
        let indexed := fun index => mkAppM ``Prod
          #[mkApp (mkConst ``Fin) index, mkApp (mkConst ``Fin) m]
        withLocalDeclD `point (← indexed n) fun point => do
          withLocalDeclD `aliasPoint (← indexed aliasValue) fun aliasPoint => do
            withLocalDeclD `changedPoint (← indexed m) fun changedPoint => do
              let bindings : Array LocalBinding := #[
                { id := ⟨"distinct-consuming-context", 0⟩, role := .definition, expression := n },
                { id := ⟨"distinct-consuming-context", 1⟩, role := .definition, expression := m },
                { id := ⟨"distinct-consuming-context", 2⟩, role := .definition, expression := aliasValue },
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
    withLetDecl `alias pairType r fun aliasValue => do
      let width ← mkProjection r `fst
      let aliasWidth ← mkProjection aliasValue `fst
      let indexed := fun index => mkAppM ``Prod
        #[mkApp (mkConst ``Fin) index, mkApp (mkConst ``Fin) aliasWidth]
      withLocalDeclD `point (← indexed width) fun point => do
        let bindings : Array LocalBinding := #[
          { id := ⟨"projected-alias-context", 0⟩, role := .parameter, expression := r },
          { id := ⟨"projected-alias-context", 1⟩, role := .definition, expression := aliasValue },
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

-- A direct value keeps its actual marked type suppliers without any record-field association.
run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let written := mkNatLit 7
  let scalar ← SourceLayout.ofTerm (← context.close written)
  let (graph, first) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, second) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless first.value != second.value do
    throwError "the marked type control did not retain two distinct actual suppliers"
  let marks ← liftM (m := IO) <| IO.mkRef (#[] : Array ValueBinding)
  let firstMark ← markValue marks first written
  let secondMark ← markValue marks second written
  let aliasMark ← markValue marks first written
  let source := fun width => Expr.lam `x (mkApp (mkConst ``Fin) width) (mkBVar 0) .default
  let original ← SourceLayout.ofTerm (← context.close (source firstMark))
  let changed ← SourceLayout.ofTerm (← context.close (source secondMark))
  let aliasRole ← SourceLayout.ofTerm (← context.close (source aliasMark))
  let actual ← liftM (m := IO) marks.get
  let mut captured := #[]
  for role in #[original, changed, aliasRole] do
    let selected ← IO.ofExcept <| (captureSourceMarks actual role.source).mapError IO.userError
    captured ← IO.ofExcept <| (mergeSourceMarks captured selected).mapError IO.userError
  let producing ← RuntimeEnvironment.capture owners.worker context #[] captured (some graph)
  let origin ← producing.origin program occurrence original
  let (graph, value) ← liftM (m := IO) <|
    graph.stage owners.identities origin (.closure program #[])
  unless value.instantiations.isEmpty do
    throwError "the direct marked type control unexpectedly acquired a field association"
  let consuming ← RuntimeEnvironment.capture owners.worker context #[] captured (some graph)
  for role in #[original, aliasRole] do
    let accepted ← consuming.checkResult graph role value
    unless accepted.root.value == value.value do
      throwError "marked type admission changed the original actual value"
  withLetDecl `width (mkConst ``Nat) written fun width => do
    let binding : LocalBinding :=
      { id := ⟨"marked-direct-alias", 0⟩, role := .definition, expression := width }
    let aliased ← ContextTelescope.capture #[binding]
    let .ok parameter := RuntimeParameter.ofValue graph binding.id first
      | throwError "the same-supplier alias is outside its actual graph"
    let environment ← RuntimeEnvironment.capture owners.worker aliased #[parameter]
      captured (some graph)
    let role ← SourceLayout.ofTerm (← aliased.close (source width))
    discard <| environment.checkResult graph role value
  let failure : Option Exception ← try
    discard <| consuming.checkResult graph changed value
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a direct native value accepted a different equal-valued marked type supplier"
  unless (← failure.toMessageData.toString).startsWith
      "the runtime value has a different marked source type dependency" do throw failure

  -- A surrounding native reduction cannot erase a failed marked supplier comparison.
  let plusZero := fun width => mkApp2 (mkConst ``Nat.add) (mkNatLit 0) width
  let arithmetic ← SourceLayout.ofTerm (← context.close (source (plusZero firstMark)))
  let arithmeticAlias ← SourceLayout.ofTerm (← context.close (source (plusZero aliasMark)))
  let arithmeticChanged ← SourceLayout.ofTerm (← context.close (source (plusZero secondMark)))
  let arithmeticOrigin ← consuming.origin program occurrence arithmetic
  let (graph, arithmeticValue) ← liftM (m := IO) <|
    graph.stage owners.identities arithmeticOrigin (.closure program #[])
  let arithmeticEnvironment ←
    RuntimeEnvironment.capture owners.worker context #[] captured (some graph)
  discard <| arithmeticEnvironment.checkResult graph arithmeticAlias arithmeticValue
  let failure : Option Exception ← try
    discard <| arithmeticEnvironment.checkResult graph arithmeticChanged arithmeticValue
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "native Nat.add reduction erased a different marked type supplier"
  unless (← failure.toMessageData.toString).startsWith
      "the runtime value has a different marked source type dependency" do throw failure

  -- Formal source lets retain the same authority without acquiring runtime parameters.
  withLetDecl `firstWidth (mkConst ``Nat) firstMark fun firstWidth =>
    withLetDecl `secondWidth (mkConst ``Nat) secondMark fun secondWidth =>
      withLetDecl `sameWidth (mkConst ``Nat) aliasMark fun sameWidth => do
        let bindings : Array LocalBinding := #[
          { id := ⟨"formal-marked-widths", 0⟩, role := .definition, expression := firstWidth },
          { id := ⟨"formal-marked-widths", 1⟩, role := .definition, expression := secondWidth },
          { id := ⟨"formal-marked-widths", 2⟩, role := .definition, expression := sameWidth }]
        let complete ← ContextTelescope.capture bindings
        let firstRole ← SourceLayout.ofTerm (← complete.close (source firstWidth))
        let secondRole ← SourceLayout.ofTerm (← complete.close (source secondWidth))
        let sameRole ← SourceLayout.ofTerm (← complete.close (source sameWidth))
        let producing ← RuntimeEnvironment.capture owners.worker complete #[] captured (some graph)
        unless producing.values.all (·.isNone) do
          throwError "a formal marked width acquired a runtime parameter"
        let origin ← producing.origin program occurrence firstRole
        let (graph, formalValue) ← liftM (m := IO) <|
          graph.stage owners.identities origin (.closure program #[])
        let environment ← RuntimeEnvironment.capture owners.worker complete #[] captured (some graph)
        discard <| environment.checkResult graph firstRole formalValue
        discard <| environment.checkResult graph sameRole formalValue
        let failure : Option Exception ← try
          discard <| environment.checkResult graph secondRole formalValue
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "formal source definitions erased a different marked type supplier"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime value has a different marked source type dependency" do throw failure

  -- A later native role can add a marked type to a node whose original type was closed.
  -- A subsequent raw role rebind must not erase that earlier, admitted type supplier.
  let plainRole ← SourceLayout.ofTerm (← context.close (source written))
  let plainOrigin ← consuming.origin program occurrence plainRole
  let (graph, plain) ← liftM (m := IO) <|
    graph.stage owners.identities plainOrigin (.closure program #[])
  withLetDecl `writtenFirst (mkConst ``Nat) firstMark fun writtenFirst =>
    withLetDecl `writtenSecond (mkConst ``Nat) secondMark fun writtenSecond => do
      let bindings : Array LocalBinding := #[
        { id := ⟨"marked-role-context", 0⟩, role := .definition, expression := writtenFirst },
        { id := ⟨"marked-role-context", 1⟩, role := .definition, expression := writtenSecond }]
      let complete ← ContextTelescope.capture bindings
      let firstRole ← SourceLayout.ofTerm (← complete.close (source firstMark))
      let secondRole ← SourceLayout.ofTerm (← complete.close (source secondMark))
      let environment ← RuntimeEnvironment.capture owners.worker complete #[] captured (some graph)
      let admitted ← environment.checkResult graph firstRole plain
      unless !admitted.root.sourceDependencies.isEmpty &&
          admitted.root.sourceMarks.any (fun (key, _) => key == 1) do
        throwError "the later role control lost its selected type or inert complete-context mark"
      let .ok same := graph.rebind admitted.root firstRole
        | throwError "the unchanged marked source role could not be retained"
      discard <| environment.checkResult graph firstRole same
      let .ok rebound := graph.rebind admitted.root secondRole
        | throwError "the existing coarse role rebind could not be prepared"
      let failure : Option Exception ← try
        discard <| environment.checkResult graph secondRole rebound
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "a later role rebind erased an admitted marked type supplier"
      unless (← failure.toMessageData.toString).startsWith
          "the runtime value has a different marked source type dependency" do throw failure
