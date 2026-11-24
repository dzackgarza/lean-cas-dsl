module

import CasRuntime.Kernel
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel

namespace CasRuntime.ProjectionRecordDependencyTests

open Lean Meta CasCompiler

-- The original lazy input contains an ordinary native dependent record. Projecting that
-- record must succeed through its actual retained parent before any later field demand.
-- No provider or mathematical result is supplied, and no payload value is asserted.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let term ← Elab.Term.elabTermAndSynthesize
      (← `(((⟨7, ⟨0, Nat.zero_lt_succ 7⟩⟩ : Sigma (fun n : Nat => Fin (n + 1))), ()))) none
    let source ← empty.close term
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let code ← owners.identities.fresh .program
      kernel.codes.modify (·.insert code (.term source))
      let input ← producer.stage
        { program := code, occurrence := ← kernel.ledger.allocate,
          role := ← SourceLayout.ofTerm source, parameters := #[] }
        (.closure code #[])
      let .error _ := (← producer.view).project input 0
        | throwError "the native dependent-record control already has a stored first field"
      let .ok _ ← producer.commit
        | throwError "the original lazy dependent record could not publish"
      withLocalDeclD `x (← inferType term) fun x => do
        let binding : LocalBinding := {
          id := { session := "native-record-projection", serial := 0 },
          role := .parameter, expression := x }
        let context ← ContextTelescope.capture #[binding]
        let bound : Std.HashMap BindingId ValueBinding := {}
        let consumer ← CellTransaction.begin kernel.ledger
        try
          let result ← kernel.run consumer context (bound.insert binding.id input)
            (mkProj ``Prod 0 x)
          unless result.projectionAccesses.any (fun (parent, path) =>
              parent.value == input.value && parent.associationIds == input.associationIds &&
                path == #[``Prod.fst]) do
            throwError "the native record projection lost its exact original lazy parent"
          unless (← kernel.dispatches.get).isEmpty do
            throwError "the native record projection dispatched a provider"
        finally discard <| consumer.abort
      -- Session retains a definition's exact let role on the same original value node.
      -- Native conversion can still read its definition; reference selection keeps x.
      withLetDecl `x (← inferType term) term fun x => do
        let binding : LocalBinding := {
          id := { session := "native-record-projection-alias", serial := 0 },
          role := .definition, expression := x }
        let context ← ContextTelescope.capture #[binding]
        let .ok selected := input.withRole (← SourceLayout.ofTerm (← context.close x))
          | throwError "the native dependent record could not retain its source alias"
        let bound : Std.HashMap BindingId ValueBinding := {}
        let consumer ← CellTransaction.begin kernel.ledger
        try
          let result ← kernel.run consumer context (bound.insert binding.id selected)
            (mkProj ``Prod 0 x)
          unless result.projectionAccesses.any (fun (parent, path) =>
              parent.value == selected.value &&
                parent.associationIds == selected.associationIds && path == #[``Prod.fst]) do
            throwError "the aliased native record projection lost its exact original parent"
          unless (← kernel.dispatches.get).isEmpty do
            throwError "the aliased native record projection dispatched a provider"
        finally discard <| consumer.abort
    finally kernel.close
  finally setEnv original

-- Two accesses to a stored nested record retain distinct consuming fields. Publishing
-- the first nested access must not make its new field associations the original stored
-- baseline for the second one. Both still require their exact parent and native path.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let outer ← mkAppM ``Prod.mk #[pair, mkNatLit 7]
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let innerRole ← SourceLayout.ofTerm (← context.close (mkProj ``Prod 0 outer))
    let outerRole ← SourceLayout.ofTerm (← context.close outer)
    let owners ← OwnerRegistry.new
    let ledger ← OccurrenceLedger.new owners
    discard <| SessionSnapshot.initialize owners
    let transaction ← CellTransaction.begin ledger
    try
      let program ← owners.identities.fresh .program
      let occurrence ← ledger.allocate
      let producing := fun role =>
        ({ program, occurrence, role, parameters := #[] } : ValueOrigin)
      let scalar ← transaction.stage (producing scalarRole) (.portable "7".toUTF8)
      let inner ← transaction.stage (producing innerRole) (.product #[scalar, scalar])
      let parent ← transaction.stage (producing outerRole) (.product #[inner, scalar])
      let otherParent ← transaction.stage (producing outerRole) (.product #[inner, scalar])
      let publish (parent : ValueBinding) (index : Nat) : MetaM ValueBinding := do
        let graph ← transaction.view
        let .ok stored := graph.project parent index
          | throwError "the repeated projection lost its original stored field"
        let request ← PreparedRequest.forProjection owners.identities program
          (← ledger.allocate) context graph parent index #[]
        let (draft, selected) ← request.associateResult owners.identities request.source
          (← transaction.draft) stored
        discard <| request.admitResult draft.view selected
        let .ok () ← transaction.installDraft draft
          | throwError "the repeated projection lost its complete admitted draft"
        return selected
      let first ← publish parent 0
      let second ← publish parent 0
      let other ← publish otherParent 0
      unless first.value == inner.value && second.value == inner.value &&
          other.value == inner.value && first.associationIds != second.associationIds &&
          first.associationIds != other.associationIds do
        throwError "the repeated projection control lost its distinct consuming parents"
      let firstField ← publish first 0
      let secondField ← publish second 0
      let otherField ← publish other 0
      let graph ← transaction.view
      for (parent, field) in #[(first, firstField), (second, secondField), (other, otherField)] do
        let .ok (some baseline) := graph.projected? parent #[``Prod.fst]
          | throwError "a repeated nested projection lost its stored baseline"
        unless baseline.value == scalar.value &&
            baseline.associationIds == scalar.associationIds do
          throwError "a nested projection published a consuming view as its stored baseline"
        let .ok (some access) := graph.projectedAccess? parent #[``Prod.fst]
          | throwError "a repeated nested projection lost its exact parent access"
        unless access.value == field.value && access.associationIds == field.associationIds do
          throwError "a repeated nested projection reused another parent's access"
      let environment ← RuntimeEnvironment.capture owners.worker context #[]
      let check (parent : ValueBinding) (path : Name) (field : ValueBinding)
          (accepted : Bool) : MetaM Unit := do
        let marks ← IO.mkRef (#[] : Array ValueBinding)
        let selected ← markValue marks parent (← parent.role.source.inContext context)
        let specified ← context.close (← mkProjection selected path)
        let .ok argument := RuntimeArgument.ofValue graph 0 field (← marks.get)
          | throwError "the repeated projection argument is outside its graph"
        let failure : Option Exception ← try
            discard <| environment.checkArgument specified argument
            pure none
          catch error => pure (some error)
        match accepted, failure with
        | true, none => pure ()
        | true, some error =>
          throwError "the exact nested parent access was rejected ({repr parent.associationIds}): {error.toMessageData}"
        | false, none => throwError "a nested projection accepted a different parent or field path"
        | false, some error =>
          unless error.toMessageData.hasTag
              (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do throw error
      check first `fst firstField true
      check second `fst secondField true
      check other `fst otherField true
      check first `fst secondField false
      check first `fst otherField false
      check first `snd firstField false
      -- A verified inner occurrence cannot bypass a conflicting outer occurrence.
      let marks ← IO.mkRef (#[] : Array ValueBinding)
      let wrongOuter ← markValue marks otherParent outer
      let wrongInner ← mkProjection wrongOuter `fst
      let relabelled ← markValue marks first wrongInner
      let specified ← context.close (← mkProjection relabelled `fst)
      let .ok argument := RuntimeArgument.ofValue graph 0 firstField (← marks.get)
        | throwError "the relabelled nested projection is outside its graph"
      let failure : Option Exception ← try
          discard <| environment.checkArgument specified argument
          pure none
        catch error => pure (some error)
      let some failure := failure
        | throwError "an inner occurrence mark bypassed its different original outer parent"
      unless failure.toMessageData.hasTag
          (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do throw failure
    finally discard <| transaction.abort
  finally setEnv original

-- The public native lowering path must retain these same stored baselines when the
-- inner record has a dependent field. Every access keeps its exact consuming parent.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let term ← Elab.Term.elabTermAndSynthesize
      (← `(((⟨7, ⟨0, Nat.zero_lt_succ 7⟩⟩ : Sigma (fun n : Nat => Fin (n + 1))), ()))) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let outer ← kernel.run transaction context {} term
        let graph ← transaction.view
        let .ok originalInner := graph.project outer 0
          | throwError "the repeated native projection lost its original stored record"
        let .ok originalField := graph.project originalInner 0
          | throwError "the repeated native projection lost its original stored prefix"
        let markedOuter ← markValue kernel.marks outer term
        let innerSource := mkProj ``Prod 0 term
        let first ← kernel.run transaction context {} (mkProj ``Prod 0 markedOuter)
        let markedFirst ← markValue kernel.marks first innerSource
        let firstField ← kernel.run transaction context {} (mkProj ``Sigma 0 markedFirst)
        let second ← kernel.run transaction context {} (mkProj ``Prod 0 markedOuter)
        let markedSecond ← markValue kernel.marks second innerSource
        let secondField ← kernel.run transaction context {} (mkProj ``Sigma 0 markedSecond)
        unless first.value == originalInner.value && second.value == originalInner.value &&
            first.associationIds != second.associationIds do
          throwError "the repeated native projection lost its two distinct consuming views"
        let graph ← transaction.view
        for (parent, selected) in #[(first, firstField), (second, secondField)] do
          let .ok stored := graph.project parent 0
            | throwError "a consuming native projection lost its actual stored field"
          unless selected.value == originalField.value && stored.value == selected.value &&
              stored.associationIds.toList.isPrefixOf selected.associationIds.toList do
            throwError "a repeated native projection changed its current parent's original field"
          let .ok (some baseline) := graph.projected? parent #[``Sigma.fst]
            | throwError "the repeated native projection lost its original baseline"
          unless baseline.value == originalField.value &&
              baseline.associationIds == originalField.associationIds do
            throwError "a sibling native projection supplied a consuming view as the original field"
          unless selected.projectionAccesses.any (fun (original, path) =>
              original.value == parent.value &&
                original.associationIds == parent.associationIds && path == #[``Sigma.fst]) do
            throwError "the repeated native projection changed its exact consuming parent"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "a stored native projection dispatched a mathematical provider"
      finally discard <| transaction.abort
    finally kernel.close
  finally setEnv original

end CasRuntime.ProjectionRecordDependencyTests
