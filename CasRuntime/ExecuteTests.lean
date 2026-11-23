module

import CasRuntime.Execute
import CasRuntime.Kernel
import CasContract.Port
public meta import Lean.Elab.Command
meta import CasRuntime.Execute
meta import CasRuntime.Kernel
meta import CasContract.Port

open Lean Meta CasCompiler CasRuntime

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let function ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.add))
    let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let transaction ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let callable ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := function, parameters := #[] } (.closure program #[])
    let number ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
    let graph ← liftM (m := IO) transaction.view
    let .ok argument := RuntimeArgument.ofValue graph 0 number
      | throwError "the admitted argument is outside its graph"
    let request ← PreparedRequest.forApplication owners.identities program occurrence context callable
      #[← context.close (mkNatLit 7), ← context.close (mkNatLit 7)] #[argument] #[]
    let executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
      fun _ _ => throwError "an incomplete role map reached effect execution"
    let failure : Option Exception ← try
      discard <| Execute.run executor
        (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction
      pure none
    catch error => pure (some error)
    let some failure := failure | throwError "an incomplete input role map became executable"
    unless (← failure.toMessageData.toString).startsWith
        "a demanded computational argument role has no actual binding" do throw failure
    unless (← liftM (m := BaseIO) transaction.activeGraph).isNone do
      throwError "failed role-map admission retained a publishable cell"
  finally setEnv original

private def unavailableExecutor (request : PreparedRequest) (_ : CellTransaction) :
    MetaM (PreparedResponse request × CellTransaction) :=
  throwError "unavailable: this control has no external execution registration"

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let callableRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
    let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
    let recordRole ← SourceLayout.ofTerm (← context.close pair)
    let preparedRecord ← RecordLayout.ofSource recordRole
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let producer ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let scalar ← liftM (m := IO) <| producer.stage
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "stored scalar".toUTF8)
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let token ← liftM (m := IO) do
        child.child.stdin.putStr "owned callable\n"
        child.child.stdin.flush
        return (← child.child.stdout.getLine).trimAscii.toString
      let callable ← liftM (m := IO) <| producer.stage
        { program, occurrence, role := callableRole, parameters := #[] } (.ownedExport child token #[])
      let record ← liftM (m := IO) <| producer.stage
        { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar, callable])
      let associated ← liftM (m := IO) do
        let draft ← producer.draft
        let fields ← RecordPrefix.begin owners.identities program occurrence preparedRecord
        let (draft, fields, _) ← draft.bindField fields scalar
        let (draft, fields, _) ← draft.bindField fields callable
        let payload ← IO.ofExcept <| fields.finish.mapError IO.userError
        let (draft, binding) ← draft.stage
          { program, occurrence, role := recordRole, parameters := #[] } payload
        let .ok () ← producer.installDraft draft
          | throw <| IO.userError "the associated record draft could not install"
        return binding
      let packet ← IO.ofExcept <| (ValuePayload.container
        (Json.mkObj [("args", .arr #[.null, .null]), ("description", .str "retained packet")])
        #[{ path := #[.field "args", .index 0], binding := scalar, fieldIndex := some 0 },
          { path := #[.field "args", .index 1], binding := callable, fieldIndex := some 1 }]
        #[scalar, callable] none).mapError IO.userError
      let packetRecord ← liftM (m := IO) <| producer.stage
        { program, occurrence, role := recordRole, parameters := #[] } packet
      let .ok _ ← producer.commit | throwError "the stored record could not commit"
      liftM (m := IO) <| owners.close child.generation
      let consumer ← CellTransaction.begin ledger
      let graph ← liftM (m := IO) consumer.view
      let first ← liftM (m := BaseIO) ledger.allocate
      let second ← liftM (m := BaseIO) ledger.allocate
      let left ← PreparedRequest.forProjection owners.identities program first context graph record 0 #[]
      let again ← PreparedRequest.forProjection owners.identities program second context graph record 0 #[]
      let packetOccurrence ← liftM (m := BaseIO) ledger.allocate
      let packetProjection ←
        PreparedRequest.forProjection owners.identities program packetOccurrence context graph packetRecord 0 #[]
      let associatedOccurrence ← liftM (m := BaseIO) ledger.allocate
      let associatedProjection ←
        PreparedRequest.forProjection owners.identities program associatedOccurrence context graph associated 0 #[]
      let code : OperationalProgram (Array ValueBinding) := do
        let a ← PFunctor.FreeM.lift (P := OperationalSignature) left
        let b ← PFunctor.FreeM.lift (P := OperationalSignature) again
        let c ← PFunctor.FreeM.lift (P := OperationalSignature) packetProjection
        let d ← PFunctor.FreeM.lift (P := OperationalSignature) associatedProjection
        pure #[a.root, b.root, c.root, d.root]
      let result ← Execute.run unavailableExecutor code consumer
      unless result.map (·.value) == #[scalar.value, scalar.value, scalar.value, scalar.value] do
        throwError "stateful execution replaced a stored field node"
      unless result[3]?.map (·.instantiations.size) == some 1 do
        throwError "stateful execution discarded the projected field's runtime instantiation"
      for (request, binding) in #[left, again, packetProjection, associatedProjection].zip result do
        let some role := request.roles.results[0]?
          | throwError "the stored projection lost its prepared result role"
        match ← liftM (m := BaseIO) <| consumer.reuse request.occurrence role.role.id with
        | .ok (.ready retained) =>
          unless retained.value == binding.value &&
              retained.associationIds == binding.associationIds do
            throwError "a stored projection completion changed its actual reference"
        | _ => throwError "a stored projection did not stage its exact completion"
        if ← liftM (m := BaseIO) <| ledger.isFresh request.occurrence then
          throwError "a completed stored projection retained a dispatch right"
      let .ok published ← consumer.commit
        | throwError "a dead unrelated field blocked the portable projection"
      unless published.outputBatches.size == 2 do
        throwError "the successful projection cell was not committed"
      for (request, binding) in #[left, again, packetProjection, associatedProjection].zip result do
        let some receipt := published.receipt request.occurrence
          | throwError "a committed stored projection omitted its receipt"
        unless receipt.association.response.root.value == binding.value &&
            receipt.association.response.root.associationIds == binding.associationIds do
          throwError "a stored projection receipt changed its actual reference"
        match receipt.association.producer with
        | .kernel => pure ()
        | .invocation .. => throwError "a stored projection invented an external invocation"
      let failed ← CellTransaction.begin ledger
      let third ← liftM (m := BaseIO) ledger.allocate
      let right ← PreparedRequest.forProjection owners.identities program third context graph associated 1 #[]
      let denied ← do
        try
          discard <| Execute.run unavailableExecutor
            (PFunctor.FreeM.lift (P := OperationalSignature) right) failed
          pure false
        catch error => pure <| (← error.toMessageData.toString).endsWith "unavailable: stale_owner"
      unless denied do throwError "a dead stored field reached execution"
      match ← failed.commit with
      | .error .settled => pure ()
      | _ => throwError "failed execution retained a publishable transaction"
      let visible ← SessionSnapshot.current
      unless visible.id == published.id do
        throwError "failed execution changed the committed Environment"
    finally liftM (m := IO) <| owners.close child.generation
  finally setEnv original

run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let callableRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let producer ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let child ← liftM (m := IO) <| owners.spawn { cmd := "/bin/cat" }
    try
      let token ← liftM (m := IO) do
        child.child.stdin.putStr "malformed-peer token\n"
        child.child.stdin.flush
        return (← child.child.stdout.getLine).trimAscii.toString
      let callable ← liftM (m := IO) <| producer.stage
        { program, occurrence, role := callableRole, parameters := #[] } (.ownedExport child token #[])
      let scalar ← liftM (m := IO) <| producer.stage
        { program, occurrence, role := scalarRole, parameters := #[] } (.portable "argument".toUTF8)
      let .ok _ ← producer.commit | throwError "the control inputs could not commit"
      let consumer ← CellTransaction.begin ledger
      let invocation ← liftM (m := BaseIO) ledger.allocate
      let .ok actualArgument :=
          RuntimeArgument.ofValue (← SessionSnapshot.current).graph 0 scalar
        | throwError "the actual execution argument is outside the committed graph"
      let request ← PreparedRequest.forApplication owners.identities program invocation context callable
        #[← context.close (mkNatLit 7)] #[actualArgument] #[]
      let selected : DispatchIdentity := {
        manifestDigest := "resource-test-manifest"
        registration := { operation := "resource-test", input := "resource-test", backend := "cat" }
        profileDigest := "resource-test-profile" }
      let malformedPeer : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
        fun demand transaction => do
          let .ok _ ← transaction.reserve demand.occurrence selected child demand.scope
            | throwError "the malformed-peer invocation could not reserve"
          CasCatalogue.Backend.writeFrame child.child.stdin
            (Json.mkObj [("probe", .str "malformed-peer control")])
          let .ok frame ← CasCatalogue.Backend.readFrame child.child.stdout
            | throwError "the actual peer frame could not be read"
          match CasCatalogue.Backend.field frame "status" with
          | .error _ => throwError "malformed: reply status is missing"
          | .ok _ => throwError "the malformed peer unexpectedly supplied a status"
      let rejected ← do
        try
          discard <| Execute.run malformedPeer
            (PFunctor.FreeM.lift (P := OperationalSignature) request) consumer
          pure false
        catch error => pure <| (← error.toMessageData.toString).endsWith "malformed: reply status is missing"
      unless rejected do throwError "malformed peer execution did not fail at the real frame boundary"
      if (← liftM (m := BaseIO) (ledger.pendingFor invocation consumer.id)).isSome then
        throwError "failed execution kept a pending invocation"
      let next ← owners.identities.fresh .transaction
      let graph := (← SessionSnapshot.current).graph
      match ← liftM (m := BaseIO) <| ledger.reserve invocation next selected child graph request.scope with
      | .error .consumed => pure ()
      | _ => throwError "failed execution replenished its consumed dispatch right"
      unless (← SessionSnapshot.current).outputBatches.size == 1 do
        throwError "malformed execution published an output batch"
    finally liftM (m := IO) <| owners.close child.generation
  finally setEnv original

-- Stateful execution checks the actual result's native type before retaining it.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let callableRole ← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ))
    let booleanRole ← SourceLayout.ofTerm (← context.close (mkConst ``Bool.true))
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let producer ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let scalar ← liftM (m := IO) <| producer.stage
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
    let callable ← liftM (m := IO) <| producer.stage
      { program, occurrence, role := callableRole, parameters := #[] } (.closure program #[])
    let boolean ← liftM (m := IO) <| producer.stage
      { program, occurrence, role := booleanRole, parameters := #[] } (.portable "true".toUTF8)
    let .ok base ← producer.commit | throwError "the native execution inputs could not commit"
    let transaction ← CellTransaction.begin ledger
    let invocation ← liftM (m := BaseIO) ledger.allocate
    let .ok argument := RuntimeArgument.ofValue base.graph 0 scalar
      | throwError "the actual native execution argument is absent"
    let request ← PreparedRequest.forApplication owners.identities program invocation context callable
      #[← context.close (mkNatLit 7)] #[argument] #[]
    let executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
      fun request transaction => do
        let graph ← transaction.view
        let candidate ← request.admitResult graph boolean
        return (candidate, transaction)
    let failure : Option String ← try
      discard <| Execute.run executor
        (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    let some failure := failure
      | throwError "stateful execution retained a result with a different native type"
    unless failure.endsWith "the runtime value has an incompatible complete source type" do
      throwError "native execution failed at a different boundary: {failure}"
    unless (← liftM (m := BaseIO) transaction.activeGraph).isNone &&
        (← SessionSnapshot.current).id == base.id do
      throwError "native result rejection retained a publishable transaction or changed the Environment"
  finally setEnv original

-- Complete result admission checks the actual stored children under their native field roles.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let booleanRole ← SourceLayout.ofTerm (← context.close (mkConst ``Bool.true))
    let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let recordRole ← SourceLayout.ofTerm (← context.close pair)
    let callable ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      let successor ← mkAppM ``Nat.succ #[n]
      mkLambdaFVars #[n] (← mkAppM ``Prod.mk #[successor, successor])
    let callableRole ← SourceLayout.ofTerm (← context.close callable)
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let transaction ← CellTransaction.begin ledger
    let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
    let occurrence ← liftM (m := BaseIO) ledger.allocate
    let scalar ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
    let boolean ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := booleanRole, parameters := #[] } (.portable "true".toUTF8)
    let retained ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := callableRole, parameters := #[] } (.closure program #[])
    let malformed ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar, boolean])
    let graph ← liftM (m := IO) transaction.view
    let .ok argument := RuntimeArgument.ofValue graph 0 scalar
      | throwError "the record execution argument is absent"
    let request ← PreparedRequest.forApplication owners.identities program occurrence context retained
      #[← context.close (mkNatLit 7)] #[argument] #[]
    let beforeResults := graph
    let valid ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar, scalar])
    let graph ← liftM (m := IO) transaction.view
    let checked ← request.environment.checkResult graph request.source valid
    unless checked.root.value == valid.value do
      throwError "stored result admission replaced the valid record"
    let admitted ← request.admitResult graph valid
    unless admitted.root.value == valid.value do
      throwError "result-role admission replaced the actual record"
    let some rootRole := request.roles.results[0]?
      | throwError "the result telescope lost its root"
    if (admitted.roles.lookup beforeResults rootRole.role.id).isOk then
      throwError "a result role recovered a returned value outside its visible snapshot"
    let mut fieldRoles := #[]
    for declared in request.roles.results do
      if declared.wirePath.isSome && declared.wirePath != some #[] then
        let .ok value := admitted.roles.lookup graph declared.role.id
          | throwError "an admitted stored field has no scoped result binding"
        unless value.value == scalar.value do
          throwError "a result role recovered another actual field"
        fieldRoles := fieldRoles.push declared.role.id
    unless fieldRoles.size == 2 && fieldRoles[0]? != fieldRoles[1]? do
      throwError "aliased result fields lost their distinct source roles"
    let next ← liftM (m := BaseIO) ledger.allocate
    let other ← PreparedRequest.forApplication owners.identities program next context retained
      #[← context.close (mkNatLit 7)] #[argument] #[]
    let some foreignRole := other.roles.results[0]?
      | throwError "the other result telescope has no root"
    match admitted.roles.lookup graph foreignRole.role.id with
    | .error message =>
      unless message == "the result role belongs to a different scope" do throwError message
    | .ok _ => throwError "a result role escaped its producing occurrence"
    let lazyRecord ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := recordRole, parameters := #[] } (.closure program #[])
    let graph ← liftM (m := IO) transaction.view
    let lazyResult ← request.admitResult graph lazyRecord
    let some fieldRole := request.roles.results[1]?
      | throwError "the lazy record has no declared field role"
    match lazyResult.roles.lookup graph fieldRole.role.id with
    | .error message =>
      unless message == "the result role has no materialized binding" do throwError message
    | .ok _ => throwError "a lazy result declaration supplied an unexecuted field"
    let nestedRole ← SourceLayout.ofTerm (← context.close (← mkAppM ``Prod.mk #[pair, pair]))
    let nestedLazy ← transaction.stage
      { program, occurrence, role := nestedRole, parameters := #[] } (.product #[lazyRecord, lazyRecord])
    let lazyProjection ← PreparedRequest.forProjection owners.identities program
      (← ledger.allocate) context (← transaction.view) nestedLazy 0 #[]
    let retainedLazy ← Execute.run unavailableExecutor
      (PFunctor.FreeM.lift (P := OperationalSignature) lazyProjection) transaction
    unless retainedLazy.root.value == lazyRecord.value do
      throwError "projecting a stored lazy record replaced or prematurely executed its value"
    let nestedValid ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := nestedRole, parameters := #[] } (.product #[valid, valid])
    let nestedOccurrence ← liftM (m := BaseIO) ledger.allocate
    let nestedTelescope ← RoleTelescope.ofRequest owners.identities program nestedOccurrence context none nestedRole #[]
    let graph ← liftM (m := IO) transaction.view
    let nestedMap ← ResultRoleMap.admit nestedTelescope request.environment graph nestedValid
    unless nestedTelescope.results.size == 7 do
      throwError "the result telescope lost nested source field positions"
    for declared in nestedTelescope.results do
      let .ok actual := nestedMap.lookup graph declared.role.id
        | throwError "a stored nested result has no declared role binding"
      let some path := declared.wirePath
        | throwError "the data-only nested result acquired a proof position"
      unless actual.value == (if path.size == 0 then nestedValid.value
          else if path.size == 1 then valid.value else scalar.value) do
        throwError "a nested role selected a different actual returned node"
    let nested ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := nestedRole, parameters := #[] } (.product #[valid, malformed])
    let graph ← liftM (m := IO) transaction.view
    let nestedFailure : Option Exception ← try
      discard <| request.environment.checkResult graph nestedRole nested
      pure none
    catch error => pure (some error)
    let some nestedFailure := nestedFailure
      | throwError "result admission retained a mistyped nested field"
    unless (← nestedFailure.toMessageData.toString).endsWith
        "the runtime value has an incompatible complete source type" do throw nestedFailure
    let executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
      fun request state => do
        let candidate ← request.admitResult (← state.view) malformed
        return (candidate, state)
    let directFailure : Option Exception ← try
      discard <| request.admitResult (← transaction.view) malformed
      pure none
    catch error => pure (some error)
    unless directFailure.isSome do
      throwError "direct malformed result admission accepted a mistyped stored field"
    let failure : Option Exception ← try
      discard <| Execute.run executor
        (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction
      pure none
    catch error => pure (some error)
    let some failure := failure
      | throwError "result admission retained a record with a mistyped stored field"
    unless (← failure.toMessageData.toString).endsWith
        "the runtime value has an incompatible complete source type" do throw failure
    unless (← liftM (m := BaseIO) transaction.activeGraph).isNone do
      throwError "stored field rejection retained a publishable transaction"
  finally setEnv original

-- T007 / C23: a projected operand belongs to its selected record, even when another
-- record has the same source definition and stores the very same scalar node.
-- This is source-association acceptance, not a mathematical oracle for a provider.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let recordRole ← SourceLayout.ofTerm (← empty.close pair)
    let scalarRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
    let callableRole ← SourceLayout.ofTerm (← empty.close (mkConst ``Nat.succ))
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let producer ← CellTransaction.begin ledger
    let program ← owners.identities.fresh .program
    let occurrence ← ledger.allocate
    let scalar ← producer.stage
      { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
    let callable ← producer.stage
      { program, occurrence, role := callableRole, parameters := #[] } (.closure program #[])
    let first ← producer.stage
      { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar, scalar])
    let second ← producer.stage
      { program, occurrence, role := recordRole, parameters := #[] } (.product #[scalar, scalar])
    let .ok _ ← producer.commit | throwError "the projection inputs could not commit"
    withLetDecl `r (← inferType pair) pair fun r => do
      withLetDecl `s (← inferType pair) pair fun s => do
        let bindings : Array LocalBinding := #[
          { id := ⟨"projection-input", 0⟩, role := .definition, expression := r },
          { id := ⟨"projection-input", 1⟩, role := .definition, expression := s }]
        let context ← ContextTelescope.capture bindings
        let transaction ← CellTransaction.begin ledger
        let graph ← transaction.view
        let .ok left := RuntimeParameter.ofValue graph bindings[0]!.id first
          | throwError "the first record is outside the graph"
        let .ok right := RuntimeParameter.ofValue graph bindings[1]!.id second
          | throwError "the second record is outside the graph"
        let parameters := #[left, right]
        let environment ← RuntimeEnvironment.capture owners.worker context parameters
        let .ok (some left) := environment.lookup bindings[0]!.id
          | throwError "the first record lost its source binding"
        let .ok (some right) := environment.lookup bindings[1]!.id
          | throwError "the second record lost its source binding"
        let firstRequest ← PreparedRequest.forProjection owners.identities program
          (← ledger.allocate) context graph left 0 parameters
        let secondRequest ← PreparedRequest.forProjection owners.identities program
          (← ledger.allocate) context graph right 0 parameters
        let actual ← Execute.run unavailableExecutor
          (PFunctor.FreeM.lift (P := OperationalSignature) firstRequest) transaction
        -- A new projection may carry an auxiliary input view, but that extra consuming
        -- association must not replace the exact field already stored by its parent.
        do
          let draft ← transaction.draft
          let (draft, enriched) ← draft.bindProjection
            (← secondRequest.originFor secondRequest.source) actual.root #[]
          unless enriched.value == scalar.value &&
              actual.root.associationIds.toList.isPrefixOf enriched.associationIds.toList do
            throwError "a projected result discarded its supplied auxiliary associations"
          let .ok (some baseline) := draft.view.projected? right #[``Prod.fst]
            | throwError "the second selected field lost its published baseline"
          unless baseline.value == scalar.value && baseline.associationIds == scalar.associationIds do
            throwError "a consuming projection view replaced the original stored field baseline"
          let .ok (some original) := draft.view.projectionBasis enriched right #[``Prod.fst]
            | throwError "the enriched projection lost its exact original parent path"
          unless original.value == scalar.value && original.associationIds == scalar.associationIds do
            throwError "a projection relation retained a new consuming view as its source input"
          let .ok () ← transaction.installDraft draft
            | throwError "the auxiliary projection view could not be published"
        let other ← Execute.run unavailableExecutor
          (PFunctor.FreeM.lift (P := OperationalSignature) secondRequest) transaction
        unless actual.root.value == scalar.value && other.root.value == scalar.value do
          throwError "projection replaced the shared stored scalar"
        let graph ← transaction.view
        let .ok accepted := RuntimeArgument.ofValue graph 0 actual.root
          | throwError "the selected projection is outside the graph"
        let .ok rejected := RuntimeArgument.ofValue graph 0 other.root
          | throwError "the other projection is outside the graph"
        let argument ← context.close (← mkProjection r `fst)
        discard <| PreparedRequest.forApplication owners.identities program
          (← ledger.allocate) context callable #[argument] #[accepted] parameters
        let failure : Option Exception ← try
          discard <| PreparedRequest.forApplication owners.identities program
            (← ledger.allocate) context callable #[argument] #[rejected] parameters
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "an equal field from a different record satisfied the selected projection"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw failure
        let repackedSource ← mkAppM ``Prod.mk #[← mkProjection r `fst, mkNatLit 7]
        let repackedRole ← SourceLayout.ofTerm (← context.close repackedSource)
        let repackedOrigin ← environment.origin program (← ledger.allocate) repackedRole
        let repacked ← transaction.stage repackedOrigin (.product #[actual.root, scalar])
        let repackedRequest ← PreparedRequest.forProjection owners.identities program
          (← ledger.allocate) context (← transaction.view) repacked 0 parameters
        let extended ← Execute.run unavailableExecutor
          (PFunctor.FreeM.lift (P := OperationalSignature) repackedRequest) transaction
        let .ok extendedArgument := RuntimeArgument.ofValue (← transaction.view) 0 extended.root
          | throwError "the extended projection is outside the graph"
        discard <| PreparedRequest.forApplication owners.identities program
          (← ledger.allocate) context callable #[argument] #[extendedArgument] parameters
        let siblingRequest ← PreparedRequest.forProjection owners.identities program
          (← ledger.allocate) context graph left 1 parameters
        let sibling ← Execute.run unavailableExecutor
          (PFunctor.FreeM.lift (P := OperationalSignature) siblingRequest) transaction
        let graph ← transaction.view
        let .ok siblingArgument := RuntimeArgument.ofValue graph 0 sibling.root
          | throwError "the sibling projection is outside the graph"
        let failure : Option Exception ← try
          discard <| PreparedRequest.forApplication owners.identities program
            (← ledger.allocate) context callable #[argument] #[siblingArgument] parameters
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "an equal field at another path satisfied the selected projection"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw failure
        withLetDecl `projected (mkConst ``Nat) (← mkProjection r `fst) fun projected => do
          let aliasBinding : LocalBinding :=
            { id := ⟨"projection-input", 2⟩, role := .definition, expression := projected }
          let aliasedContext ← ContextTelescope.capture (bindings.push aliasBinding)
          let .ok retainedAlias := RuntimeParameter.ofValue graph aliasBinding.id actual.root
            | throwError "the projected alias is outside the graph"
          let aliasSource ← aliasedContext.close projected
          discard <| PreparedRequest.forApplication owners.identities program
            (← ledger.allocate) aliasedContext callable #[aliasSource] #[accepted]
            (parameters.push retainedAlias)
          let .ok originalScalar := RuntimeArgument.ofValue graph 0 scalar
            | throwError "the original scalar is outside the graph"
          let failure : Option Exception ← try
            discard <| PreparedRequest.forApplication owners.identities program
              (← ledger.allocate) aliasedContext callable #[aliasSource] #[originalScalar]
              (parameters.push retainedAlias)
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "a projected alias accepted a value without its consuming associations"
          unless (← failure.toMessageData.toString).startsWith
              "the runtime argument does not retain its specified source value" do throw failure
        let marks ← liftM (m := IO) <| IO.mkRef (#[] : Array ValueBinding)
        let markedParent ← markValue marks first pair
        let markedSource ← context.close (← mkProjection markedParent `fst)
        let graph ← transaction.view
        let .ok markedActual := RuntimeArgument.ofValue graph 0 actual.root (← marks.get)
          | throwError "the marked projection is outside the graph"
        discard <| environment.checkArgument markedSource markedActual
        let .ok markedOther := RuntimeArgument.ofValue graph 0 other.root (← marks.get)
          | throwError "the other marked projection is outside the graph"
        let failure : Option Exception ← try
          discard <| environment.checkArgument markedSource markedOther
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "an equal unnamed parent replaced the explicitly marked occurrence"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw failure
        let relabelled ← context.close (← markValue marks second r)
        let .ok relabelledArgument := RuntimeArgument.ofValue graph 0 second (← marks.get)
          | throwError "the relabelled record is outside the graph"
        let failure : Option Exception ← try
          discard <| environment.checkArgument relabelled relabelledArgument
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "an occurrence mark bypassed the original source binder"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw failure
        let .ok _ ← transaction.commit | throwError "the selected projections could not commit"
  finally setEnv original

-- A nested native projection demands only its final selected field.
-- The intermediate record contains a different field whose real owner has exited.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
    let callableRole ← SourceLayout.ofTerm (← empty.close (mkConst ``Nat.succ))
    let innerTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
    let outerTerm ← mkAppM ``Prod.mk #[innerTerm, mkNatLit 7]
    let innerRole ← SourceLayout.ofTerm (← empty.close innerTerm)
    let outerRole ← SourceLayout.ofTerm (← empty.close outerTerm)
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    try
      discard <| SessionSnapshot.initialize owners
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let occurrence ← kernel.ledger.allocate
      let child ← owners.spawn { cmd := "/bin/cat" }
      try
        child.child.stdin.putStr "nested stored callable\n"
        child.child.stdin.flush
        let token := (← child.child.stdout.getLine).trimAscii.toString
        let scalar ← producer.stage
          { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
        let callable ← producer.stage
          { program, occurrence, role := callableRole, parameters := #[] } (.ownedExport child token #[])
        let inner ← producer.stage
          { program, occurrence, role := innerRole, parameters := #[] } (.product #[scalar, callable])
        let outer ← producer.stage
          { program, occurrence, role := outerRole, parameters := #[] } (.product #[inner, scalar])
        let identityTerm ← withLocalDeclD `n (mkConst ``Nat) fun n => mkLambdaFVars #[n] n
        let identityValue ← kernel.run producer empty {} identityTerm
        let .ok base ← producer.commit | throwError "the nested projection inputs could not commit"
        owners.close child.generation
        if ← owners.isLive child.generation then
          throwError "the nested projection control did not close its field owner"
        unless (← base.graph.isAvailable owners scalar) &&
            !(← base.graph.isAvailable owners inner) do
          throwError "the nested projection control lost its independent field and unavailable parent"
        withLetDecl `r (← inferType outerTerm) outerTerm fun r => do
          let id : BindingId := ⟨"nested-owner-projection", 0⟩
          let context ← ContextTelescope.capture #[{ id, role := .definition, expression := r }]
          let .ok parameter := RuntimeParameter.ofValue base.graph id outer
            | throwError "the nested source record is outside the graph"
          let environment ← RuntimeEnvironment.capture owners.worker context #[parameter]
          let .ok (some retained) := environment.lookup id
            | throwError "the nested source record lost its stable binding"
          let bound := ({} : Std.HashMap BindingId ValueBinding).insert id retained
          let innerSource ← mkProjection r `fst
          let consumer ← CellTransaction.begin kernel.ledger
          try
            let selected ← kernel.run consumer context bound (← mkProjection innerSource `fst)
            unless selected.value == scalar.value do
              throwError "nested source projection replaced its actual portable grandchild"
            let .ok _ ← consumer.commit
              | throwError "an unrelated nested field owner blocked the selected grandchild's publication"
          finally discard <| consumer.abort
          -- Asking for the whole intermediate record still demands its owned field.
          let whole ← CellTransaction.begin kernel.ledger
          let wholeFailure : Option Exception ← try
            discard <| kernel.run whole context bound innerSource
            pure none
          catch error => pure (some error)
          let some wholeFailure := wholeFailure
            | throwError "whole intermediate access ignored its dead owned field"
          unless (← wholeFailure.toMessageData.toString).endsWith "unavailable: stale_owner" do
            throw wholeFailure
          match ← whole.commit with
          | .error .settled => pure ()
          | _ => throwError "failed whole-record access retained a publishable transaction"
          -- The retained compiled callable forces actual argument preparation and admission;
          -- native beta reduction cannot remove this source application before lowering.
          withLetDecl `g (← inferType identityTerm) identityTerm fun g => do
            let callableId : BindingId := ⟨"nested-owner-projection", 1⟩
            let appliedContext ← ContextTelescope.capture #[
              { id, role := .definition, expression := r },
              { id := callableId, role := .definition, expression := g }]
            let supplied := bound.insert callableId identityValue
            let application ← CellTransaction.begin kernel.ledger
            try
              let returned ← kernel.run application appliedContext supplied
                (mkApp g (← mkProjection innerSource `fst))
              unless returned.value == scalar.value do
                throwError "a retained application replaced its actual nested scalar argument"
              let .ok _ ← application.commit
                | throwError "an unrelated field owner blocked nested argument publication"
            finally discard <| application.abort
          let failed ← CellTransaction.begin kernel.ledger
          let failure : Option Exception ← try
            discard <| kernel.run failed context bound (← mkProjection innerSource `snd)
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "nested source projection returned its dead owned grandchild"
          unless (← failure.toMessageData.toString).endsWith "unavailable: stale_owner" do
            throw failure
          match ← failed.commit with
          | .error .settled => pure ()
          | _ => throwError "failed nested source projection retained a publishable transaction"
      finally owners.close child.generation
    finally kernel.close
  finally setEnv original

-- A nested stored result retains the actual index on which its selected type depends.
-- The other inner field is independent of that index and remains available after its owner exits.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let scalarRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
    let zeroRole ← SourceLayout.ofTerm (← empty.close (mkNatLit 0))
    let family ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkLambdaFVars #[n] (← mkAppM ``Prod #[mkApp (mkConst ``Fin) n, mkConst ``Nat])
    let sigma := mkApp2 (mkConst ``Sigma [.zero, .zero]) (mkConst ``Nat) family
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    try
      discard <| SessionSnapshot.initialize owners
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let occurrence ← kernel.ledger.allocate
      let child ← owners.spawn { cmd := "/bin/cat" }
      try
        child.child.stdin.putStr "retained dependent index\n"
        child.child.stdin.flush
        let token := (← child.child.stdout.getLine).trimAscii.toString
        let index ← producer.stage
          { program, occurrence, role := scalarRole, parameters := #[] }
          (.ownedExport child token #[])
        let scalar ← producer.stage
          { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
        let zero ← producer.stage
          { program, occurrence, role := zeroRole, parameters := #[] } (.portable "0".toUTF8)
        withLocalDeclD `r sigma fun r => do
          let id : BindingId := ⟨"nested-dependent-owner", 0⟩
          let context ← ContextTelescope.capture #[{ id, role := .result, expression := r }]
          let innerSource ← mkProjection r `snd
          let pointSource ← mkProjection innerSource `fst
          let independentSource ← mkProjection innerSource `snd
          let outerRole ← SourceLayout.ofTerm (← context.close r)
          let innerRole ← SourceLayout.ofTerm (← context.close innerSource)
          let pointRole ← SourceLayout.ofTerm (← context.close pointSource)
          let mut draft ← producer.draft
          let finite ← RecordPrefix.begin owners.identities program occurrence
            (← RecordLayout.ofSource pointRole)
          let (next, finite, _) ← draft.bindField finite zero
          draft := next
          let .ok finitePayload := finite.finish
            | throwError "the nested dependent control lost its complete finite interface"
          let (next, point) ← draft.stage
            { program, occurrence, role := pointRole, parameters := #[none] } finitePayload
          draft := next
          let inner ← RecordPrefix.begin owners.identities program occurrence
            (← RecordLayout.ofSource innerRole)
          let (next, inner, _) ← draft.bindField inner point
          draft := next
          let (next, inner, _) ← draft.bindField inner scalar
          draft := next
          let .ok innerPayload := inner.finish
            | throwError "the nested dependent control lost its complete inner record"
          let (next, inner) ← draft.stage
            { program, occurrence, role := innerRole, parameters := #[none] } innerPayload
          draft := next
          let outer ← RecordPrefix.begin owners.identities program occurrence
            (← RecordLayout.ofSource outerRole)
          let (next, outer, _) ← draft.bindField outer index
          draft := next
          let (next, outer, dependentInner) ← draft.bindField outer inner
          draft := next
          unless dependentInner.instantiations.any (·.field.precedingDependencies.contains 0) do
            throwError "the native outer field lost its declared index dependency"
          let .ok outerPayload := outer.finish
            | throwError "the nested dependent control lost its complete outer record"
          let (finalDraft, outer) ← draft.stage
            { program, occurrence, role := outerRole, parameters := #[none] } outerPayload
          let .ok () ← producer.installDraft finalDraft
            | throwError "the nested dependent control could not install its complete records"
          let .ok base ← producer.commit
            | throwError "the nested dependent control could not publish its live inputs"
          -- The enriched descendant must also retain the same index during later native
          -- environment admission, even when another actual index has the same native value.
          let .ok liveParameter := RuntimeParameter.ofValue base.graph id outer
            | throwError "the live nested dependent record is outside its graph"
          let liveEnvironment ← RuntimeEnvironment.capture owners.worker context #[liveParameter]
          let .ok (some liveRoot) := liveEnvironment.lookup id
            | throwError "the live nested dependent record lost its source binding"
          let liveBound := ({} : Std.HashMap BindingId ValueBinding).insert id liveRoot
          let live ← CellTransaction.begin kernel.ledger
          let selectedPoint ← kernel.run live context liveBound pointSource
          let .ok liveSnapshot ← live.commit
            | throwError "the live dependent descendant could not commit"
          let .ok originalIndex := liveSnapshot.graph.project outer 0
            | throwError "the live dependent descendant lost its original index"
          -- An already staged computed source has no context alias for its outer index.
          -- Its exact composed projection must retain that outer prefix through Prod.fst.
          withLocalDeclD `computed (← mkArrow sigma sigma) fun function => do
            let computedContext ← ContextTelescope.capture #[
              { id, role := .result, expression := r },
              { id := ⟨id.session, 3⟩, role := .parameter, expression := function }]
            let computedSource := mkApp function r
            let computedInnerSource ← mkProjection computedSource `snd
            let computedPointSource ← mkProjection computedInnerSource `fst
            let computedRole ← SourceLayout.ofTerm (← computedContext.close computedSource)
            let computedInnerRole ← SourceLayout.ofTerm (← computedContext.close computedInnerSource)
            let computedPointRole ← SourceLayout.ofTerm (← computedContext.close computedPointSource)
            let originalParent := outer
            let cell ← CellTransaction.begin kernel.ledger
            try
              let occurrence ← kernel.ledger.allocate
              let mut draft ← cell.draft
              let finite ← RecordPrefix.begin owners.identities program occurrence
                (← RecordLayout.ofSource computedPointRole)
              let (next, finite, _) ← draft.bindField finite zero
              draft := next
              let .ok finitePayload := finite.finish
                | throwError "the computed source lost its finite field interface"
              let (next, computedPoint) ← draft.stage
                { program, occurrence, role := computedPointRole, parameters := #[none, none] }
                finitePayload
              draft := next
              let inner ← RecordPrefix.begin owners.identities program occurrence
                (← RecordLayout.ofSource computedInnerRole)
              let (next, inner, _) ← draft.bindField inner computedPoint
              draft := next
              let (next, inner, _) ← draft.bindField inner scalar
              draft := next
              let .ok innerPayload := inner.finish
                | throwError "the computed source lost its inner record"
              let (next, computedInner) ← draft.stage
                { program, occurrence, role := computedInnerRole, parameters := #[none, none] }
                innerPayload
              draft := next
              let outer ← RecordPrefix.begin owners.identities program occurrence
                (← RecordLayout.ofSource computedRole)
              let (next, outer, _) ← draft.bindField outer originalIndex
              draft := next
              let (next, outer, dependentComputedInner) ← draft.bindField outer computedInner
              draft := next
              let .ok outerPayload := outer.finish
                | throwError "the computed source lost its outer record"
              let (completedDraft, computedParent) ← draft.stage
                { program, occurrence, role := computedRole, parameters := #[none, none] }
                outerPayload
              let .ok () ← cell.installDraft completedDraft
                | throwError "the computed source fields could not be staged"
              let graph ← cell.view
              let .ok parameter := RuntimeParameter.ofValue graph id originalParent
                | throwError "the computed source lost its original context input"
              let environment ← RuntimeEnvironment.capture owners.worker computedContext #[parameter]
              let request ← PreparedRequest.forStoredProjection owners.identities program
                (← kernel.ledger.allocate) computedContext graph computedParent
                #[``Sigma.snd, ``Prod.fst] #[parameter]
              let executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
                fun _ _ => throwError "a stored computed-source projection dispatched an executor"
              let response ← Execute.run executor
                (PFunctor.FreeM.lift (P := OperationalSignature) request) cell
              unless response.root.value == computedPoint.value do
                throwError "the composed computed-source projection changed its exact field"
              let wrongParent ← cell.stage
                { program, occurrence, role := computedRole, parameters := #[none, none] }
                (.product #[scalar, dependentComputedInner])
              let some field := computedRole.fields.find? (·.projection == ``Sigma.snd)
                | throwError "the computed source lost its dependent field"
              let failure : Option Exception ← try
                discard <| environment.checkProjectionResult (← cell.view) (← field.toLayout)
                  dependentComputedInner wrongParent field
                pure none
              catch error => pure (some error)
              let some failure := failure
                | throwError "a computed source accepted another actual equal-valued prefix"
              unless (← failure.toMessageData.toString).startsWith
                  "the runtime value has a different consuming dependent reference" do throw failure
              -- A stored projection may itself be lazy. Its next native field request must
              -- retain the original computed parent rather than reconstruct its index.
              let lazyInner ← cell.stage
                { program, occurrence, role := computedInnerRole, parameters := #[none, none] }
                (.closure program #[])
              let lazyDraft ← cell.draft
              let lazyPrefix ← RecordPrefix.begin owners.identities program occurrence
                (← RecordLayout.ofSource computedRole)
              let (lazyDraft, lazyPrefix, _) ← lazyDraft.bindField lazyPrefix originalIndex
              let (lazyDraft, lazyPrefix, dependentLazyInner) ←
                lazyDraft.bindField lazyPrefix lazyInner
              let .ok lazyPayload := lazyPrefix.finish
                | throwError "the lazy computed source lost its complete parent"
              let (lazyDraft, lazyParent) ← lazyDraft.stage
                { program, occurrence, role := computedRole, parameters := #[none, none] }
                lazyPayload
              let .ok () ← cell.installDraft lazyDraft
                | throwError "the lazy computed source could not install its parent"
              let graph ← cell.view
              let lazyRequest ← PreparedRequest.forProjection owners.identities program
                (← kernel.ledger.allocate) computedContext graph lazyParent 1 #[parameter]
              let lazyResponse ← Execute.run executor
                (PFunctor.FreeM.lift (P := OperationalSignature) lazyRequest) cell
              let graph ← cell.view
              let admitted ← environment.checkOperand graph lazyRequest.source lazyResponse.root
              unless admitted.root.value == lazyInner.value &&
                  admitted.root.associationIds == lazyResponse.root.associationIds do
                throwError "operand admission changed the retained lazy projection"
              let graph : ValueGraph ← (show MetaM ValueGraph from do
                let nextRequest ← PreparedRequest.forProjection owners.identities program
                  (← kernel.ledger.allocate) computedContext graph lazyResponse.root 0 #[parameter]
                let .ok .producer ← cell.claim nextRequest.roles.scope
                  | throwError "the next lazy projection did not claim its occurrence"
                let nextDraft ← cell.draft
                let (nextDraft, nextValue) ← nextRequest.associateResult owners.identities
                  nextRequest.source nextDraft computedPoint
                let nextResponse ← nextRequest.admitResult nextDraft.view nextValue
                let .ok () ← cell.installDraft nextDraft
                  | throwError "the next lazy projection could not publish its checked field"
                let .ok completed ← cell.completeKernel nextRequest nextResponse
                  | throwError "the next lazy projection did not retain a completion"
                let graph ← cell.view
                let repeated ← nextRequest.admitResult graph completed.response.root
                unless repeated.root.value == computedPoint.value &&
                    repeated.root.associationIds == nextResponse.root.associationIds do
                  throwError "repeated admission changed the completed lazy projection"
                discard <| PreparedRequest.forProjection owners.identities program
                  (← kernel.ledger.allocate) computedContext graph repeated.root 0 #[parameter]
                return graph)
              -- A convertible computed source is not the original selected source.
              withLetDecl `otherFunction (← inferType function) function fun otherFunction => do
                let otherContext ← ContextTelescope.capture #[
                  { id, role := .result, expression := r },
                  { id := ⟨id.session, 3⟩, role := .parameter, expression := function },
                  { id := ⟨id.session, 4⟩, role := .definition, expression := otherFunction }]
                let otherInnerSource ← mkProjection (mkApp otherFunction r) `snd
                unless ← isDefEq (← inferType otherInnerSource) (← inferType computedInnerSource) do
                  throwError "the operand relabel control lost its convertible native type"
                let otherRole ← SourceLayout.ofTerm (← otherContext.close otherInnerSource)
                let .ok relabeled := lazyResponse.root.withRole otherRole
                  | throwError "the operand relabel control lost its computational role"
                let otherEnvironment ← RuntimeEnvironment.capture owners.worker otherContext #[parameter]
                let failure : Option Exception ← try
                  discard <| otherEnvironment.checkOperand graph otherRole relabeled
                  pure none
                catch error => pure (some error)
                let some failure := failure
                  | throwError "operand admission borrowed a prefix for another computed source"
                unless (← failure.toMessageData.toString).startsWith
                    "the runtime value has an unresolved consuming dependent reference" do throw failure
              -- A separately supplied alias names this exact parent; its native field may
              -- retain the selected lazy operand, but a wrong or missing prefix must fail.
              withLetDecl `aliasParent sigma computedSource fun aliasParent => do
                let aliasId : BindingId := ⟨id.session, 4⟩
                let aliasContext ← ContextTelescope.capture #[
                  { id, role := .result, expression := r },
                  { id := ⟨id.session, 3⟩, role := .parameter, expression := function },
                  { id := aliasId, role := .definition, expression := aliasParent }]
                let aliasInnerSource ← mkProjection aliasParent `snd
                let aliasRole ← SourceLayout.ofTerm (← aliasContext.close aliasInnerSource)
                let .ok aliasParameter := RuntimeParameter.ofValue graph aliasId lazyParent
                  | throwError "the exact operand alias is outside its graph"
                let aliasEnvironment ← RuntimeEnvironment.capture owners.worker aliasContext
                  #[parameter, aliasParameter]
                let aliased ← aliasEnvironment.checkOperand graph aliasRole lazyResponse.root
                unless aliased.root.value == lazyInner.value &&
                    aliased.root.associationIds == lazyResponse.root.associationIds do
                  throwError "the explicit operand alias changed its selected field"
                let .ok aliasOperand := lazyResponse.root.withRole aliasRole
                  | throwError "the explicit operand alias lost its source role"
                discard <| PreparedRequest.forProjection owners.identities program
                  (← kernel.ledger.allocate) aliasContext graph aliasOperand 0
                  #[parameter, aliasParameter]
                let wrongLazyParent ← cell.stage
                  { program, occurrence, role := computedRole, parameters := #[none, none] }
                  (.product #[scalar, dependentLazyInner])
                let graph ← cell.view
                let .ok wrongAlias := RuntimeParameter.ofValue graph aliasId wrongLazyParent
                  | throwError "the conflicting operand alias is outside its graph"
                let wrongEnvironment ← RuntimeEnvironment.capture owners.worker aliasContext
                  #[parameter, wrongAlias]
                let failure : Option Exception ← try
                  discard <| wrongEnvironment.checkOperand graph aliasRole aliasOperand
                  pure none
                catch error => pure (some error)
                let some failure := failure
                  | throwError "an operand alias accepted another actual equal-valued index"
                unless (← failure.toMessageData.toString).startsWith
                    "the runtime value has a different consuming dependent reference" do throw failure
                let missingEnvironment ← RuntimeEnvironment.capture owners.worker aliasContext #[parameter]
                let failure : Option Exception ← try
                  discard <| missingEnvironment.checkOperand graph aliasRole aliasOperand
                  pure none
                catch error => pure (some error)
                let some failure := failure
                  | throwError "an operand alias supplied its own missing parent"
                unless missingValueOf failure aliasId do throw failure
              let .ok _ ← cell.commit
                | throwError "the computed-source projection did not retain a complete receipt"
            finally discard <| cell.abort
          withLetDecl `n (mkConst ``Nat) (← mkProjection r `fst) fun n => do
            withLocalDeclD `point (mkApp (mkConst ``Fin) n) fun suppliedPoint => do
              let bindings : Array LocalBinding := #[
                { id, role := .result, expression := r },
                { id := ⟨id.session, 1⟩, role := .definition, expression := n },
                { id := ⟨id.session, 2⟩, role := .parameter, expression := suppliedPoint }]
              let consuming ← ContextTelescope.capture bindings
              let parameter (position : Nat) (value : ValueBinding) : MetaM RuntimeParameter := do
                let .ok parameter :=
                    RuntimeParameter.ofValue liveSnapshot.graph bindings[position]!.id value
                  | throwError "a nested consuming reference is outside the published graph"
                return parameter
              let root ← parameter 0 outer
              let point ← parameter 2 selectedPoint
              discard <| RuntimeEnvironment.capture owners.worker consuming
                #[root, ← parameter 1 originalIndex, point]
              let failure : Option Exception ← try
                discard <| RuntimeEnvironment.capture owners.worker consuming
                  #[root, ← parameter 1 scalar, point]
                pure none
              catch error => pure (some error)
              let some failure := failure
                | throwError "a different actual index satisfied a nested descendant's native type"
              unless (← failure.toMessageData.toString).startsWith
                  "the runtime value has a different consuming dependent reference" do throw failure
          owners.close child.generation
          unless !(← base.graph.isAvailable owners dependentInner) &&
              (← base.graph.isAvailable owners point) &&
              (← base.graph.isAvailable owners scalar) do
            throwError "the nested dependent control did not isolate its consuming index owner"
          let .ok parameter := RuntimeParameter.ofValue base.graph id outer
            | throwError "the nested dependent record is outside its published graph"
          let environment ← RuntimeEnvironment.capture owners.worker context #[parameter]
          let .ok (some retained) := environment.lookup id
            | throwError "the nested dependent record lost its original source binding"
          let bound := ({} : Std.HashMap BindingId ValueBinding).insert id retained
          let independent ← CellTransaction.begin kernel.ledger
          try
            let returned ← kernel.run independent context bound independentSource
            unless returned.value == scalar.value do
              throwError "nested independent access replaced its original portable value"
            let .ok _ ← independent.commit
              | throwError "an unrelated outer index owner blocked the independent nested result"
          finally discard <| independent.abort
          let dependent ← CellTransaction.begin kernel.ledger
          let failure : Option Exception ← try
            discard <| kernel.run dependent context bound pointSource
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "nested projection dropped its actual preceding-field owner dependency"
          unless (← failure.toMessageData.toString).endsWith "unavailable: stale_owner" do
            throw failure
          match ← dependent.commit with
          | .error .settled => pure ()
          | _ => throwError "failed dependent access retained a publishable transaction"
      finally owners.close child.generation
    finally kernel.close
  finally setEnv original

-- A published field access belongs to its complete parent association, even when
-- two consuming applications retain the same parent node and its same stored fields.
-- These native identity/projection requests do not execute a mathematical provider.
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let owners ← OwnerRegistry.new
    let program ← owners.identities.fresh .program
    let pairSource ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let pairRole ← SourceLayout.ofTerm (← context.close pairSource)
    let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let identitySource ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => p)) none
    let identityRole ← SourceLayout.ofTerm (← context.close identitySource)
    let (graph, scalar) ← (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence := ← owners.identities.fresh .occurrence,
        role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
    let (graph, originalParent) ← graph.stage owners.identities
      { program, occurrence := ← owners.identities.fresh .occurrence,
        role := pairRole, parameters := #[] } (.product #[scalar, scalar])
    let (graph, callable) ← graph.stage owners.identities
      { program, occurrence := ← owners.identities.fresh .occurrence,
        role := identityRole, parameters := #[] } (.closure program #[])
    let parentView (graph : ValueGraph) : MetaM (ValueGraph × ValueBinding) := do
      let .ok argument := RuntimeArgument.ofValue graph 0 originalParent
        | throwError "the exact-parent control lost its original input"
      let request ← PreparedRequest.forApplication owners.identities program
        (← owners.identities.fresh .occurrence) context callable
        #[← context.close pairSource] #[argument] #[]
      graph.bindApplication owners.identities request.origin originalParent #[scalar, scalar]
    let publish (graph : ValueGraph) (parent : ValueBinding) :
        MetaM (ValueGraph × ValueBinding) := do
      let request ← PreparedRequest.forProjection owners.identities program
        (← owners.identities.fresh .occurrence) context graph parent 0 #[]
      graph.bindProjection owners.identities (← request.originFor request.source) scalar #[]
    let environment ← RuntimeEnvironment.capture owners.worker context #[]
    let checkSource (graph : ValueGraph) (parent access : ValueBinding)
        (accepted : Bool) : MetaM Unit := do
      let marks ← IO.mkRef (#[] : Array ValueBinding)
      let markedParent ← markValue marks parent (← parent.role.source.inContext context)
      let specified ← context.close (← mkProjection markedParent `fst)
      let .ok argument := RuntimeArgument.ofValue graph 0 access (← marks.get)
        | throwError "the exact-parent access is outside its actual graph"
      let failure : Option Exception ← try
          discard <| environment.checkArgument specified argument
          pure none
        catch error => pure (some error)
      match accepted, failure with
      | true, none => pure ()
      | true, some error => throw error
      | false, none =>
        throwError "a projection access dropped a required parent association"
      | false, some error =>
        unless (← error.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw error
    let (graph, parentA) ← parentView graph
    let (graph, parentB) ← parentView graph
    unless originalParent.value == parentA.value && parentA.value == parentB.value &&
        parentA.associationIds.size == originalParent.associationIds.size + 1 &&
        parentB.associationIds.size == originalParent.associationIds.size + 1 &&
        parentA.associationIds != parentB.associationIds do
      throwError "the control did not retain distinct consuming parent associations"
    let .ok none := graph.projectedAccess? originalParent #[``Prod.fst]
      | throwError "stored data fabricated an unpublished projection access"
    -- A later parent's real access cannot manufacture an earlier parent's publication.
    do
      let (laterGraph, _) ← publish graph parentA
      let .ok none := laterGraph.projectedAccess? originalParent #[``Prod.fst]
        | throwError "a later parent access fabricated an earlier exact-parent publication"
      let .ok none := laterGraph.projectedAccess? parentB #[``Prod.fst]
        | throwError "a later parent access fabricated a sibling publication"
    let (graph, originalAccess) ← publish graph originalParent
    let .ok (some retainedOriginal) := graph.projectedAccess? originalParent #[``Prod.fst]
      | throwError "the original parent lost its published access"
    unless retainedOriginal.associationIds == originalAccess.associationIds do
      throwError "the original published access changed its consuming associations"
    for parent in #[parentA, parentB] do
      let .ok none := graph.projectedAccess? parent #[``Prod.fst]
        | throwError "an older baseline access authenticated a later parent association"
      checkSource graph parent retainedOriginal false
    let (graph, accessA) ← publish graph parentA
    let .ok (some retainedA) := graph.projectedAccess? parentA #[``Prod.fst]
      | throwError "the first associated parent lost its own published access"
    unless retainedA.associationIds == accessA.associationIds do
      throwError "the first associated parent reused another access"
    checkSource graph parentA retainedA true
    let .ok none := graph.projectedAccess? parentB #[``Prod.fst]
      | throwError "a sibling parent association authenticated an unpublished access"
    checkSource graph parentB retainedA false
    let (graph, accessB) ← publish graph parentB
    let .ok (some retainedB) := graph.projectedAccess? parentB #[``Prod.fst]
      | throwError "the second associated parent lost its own published access"
    unless retainedB.associationIds == accessB.associationIds do
      throwError "the second associated parent reused another access"
    checkSource graph parentB retainedB true
    checkSource graph parentA retainedB false
    let .ok aliasParent := parentA.withRole parentA.role
      | throwError "the exact-parent control could not retain an ordinary role alias"
    let .ok (some aliasAccess) := graph.projectedAccess? aliasParent #[``Prod.fst]
      | throwError "an ordinary role alias lost its exact published parent"
    unless aliasAccess.associationIds == accessA.associationIds do
      throwError "a role alias replaced its original published access"
    for (parent, access) in #[
        (originalParent, originalAccess), (parentA, accessA), (parentB, accessB)] do
      let .ok (some retained) := graph.projectedAccess? parent #[``Prod.fst]
        | throwError "a later publication hid an earlier exact-parent access"
      unless retained.value == scalar.value &&
          retained.associationIds == access.associationIds do
        throwError "an exact-parent query changed its selected access"
      let .ok (some (_, selectedParent, path)) := graph.projectionSelection retained
        | throwError "the published access lost its immutable source selection"
      unless selectedParent.value == parent.value &&
          selectedParent.associationIds == parent.associationIds &&
          path == #[``Prod.fst] do
        throwError "the published access changed its complete parent or native path"
      let .ok (some baseline) := graph.projected? parent #[``Prod.fst]
        | throwError "the exact-parent publication lost the original field baseline"
      let .ok stored := graph.project parent 0
        | throwError "the exact-parent publication lost its original stored field"
      unless baseline.value == scalar.value && stored.value == scalar.value &&
          baseline.associationIds == scalar.associationIds &&
          stored.associationIds == scalar.associationIds do
        throwError "an access publication replaced the original stored field baseline"
  finally setEnv originalEnvironment
