module

import CasRuntime.Execute
import CasContract.Port
public meta import Lean.Elab.Command
meta import CasRuntime.Execute
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
    let request ← PreparedRequest.forApplication program occurrence context callable
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
      let left ← PreparedRequest.forProjection program first context graph record 0 #[]
      let again ← PreparedRequest.forProjection program second context graph record 0 #[]
      let packetOccurrence ← liftM (m := BaseIO) ledger.allocate
      let packetProjection ←
        PreparedRequest.forProjection program packetOccurrence context graph packetRecord 0 #[]
      let associatedOccurrence ← liftM (m := BaseIO) ledger.allocate
      let associatedProjection ←
        PreparedRequest.forProjection program associatedOccurrence context graph associated 0 #[]
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
      let .ok published ← consumer.commit
        | throwError "a dead unrelated field blocked the portable projection"
      unless published.outputBatches.size == 2 do
        throwError "the successful projection cell was not committed"
      let failed ← CellTransaction.begin ledger
      let third ← liftM (m := BaseIO) ledger.allocate
      let right ← PreparedRequest.forProjection program third context graph associated 1 #[]
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
      let request ← PreparedRequest.forApplication program invocation context callable
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
    let request ← PreparedRequest.forApplication program invocation context callable
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
      mkLambdaFVars #[n] (← mkAppM ``Prod.mk #[n, n])
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
    let request ← PreparedRequest.forApplication program occurrence context retained
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
    let other ← PreparedRequest.forApplication program next context retained
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
    let nestedValid ← liftM (m := IO) <| transaction.stage
      { program, occurrence, role := nestedRole, parameters := #[] } (.product #[valid, valid])
    let nestedOccurrence ← liftM (m := BaseIO) ledger.allocate
    let nestedTelescope ← RoleTelescope.ofRequest program nestedOccurrence context none nestedRole #[]
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
