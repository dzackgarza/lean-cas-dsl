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
        let acceptedRequest ← PreparedRequest.forApplication owners.identities program
          (← ledger.allocate) context callable #[argument] #[accepted] parameters
        let path := Json.arr #[CasTools.NativeExpression.nameJson ``Prod.fst]
        let origin := (firstRequest.observation.native.getObjValD "request").getObjValD "origin"
        unless origin.getObjValD "accessPath" == path do
          throwError "the projection observation lost its exact native access path"
        let document := acceptedRequest.observation.native.getObjValD "request"
        let .ok scope := document.getObjValAs? (Array Json) "scope"
          | throwError "the application observation lost its actual input scope"
        let some observedArgument := scope[1]?
          | throwError "the application observation lost its actual projected operand"
        let .ok accesses := observedArgument.getObjValAs? (Array Json) "projections"
          | throwError "the actual operand observation lost its selected parent and path"
        let some access := accesses[0]?
          | throwError "the actual operand observation has no selected projection"
        let expectedParent := Json.mkObj [("worker", toJson first.value.worker),
          ("serial", toJson first.value.serial)]
        unless accesses.size == 1 && access.getObjValD "path" == path &&
            (access.getObjValD "parent").getObjValD "value" == expectedParent do
          throwError "the actual operand observation changed its retained parent or native path"
        let marks ← IO.mkRef (#[] : Array ValueBinding)
        discard <| markValue marks right s
        let markedParent ← markValue marks left r
        let markedSource ← context.close (← mkProjection markedParent `fst)
        let .ok markedArgument := RuntimeArgument.ofValue graph 0 actual.root (← marks.get)
          | throwError "the marked projection is outside the graph"
        let markedRequest ← PreparedRequest.forApplication owners.identities program
          (← ledger.allocate) context callable #[markedSource] #[markedArgument] parameters
        discard <| markedRequest.admitInputs graph
        let markedDocument := markedRequest.observation.native.getObjValD "request"
        let .ok observedArguments := markedDocument.getObjValAs? (Array Json) "actualArguments"
          | throwError "the native observation lost its indexed actual arguments"
        let some observedArgument := observedArguments[0]?
          | throwError "the native observation lost its marked actual argument"
        let expectedArgument := Json.mkObj [
          ("value", Observation.identityJson actual.root.value),
          ("associations", toJson (actual.root.associationIds.map Observation.identityJson))]
        let expectedMark := Json.mkObj [("key", toJson (1 : Nat)),
          ("reference", Json.mkObj [("value", expectedParent),
            ("associations", toJson (left.associationIds.map Observation.identityJson))])]
        unless observedArguments.size == 1 &&
            observedArgument.getObjValD "sourceIndex" == toJson (0 : Nat) &&
            observedArgument.getObjValD "reference" == expectedArgument &&
            observedArgument.getObjValD "marks" == Json.arr #[expectedMark] do
          throwError "argument observation changed its source mark or exposed an unrelated mark"
        let failure : Option Exception ← try
          discard <| PreparedRequest.forApplication owners.identities program
            (← ledger.allocate) context callable #[argument] #[rejected] parameters
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "an equal field from a different record satisfied the selected projection"
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
            let selected ← kernel.run consumer context bound (← mkProjection innerSource `fst) none
            unless selected.value == scalar.value do
              throwError "nested source projection replaced its actual portable grandchild"
            let .ok _ ← consumer.commit
              | throwError "an unrelated nested field owner blocked the selected grandchild's publication"
          finally discard <| consumer.abort
          let failed ← CellTransaction.begin kernel.ledger
          let failure : Option Exception ← try
            discard <| kernel.run failed context bound (← mkProjection innerSource `snd) none
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
