module

import CasRuntime.Materialize
import CasRuntime.Transport
import CasRuntime.Execute
public meta import Lean.Elab.Command
meta import CasRuntime.Materialize
meta import CasRuntime.Transport
meta import CasRuntime.Execute

open Lean Meta CasCompiler CasRuntime CasCatalogue.Backend

-- The public SDK echoes packets and exports a stored diagnostic callable; it computes no mathematics.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let contract ← liftM (m := IO) <| packageDir contractPackage
    let root ← liftM (m := IO) IO.currentDir
    let owners ← liftM (m := IO) OwnerRegistry.new
    let ledger ← liftM (m := BaseIO) (OccurrenceLedger.new owners)
    discard <| SessionSnapshot.initialize owners
    let .ok wire ← liftM (m := IO) <| FramedConnection.start owners "materialization-peer" {
        cmd := (contract / ".venv/bin/python").toString
        args := #[(root / "scripts/probes/protocol_v2_peer.py").toString]
        env := #[("PYTHONPATH", some (contract / "python").toString)] } 5000
      | throwError "the materialization control peer did not negotiate"
    try
      let context ← ContextTelescope.capture #[]
      let transaction ← CellTransaction.begin ledger
      let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
      let prepare (term : Expr) (occurrence : RuntimeId .occurrence) :
          MetaM PreparedRequest := do
        let type ← inferType term
        let identity ← context.close (mkConst ``id [← getLevel type])
        let layout ← SourceLayout.ofTerm identity
        let callable ← liftM (m := IO) <| transaction.stage
          { program, occurrence, role := layout, parameters := #[] } (.closure program #[])
        PreparedRequest.forApplication program occurrence context callable
          #[← context.close type, ← context.close term] #[] #[]
      let nativeOccurrence ← liftM (m := BaseIO) ledger.allocate
      let nativeRequest ← prepare (mkConst ``Nat.succ) nativeOccurrence
      let selected : DispatchIdentity := {
        manifestDigest := "materialization-manifest", profileDigest := "materialization-profile"
        registration := {
          operation := "stored", input := "materialization#input", backend := wire.backend } }
      let .ok reservation ← liftM (m := BaseIO) <|
        transaction.reserve nativeOccurrence selected wire.connection #[]
        | throwError "the native result control could not reserve"
      let before ← liftM (m := IO) transaction.view
      let scope ← liftM (m := IO) <| RequestScope.issue ledger reservation before #[] #[] #[]
      let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger transaction reservation scope
        (.str "retained diagnostic callable") 5000
        | throwError "the native result control did not return"
      let (draft, native) ← reply.materialize nativeRequest transaction scope wire.connection
      let some node := draft.view.find native.root.value
        | throwError "materialization lost the returned native node"
      let .ownedToken owner token captures := node.payload.data
        | throwError "materialization replaced the actual native export"
      unless owner == wire.connection.generation && captures.isEmpty &&
          reply.exports.any (·.token == token) do
        throwError "materialization changed the actual native owner, token or capture table"
      if ((← liftM (m := IO) transaction.view).find native.root.value).isSome then
        throwError "materialization installed a tentative native reply"
      let .ok () ← liftM (m := BaseIO) <| transaction.installDraft draft
        | throwError "the complete native draft could not enter the active graph"
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let pair ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
      let request ← prepare pair occurrence
      let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
      let scalar ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := scalarRole, parameters := #[] } (.portable "7".toUTF8)
      let selected := { selected with registration := { selected.registration with operation := "echo" } }
      let .ok reservation ← liftM (m := BaseIO) <|
        transaction.reserve occurrence selected wire.connection #[scalar, native.root]
        | throwError "the joint result control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let scope ← liftM (m := IO) <|
        RequestScope.issue ledger reservation graph #[scalar, native.root] #[] #[]
      let packet := Json.arr #[(ScopedReference.scope 0).encode, (ScopedReference.scope 1).encode]
      let .ok reply ← liftM (m := IO) <|
        wire.invokeBefore ledger transaction reservation scope packet 5000
        | throwError "the joint result control did not return"
      let (draft, response) ← reply.materialize request transaction scope wire.connection
      let .ok first := draft.view.project response.root 0
        | throwError "the materialized record lost its first actual field"
      let .ok second := draft.view.project response.root 1
        | throwError "the materialized record lost its actual callable"
      unless first.value == scalar.value && second.value == native.root.value &&
          second.instantiations.size == native.root.instantiations.size + 1 do
        throwError "joint materialization replaced a retained input or its consuming role"
      if ((← liftM (m := IO) transaction.view).find response.root.value).isSome then
        throwError "joint materialization exposed an uninstalled result"
      let some node := draft.view.find response.root.value
        | throwError "the materialized literal packet is absent"
      let .container stored := node.payload.data
        | throwError "joint materialization discarded the original packet structure"
      let .ok filled := stored.fill #[.str "scalar-slot", .str "callable-slot"]
        | throwError "the materialized packet lost its exact reference positions"
      unless filled == Json.arr #[.str "scalar-slot", .str "callable-slot"] do
        throwError "materialization changed its original packet layout"
      if ((← SessionSnapshot.current).graph.find response.root.value).isSome then
        throwError "materialization published a tentative reply"
      let aliasOccurrence ← liftM (m := BaseIO) ledger.allocate
      let aliasRequest ← prepare (mkNatLit 7) aliasOccurrence
      let .ok aliasReservation ← liftM (m := BaseIO) <|
        transaction.reserve aliasOccurrence selected wire.connection #[scalar]
        | throwError "the returned-reference control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let aliasScope ← liftM (m := IO) <|
        RequestScope.issue ledger aliasReservation graph #[scalar] #[] #[]
      let .ok aliasReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        aliasReservation aliasScope (ScopedReference.scope 0).encode 5000
        | throwError "the returned-reference control did not return"
      let retainAlias : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
        fun demand active => do
          let (aliasDraft, aliasValue) ←
            aliasReply.materialize demand active aliasScope wire.connection
          unless aliasValue.root.value == scalar.value && !aliasDraft.view.sameRevision graph do
            throwError "returning a reference changed its node or lost its new application revision"
          let .ok () ← liftM (m := BaseIO) <| active.installDraft aliasDraft
            | throwError "a complete reply containing only an existing reference could not install"
          match ← liftM (m := BaseIO) <| active.installDraft aliasDraft with
          | .error .staleDraft => pure ()
          | _ => throwError "a reference-only reply draft installed twice"
          return (aliasValue, active)
      let retained ← Execute.run retainAlias
        (PFunctor.FreeM.lift (P := OperationalSignature) aliasRequest) transaction
      unless retained.root.value == scalar.value &&
          (← retained.root.role.source.inContext context) ==
            (← aliasRequest.source.source.inContext context) do
        throwError "native execution changed the returned reference or its consuming source role"
      let badOccurrence ← liftM (m := BaseIO) ledger.allocate
      let badRequest ← prepare pair badOccurrence
      let boolRole ← SourceLayout.ofTerm (← context.close (mkConst ``Bool.true))
      let wrong ← liftM (m := IO) <| transaction.stage
        { program, occurrence := badOccurrence, role := boolRole, parameters := #[] }
        (.portable "true".toUTF8)
      let .ok badReservation ← liftM (m := BaseIO) <|
        transaction.reserve badOccurrence selected wire.connection #[wrong]
        | throwError "the joint rejection control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let badScope ← liftM (m := IO) <|
        RequestScope.issue ledger badReservation graph #[wrong] #[] #[]
      let .ok badReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        badReservation badScope (.arr #[toJson (7 : Nat), (ScopedReference.scope 0).encode]) 5000
        | throwError "the joint rejection control did not return"
      let failure : Option Exception ← try
        discard <| badReply.materialize badRequest transaction badScope wire.connection
        pure none
      catch error => pure (some error)
      let some failure := failure | throwError "joint materialization accepted a mistyped later field"
      unless (← failure.toMessageData.toString).startsWith
          "the runtime value has an incompatible complete source type" do throw failure
      unless (← liftM (m := IO) transaction.view).sameRevision graph do
        throwError "a rejected later field installed an earlier tentative reply prefix"
      let rational ← Elab.Term.elabTermAndSynthesize (← `(((1 : Rat) / 2))) none
      for packet in #[Json.arr #[toJson (-2 : Int), toJson (3 : Nat)],
          .arr #[toJson (1 : Int), toJson (0 : Nat)],
          .arr #[toJson (2 : Int), toJson (4 : Nat)]] do
        let occurrence ← liftM (m := BaseIO) ledger.allocate
        let request ← prepare rational occurrence
        let .ok reservation ← liftM (m := BaseIO) <|
          transaction.reserve occurrence selected wire.connection #[]
          | throwError "the scalar representation control could not reserve"
        let graph ← liftM (m := IO) transaction.view
        let scope ← liftM (m := IO) <|
          RequestScope.issue ledger reservation graph #[] #[] #[]
        let .ok reply ← liftM (m := IO) <|
          wire.invokeBefore ledger transaction reservation scope packet 5000
          | throwError "the scalar representation control did not return"
        if packet == Json.arr #[toJson (-2 : Int), toJson (3 : Nat)] then
          let (draft, result) ← reply.materialize request transaction scope wire.connection
          let .ok numerator := draft.view.project result.root 0
            | throwError "the scalar packet lost its actual numerator"
          let some node := draft.view.find numerator.value
            | throwError "the scalar numerator is absent from its draft"
          let .container stored := node.payload.data
            | throwError "the scalar numerator lost its original literal data"
          unless stored.template == toJson (-2 : Int) do
            throwError "scalar validation substituted the source answer for the actual returned data"
        else
          let failure : Option Exception ← try
            discard <| reply.materialize request transaction scope wire.connection
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "immediate materialization accepted a malformed scalar representation"
          unless (← failure.toMessageData.toString).startsWith
              "a scalar literal violates its declared representation constraint" do throw failure
        unless (← liftM (m := IO) transaction.view).sameRevision graph do
          throwError "scalar representation checking installed tentative data"
      let indexOccurrence ← liftM (m := BaseIO) ledger.allocate
      let indexRequest ← prepare (mkNatLit 7) indexOccurrence
      let stored := { selected with registration := { selected.registration with operation := "stored" } }
      let .ok indexReservation ← liftM (m := BaseIO) <|
        transaction.reserve indexOccurrence stored wire.connection #[]
        | throwError "the actual native index control could not reserve"
      let graph ← liftM (m := IO) transaction.view
      let indexScope ← liftM (m := IO) <|
        RequestScope.issue ledger indexReservation graph #[] #[] #[]
      let .ok indexReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        indexReservation indexScope (.str "native index ownership") 5000
        | throwError "the SDK did not supply the native index control"
      let (indexDraft, indexValue) ←
        indexReply.materialize indexRequest transaction indexScope wire.connection
      let .ok () ← liftM (m := BaseIO) <| transaction.installDraft indexDraft
        | throwError "the native index could not enter the active graph"
      let occurrence ← liftM (m := BaseIO) ledger.allocate
      let functionRole ← SourceLayout.ofTerm (← context.close (mkConst ``Fin.last))
      let function ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := functionRole, parameters := #[] } (.closure program #[])
      let graph ← liftM (m := IO) transaction.view
      let .ok actual := RuntimeArgument.ofValue graph 0 indexValue.root
        | throwError "the native index is outside its current graph"
      let request ← PreparedRequest.forApplication program occurrence context function
        #[← context.close (mkNatLit 7)] #[actual] #[]
      let .ok reservation ← liftM (m := BaseIO) <|
        transaction.reserve occurrence selected wire.connection request.scope
        | throwError "the dependent materialization control could not reserve"
      let scope ← liftM (m := IO) <|
        RequestScope.issue ledger reservation graph #[] #[] #[]
      let .ok reply ← liftM (m := IO) <| wire.invokeBefore ledger transaction reservation scope
        (toJson (0 : Nat)) 5000
        | throwError "the dependent scalar packet did not return"
      let (draft, point) ← reply.materialize request transaction scope wire.connection
      let .ok number := draft.view.project point.root 0
        | throwError "the dependent packet lost its numeric field"
      let some node := draft.view.find point.root.value
        | throwError "the dependent point is absent from its draft"
      let some application := node.origin.application
        | throwError "materialization discarded actual application provenance"
      unless application.dependencies == #[0] &&
          (application.arguments[0]?.bind id).map (·.value) == some indexValue.root.value do
        throwError "materialization changed the actual argument-index association"
      let .ok () ← liftM (m := BaseIO) <| transaction.installDraft draft
        | throwError "the numeric field could not enter the active graph"
      let plain ← liftM (m := IO) <| transaction.stage
        { program, occurrence, role := request.source, parameters := #[] } (.product #[number])
      let reuseOccurrence ← liftM (m := BaseIO) ledger.allocate
      let reuseRequest ← PreparedRequest.forApplication program reuseOccurrence context function
        #[← context.close (mkNatLit 7)] #[actual] #[]
      let graph ← liftM (m := IO) transaction.view
      let .ok baselineOwners := graph.requiredOwners #[plain]
        | throwError "the existing point is outside its graph"
      unless baselineOwners.isEmpty do
        throwError "the existing point acquired an unrelated index owner"
      let .ok reuseReservation ← liftM (m := BaseIO) <|
        transaction.reserve reuseOccurrence selected wire.connection (reuseRequest.scope.push plain)
        | throwError "the reused dependent result could not reserve"
      let reuseScope ← liftM (m := IO) <|
        RequestScope.issue ledger reuseReservation graph #[plain] #[] #[]
      let .ok reuseReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        reuseReservation reuseScope (ScopedReference.scope 0).encode 5000
        | throwError "the SDK did not return the existing dependent result"
      let (reusedDraft, reused) ←
        reuseReply.materialize reuseRequest transaction reuseScope wire.connection
      let .ok reuseOwners := reusedDraft.view.requiredOwners #[reused.root]
        | throwError "the reused result is outside its isolated graph"
      unless reused.root.value == plain.value && reuseOwners == #[wire.connection.generation] do
        throwError "a reused result lost its consuming application's actual index dependency"
      if (graph.requiredOwners #[reused.root]).isOk then
        throwError "an older graph recovered the new consuming application association"
      let some association := reused.root.applications.back?
        | throwError "the reused result lost its consuming application table"
      unless association.association.occurrence == reuseOccurrence &&
          association.association.program == program &&
          association.association.dependencies == #[0] &&
          (association.arguments[0]?.bind id).map (·.value) == some indexValue.root.value &&
          association.callable.map (·.value) == some function.value do
        throwError "a reused result changed its actual consuming application provenance"
      let some originalPoint := reusedDraft.view.find plain.value
        | throwError "the original point is absent from the extended graph"
      unless originalPoint.origin.occurrence == occurrence && originalPoint.origin.application.isNone do
        throwError "consuming application binding rewrote the original producer"
      let .ok reusedNumber := reusedDraft.view.project reused.root 0
        | throwError "the reused result lost its stored numeric projection"
      let .ok numericOwners := reusedDraft.view.requiredOwners #[reusedNumber]
        | throwError "the reused numeric projection is outside the extended graph"
      unless reusedNumber.value == number.value && numericOwners.isEmpty &&
          number.associationIds.toList.isPrefixOf reusedNumber.associationIds.toList &&
          reusedNumber.instantiations.size == number.instantiations.size + 1 do
        throwError "a reused field changed its node, earlier roles or independent owner requirements"
      if (graph.requiredOwners #[reusedNumber]).isOk then
        throwError "an older graph recovered a later consuming application field view"
      let .ok () ← liftM (m := BaseIO) <| transaction.installDraft reusedDraft
        | throwError "the reused application draft could not install"
      let chainedOccurrence ← liftM (m := BaseIO) ledger.allocate
      let chainedRequest ← PreparedRequest.forApplication program chainedOccurrence context function
        #[← context.close (mkNatLit 7)] #[actual] #[]
      let chainedGraph ← liftM (m := IO) transaction.view
      let .ok chainedReservation ← liftM (m := BaseIO) <| transaction.reserve chainedOccurrence
        selected wire.connection (chainedRequest.scope.push reused.root)
        | throwError "the successive application could not reserve"
      let chainedScope ← liftM (m := IO) <| RequestScope.issue ledger chainedReservation
        chainedGraph #[reused.root] #[] #[]
      let .ok chainedReply ← liftM (m := IO) <| wire.invokeBefore ledger transaction
        chainedReservation chainedScope (ScopedReference.scope 0).encode 5000
        | throwError "the SDK did not return the successively reused point"
      let (chainedDraft, chained) ← chainedReply.materialize chainedRequest transaction
        chainedScope wire.connection
      unless chained.root.value == plain.value &&
          chained.root.applications.size == reused.root.applications.size + 1 &&
          reused.root.associationIds.toList.isPrefixOf chained.root.associationIds.toList do
        throwError "successive reuse discarded an earlier application association"
      let pointType ← inferType (← reuseRequest.source.source.inContext context)
      withLocalDeclD `retainedPoint pointType fun pointName => do
        let binding : LocalBinding := {
          id := ⟨"retained-point", 0⟩, role := .parameter, expression := pointName }
        let pointContext ← ContextTelescope.capture #[binding]
        let .ok parameter := RuntimeParameter.ofValue chainedDraft.view binding.id reused.root
          | throwError "the earlier consuming result is absent from the extended graph"
        let environment ← RuntimeEnvironment.capture owners.worker pointContext #[parameter]
        let .ok argument := RuntimeArgument.ofValue chainedDraft.view 0 chained.root
          | throwError "the successively reused result is absent from its graph"
        let retained ← environment.checkArgument (← pointContext.close pointName) argument
        unless retained.associationIds == chained.root.associationIds do
          throwError "source argument capture lost successive application associations"
        let .ok originalArgument := RuntimeArgument.ofValue chainedDraft.view 0 plain
          | throwError "the original point is absent from the extended graph"
        let failure : Option Exception ← try
          discard <| environment.checkArgument (← pointContext.close pointName) originalArgument
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "source argument checking erased the retained consuming application identity"
        unless (← failure.toMessageData.toString).startsWith
            "the runtime argument does not retain its specified source value" do throw failure
      liftM (m := IO) wire.close
      if ← liftM (m := BaseIO) (draft.view.isAvailable owners point.root) then
        throwError "a materialized dependent point survived its actual index owner"
      unless ← liftM (m := BaseIO) (draft.view.isAvailable owners number) do
        throwError "a materialized numeric field retained its unrelated index owner"
      if ← liftM (m := BaseIO) (reusedDraft.view.isAvailable owners reused.root) then
        throwError "a reused dependent result survived its consuming index owner"
      unless ← liftM (m := BaseIO) (graph.isAvailable owners plain) do
        throwError "a consuming application changed its original result's owner requirements"
      unless ← liftM (m := BaseIO) (reusedDraft.view.isAvailable owners reusedNumber) do
        throwError "the reused numeric field acquired its parent application's unrelated owner"
      discard <| liftM (m := BaseIO) transaction.abort
    finally liftM (m := IO) wire.close
  finally setEnv original
