module

import CasRuntime.Materialize
import CasRuntime.Point
import LeanCategories.Catalogue.Semantics.Foundation.Objects
public meta import Lean.Elab.Command
meta import CasRuntime.Materialize
meta import CasRuntime.Point
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects

namespace CasRuntime.MaterializeCodecTests

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

-- The ordinary scope parser and native materializer consume exact complete packets.
-- The supplying process returns only a diagnostic handle; no mathematical implementation
-- or graph evaluator participates in these representation and ownership controls.
run_cmd Lean.Elab.Command.liftTermElabM do
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners none none 5000
  discard <| SessionSnapshot.initialize owners
  let transaction ← CellTransaction.begin kernel.ledger
  let supplier ← owners.spawn { cmd := "/bin/cat" }
  let retainedOwner ← IO.mkRef (none : Option (ValueGraph × ValueBinding))
  try
    supplier.child.stdin.putStr "original-map-handle\n"
    supplier.child.stdin.flush
    let token := (← supplier.child.stdout.getLine).trimAscii.toString
    let program ← owners.identities.fresh .program
    let context ← ContextTelescope.capture #[]
    let native := mkApp (mkConst ``Fin) (mkNatLit 2)
    let endpointRole ← SourceLayout.ofTerm (← context.close native)
    let node := fun (tag : String) (args : Array Json) =>
      Json.mkObj [("ctor", toJson tag), ("args", .arr args)]
    let endpoint := node "finiteData"
      #[node "original-object-data" #[], .arr #[toJson (0 : Nat), toJson (1 : Nat)]]
    let produced ← kernel.ledger.allocate
    let origin : ValueOrigin := { program, occurrence := produced, role := endpointRole, parameters := #[] }
    let source ← transaction.stage origin (.portable endpoint.compress.toUTF8)
    let target ← transaction.stage origin (.portable endpoint.compress.toUTF8)
    let equalOther ← transaction.stage origin (.portable endpoint.compress.toUTF8)
    let points := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (1 : Nat)],
      Json.arr #[toJson (1 : Nat), toJson (0 : Nat)]]
    let identityPoints := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (0 : Nat)],
      Json.arr #[toJson (1 : Nat), toJson (1 : Nat)]]
    let scopeRef := fun index => (ScopedReference.scope index).encode
    let typedMap := fun left right callable => node "typedMap" #[left, right, callable]
    let makeRequest (actualTarget : ValueBinding) (plainFunction : Bool := false) :
        MetaM PreparedRequest := do
      let sourceType ← markValue kernel.marks source native
      let targetType ← markValue kernel.marks actualTarget native
      let function := mkLambda `point .default sourceType (.bvar 0)
      let arrow ← if plainFunction then
          pure (mkLambda `point .default sourceType (mkNatLit 0))
        else mkAppOptM ``TypeCat.ofHom #[some sourceType, some targetType, some function]
      check arrow
      let functionRole ← SourceLayout.ofTerm (← context.close
        (mkLambda `ignored .default (mkConst ``Nat) arrow))
      let scalarRole ← SourceLayout.ofTerm (← context.close (mkNatLit 0))
      let occurrence ← kernel.ledger.allocate
      let sourceMarks := (← kernel.marks.get).mapIdx fun index value => (index, value)
      let dummy ← transaction.stage
        { program, occurrence, role := scalarRole, parameters := #[] } (.portable "0".toUTF8)
      let function ← transaction.stage
        { program, occurrence, role := functionRole, parameters := #[], sourceMarks }
        (.closure program #[source, actualTarget])
      let graph ← transaction.view
      let .ok argument := RuntimeArgument.ofValue graph 0 dummy (← kernel.marks.get)
        | throwError "the materializer control lost its original source argument"
      PreparedRequest.forApplication owners.identities program occurrence context function
        #[scalarRole.source] #[argument] #[] (some graph) sourceMarks
    let runCase (label : String) (packet : Json) (valid : Bool)
        (owned : Bool := false) (identityTarget : Bool := false)
        (symbolicExpected : Option Bool := none)
        (scopedCallable : Bool := false) : MetaM Unit := do
      let actualTarget := if identityTarget then source else target
      let request ← makeRequest actualTarget
      let bundle ← nativeCategoryFamily (← semanticState) (.atom CategoryId.sets) (fun _ => pure .zero)
      let carrier ← NativePointPath.prepare request.source (.atom CategoryId.sets) (← context.close bundle)
      let originalCallable ← if scopedCallable then do
          let mut native := request.source
          for projection in carrier.path do
            let some field := native.fields.find? (·.projection == projection)
              | throwError "the retained-callable control lost its original native field"
            native ← field.toLayout
          let occurrence ← kernel.ledger.allocate
          let origin ← request.environment.origin program occurrence native
          let binding ← transaction.stage origin (.ownedExport supplier token #[source])
          pure (some binding)
        else pure none
      let graph ← transaction.view
      let symbolicReached ← IO.mkRef false
      let check : PreparedSymbolicCheck := fun graph nodes => do
        symbolicReached.set true
        preparedSymbolicCheck kernel request transaction graph nodes
      let codec ← PreparedResultCodec.forMap request graph source actualTarget (← kernel.marks.get)
        none (some carrier) none #[] (some check)
      let selected : DispatchIdentity := {
        manifestDigest := "materialize-codec", profileDigest := "materialize-codec",
        registration := { operation := "materialize-codec", input := "materialize-codec", backend := "cat" } }
      let values := match originalCallable with
        | none => #[source, actualTarget, equalOther]
        | some callable => #[source, actualTarget, equalOther, callable]
      let .ok reservation ← transaction.reserve request.occurrence selected supplier (request.scope ++ values)
        | throwError "the complete materializer control could not reserve"
      let scope ← RequestScope.issue kernel.ledger reservation graph values #[] #[]
      try
        let exports := if owned then #[Json.mkObj [("token", toJson token),
          ("captures", .arr #[scopeRef 0])]] else #[]
        let frame := Json.mkObj [
          ("request_id", toJson (57 : Nat)), ("status", "ok"), ("value", packet), ("exports", .arr exports)]
        let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 57 frame
        let original ← IO.ofExcept <| (reply.packetDescriptor graph supplier #[]).mapError IO.userError
        let result : Except Exception (CellDraft × PreparedResponse request) ← try
            pure (.ok (← reply.materialize request transaction scope supplier none (some codec)))
          catch failure => pure (.error failure)
        if let some expected := symbolicExpected then
          unless (← symbolicReached.get) == expected do
            throwError "materializer control {label} crossed the wrong symbolic endpoint boundary"
        match result with
        | .error failure =>
          if valid then throwError "complete materializer control {label}: {← failure.toMessageData.toString}"
          let message ← failure.toMessageData.toString
          unless ["endpoint", "inventory", "domain", "codomain", "total"].any
              (fun expected => (message.splitOn expected).length > 1) do
            throwError "materializer control {label} failed outside its endpoint/framing gate: {message}"
        | .ok (draft, response) =>
          unless valid do throwError "malformed materializer control {label} was admitted"
          if ((← transaction.view).find response.root.value).isSome then
            throwError "materialization installed an isolated result before whole completion"
          let some root := draft.view.find response.root.value
            | throwError "the complete map disappeared from its isolated draft"
          let .container stored := root.payload.data
            | throwError "the native map lost its complete original packet"
          unless stored.retainsOriginalPacket original do
            throwError "native field enrichment changed the admitted whole map packet"
          let some (callable, remaining) ← IO.ofExcept <|
              (draft.view.projectionFrontier response.root carrier.path).mapError IO.userError
            | throwError "the complete native map lost its original carrier field"
          unless remaining.isEmpty && callable.role.kind == .function do
            throwError "native field enrichment omitted a complete original carrier"
          if let some original := originalCallable then
            let retained ← IO.ofExcept <| (draft.view.callable callable).mapError IO.userError
            unless retained.value == original.value &&
                original.associationIds.toList.isPrefixOf retained.associationIds.toList do
              throwError "the map replaced its original scoped native callable"
          if label == "finite" then
            let encoded ← IO.ofExcept <| (draft.view.encodeInputs supplier.generation
              #[{ path := #[], binding := response.root }]).mapError IO.userError
            unless encoded.values == #[node "valueData" #[typedMap endpoint endpoint points]] do
              throwError "native field storage dropped a typedMap endpoint or changed its callable"
          if owned || scopedCallable then
            let owners ← IO.ofExcept <| (draft.view.requiredOwners #[response.root]).mapError IO.userError
            unless owners.contains supplier.generation do
              throwError "the complete map lost its actual callable owner"
            retainedOwner.set (some (draft.view, response.root))
      finally
        scope.retire
        discard <| kernel.ledger.retire reservation
    -- A plain function has the authenticated finite source but a closed scalar codomain
    -- with no runtime object supplier. Its domain still constrains every finite graph.
    -- Complete passive data re-encodes for the next declared consumer and receives no
    -- graph evaluator or fabricated direct continuation. Owned data keeps the old export.
    let runNativeCase (packet : Json) (valid : Bool) (owned : Bool := false) : MetaM Unit := do
      let request ← makeRequest target true
      unless request.source.kind == .function do
        throwError "the native control lost its ordinary function result"
      let graph ← transaction.view
      let codec ← PreparedResultCodec.forNative request (preparedSymbolicCheck kernel request transaction)
      let selected : DispatchIdentity := {
        manifestDigest := "native-codec", profileDigest := "native-codec",
        registration := { operation := "native-codec", input := "native-codec", backend := "cat" } }
      let values := #[source, target, equalOther]
      let .ok reservation ← transaction.reserve request.occurrence selected supplier (request.scope ++ values)
        | throwError "the native function control could not reserve"
      let scope ← RequestScope.issue kernel.ledger reservation graph values #[] #[]
      try
        let exports := if owned then #[Json.mkObj [("token", toJson token),
          ("captures", .arr #[scopeRef 0])]] else #[]
        let frame := Json.mkObj [("request_id", toJson (58 : Nat)), ("status", "ok"),
          ("value", packet), ("exports", .arr exports)]
        let reply ← ImmediateReply.parseControl scope reservation graph scope.wireId 58 frame
        let result : Except Exception (CellDraft × PreparedResponse request) ← try
            pure (.ok (← reply.materialize request transaction scope supplier none (some codec)))
          catch failure => pure (.error failure)
        match result with
        | .error failure =>
          if valid then throw failure
          let message ← failure.toMessageData.toString
          unless (message.splitOn "inventory").length > 1 ||
              (message.splitOn "domain").length > 1 do
            throwError "the native inventory control failed outside framing: {message}"
        | .ok (draft, response) =>
          unless valid do
            throwError "an absent scalar codomain discarded the function's fixed source inventory"
          let some result := draft.view.find response.root.value
            | throwError "the native function lost its complete original result"
          if owned then
            let .ownedToken owner actual captures := result.payload.data
              | throwError "the native codec replaced the actual callable export"
            unless owner == supplier.generation && actual == token &&
                captures.map (·.value) == #[source.value] do
              throwError "the native codec changed the callable's owner or original captures"
          else
            let .container stored := result.payload.data
              | throwError "the passive native callable lost its complete original packet"
            unless stored.callableData && stored.callable.isNone do
              throwError "passive finite data acquired an invented computation"
            let actual ← IO.ofExcept <| (draft.view.callable response.root).mapError IO.userError
            unless actual.value == response.root.value do
              throwError "the passive native callable was replaced by another implementation"
          let encoded ← IO.ofExcept <| (draft.view.encodeInputs supplier.generation
            #[{ path := #[.field "argument"], binding := response.root }]).mapError IO.userError
          unless encoded.values == #[packet] do
            throwError "the later declared consumer lost the actual native callable packet"
          if ((← transaction.view).find response.root.value).isSome then
            throwError "the native codec published an isolated intermediate result"
      finally
        scope.retire
        discard <| kernel.ledger.retire reservation
    runCase "finite" (node "valueData" #[typedMap (scopeRef 0) (scopeRef 1) points]) true
    runCase "wrong equal endpoint" (typedMap (scopeRef 2) (scopeRef 1) points) false
    runCase "incomplete" (typedMap (scopeRef 0) (scopeRef 1)
      (.arr #[.arr #[toJson (0 : Nat), toJson (1 : Nat)]])) false
    runCase "short inventory" (typedMap (scopeRef 0) (scopeRef 1)
      (node "finiteGraph" #[.arr #[toJson (0 : Nat)],
        .arr #[.arr #[toJson (0 : Nat), toJson (1 : Nat)]]])) false
    runCase "identity" (typedMap (scopeRef 0) (scopeRef 1)
      (node "identity" #[scopeRef 0, scopeRef 1])) true false true
    runCase "wrong identity occurrence" (typedMap (scopeRef 0) (scopeRef 1)
      (node "identity" #[scopeRef 0, scopeRef 1])) false
    let composite := node "compose"
      #[points, typedMap (scopeRef 0) (scopeRef 1) identityPoints]
    runCase "complete composition" (typedMap (scopeRef 0) (scopeRef 1) composite) true
    let wrongMiddle : Json := .arr #[.arr #[toJson (0 : Nat), toJson (2 : Nat)],
      .arr #[toJson (1 : Nat), toJson (0 : Nat)]]
    runCase "late middle inventory" (typedMap (scopeRef 0) (scopeRef 1)
      (node "compose" #[wrongMiddle, typedMap (scopeRef 0) (scopeRef 1) identityPoints])) false
    let opaqueCallable := (ComputationalValue.opaque token).encode
    -- Repeated original references share an endpoint; equal opaque bytes at two fresh
    -- reply positions do not. The negative must stop before the native symbolic checker.
    runCase "shared retained middle" (typedMap (scopeRef 0) (scopeRef 1)
      (node "compose" #[
        typedMap (scopeRef 0) (scopeRef 0) opaqueCallable,
        typedMap (scopeRef 0) (scopeRef 1) opaqueCallable])) true true false (some true)
    runCase "distinct opaque middle occurrences" (typedMap (scopeRef 0) (scopeRef 1)
      (node "compose" #[
        typedMap (scopeRef 0) opaqueCallable opaqueCallable,
        typedMap opaqueCallable (scopeRef 1) opaqueCallable])) false true false (some false)
    runNativeCase points true
    runNativeCase (node "finiteGraph" #[.arr #[toJson (0 : Nat)],
      .arr #[.arr #[toJson (0 : Nat), toJson (1 : Nat)]]]) false
    runNativeCase (ComputationalValue.opaque token).encode true true
    runCase "owned callable" (typedMap (scopeRef 0) (scopeRef 1)
      (ComputationalValue.opaque token).encode) true true
    runCase "retained native callable" (typedMap (scopeRef 0) (scopeRef 1)
      (scopeRef 3)) true false false none true
    let some (graph, result) ← retainedOwner.get
      | throwError "the owned map control did not retain its actual complete result"
    owners.close supplier.generation
    if ← graph.isAvailable owners result then
      throwError "the retained map outlived its actual supplying callable owner"
  finally
    owners.close supplier.generation
    discard <| transaction.abort
    kernel.close

end CasRuntime.MaterializeCodecTests
