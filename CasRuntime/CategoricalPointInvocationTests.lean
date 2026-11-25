module

import CasRuntime.Kernel
import CasRuntime.Point
import CasCompiler.CategoricalPointSource
import CasCompiler.SourcePointOrigin
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.ConstructorRegistration
import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.Point
meta import CasCompiler.CategoricalPointSource
meta import CasCompiler.SourcePointOrigin
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.ConstructorRegistration
meta import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteSums
meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialPresentations
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials

namespace CasRuntime.CategoricalPointInvocationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def withPeer (family : CategoricalPointFamily) (configuration : List (String × Json))
    (action : Kernel → TermElabM Unit) (available : Bool := true) : TermElabM Unit := do
  let contract ← IO.FS.realPath (← packageDir contractPackage)
  let root ← IO.currentDir
  let log := root / ".tmp/categorical-point-native-observations.jsonl"
  IO.FS.createDirAll (root / ".tmp")
  IO.FS.writeFile log ""
  let config := Json.mkObj (("operation", toJson family.operation) ::
    ("log", toJson log.toString) :: configuration)
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "categorical-packet-peer"),
      ("command", toJson (contract / ".venv/bin/python").toString),
      ("args", .arr #[toJson (root / "scripts/probes/categorical_point_peer.py").toString,
        toJson config.compress])]]),
    ("registrations", .arr (if available then #[Json.mkObj [
      ("operation", toJson family.operation), ("input", toJson family.owner.input),
      ("backend", "categorical-packet-peer")]] else #[]))]
  IO.FS.createDirAll (root / ".tmp")
  let path := root / ".tmp/categorical-point-native-consumer.json"
  IO.FS.writeFile path manifest.compress
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners (some path) none 5000
  discard <| SessionSnapshot.initialize owners
  try
    unless kernel.rejected.isEmpty do
      throwError "the original categorical operation lost its native registration"
    action kernel
  finally kernel.close

private def stageOriginal (kernel : Kernel) (transaction : CellTransaction)
    (context : OpenContext) (source : Expr) (payload : ValuePayload) :
    MetaM ValueBinding := do
  transaction.stage {
    program := ← kernel.ledger.owners.identities.fresh .program
    occurrence := ← kernel.ledger.allocate
    role := ← SourceLayout.ofTerm (← context.close source)
    parameters := Array.replicate context.bindings.size none
    sourceMarks := (← kernel.marks.get).mapIdx fun index value => (index, value) } payload

-- The original List(Fin 0) object carries the independently supplied inventory [[]].
-- The peer returns that complete graph once and requires the actual unchanged
-- typedMap on later application. It never computes the list operation.
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let #[entry] := (← semanticState).cells.filter (·.id == NaturalTransformationId.listReverse)
      | throwError "the original list-reversal cell is absent"
    let family ← CategoricalPointFamily.forOwner (.component entry #[] false)
    withPeer family [("mode", "inline"), ("point", .arr #[])] fun kernel => do
      let context ← ContextTelescope.capture #[]
      let transaction ← CellTransaction.begin kernel.ledger
      try
        let receiverSource ← sourceNamedObjectAlias CategoryId.sets
          (mkApp (mkConst ``Fin) (mkNatLit 0))
        let receiverPacket := Json.mkObj [("ctor", "finiteData"),
          ("args", .arr #[Json.mkObj [("ctor", "obj.sets.fin"), ("args", .arr #[toJson (0 : Nat)])],
            .arr #[]])]
        let receiver ← stageOriginal kernel transaction context receiverSource
          (.portable receiverPacket.compress.toUTF8)
        let selectedReceiver ← markValue kernel.marks receiver receiverSource
        let levels := family.universeParams.map (fun _ => Level.zero)
        let parameters := #[selectedReceiver]
        let (arrowSource, bundle) ← family.arrowAt levels parameters
        let (source, target) ← categoricalPointEndpoints arrowSource
        unless ← isDefEq source target do
          throwError "the original list reversal changed its native endpoints"
        let endpointPacket := Json.mkObj [("ctor", "finiteData"),
          ("args", .arr #[Json.mkObj [("ctor", "fun.sets.list"), ("args", .arr #[]),
            ("receiver", receiverPacket)], .arr #[.arr #[]]])]
        let endpoint ← stageOriginal kernel transaction context source
          (.portable endpointPacket.compress.toUTF8)
        let selectedEndpoint ← markValue kernel.marks endpoint source
        let reference ← family.asReference
        let referenceSource ← reference.mark levels parameters source
          (← categoricalPointIdentity bundle source)
        let arrow ← kernel.run transaction context {} referenceSource
        unless (← kernel.dispatches.get).isEmpty do
          throwError "forming the native component invoked a provider"
        let selectedArrow ← markValue kernel.marks arrow referenceSource
        let identitySource ← categoricalPointIdentity bundle selectedEndpoint
        let identityPayload ← IO.ofExcept <| (ValuePayload.descriptor
          (Json.mkObj [("ctor", "identity"), ("args", .arr #[.null, .null])]) #[
            { path := #[.field "args", .index 0], binding := endpoint, fieldIndex := none },
            { path := #[.field "args", .index 1], binding := endpoint, fieldIndex := none }]).mapError IO.userError
        let identity ← stageOriginal kernel transaction context identitySource identityPayload
        let selectedIdentity ← markValue kernel.marks identity identitySource
        let whole ← family.asWhole
        let originalPoint ← whole.withRequest levels parameters selectedArrow selectedEndpoint
          selectedEndpoint selectedEndpoint selectedIdentity
        let requested ← whole.mark levels parameters selectedEndpoint originalPoint
        let result ← kernel.run transaction context {} requested
        let graph ← transaction.view
        let some resultNode := graph.find result.value
          | throwError "the complete returned component lost its original result node"
        let .container complete := resultNode.payload.data
          | throwError "the complete typedMap result was reduced to its callable body"
        unless complete.originalPacket.isSome do
          throwError "the result lost its immutable original reply packet"
        let .ok owners := graph.requiredOwners #[result]
          | throwError "the complete returned component lost its owner closure"
        unless owners.isEmpty do
          throwError "the wholly inline component acquired a supplier owner"
        let selectedResult ← markValue kernel.marks result requested
        let value ← mkAppOptM ``List.nil #[some receiverSource]
        let pointSource ← retainGlobalSourcePoint value
        let point ← kernel.run transaction context {} pointSource
        let retainedPoint ← markValue kernel.marks point pointSource
        let function ← family.function levels parameters selectedResult
        let output ← kernel.run transaction context {} (mkApp function retainedPoint)
        unless output.value == point.value &&
            point.associationIds.toList.isPrefixOf output.associationIds.toList do
          throwError "the actual returned callable did not retain its original supplied point"
        let dispatches ← kernel.dispatches.get
        unless dispatches.size == 2 && dispatches.all (·.operation == family.operation) &&
            dispatches[0]! == dispatches[1]! do
          throwError "the returned component changed its original selected registration"
      finally discard <| transaction.abort
  finally setEnv originalEnvironment


-- Complete record results exercise the same seven-field invocation at every native
-- owner. Cartesian base projection must return the captured original base map.
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let state ← semanticState
    let #[component] := state.cells.filter (·.id == NaturalTransformationId.listReverse)
      | throwError "the original list-reversal cell is absent"
    let #[cartesian] := state.functors.filter (·.id == FunctorId.modulesReindex)
      | throwError "the original module reindexing is absent"
    let mut selected : Array CategoricalPointOwner := #[
      .component component #[] false, .component component #[] true,
      .component component #[ConstructorId.arrow] false, .cartesian cartesian,
      .action (.functor FunctorId.setsList),
      .action (.classifierForget ClassifierId.setsFinite),
      .action (.constructMap ConstructorId.arrow (.functor FunctorId.setsList))]
    for id in #["bind.sets.finite_sum", "bind.sets.finite_product"] do
      let #[entry] := state.binders.filter (·.id.raw == id)
        | throwError "an original finite binder is absent"
      selected := selected.push (.binder entry)
    for declaration in #[
        ``CasCatalogue.Algebra.PolynomialPresentations.firstConstants,
        ``CasCatalogue.Algebra.PolynomialPresentations.secondConstants] do
      let #[entry] := state.morphisms.filter (·.declaration == declaration)
        | throwError "an original F9 constant map is absent"
      selected := selected.push (.named (.morphism entry))
    let #[application] := state.objects.filter (·.id.raw == "obj.sets.polynomials")
      | throwError "the original polynomial application is absent"
    selected := selected.push (.named (.application application))
    for (owner, available) in selected.flatMap (fun owner => #[(owner, false), (owner, true)]) do
      let family ← CategoricalPointFamily.forOwner owner
      let isCartesian := match owner with | .cartesian _ => true | _ => false
      let configuration := [("mode", toJson "opaque")] ++
        (if isCartesian then [("capture", Json.arr
          #[toJson "args", toJson (1 : Nat), toJson (0 : Nat), toJson (0 : Nat)])] else [])
      withPeer family configuration (available := available) fun kernel => do
        let sourceOwner ← kernel.ledger.owners.spawn { cmd := "/bin/cat" }
        try
          let levels := family.universeParams.map Level.param
          let type ← inferType
            (family.arrowFamily.instantiateLevelParams family.universeParams levels)
          forallTelescopeReducing type fun parameters _ => do
            let bindings ← parameters.mapIdxM fun index expression => do
              let declaration ← getFVarLocalDecl expression
              let role := if declaration.binderInfo.isInstImplicit then
                BindingRole.instance else BindingRole.parameter
              return ({ id := ⟨"original-categorical-parameters", index⟩, role, expression } : LocalBinding)
            let context ← ContextTelescope.capture bindings
            let transaction ← CellTransaction.begin kernel.ledger
            try
              let program ← kernel.ledger.owners.identities.fresh .program
              let mut runtimeParameters : Array RuntimeParameter := #[]
              let mut bound : Std.HashMap BindingId ValueBinding := {}
              let mut parameterValues : Array (Option ValueBinding) := #[]
              for binding in bindings do
                if ← isProof binding.expression then
                  parameterValues := parameterValues.push none
                  continue
                let environment ← RuntimeEnvironment.capture kernel.ledger.owners.identities.worker
                  context runtimeParameters #[] (some (← transaction.view))
                let source ← SourceLayout.ofTerm (← context.close binding.expression)
                let value ← transaction.stage
                  (← environment.origin program (← kernel.ledger.allocate) source)
                  (.ownedExport sourceOwner s!"native-parameter-{binding.id.serial}"
                    (parameterValues.filterMap id))
                let .ok parameter := RuntimeParameter.ofValue (← transaction.view) binding.id value
                  | throwError "an original categorical parameter lost its runtime identity"
                runtimeParameters := runtimeParameters.push parameter
                parameterValues := parameterValues.push (some value)
                bound := bound.insert binding.id value
              let (nativeArrow, bundle) ← family.arrowAt levels parameters
              let (source, _) ← categoricalPointEndpoints nativeArrow
              let identity ← categoricalPointIdentity bundle source
              let reference ← family.asReference
              let delayed ← kernel.run transaction context bound
                (← reference.mark levels parameters source identity)
              unless (← kernel.dispatches.get).isEmpty do
                throwError "forming a complete native arrow invoked a provider"
              let graph ← transaction.view
              let some delayedNode := graph.find delayed.value
                | throwError "the native arrow formation lost its retained result"
              unless ← isDefEq (← inferType (← delayedNode.origin.role.source.inContext context))
                  (← inferType nativeArrow) do
                throwError "native formation changed its complete original Hom interface"
              if !available then return
              let requested ← family.mark levels parameters source identity (whole := true)
              let result ← kernel.run transaction context bound requested
              let graph ← transaction.view
              let some resultNode := graph.find result.value
                | throwError "the complete categorical request has no actual result"
              let .container packet := resultNode.payload.data
                | throwError "the native whole Hom result lost its complete typedMap wrapper"
              unless packet.originalPacket.isSome do
                throwError "the native map lost its complete original reply packet"
              let .ok required := graph.requiredOwners #[result]
                | throwError "the complete record lost its actual owner closure"
              let .ok inputOwners := graph.requiredOwners (parameterValues.filterMap id)
                | throwError "the original categorical inputs lost their owners"
              unless inputOwners.all required.contains && required.size > inputOwners.size do
                throwError "the original inputs or returned native export lost their actual owners"
              let dispatches ← kernel.dispatches.get
              unless dispatches.size == 1 && dispatches[0]!.operation == family.operation do
                throwError "the native categorical request dispatched another owner or operation"
              if isCartesian then
                let #[baseIndex] ← family.explicitParameters
                  | throwError "the original cartesian declaration changed its base-map port"
                let some originalBase := parameterValues[baseIndex]?.bind id
                  | throwError "the original cartesian base map lost its binding"
                let retained ← markValue kernel.marks result requested
                let base ← mkAppM ``CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.base #[retained]
                let actualBase ← kernel.run transaction context bound base
                unless actualBase.value == originalBase.value &&
                    originalBase.associationIds.toList.isPrefixOf actualBase.associationIds.toList do
                  throwError "the actual cartesian result replaced its original base map"
                let observed ← IO.FS.readFile ((← IO.currentDir) /
                  ".tmp/categorical-point-native-observations.jsonl")
                let events ← (observed.splitOn "\n").filter (· != "") |>.toArray.mapM fun line => do
                  IO.ofExcept <| (Json.parse line).mapError IO.userError
                unless events.any (fun event =>
                    ((event.getObjValAs? String "prepared_role").toOption.getD "").startsWith "project:") do
                  throwError "the cartesian native continuation did not inspect its actual returned export"
            finally discard <| transaction.abort
        finally kernel.ledger.owners.close sourceOwner.generation
  finally setEnv originalEnvironment

end CasRuntime.CategoricalPointInvocationTests
