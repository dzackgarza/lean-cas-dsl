module

import CasRuntime.Kernel
import CasRuntime.Limit
import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.Limit
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

namespace CasRuntime.RawLimitInvocationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def withConstructionPeer (mode : String) (action : Kernel → TermElabM Unit) :
    TermElabM Unit := do
  let originalEnvironment ← getEnv
  let contract ← IO.FS.realPath (← packageDir contractPackage)
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  let log := root / ".tmp/raw-construction-observations.jsonl"
  IO.FS.writeFile log ""
  let configuration := Json.mkObj [("mode", toJson mode), ("log", toJson log.toString)]
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "raw-construction-peer"),
      ("command", toJson (contract / ".venv/bin/python").toString),
      ("args", .arr #[toJson (root / "scripts/probes/raw_construction_peer.py").toString,
        toJson configuration.compress])]]),
    ("registrations", .arr #[Json.mkObj [("operation", "lim.sets.product"),
      ("input", "cat.sets"), ("backend", "raw-construction-peer")]])]
  let path := root / ".tmp/raw-construction-manifest.json"
  IO.FS.writeFile path manifest.compress
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners (some path) none 5000
  try
    discard <| SessionSnapshot.initialize owners
    unless kernel.rejected.isEmpty do
      throwError "the original raw limit lost its declared registration"
    action kernel
  finally
    try kernel.close
    finally setEnv originalEnvironment




run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    let scenarios := (#["inline", "bare", "owned", "wrapped", "wrapped-owned",
      "swapped", "missing", "opaque"].map fun mode => (mode, false)).push ("inline", true)
    for (mode, sharedEndpoint) in scenarios do
      withConstructionPeer mode fun kernel => do
        let family ← LimitFamily.forId ⟨"lim.sets.product"⟩
        let context ← ContextTelescope.capture #[]
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let nativeSelection ← sourceNamedObjectAlias CategoryId.sets
            { value := mkApp (mkConst ``Fin) (mkNatLit 1) }
          let packet := Json.mkObj [("ctor", "finiteData"),
            ("args", .arr #[Json.mkObj [("ctor", "obj.sets.fin"),
              ("args", .arr #[toJson (1 : Nat)])], .arr #[toJson (0 : Nat)]])]
          let program ← kernel.ledger.owners.identities.fresh .program
          let occurrence ← kernel.ledger.allocate
          SourceSelectionScope.withBinding kernel.ledger.owners.identities {} context nativeSelection
              fun context selections leftSource =>
            SourceSelectionScope.withBinding kernel.ledger.owners.identities selections context nativeSelection
                fun context selections rightSource => do
              let some leftBinding := context.bindings.find? (·.expression == leftSource)
                | throwError "the original left endpoint lost its typed source binding"
              let some rightBinding := context.bindings.find? (·.expression == rightSource)
                | throwError "the original right endpoint lost its typed source binding"
              let closedSelections ← selections.close context
              let leftRole ← SourceLayout.ofTerm (← context.close leftSource)
                closedSelections (some leftBinding.id)
              let rightRole ← SourceLayout.ofTerm (← context.close rightSource)
                closedSelections (some rightBinding.id)
              let environment ← RuntimeEnvironment.captureBound program.worker context {}
                (← transaction.view) (selections := selections)
              let left ← transaction.stage (← environment.origin program occurrence leftRole)
                (.portable packet.compress.toUTF8)
              let right ← transaction.stage (← environment.origin program occurrence rightRole)
                (.portable packet.compress.toUTF8)
              unless left.value != right.value do
                throwError "the original equal-data endpoint control merged its two occurrences"
              withBoundValue kernel.ledger.owners.identities context {} leftSource left
                  fun context bound firstSource =>
                withBoundValue kernel.ledger.owners.identities context bound rightSource right
                    fun context bound secondSource => do
                  let parameters := #[firstSource, if sharedEndpoint then firstSource else secondSource]
                  let levels := family.universeParams.map (fun _ => Level.zero)
                  let selected ← family.selected kernel.ledger.owners.identities levels parameters
                  SourceSelectionScope.withBinding kernel.ledger.owners.identities selections context selected
                      fun context selections requested => do
                    checkWithKernel requested
                    let result : Except Exception ValueBinding ← try
                        pure (.ok (← kernel.run transaction context bound requested (selections := selections)))
                      catch error => pure (.error error)
                    let dispatches ← kernel.dispatches.get
                    unless dispatches.size == 1 && dispatches[0]!.operation == family.operation do
                      throwError "the raw cone did not reach its one original declared supplying operation"
                    let observed ← IO.FS.readFile ((← IO.currentDir) / ".tmp/raw-construction-observations.jsonl")
                    unless !observed.isEmpty do
                      throwError "the raw construction control failed before its actual framed reply"
                    if #["swapped", "missing", "opaque"].contains mode then
                      let .error failure := result
                        | throwError "an incomplete or wrong-original-endpoint cone was admitted"
                      let message ← failure.toMessageData.toString
                      unless (message.splitOn (if mode == "swapped" then "endpoint" else "port")).length > 1 do
                        throw failure
                    else
                      let result ← match result with
                        | .ok value => pure value
                        | .error failure => throw failure
                      let graph ← transaction.view
                      let some node := graph.find result.value
                        | throwError "the admitted raw cone has no original graph node"
                      let .container complete := node.payload.data
                        | throwError "the raw construction lost its complete original cone envelope"
                      unless complete.originalPacket.isSome && complete.fields.map (·.size) == some 2 do
                        throwError "the whole raw packet was not attached to its native Cone fields"
                      if mode.startsWith "wrapped" then
                        let some original := complete.originalPacket
                          | throwError "the wrapped cone lost its complete original packet"
                        unless (original.template.getObjValAs? String "ctor").toOption == some "valueData" do
                          throwError "the complete cone discarded an original inline envelope"
                      withBindingContext graph context bound result fun context bound => do
                        let selections ← SourceSelectionScope.merge selections (← result.role.selections.inContext context)
                        withBoundValue kernel.ledger.owners.identities context bound
                            (← result.selectedSource context) result fun context bound selected => do
                          let apexSource ← mkAppM ``CategoryTheory.Limits.Cone.pt #[selected]
                          let apex ← kernel.run transaction context bound apexSource (selections := selections)
                          let graph ← transaction.view
                          let some _ ← IO.ofExcept <|
                              (graph.projectionBasis apex result #[family.apexProjection]).mapError IO.userError
                            | throwError "the actual apex lost its original whole-cone projection parent"
                          let .ok apexOwners := graph.requiredOwners #[apex]
                            | throwError "the actual apex lost its original ownership information"
                          unless apexOwners.isEmpty do
                            throwError "the inline apex inherited an unrelated native leg owner"
                          let transformation ← mkAppM ``CategoryTheory.Limits.Cone.π #[selected]
                          let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation]
                          let indexSource ← mkAppM ``CategoryTheory.Discrete.mk
                            #[mkConst (if sharedEndpoint then ``CategoryTheory.Limits.WalkingPair.right
                              else ``CategoryTheory.Limits.WalkingPair.left)]
                          checkWithKernel indexSource
                          let index ← kernel.run transaction context bound indexSource (selections := selections)
                          withBindingContext (← transaction.view) context bound index fun context bound =>
                            withBoundValue kernel.ledger.owners.identities context bound indexSource index
                                fun context bound retainedIndex => do
                              let leg ← kernel.run transaction context bound (mkApp component retainedIndex) (selections := selections)
                              let graph ← transaction.view
                              let some legNode := graph.find leg.value
                                | throwError "the original cone component has no retained graph node"
                              let .container descriptor := legNode.payload.data
                                | throwError "the original cone component lost its complete symbolic packet"
                              unless descriptor.callableData &&
                                  (descriptor.template.getObjValAs? String "ctor").toOption == some "constructionLeg" do
                                throwError "the cone component did not retain its passive native map interface"
                              let some originalCone := descriptor.slots.find? (·.path == #[.field "args", .index 2])
                                | throwError "the leg lost its original whole-cone typed slot"
                              let some originalIndex := descriptor.slots.find? (·.path == #[.field "args", .index 3])
                                | throwError "the leg lost its exact typed diagram index"
                              unless originalCone.binding.value == result.value &&
                                  originalCone.binding.associationIds == result.associationIds &&
                                  originalIndex.binding.value == index.value &&
                                  originalIndex.binding.associationIds == index.associationIds do
                                throwError "the cone component replaced an original parent or native index"
                              let some legCompletion ← transaction.completionFor? legNode.origin.occurrence
                                | throwError "the original cone component lost its prepared source request"
                              let symbolic : PreparedSymbolicNode := {
                                source := leg.role
                                environment := legCompletion.request.environment
                                tag := "constructionLeg"
                                operands := #[]
                                action := some descriptor
                                framed := (.value apex, .value left)
                                inputActions := #[] }
                              let validate := preparedSymbolicCheck kernel legCompletion.request transaction
                              validate graph #[symbolic]
                              let wrongEndpoint ← try
                                  validate graph #[{ symbolic with framed := (.value apex, .value right) }]
                                  pure false
                                catch _ => pure true
                              unless wrongEndpoint do
                                throwError "a construction leg accepted another original framed endpoint"
                              let swapped := descriptor.slots.map fun slot =>
                                if slot.path == #[.field "args", .index 1, .field "args", .index 0] then
                                  { slot with binding := right }
                                else if slot.path == #[.field "args", .index 1, .field "args", .index 1] then
                                  { slot with binding := left }
                                else slot
                              let changed ← IO.ofExcept <|
                                (ValuePayload.descriptor descriptor.template swapped descriptor.exports).mapError IO.userError
                              let .container changed := changed.data
                                | throwError "the changed diagram control lost its complete native descriptor"
                              let rejected ← try
                                validate graph #[{ symbolic with action := some changed }]
                                pure false
                              catch _ => pure true
                              unless rejected do
                                throwError "a returned construction leg accepted another equal-data diagram occurrence"
                              unless (← kernel.dispatches.get).size == 1 do
                                throwError "the passive leg invented another call under the raw limit address"
                              if mode == "owned" || mode == "wrapped-owned" then
                                let .ok owners := graph.requiredOwners #[leg]
                                  | throwError "the returned leg lost its packet export owners"
                                unless !owners.isEmpty do
                                  throwError "an owned raw map became portable"
                                for owner in owners do kernel.ledger.owners.close owner
                                unless ← graph.isAvailable kernel.ledger.owners apex do
                                  throwError "closing a leg owner invalidated the independent portable apex"
                                if ← graph.isAvailable kernel.ledger.owners leg then
                                  throwError "a dependent construction leg survived its actual export owner"
                              else
                                let .ok owners := graph.requiredOwners #[leg]
                                  | throwError "the inline cone leg has an invalid owner closure"
                                unless owners.isEmpty do
                                  throwError "an entirely inline cone acquired a supplier owner"
        finally discard <| transaction.abort
  finally setEnv originalEnvironment





run_cmd Lean.Elab.Command.liftTermElabM do
  withConstructionPeer "inline" fun kernel => do
    let family ← LimitFamily.forId ⟨"lim.sets.product"⟩
    let context ← ContextTelescope.capture #[]
    let transaction ← CellTransaction.begin kernel.ledger
    try
      let nativeSelection ← sourceNamedObjectAlias CategoryId.sets
        { value := mkApp (mkConst ``Fin) (mkNatLit 1) }
      let packet := Json.mkObj [("ctor", "finiteData"),
        ("args", .arr #[Json.mkObj [("ctor", "obj.sets.fin"),
          ("args", .arr #[toJson (1 : Nat)])], .arr #[toJson (0 : Nat)]])]
      let program ← kernel.ledger.owners.identities.fresh .program
      let occurrence ← kernel.ledger.allocate
      SourceSelectionScope.withBinding kernel.ledger.owners.identities {} context nativeSelection
          fun context selections leftSource =>
        SourceSelectionScope.withBinding kernel.ledger.owners.identities selections context nativeSelection
            fun context selections rightSource => do
          let some leftBinding := context.bindings.find? (·.expression == leftSource)
            | throwError "the original left endpoint lost its typed source binding"
          let some rightBinding := context.bindings.find? (·.expression == rightSource)
            | throwError "the original right endpoint lost its typed source binding"
          let closedSelections ← selections.close context
          let leftRole ← SourceLayout.ofTerm (← context.close leftSource)
            closedSelections (some leftBinding.id)
          let rightRole ← SourceLayout.ofTerm (← context.close rightSource)
            closedSelections (some rightBinding.id)
          let environment ← RuntimeEnvironment.captureBound program.worker context {}
            (← transaction.view) (selections := selections)
          let left ← transaction.stage (← environment.origin program occurrence leftRole)
            (.portable packet.compress.toUTF8)
          let right ← transaction.stage (← environment.origin program occurrence rightRole)
            (.portable packet.compress.toUTF8)
          withBoundValue kernel.ledger.owners.identities context {} leftSource left
              fun context bound firstSource =>
            withBoundValue kernel.ledger.owners.identities context bound rightSource right
                fun context bound secondSource => do
              let initial : SourceReadScope := { identities := kernel.ledger.owners.identities,
                context, selections }
              (sourceBinaryLimit { value := firstSource, category := none }
                { value := secondSource, category := none } false).runK initial fun original scope => do
                let context := scope.context
                let selections := scope.selections
                let demand : OpenContext → Std.HashMap BindingId ValueBinding →
                    SourceSelectionScope Expr → NativeSourceJudgement → ValueBinding →
                    TermElabM ValueBinding := fun context bound selections original owner => do
                  let before := (← kernel.dispatches.get).size
                  withBindingContext (← transaction.view) context bound owner fun context bound => do
                    let selections ← SourceSelectionScope.merge selections
                      (← owner.role.selections.inContext context)
                    withBoundValue kernel.ledger.owners.identities context bound
                        (← owner.selectedSource context) owner fun context bound selectedOwner => do
                      let initial : SourceReadScope := {
                        identities := kernel.ledger.owners.identities, context, selections }
                      (sourceLimitLeg? { original with value := selectedOwner } 0).runK initial
                          fun legSource scope => do
                        let some legSource := legSource
                          | throwError "the original direct construction lost its source-selected leg"
                        let context := scope.context
                        let selections := scope.selections
                        let formal ← kernel.run transaction context bound legSource.value
                          (selections := selections)
                        unless (← kernel.dispatches.get).size == before do
                          throwError "formal leg formation dispatched its deferred construction"
                        let graph ← transaction.view
                        let some node := graph.find formal.value
                          | throwError "the formal leg lost its actual retained node"
                        let .closure code _ := node.payload.data
                          | throwError "the formal leg lost its delayed native continuation"
                        let some (.formalLeg source (some originalPacket) codeSelections) :=
                            (← kernel.codes.get)[code]?
                          | throwError "the formal direct leg lost its original packet and source plan"
                        let some view ← InputDescriptorView.namedPoint? graph (← kernel.codes.get) formal
                          | throwError "the formal leg lost its unchanged declared-consumer packet"
                        unless view.packet.template == originalPacket.template &&
                            (view.packet.template.getObjValAs? String "ctor").toOption ==
                              some "lim.sets.product#leg" && view.packet.slots.size == 3 do
                          throwError "the formal leg changed its original named descriptor or ordinal slot"
                        withBindingContext graph context bound formal fun context bound => do
                          let selections ← SourceSelectionScope.merge selections
                            (← formal.role.selections.inContext context)
                          let selections ← SourceSelectionScope.merge selections
                            (← codeSelections.inContext context)
                          let first ← kernel.run transaction context bound
                            (← source.inContext context) (selections := selections)
                          let second ← kernel.run transaction context bound
                            (← source.inContext context) (selections := selections)
                          let graph ← transaction.view
                          let component : ValueBinding → MetaM (ValueBinding × ValueBinding) :=
                              fun value => do
                            let some node := graph.find value.value
                              | throwError "the native component demand lost its actual map data"
                            let .container complete := node.payload.data
                              | throwError "the native component demand did not return its complete map packet"
                            unless complete.callableData &&
                                (complete.template.getObjValAs? String "ctor").toOption ==
                                  some "constructionLeg" do
                              throwError "the native component demand changed its complete original map data"
                            let some cone := complete.slots.find?
                                (·.path == #[.field "args", .index 2])
                              | throwError "the demanded component lost its original complete Cone"
                            let some index := complete.slots.find?
                                (·.path == #[.field "args", .index 3])
                              | throwError "the demanded component lost its original typed index"
                            return (cone.binding, index.binding)
                          let (firstCone, firstIndex) ← component first
                          let (secondCone, secondIndex) ← component second
                          unless firstCone.value == secondCone.value &&
                              firstCone.associationIds == secondCone.associationIds &&
                              firstIndex.value == secondIndex.value &&
                              firstIndex.associationIds == secondIndex.associationIds do
                            throwError "repeated native leg demand replaced its exact owner completion or typed index"
                          let some selectedConstruction := selections.findAt? context original.value.getAppFn
                            | throwError "the original source lost its exact construction selection"
                          let some selection := (← selectedConstruction.specialize original.value.getAppArgs).limit
                            | throwError "the original source lost its exact construction selection"
                          let .ok (some cached) ← transaction.selectedAt selection.source.construction
                              family.coneProjection owner
                            | throwError "the first native leg demand did not retain its exact owner's complete Cone"
                          unless cached.value == firstCone.value &&
                              cached.associationIds == firstCone.associationIds &&
                              (← kernel.dispatches.get).size == before + 1 do
                            throwError "the exact original owner did not reuse its single completed Cone"
                          return firstCone
                let owner ← kernel.run transaction context bound original.value
                  (selections := selections)
                let firstCone ← demand context bound selections original owner
                let some selectedConstruction := selections.findAt? context original.value.getAppFn
                  | throwError "the original construction lost its retained positional source family"
                let some originalSelection := (← selectedConstruction.specialize original.value.getAppArgs).limit
                  | throwError "the original construction lost its retained positional source family"
                let some ownerSource := originalSelection.source.ownerFamily
                  | throwError "the original construction lost its complete owner template"
                let ownerTemplate ← SelectedLimitOwner.ofBinding context selections ownerSource
                let some retained := selections.findAt? context original.value
                  | throwError "the rebound construction lost its original selection"
                let some family := retained.limitFamily
                  | throwError "the rebound construction lost its complete selected limit family"
                let some rebound ← LimitFamily.formalAt family context originalSelection ownerTemplate
                    #[secondSource, firstSource]
                  | throwError "the original construction lost its retained positional source family"
                let category : NativeSourceCategory := {
                  role := .object, expression := rebound.source.category,
                  bundle := rebound.source.bundle, limit := some rebound.source }
                let changed : SourceSelection Expr := {
                  retained with value := rebound.receiver, limit := some rebound,
                    originalApplication := some rebound.source.presentation, category := some category }
                SourceSelectionScope.withBinding kernel.ledger.owners.identities selections context changed
                    fun context selections rebound => do
                  let changed : NativeSourceJudgement := { value := rebound, category := some category }
                  let anotherOwner ← kernel.run transaction context bound rebound (selections := selections)
                  unless owner.value != anotherOwner.value do
                    throwError "independent equal source receivers merged their original occurrences"
                  let secondCone ← demand context bound selections changed anotherOwner
                  unless firstCone.value != secondCone.value && (← kernel.dispatches.get).size == 2 do
                    throwError "one compiled construction reused another receiver's actual completed Cone"
    finally discard <| transaction.abort

end CasRuntime.RawLimitInvocationTests
