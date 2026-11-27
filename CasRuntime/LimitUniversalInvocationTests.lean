module

import CasRuntime.Kernel
import CasRuntime.LimitUniversal
import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.LimitUniversal
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

namespace CasRuntime.LimitUniversalInvocationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def withUniversalPeer (mode : String) (action : Kernel → TermElabM Unit) :
    TermElabM Unit := do
  let originalEnvironment ← getEnv
  let contract ← IO.FS.realPath (← packageDir contractPackage)
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  let log := root / ".tmp/universal-construction-observations.jsonl"
  IO.FS.writeFile log ""
  let configuration := Json.mkObj [("mode", toJson mode), ("log", toJson log.toString)]
  let registrations := #[
    ("lim.sets.product", "cat.sets"),
    ("lim.sets.product#isLimit", "lim.sets.product#isLimit#input")]
  let manifest := Json.mkObj [
    ("backends", .arr #[Json.mkObj [("name", "universal-construction-peer"),
      ("command", toJson (contract / ".venv/bin/python").toString),
      ("args", .arr #[toJson (root / "scripts/probes/universal_construction_peer.py").toString,
        toJson configuration.compress])]]),
    ("registrations", .arr (registrations.map fun (operation, input) =>
      Json.mkObj [("operation", toJson operation), ("input", toJson input),
        ("backend", "universal-construction-peer")]))]
  let path := root / ".tmp/universal-construction-manifest.json"
  IO.FS.writeFile path manifest.compress
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners (some path) none 5000
  try
    discard <| SessionSnapshot.initialize owners
    unless kernel.rejected.isEmpty do
      throwError "the exact native universal family lost its declared registration"
    action kernel
  finally
    kernel.close
    setEnv originalEnvironment




run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    for mode in #["retained", "wrong-target"] do
      withUniversalPeer mode fun kernel => do
        let family ← LimitFamily.forId ⟨"lim.sets.product"⟩
        let universal ← LimitUniversalFamily.forId family.entry.id
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
                  fun context bound leftSource =>
                withBoundValue kernel.ledger.owners.identities context bound rightSource right
                    fun context bound rightSource => do
                  let parameters := #[leftSource, rightSource]
                  let levels := family.universeParams.map (fun _ => Level.zero)
                  let construction ← mkFreshUserName `universalOccurrenceControl
                  let ownerFamily ← family.prepareOwner kernel.ledger.owners.identities levels construction
                  let selected ← family.selectedAtOwner ownerFamily levels parameters
                  SourceSelectionScope.withBinding kernel.ledger.owners.identities selections context selected
                      fun context selections requested => do
                    dbg_trace "[universal.control] first raw"
                    let first ← kernel.run transaction context bound requested (selections := selections)
                    dbg_trace "[universal.control] second raw"
                    let second ← kernel.run transaction context bound requested (selections := selections)
                    unless first.value != second.value do
                      throwError "two raw cone invocations merged their original result occurrences"


                    let otherOwnerFamily ← family.prepareOwner kernel.ledger.owners.identities levels
                      (← mkFreshUserName `differentUniversalOwner)
                    let closed ← parameters.mapM fun parameter => context.close parameter
                    let graph ← transaction.view
                    let actual ← liftM (m := IO) <| #[left, right].mapIdxM fun index value =>
                      IO.ofExcept <| (RuntimeArgument.ofValue graph index value).mapError IO.userError
                    let runtimeParameters ← context.bindings.filterMapM fun binding => do
                      let some value := bound[binding.id]? | return none
                      return some (← IO.ofExcept <|
                        (RuntimeParameter.ofValue graph binding.id value).mapError IO.userError)
                    dbg_trace "[universal.control] wrong-owner preparation"
                    let wrongOwnerRequest ← PreparedRequest.forBoundary kernel.ledger.owners.identities
                      program (← kernel.ledger.allocate)
                      (.limitUniversal universal (← otherOwnerFamily.mapM context.close))
                      levels context closed actual #[first] runtimeParameters (some graph)
                      (selections := selections)
                    let wrongOwnerResult : Except Exception ValueBinding ← try
                        pure (.ok (← kernel.stageUniversal wrongOwnerRequest transaction
                          (← kernel.ledger.owners.identities.fresh .program) wrongOwnerRequest.scope))
                      catch error => pure (.error error)
                    let .error ownerFailure := wrongOwnerResult
                      | throwError "a different construction owner captured the same-row actual cone"
                    unless ((← ownerFailure.toMessageData.toString).splitOn
                        "retained construction owner").length > 1 do
                      throw ownerFailure
                    unless (← kernel.dispatches.get).size == 2 do
                      throwError "an invalid universal owner reached a supplying invocation"
                    withBindingContext (← transaction.view) context bound first fun context bound => do
                      let selections ← SourceSelectionScope.merge selections
                        (← first.role.selections.inContext context)
                      withBoundValue kernel.ledger.owners.identities context bound
                          (← first.selectedSource context) first fun context bound firstSource =>
                        withBindingContext (← transaction.view) context bound second fun context bound => do
                          let selections ← SourceSelectionScope.merge selections
                            (← second.role.selections.inContext context)
                          withBoundValue kernel.ledger.owners.identities context bound
                              (← second.selectedSource context) second fun context bound secondSource => do
                            let formation : SourceReadM (Expr × Expr) := do
                              let firstSelected ← universal.selectedAtOwner ownerFamily levels parameters
                                (fun selection expected => SourceReadM.select selection expected)
                                (cone := some firstSource)
                              let firstType ← mkAppM ``CategoryTheory.Limits.IsLimit #[firstSource]
                              let firstSelected ← SourceReadM.select firstSelected (some firstType)
                              let secondSelected ← universal.selectedAtOwner ownerFamily levels parameters
                                (fun selection expected => SourceReadM.select selection expected)
                                (cone := some secondSource)
                              let secondType ← mkAppM ``CategoryTheory.Limits.IsLimit #[secondSource]
                              let secondSelected ← SourceReadM.select secondSelected (some secondType)
                              return (firstSelected, secondSelected)
                            let initial : SourceReadScope := {
                              identities := kernel.ledger.owners.identities, context, selections }
                            formation.runK initial fun (firstUniversalSource, secondUniversalSource) scope => do
                              let context := scope.context
                              let selections := scope.selections
                              checkWithKernel firstUniversalSource
                              checkWithKernel secondUniversalSource
                              dbg_trace "[universal.control] first universal"
                              let firstUniversal ← kernel.run transaction context bound firstUniversalSource
                                (selections := selections)
                              dbg_trace "[universal.control] second universal"
                              let secondUniversal ← kernel.run transaction context bound secondUniversalSource
                                (selections := selections)
                              unless firstUniversal.value != secondUniversal.value do
                                throwError "equal original parameters merged distinct universal records"
                              let graph ← transaction.view
                              for value in #[firstUniversal, secondUniversal], cone in #[first, second] do
                                let some node := graph.find value.value
                                  | throwError "the native universal result has no original producer"
                                let some nativePrefix := node.origin.fieldPrefix
                                  | throwError "the universal result lost its original native cone prefix"
                                let #[frame] := nativePrefix.frames
                                  | throwError "the universal result changed its original presentation frame"
                                let some original := frame.preceding[0]?.bind id
                                  | throwError "the universal result has no original cone selection"
                                unless original.value == cone.value &&
                                    cone.associationIds.toList.isPrefixOf original.associationIds.toList do
                                  throwError "the universal result retained another equal-data cone"
                              unless (← kernel.dispatches.get).size == 2 do
                                throwError "retaining universal data evaluated an ordinary mathematical definition"
                              withBindingContext graph context bound firstUniversal fun context bound => do
                                let selections ← SourceSelectionScope.merge selections
                                  (← firstUniversal.role.selections.inContext context)
                                withBoundValue kernel.ledger.owners.identities context bound
                                    (← firstUniversal.selectedSource context) firstUniversal
                                    fun context bound selected => do
                                  let argument := if mode == "wrong-target" then secondSource else firstSource
                                  let mediatorSource ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
                                    #[selected, argument]
                                  checkWithKernel mediatorSource
                                  dbg_trace "[universal.control] mediator"
                                  let result : Except Exception ValueBinding ← try
                                      pure (.ok (← kernel.run transaction context bound mediatorSource
                                        (selections := selections)))
                                    catch error => pure (.error error)
                                  if mode == "wrong-target" then
                                    let .error failure := result
                                      | throwError "the mediator accepted a distinct equal-data target apex"
                                    unless ((← failure.toMessageData.toString).splitOn "endpoint").length > 1 do
                                      throw failure
                                  else
                                    let mediator ← match result with
                                      | .ok value => pure value
                                      | .error failure => throw failure
                                    let graph ← transaction.view
                                    let .ok owners := graph.requiredOwners #[mediator]
                                      | throwError "the mediator lost its original native export owners"
                                    unless !owners.isEmpty do
                                      throwError "the provider mediator lost its retained callable owner"
                                    let point ← Term.elabTerm
                                      (← `(term| ((0 : Fin 1), (0 : Fin 1)))) none
                                    let coneApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[firstSource]
                                    let apex ← kernel.run transaction context bound coneApex
                                      (selections := selections)
                                    withBindingContext (← transaction.view) context bound apex fun context bound => do
                                      let selections ← SourceSelectionScope.merge selections
                                        (← apex.role.selections.inContext context)
                                      withBoundValue kernel.ledger.owners.identities context bound
                                          (← apex.selectedSource context) apex fun context bound actualApex => do
                                        let allocated ← kernel.ledger.owners.identities.fresh .sourceBinding
                                        let pointId : BindingId := ⟨allocated.worker, allocated.serial⟩
                                        context.withLocalBinding pointId .result `originalUniversalPoint actualApex
                                          (fun context pointBinding => do
                                            let pointRole ← SourceLayout.ofTerm (← context.close pointBinding.expression)
                                              (← selections.close context)
                                            let pointEnvironment ← RuntimeEnvironment.captureBound program.worker context bound
                                              (← transaction.view) (selections := selections)
                                            let pointOrigin ← pointEnvironment.origin program
                                              (← kernel.ledger.allocate) pointRole
                                            let pointValue ← transaction.stage pointOrigin
                                              (.portable (Json.arr #[toJson (0 : Nat), toJson (0 : Nat)]).compress.toUTF8)
                                            withBoundValue kernel.ledger.owners.identities context bound
                                                pointBinding.expression pointValue fun context bound actualPoint =>
                                              withBindingContext (← transaction.view) context bound mediator fun context bound => do
                                                let selections ← SourceSelectionScope.merge selections
                                                  (← mediator.role.selections.inContext context)
                                                withBoundValue kernel.ledger.owners.identities context bound
                                                    (← mediator.selectedSource context) mediator
                                                    fun context bound actualMediator => do
                                                  let applied ← kernel.run transaction context bound
                                                    (mkApp actualMediator actualPoint) (selections := selections)
                                                  unless applied.value == pointValue.value do
                                                    throwError "the retained mediator application replaced its actual returned point"
                                                  let observations ← IO.FS.readFile
                                                    ((← IO.currentDir) / ".tmp/universal-construction-observations.jsonl")
                                                  unless (observations.splitOn "mediator-application").length > 1 do
                                                    throwError "the original mediator callable was not actually invoked")
                                          (originalSource := some point)
                                  let dispatches ← kernel.dispatches.get
                                  unless dispatches.size == 3 &&
                                      dispatches[2]!.operation == universal.operation do
                                    throwError "the mediator did not reach its exact universal subfamily"
        finally discard <| transaction.abort
  finally setEnv originalEnvironment

end CasRuntime.LimitUniversalInvocationTests
