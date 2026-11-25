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

-- The same original declaration parameters and source owner produce two distinct actual
-- cones. Each universal record must retain its own cone. A mediator to the other equal-data
-- apex cannot substitute that apex for the selected universal record's target.
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
          let native ← sourceNamedObjectAlias CategoryId.sets
            (mkApp (mkConst ``Fin) (mkNatLit 1))
          let packet := Json.mkObj [("ctor", "finiteData"),
            ("args", .arr #[Json.mkObj [("ctor", "obj.sets.fin"),
              ("args", .arr #[toJson (1 : Nat)])], .arr #[toJson (0 : Nat)]])]
          let program ← kernel.ledger.owners.identities.fresh .program
          let role ← SourceLayout.ofTerm (← context.close native)
          let occurrence ← kernel.ledger.allocate
          let left ← transaction.stage { program, occurrence, role, parameters := #[] }
            (.portable packet.compress.toUTF8)
          let right ← transaction.stage { program, occurrence, role, parameters := #[] }
            (.portable packet.compress.toUTF8)
          let parameters := #[
            ← markValue kernel.marks left native, ← markValue kernel.marks right native]
          let levels := family.universeParams.map (fun _ => Level.zero)
          let construction ← mkFreshUserName `universalOccurrenceControl
          let ownerFamily ← family.prepareOwner levels construction
          let requested ← family.markSelected ownerFamily levels parameters
          dbg_trace "[universal.control] first raw"
          let first ← kernel.run transaction context {} requested
          dbg_trace "[universal.control] second raw"
          let second ← kernel.run transaction context {} requested
          unless first.value != second.value do
            throwError "two raw cone invocations merged their original result occurrences"
          -- Direct boundary preparation must not bypass the original owner check.
          -- This owner has the same row, universes and actual parameters, but a
          -- distinct source construction identity and no corresponding raw result.
          let otherOwnerFamily ← family.prepareOwner levels
            (← mkFreshUserName `differentUniversalOwner)
          let otherWhole ← family.markSelected otherOwnerFamily levels parameters
          let .mdata _ otherBody := otherWhole
            | throwError "the different construction lost its original source marker"
          let (_, _, otherOwner, _) ← family.application otherBody
          let closed ← liftM (m := MetaM) (parameters.mapM fun parameter => context.close parameter)
          let graph ← transaction.view
          let actual ← liftM (m := IO) <| #[left, right].mapIdxM fun index value => do
            IO.ofExcept <|
              (RuntimeArgument.ofValue graph index value (← kernel.marks.get)).mapError IO.userError
          dbg_trace "[universal.control] wrong-owner preparation"
          let wrongOwnerRequest ← PreparedRequest.forBoundary kernel.ledger.owners.identities
            program (← kernel.ledger.allocate) (.limitUniversal universal (← context.close otherOwner))
            levels context closed actual #[first] #[] (some graph)
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
          let firstSource ← markValue kernel.marks first requested
          let secondSource ← markValue kernel.marks second requested
          let firstUniversalSource ← universal.markSelected ownerFamily levels parameters
            (cone := some firstSource)
          let secondUniversalSource ← universal.markSelected ownerFamily levels parameters
            (cone := some secondSource)
          checkWithKernel firstUniversalSource
          checkWithKernel secondUniversalSource
          dbg_trace "[universal.control] first universal"
          let firstUniversal ← kernel.run transaction context {} firstUniversalSource
          dbg_trace "[universal.control] second universal"
          let secondUniversal ← kernel.run transaction context {} secondUniversalSource
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
          let selected ← markValue kernel.marks firstUniversal firstUniversalSource
          let argument := if mode == "wrong-target" then secondSource else firstSource
          let mediatorSource ← mkAppM ``CategoryTheory.Limits.IsLimit.lift #[selected, argument]
          checkWithKernel mediatorSource
          dbg_trace "[universal.control] mediator"
          let result : Except Exception ValueBinding ← try
              pure (.ok (← kernel.run transaction context {} mediatorSource))
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
            let point ← Term.elabTerm (← `(term| ((0 : Fin 1), (0 : Fin 1)))) none
            let coneApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[firstSource]
            let apex ← kernel.run transaction context {} coneApex
            let markedApex ← markValue kernel.marks apex coneApex
            let point ← mkAppOptM ``id #[some markedApex, some point]
            let pointRole ← SourceLayout.ofTerm (← context.close point)
            let pointMarks ← IO.ofExcept <|
              (captureSourceMarks (← kernel.marks.get) pointRole.source).mapError IO.userError
            let pointEnvironment ← RuntimeEnvironment.capture program.worker context #[]
              pointMarks (some (← transaction.view))
            let pointOrigin ← pointEnvironment.origin program (← kernel.ledger.allocate) pointRole
            let pointValue ← transaction.stage pointOrigin
              (.portable (Json.arr #[toJson (0 : Nat), toJson (0 : Nat)]).compress.toUTF8)
            let actualPoint ← markValue kernel.marks pointValue point
            let actualMediator ← markValue kernel.marks mediator mediatorSource
            let applied ← kernel.run transaction context {} (mkApp actualMediator actualPoint)
            unless applied.value == pointValue.value do
              throwError "the retained mediator application replaced its actual returned point"
            let observations ← IO.FS.readFile
              ((← IO.currentDir) / ".tmp/universal-construction-observations.jsonl")
            unless (observations.splitOn "mediator-application").length > 1 do
              throwError "the original mediator callable was not actually invoked"
          let dispatches ← kernel.dispatches.get
          unless dispatches.size == 3 &&
              dispatches[2]!.operation == universal.operation do
            throwError "the mediator did not reach its exact universal subfamily"
        finally discard <| transaction.abort
  finally setEnv originalEnvironment

end CasRuntime.LimitUniversalInvocationTests
