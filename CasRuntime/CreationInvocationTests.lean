module

import CasRuntime.Kernel
import CasRuntime.Creation
import CasCompiler.Read
import CasCompiler.CreationSource
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import CasRuntime.Creation
meta import CasCompiler.Read
meta import CasCompiler.CreationSource
meta import LeanCategories.Catalogue

namespace CasRuntime.CreationInvocationTests

open Lean Meta Elab Term CasCompiler CasCatalogue CasCatalogue.Backend

private def originalTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original creation consumer did not parse"
  return ⟨parsed⟩

private def originalSession (identities : IdentitySupply) : TermElabM SourceSession := do
  let empty ← SourceSession.empty identities
  let f ← empty.read (← originalTerm
    "{0 ↦ 0, 1 ↦ 1, 2 ↦ 1} : (Fin(3) in FiniteSets) → (Fin(2) in FiniteSets)")
  let source ← empty.defineTerm `f' f
  let g ← source.read (← originalTerm
    "{0 ↦ 1, 1 ↦ 0} : (Fin(2) in FiniteSets) → (Fin(2) in FiniteSets)")
  source.defineTerm `g' g

private def retains (actual original : ValueBinding) : Bool :=
  actual.value == original.value &&
    original.associationIds.toList.isPrefixOf actual.associationIds.toList

private def originalInputs (transaction : CellTransaction) (result : ValueBinding) :
    MetaM (ValueBinding × ValueBinding) := do
  let graph ← transaction.view
  let some node := graph.find result.value
    | throwError "the complete creation has no original producing node"
  let some completion ← transaction.completionFor? node.origin.occurrence
    | throwError "the complete creation lost its actual prepared invocation"
  let .primitive (.creation _) _ := completion.request.action
    | throwError "the stored result was not produced by the complete creation family"
  let some application := completion.request.origin.application
    | throwError "the creation lost its complete native input table"
  let #[some cone, some universal] := application.arguments
    | throwError "the creation changed its original c/t data positions"
  let some universalNode := graph.find universal.value
    | throwError "the original universal input is outside the visible graph"
  let some nativePrefix := universalNode.origin.fieldPrefix
    | throwError "the original universal input lost its preceding cone"
  let #[frame] := nativePrefix.frames.filter
      (·.field.projection == ``CategoryTheory.Limits.LimitCone.isLimit)
    | throwError "the universal input lost its original presentation field"
  let some preceding := frame.preceding[0]?.bind id
    | throwError "the original universal input has no actual cone predecessor"
  unless retains preceding cone do
    throwError "the creation received a universal record for another actual cone"
  return (cone, universal)

private def requireProjection (transaction : CellTransaction) (value parent : ValueBinding)
    (path : Array Name) : MetaM Unit := do
  let graph ← transaction.view
  let some _ ← IO.ofExcept <| (graph.projectionBasis value parent path).mapError IO.userError
    | throwError "a creation field lost its original complete-result parent"

/-- Invoke a supplied native map on a formal point at its exact original domain.
The point is a source assumption; no native mathematical element is reconstructed from bytes. -/
private def applyNative (kernel : Kernel) (transaction : CellTransaction)
    (context : OpenContext) (source : Expr) (cone universal : ValueBinding) (label : String) :
    MetaM ValueBinding := do
  let function ← if (← whnf (← inferType source)).isForall then pure source else do
    let some function ← coerceToFunction? source
      | throwError "the returned native map has no original callable interface"
    pure function
  let callable ← kernel.run transaction context {} function
  let selected ← markValue kernel.marks callable function
  let .forallE _ domain _ _ ← whnf (← inferType function)
    | throwError "the returned map lost its exact native point domain"
  withLocalDeclD `originalCreationPoint domain fun point => do
    let pointId : BindingId := ⟨"creation-point:" ++ label, 0⟩
    let current ← ContextTelescope.capture
      (context.bindings.push ⟨pointId, .parameter, point⟩)
    let role ← SourceLayout.ofTerm (← current.close point)
    let marks ← IO.ofExcept <|
      (captureSourceMarks (← kernel.marks.get) role.source).mapError IO.userError
    let program ← kernel.ledger.owners.identities.fresh .program
    let value ← transaction.stage
      { program, occurrence := ← kernel.ledger.allocate, role,
        parameters := Array.replicate current.bindings.size none, sourceMarks := marks }
      (.portable (toJson (0 : Nat)).compress.toUTF8)
    let pointSource ← markValue kernel.marks value point
    let result ← kernel.run transaction current {} (mkApp selected pointSource)
    let graph ← transaction.view
    let some node := graph.find result.value
      | throwError "the actual native application produced no stored result"
    let .ownedToken _ _ captures := node.payload.data
      | throwError "the native continuation did not return its actual owned data"
    unless captures.any (fun actual => retains actual value) &&
        captures.any (fun actual => retains actual cone) &&
        captures.any (fun actual => retains actual universal) do
      throwError "the native continuation changed its original point or c/t captures"
    return result

private def withOriginalPeer (action : Kernel → TermElabM Unit) : TermElabM Unit := do
  let contract ← IO.FS.realPath (← packageDir contractPackage)
  let leaves : System.FilePath :=
    (← IO.getEnv "CAS_LEAVES").getD ".lake/packages/cas_leaves"
  let leaves ← IO.FS.realPath (if leaves.extension == some "json" then
    leaves.parent.getD "." else leaves)
  let root ← IO.currentDir
  IO.FS.createDirAll (root / ".tmp")
  let log := root / ".tmp/creation-invocation-observations.jsonl"
  IO.FS.writeFile log ""
  let configuration := Json.mkObj [("log", toJson log.toString)]
  let peer := Json.mkObj [("name", "creation-invocation-peer"),
    ("command", toJson (contract / ".venv/bin/python").toString),
    ("args", .arr #[toJson (root / "scripts/probes/creation_invocation_peer.py").toString,
      toJson configuration.compress])]
  -- The original set-limit implementation supplies c. This test defines no pullback algorithm.
  let raw := Json.mkObj [("name", "original-set-limits"), ("command", "python3"),
    ("args", .arr #[toJson (leaves / "backends/sage_set_limits.py").toString])]
  let manifest := Json.mkObj [
    ("backends", .arr #[raw, peer]),
    ("registrations", .arr #[
      Json.mkObj [("operation", "lim.sets.pullback"), ("input", "cat.sets"),
        ("backend", "original-set-limits")],
      Json.mkObj [("operation", "lift.finite_sets.pullbacks"),
        ("input", "lift.finite_sets.pullbacks#input"), ("backend", "creation-invocation-peer")]])]
  let path := root / ".tmp/creation-invocation-manifest.json"
  IO.FS.writeFile path manifest.compress
  let owners ← OwnerRegistry.new
  let kernel ← Kernel.load owners (some path) none 10000
  try
    discard <| SessionSnapshot.initialize owners
    unless kernel.rejected.isEmpty do
      throwError "the original finite-pullback creation lost its declared native registration"
    action kernel
  finally kernel.close

/- The original finite-pullback source is used unchanged. The target raw cone comes from the
existing set-limit provider. The peer supplies complete native interfaces, then handles the
actual retained native projections and applications; it supplies no new mathematical definition
or answer table. A source cone is never synthesized from compact createdCone data. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let originalEnvironment ← getEnv
  try
    withOriginalPeer fun kernel => do
      let source ← originalSession kernel.ledger.owners.identities
      let original ← source.read (← originalTerm "pullback(f', g')")
      original.source.withOpen fun bindings expression => do
        let context ← ContextTelescope.capture bindings
        let transaction ← CellTransaction.begin kernel.ledger
        try
          let owner ← kernel.run transaction context {} expression
          unless (← kernel.dispatches.get).isEmpty do
            throwError "forming the original created object dispatched a target computation"
          let graph ← transaction.view
          let some ownerNode := graph.find owner.value
            | throwError "the created source owner has no retained original node"
          let .closure program _ := ownerNode.payload.data
            | throwError "the created source was not retained as its complete native owner"
          let some (.creationOwner prepared) := (← kernel.codes.get)[program]?
            | throwError "the created source lost its exact source-input telescope"
          let actualOwner ← markValue kernel.marks owner
            (← prepared.owner.inContext context)
          let completionSource ← prepared.completionSource context actualOwner
          checkWithKernel completionSource
          let mut originals : Array (ValueBinding × ValueBinding) := #[]
          let mut results : Array ValueBinding := #[]
          let mut continuations : Array ValueBinding := #[]
          for mode in #["inline", "owned"] do
            let complete ← kernel.run transaction context {} completionSource
            let (cone, universal) ← originalInputs transaction complete
            originals := originals.push (cone, universal)
            results := results.push complete
            let graph ← transaction.view
            let some completeNode := graph.find complete.value
              | throwError "the complete native creation result disappeared"
            if mode == "inline" then
              let .container data := completeNode.payload.data
                | throwError "the inline creation did not retain its complete native record"
              unless data.originalPacket.isSome && data.fields.map (·.size) == some 2 do
                throwError "the inline creation lost a native data field or original packet"
            else
              let .ownedToken _ _ _ := completeNode.payload.data
                | throwError "the owned creation did not retain its actual native export"
            let selected ← markValue kernel.marks complete completionSource
            let liftableSource ← mkAppM ``CategoryTheory.LiftsToLimit.toLiftableCone #[selected]
            let coneSource ← mkAppM ``CategoryTheory.LiftableCone.liftedCone #[liftableSource]
            let sourceCone ← kernel.run transaction context {} coneSource
            let sourceConeAgain ← kernel.run transaction context {} coneSource
            unless sourceCone.value == sourceConeAgain.value do
              throwError "repeating a native source-cone projection recomputed its actual value"
            requireProjection transaction sourceCone complete
              #[``CategoryTheory.LiftsToLimit.toLiftableCone, ``CategoryTheory.LiftableCone.liftedCone]
            requireProjection transaction sourceConeAgain complete
              #[``CategoryTheory.LiftsToLimit.toLiftableCone, ``CategoryTheory.LiftableCone.liftedCone]
            let comparisonSource ← mkAppM ``CategoryTheory.LiftableCone.validLift #[liftableSource]
            let comparison ← kernel.run transaction context {} comparisonSource
            requireProjection transaction comparison complete
              #[``CategoryTheory.LiftsToLimit.toLiftableCone, ``CategoryTheory.LiftableCone.validLift]
            let actualComparison ← markValue kernel.marks comparison comparisonSource
            for direction in #[``CategoryTheory.Iso.hom, ``CategoryTheory.Iso.inv] do
              let arrow ← mkAppM direction #[actualComparison]
              let nativeMap ← mkAppM ``CategoryTheory.Limits.ConeMorphism.hom #[arrow]
              continuations := continuations.push
                (← applyNative kernel transaction context nativeMap cone universal
                  (mode ++ ":" ++ direction.toString))
            let universalSource ← mkAppM ``CategoryTheory.LiftsToLimit.makesLimit #[selected]
            let sourceUniversal ← kernel.run transaction context {} universalSource
            requireProjection transaction sourceUniversal complete
              #[``CategoryTheory.LiftsToLimit.makesLimit]
            let actualUniversal ← markValue kernel.marks sourceUniversal universalSource
            let actualCone ← markValue kernel.marks sourceCone coneSource
            let mediatorSource ← mkAppM ``CategoryTheory.Limits.IsLimit.lift
              #[actualUniversal, actualCone]
            continuations := continuations.push
              (← applyNative kernel transaction context mediatorSource cone universal
                (mode ++ ":makesLimit"))
          let #[(firstCone, firstUniversal), (secondCone, _)] := originals
            | throwError "the original creation controls lost one complete c/t invocation"
          unless firstCone.value != secondCone.value do
            throwError "equal source requests merged two actual target cone occurrences"
          let selected ← prepared.selection context
          let some targetOwner := selected.source.ownerFamily
            | throwError "the source creation lost its original target owner family"
          let parameters ← (prepared.inputs.target.arguments.mapM (fun argument =>
            argument.source.source.inContext context) : MetaM (Array Expr))
          let rawSource ← prepared.target.markSelected targetOwner prepared.targetUniverses parameters
          let firstSource ← markValue kernel.marks firstCone rawSource
          let secondSource ← markValue kernel.marks secondCone rawSource
          let universalFamily ← LimitUniversalFamily.forId prepared.target.entry.id
          let universalSource ← universalFamily.markSelected targetOwner prepared.targetUniverses
            parameters (some firstSource)
          let wrongUniversal ← markValue kernel.marks firstUniversal universalSource
          -- Establish the identical explicit-marker boundary with its original c/t before
          -- changing only c to another occurrence of the same raw native source.
          let matching ← prepared.markArguments context actualOwner firstSource wrongUniversal
          let beforeMatching := (← kernel.dispatches.get).size
          let repeated ← kernel.run transaction context {} matching
          let (repeatedCone, repeatedUniversal) ← originalInputs transaction repeated
          unless retains repeatedCone firstCone && retains repeatedUniversal firstUniversal &&
              (← kernel.dispatches.get).size == beforeMatching + 1 do
            throwError "the explicit matching c/t boundary changed or recomputed an original input"
          results := results.push repeated
          let mismatch ← prepared.markArguments context actualOwner secondSource wrongUniversal
          let before := (← kernel.dispatches.get).size
          let rejected ← try
              discard <| kernel.run transaction context {} mismatch
              pure false
            catch _ => pure true
          unless rejected && (← kernel.dispatches.get).size == before do
            throwError "creation accepted t from another equal-source c or dispatched before rejection"
          let malformed : Option Exception ← try
              discard <| kernel.run transaction context {} completionSource
              pure none
            catch error => pure (some error)
          let some malformed := malformed
            | throwError "the whole creation admitted a result missing makesLimit"
          unless ((← malformed.toMessageData.toString).splitOn "data-field arity").length > 1 do
            throw malformed
          let dispatches ← kernel.dispatches.get
          unless (dispatches.filter (·.operation == "lift.finite_sets.pullbacks")).size == 4 do
            throwError "a native field replayed or skipped the original complete creation request"
          if dispatches.any (fun entry =>
              entry.operation.startsWith "lift.finite_sets.pullbacks#") then
            throwError "a creation field acquired an undeclared independent operation"
          let observed ← IO.FS.readFile
            ((← IO.currentDir) / ".tmp/creation-invocation-observations.jsonl")
          for required in #["creation:inline", "creation:owned", "Iso.hom", "Iso.inv", "IsLimit.lift"] do
            unless (observed.splitOn required).length > 1 do
              throwError "the original creation continuation did not actually reach {required}"
          let graph ← transaction.view
          let .ok owners := graph.requiredOwners continuations
            | throwError "the created native continuations lost their actual owners"
          unless !owners.isEmpty do
            throwError "owned creation data became portable"
          for owner in owners do kernel.ledger.owners.close owner
          for result in results do
            if ← graph.isAvailable kernel.ledger.owners result then
              throwError "a complete created result survived its actual native export owner"
          unless ← graph.isAvailable kernel.ledger.owners firstCone do
            throwError "closing the creation owner invalidated its independently portable target cone"
        finally discard <| transaction.abort
  finally setEnv originalEnvironment

end CasRuntime.CreationInvocationTests
