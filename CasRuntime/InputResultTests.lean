module

import CasRuntime.Kernel
import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups
public meta import Lean.Elab.Command
meta import CasRuntime.Kernel
meta import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups

namespace CasRuntime.InputResultTests

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

private def prepare (kernel : Kernel) (transaction : CellTransaction)
    (program : RuntimeId .program) (context : OpenContext) (callable : ValueBinding)
    (arguments : Array Expr) (values : Array ValueBinding)
    (parameters : Array RuntimeParameter := #[]) : MetaM PreparedRequest := do
  unless arguments.size == values.size do
    throwError "the input-result control omitted an actual argument"
  let graph ← transaction.view
  let marks ← kernel.marks.get
  let mut actual := #[]
  for value in values, index in [:values.size] do
    let .ok argument := RuntimeArgument.ofValue graph index value marks
      | throwError "the input-result argument is outside its actual graph"
    actual := actual.push argument
  PreparedRequest.forApplication kernel.ledger.owners.identities program
    (← kernel.ledger.allocate) context callable (← arguments.mapM context.close) actual parameters
    (some graph)

private def demand (kernel : Kernel) (transaction : CellTransaction)
    (request : PreparedRequest) : MetaM (PreparedResponse request) :=
  Execute.run kernel.executor
    (PFunctor.FreeM.lift (P := OperationalSignature) request) transaction

-- A successful shortcut must complete the actual occurrence, survive ordinary publication,
-- and reuse the same retained result through the production executor in a later cell.
private def checkCompletion (kernel : Kernel) (transaction : CellTransaction)
    (request : PreparedRequest) (first : ValueBinding)
    (expectedOwners : Array ConnectionGeneration := #[]) : MetaM SessionSnapshot := do
  let .ok requiredOwners := (← transaction.view).requiredOwners #[first]
    | throwError "the input-result completion is outside its actual graph"
  unless requiredOwners == expectedOwners do
    throwError "the input result retained an unused owner or dropped a selected owner"
  let some role := request.roles.results[0]?
    | throwError "the input-result request lost its root role"
  match ← transaction.reuse request.occurrence role.role.id with
  | .ok (.ready value) =>
    unless value.value == first.value && value.associationIds == first.associationIds do
      throwError "same-cell input-result reuse changed the completed reference"
  | _ => throwError "the source-fixed result did not complete its claimed occurrence"
  let repeated ← demand kernel transaction request
  unless repeated.root.value == first.value &&
      repeated.root.associationIds == first.associationIds do
    throwError "repeated input-result execution reconstructed its result"
  if ← kernel.ledger.isFresh request.occurrence then
    throwError "the completed input-result occurrence retained a dispatch right"
  unless (← kernel.ledger.pendingFor request.occurrence transaction.id).isNone do
    throwError "the input-result shortcut left a pending provider invocation"
  unless (← kernel.dispatches.get).isEmpty do
    throwError "a wholly source-fixed result dispatched a registration"
  unless ((← SessionSnapshot.current).receipt request.occurrence).isNone do
    throwError "the input-result receipt became visible before commit"
  let .ok published ← transaction.commit
    | throwError "the source-fixed result could not commit independently of unused owners"
  let some receipt := published.receipt request.occurrence
    | throwError "input-result commit omitted its ordinary receipt"
  let .kernel := receipt.association.producer
    | throwError "the source-fixed result acquired a provider completion"
  let some batch := published.outputBatches.back?
    | throwError "input-result commit omitted its output batch"
  unless receipt.association.request.roles.scope == request.roles.scope &&
      receipt.association.response.root.value == first.value &&
      receipt.association.response.root.associationIds == first.associationIds &&
      receipt.snapshot == published.id && receipt.commit == batch.commit &&
      receipt.outputBatch == batch.id do
    throwError "input-result publication changed its request, result, or receipt identities"
  let .ok (some retained) ← published.reuse kernel.ledger.owners request.occurrence role.role.id
    | throwError "the committed input-result receipt could not supply its selected result"
  unless retained.value == first.value && retained.associationIds == first.associationIds do
    throwError "committed input-result reuse changed the selected association"
  let next ← CellTransaction.begin kernel.ledger
  try
    let reused ← demand kernel next request
    unless reused.root.value == first.value &&
        reused.root.associationIds == first.associationIds do
      throwError "later-cell execution reconstructed a committed input result"
    unless (← kernel.dispatches.get).isEmpty do
      throwError "input-result receipt reuse dispatched a registration"
  finally discard <| next.abort
  return published

-- Native source terms specify only selections and record assembly. The target payloads are
-- unpublished native exports, so evaluating an ordinary retained lambda cannot satisfy these
-- controls. Equal portable data have distinct nodes and distinct record positions.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let pairRole ← SourceLayout.ofTerm (← context.close pairTerm)
    let aliasTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p _other : Nat × Nat) => p)) none
    let secondTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => p.2)) none
    let firstTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => p.1)) none
    let duplicateTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => (p.1, p.1))) none
    let reverseTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => (p.2, p.1))) none
    let functionPairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkConst ``Nat.succ]
    let functionPairRole ← SourceLayout.ofTerm (← context.close functionPairTerm)
    let functionTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × (Nat → Nat)) => p.2)) none
    let incompleteTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => (p.1, Nat.succ p.2))) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let live ← owners.spawn { cmd := "/bin/cat" }
    let unrelated ← owners.spawn { cmd := "/bin/cat" }
    try
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let produced ← kernel.ledger.allocate
      let stage (role : SourceLayout) (payload : ValuePayload) := producer.stage
        { program, occurrence := produced, role, parameters := #[] } payload
      let left ← stage scalar (.portable "7".toUTF8)
      let right ← stage scalar (.portable "7".toUTF8)
      let input ← stage pairRole (.product #[left, right])
      let equalInput ← stage pairRole (.product #[right, left])
      unless left.value != right.value && input.value != equalInput.value do
        throwError "the input-result control merged equal-valued occurrences"
      let wholeCallable ← stage (← SourceLayout.ofTerm (← context.close aliasTerm))
        (.ownedExport unrelated "unpublished whole alias" #[])
      let second ← stage (← SourceLayout.ofTerm (← context.close secondTerm))
        (.ownedExport live "unpublished second field" #[])
      let first ← stage (← SourceLayout.ofTerm (← context.close firstTerm))
        (.ownedExport unrelated "unpublished first field" #[])
      let duplicate ← stage (← SourceLayout.ofTerm (← context.close duplicateTerm))
        (.ownedExport unrelated "unpublished duplicated first field" #[])
      let reverse ← stage (← SourceLayout.ofTerm (← context.close reverseTerm))
        (.ownedExport unrelated "unpublished reversed pair" #[])
      let selectedFunction ← stage
        (← SourceLayout.ofTerm (← context.close (mkConst ``Nat.succ)))
        (.ownedExport live "unpublished selected callable" #[])
      let functionInput ← stage functionPairRole (.product #[left, selectedFunction])
      let selectFunction ← stage (← SourceLayout.ofTerm (← context.close functionTerm))
        (.ownedExport unrelated "unpublished callable projection" #[])
      let incompleteCallable ← stage (← SourceLayout.ofTerm (← context.close incompleteTerm))
        (.ownedExport live "unpublished partially input-fixed callable" #[])
      let lazyPair ← stage pairRole (.ownedExport live "unpublished lazy input pair" #[])
      let required ← stage scalar (.ownedExport unrelated "required selected input" #[])
      let requiredInput ← stage pairRole (.product #[left, required])
      let .ok _ ← producer.commit
        | throwError "the input-result fixture could not publish its original inputs"
      owners.close unrelated.generation
      if ← owners.isLive unrelated.generation then
        throwError "the input-result control did not close its unrelated owner"

      let wholeCell ← CellTransaction.begin kernel.ledger
      let whole ← prepare kernel wholeCell program context wholeCallable
        #[pairTerm, pairTerm] #[input, equalInput]
      let wholeResult ← demand kernel wholeCell whole
      unless wholeResult.root.value == input.value && wholeResult.root.value != equalInput.value do
        throwError "whole input aliasing selected an equal but different actual record"
      let wholeGraph ← wholeCell.view
      let .ok wholeLeft := wholeGraph.project wholeResult.root 0
        | throwError "whole input aliasing lost its first stored field"
      let .ok wholeRight := wholeGraph.project wholeResult.root 1
        | throwError "whole input aliasing lost its second stored field"
      unless wholeLeft.value == left.value && wholeRight.value == right.value do
        throwError "whole input aliasing replaced its retained field occurrences"
      discard <| checkCompletion kernel wholeCell whole wholeResult.root

      let fieldCell ← CellTransaction.begin kernel.ledger
      let field ← prepare kernel fieldCell program context second #[pairTerm] #[input]
      let fieldResult ← demand kernel fieldCell field
      unless fieldResult.root.value == right.value && fieldResult.root.value != left.value do
        throwError "the fixed second field selected the equal first-field occurrence"
      discard <| checkCompletion kernel fieldCell field fieldResult.root

      -- The actual input record itself is unavailable because its second field is owned
      -- by the closed process. Selecting only its portable first field must still succeed.
      let firstCell ← CellTransaction.begin kernel.ledger
      let firstRequest ← prepare kernel firstCell program context first #[pairTerm] #[requiredInput]
      if ← (← firstCell.view).isAvailable owners requiredInput then
        throwError "the dead-sibling input-result control unexpectedly has an available whole input"
      let firstResult ← demand kernel firstCell firstRequest
      unless firstResult.root.value == left.value do
        throwError "a dead input sibling changed the selected portable first field"
      discard <| checkCompletion kernel firstCell firstRequest firstResult.root

      let duplicateCell ← CellTransaction.begin kernel.ledger
      let duplicateRequest ← prepare kernel duplicateCell program context duplicate
        #[pairTerm] #[requiredInput]
      let duplicateResult ← demand kernel duplicateCell duplicateRequest
      let duplicateGraph ← duplicateCell.view
      let some duplicateNode := duplicateGraph.find duplicateResult.root.value
        | throwError "the duplicated input record is outside its actual graph"
      let .product duplicateFields := duplicateNode.payload.data
        | throwError "duplicating the portable first field left a lazy provider demand"
      unless duplicateFields.size == 2 do
        throwError "duplicating the portable first field omitted a computational result field"
      for index in [0:2] do
        let .ok actual := duplicateGraph.project duplicateResult.root index
          | throwError "the duplicated input result lost a stored field"
        unless actual.value == left.value do
          throwError "the duplicated result substituted the dead sibling's equal native value"
      discard <| checkCompletion kernel duplicateCell duplicateRequest duplicateResult.root

      -- Returning a selected callable preserves its lazy interface and its own live owner;
      -- neither the enclosing native export nor the selected callable may be invoked.
      let functionCell ← CellTransaction.begin kernel.ledger
      let functionRequest ← prepare kernel functionCell program context selectFunction
        #[functionPairTerm] #[functionInput]
      let functionResult ← demand kernel functionCell functionRequest
      unless functionResult.root.value == selectedFunction.value do
        throwError "the input-result shortcut replaced or evaluated its selected callable"
      discard <| checkCompletion kernel functionCell functionRequest functionResult.root
        #[live.generation]

      let reverseCell ← CellTransaction.begin kernel.ledger
      let reversed ← prepare kernel reverseCell program context reverse #[pairTerm] #[input]
      let reverseResult ← demand kernel reverseCell reversed
      let reverseGraph ← reverseCell.view
      unless reverseResult.root.value != input.value && reverseResult.root.value != equalInput.value do
        throwError "record reconstruction reused an unrelated equal-valued input root"
      let some reverseNode := reverseGraph.find reverseResult.root.value
        | throwError "the reconstructed input record is outside its actual graph"
      let .product fields := reverseNode.payload.data
        | throwError "the wholly input-projected pair was left as a lazy provider demand"
      unless fields.size == 2 do
        throwError "the wholly input-projected pair omitted a computational field"
      let .ok reverseLeft := reverseGraph.project reverseResult.root 0
        | throwError "the reconstructed input pair lost its first field"
      let .ok reverseRight := reverseGraph.project reverseResult.root 1
        | throwError "the reconstructed input pair lost its second field"
      unless reverseLeft.value == right.value && reverseRight.value == left.value do
        throwError "input-result reconstruction changed the declared field order"
      let published ← checkCompletion kernel reverseCell reversed reverseResult.root

      -- The selected result's own owner remains required; the shortcut must not turn a
      -- genuine unavailable selected field into an owner-free native-typed replacement.
      let failed ← CellTransaction.begin kernel.ledger
      let selected ← prepare kernel failed program context second #[pairTerm] #[requiredInput]
      let failure : Option Exception ← try
        discard <| demand kernel failed selected
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "an input-result shortcut returned a field whose required owner is dead"
      unless CasCatalogue.Exception.stratum? failure == some .unavailable &&
          (← failure.toMessageData.toString).endsWith "stale_owner" do throw failure
      unless (← failed.activeGraph).isNone &&
          (← kernel.ledger.pendingFor selected.occurrence failed.id).isNone &&
          ((← SessionSnapshot.current).receipt selected.occurrence).isNone &&
          (← SessionSnapshot.current).id == published.id &&
          (← kernel.dispatches.get).isEmpty do
        throwError "a failed selected-owner check retained or published an input-result demand"

      let failedWhole ← CellTransaction.begin kernel.ledger
      let wholeRequired ← prepare kernel failedWhole program context wholeCallable
        #[pairTerm, pairTerm] #[requiredInput, input]
      let wholeFailure : Option Exception ← try
        discard <| demand kernel failedWhole wholeRequired
        pure none
      catch error => pure (some error)
      let some wholeFailure := wholeFailure
        | throwError "whole input aliasing dropped the selected record's dead field owner"
      unless CasCatalogue.Exception.stratum? wholeFailure == some .unavailable &&
          (← wholeFailure.toMessageData.toString).endsWith "stale_owner" do throw wholeFailure
      unless (← failedWhole.activeGraph).isNone &&
          ((← SessionSnapshot.current).receipt wholeRequired.occurrence).isNone &&
          (← SessionSnapshot.current).id == published.id do
        throwError "a failed whole-record owner check published an input-result alias"

      -- The first result field is input-fixed and the second is not. Keep this request on
      -- the production execution path: a partial prefix cannot become a completed record.
      let incompleteCell ← CellTransaction.begin kernel.ledger
      let incompleteRequest ← prepare kernel incompleteCell program context incompleteCallable
        #[pairTerm] #[lazyPair]
      let resolutionCalls ← IO.mkRef (0 : Nat)
      let rejectedResolution : FixedInput → MetaM ValueBinding := fun _ => do
        resolutionCalls.modify (· + 1)
        throwError "incomplete result coverage forced a lazy input"
      let incompleteFailure : Option Exception ← try
        discard <| Execute.run kernel.executor
          (PFunctor.FreeM.lift (P := OperationalSignature) incompleteRequest) incompleteCell
          (some rejectedResolution)
        pure none
      catch error => pure (some error)
      let some incompleteFailure := incompleteFailure
        | throwError "a known input-result prefix was admitted as a complete reconstructed record"
      unless CasCatalogue.Exception.stratum? incompleteFailure == some .unavailable &&
          (← incompleteFailure.toMessageData.toString).endsWith "stale_owner" do
        throw incompleteFailure
      unless (← incompleteCell.activeGraph).isNone &&
          (← resolutionCalls.get) == 0 &&
          (← SessionSnapshot.current).id == published.id &&
          ((← SessionSnapshot.current).receipt incompleteRequest.occurrence).isNone &&
          (← kernel.dispatches.get).isEmpty do
        throwError "an incomplete input-result prefix entered the committed result graph"
    finally
      owners.close unrelated.generation
      owners.close live.generation
      kernel.close
  finally setEnv original

-- The earlier application owns its original argument and context tables. A later source
-- scope adds a shadowing binder and a different equal-valued actual argument; it cannot
-- replace the earlier selected actual when the residual callable is finally applied.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let empty ← ContextTelescope.capture #[]
    let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let owner ← owners.spawn { cmd := "/bin/cat" }
    try
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let produced ← kernel.ledger.allocate
      let left ← producer.stage
        { program, occurrence := produced, role := scalar, parameters := #[] }
        (.portable "7".toUTF8)
      let right ← producer.stage
        { program, occurrence := produced, role := scalar, parameters := #[] }
        (.portable "7".toUTF8)
      withLocalDeclD `n (mkConst ``Nat) fun originalParameter => do
        let oldBinding : LocalBinding := {
          id := ⟨"input-result-context", 0⟩, role := .parameter,
          expression := originalParameter }
        let context ← ContextTelescope.capture #[oldBinding]
        let .ok oldActual := RuntimeParameter.ofValue (← producer.view) oldBinding.id left
          | throwError "the original input-result context binding is outside its graph"
        let source ← Elab.Term.elabTermAndSynthesize
          (← `(fun (x _y : Nat) => x)) none
        let callableRole ← SourceLayout.ofTerm (← context.close source)
        let callable ← producer.stage
          { program, occurrence := produced, role := callableRole, parameters := #[some left] }
          (.ownedExport owner "unpublished original partial application" #[])
        let first ← prepare kernel producer program context callable #[mkNatLit 7] #[left]
          #[oldActual]
        let residual ← producer.stage first.origin
          (.ownedExport owner "unpublished residual callable" #[])
        let some earlier := first.origin.application
          | throwError "the partial input-result fixture lost its producing application"
        let .ok _ ← producer.commit
          | throwError "the captured input-result fixture could not publish"
        owners.close owner.generation
        withLocalDeclD `n (mkConst ``Nat) fun shadowParameter => do
          let newBinding : LocalBinding := {
            id := ⟨"input-result-context", 1⟩, role := .parameter,
            expression := shadowParameter }
          let current ← ContextTelescope.capture #[oldBinding, newBinding]
          let consumer ← CellTransaction.begin kernel.ledger
          let .ok newActual := RuntimeParameter.ofValue (← consumer.view) newBinding.id right
            | throwError "the shadowing input-result context binding is outside its graph"
          let request ← prepare kernel consumer program current residual #[mkNatLit 7] #[right]
            #[oldActual, newActual]
          let response ← demand kernel consumer request
          unless response.root.value == left.value && response.root.value != right.value do
            throwError "partial input-result execution selected a later equal-valued actual"
          let some later := request.origin.application
            | throwError "the final input-result demand lost its actual argument table"
          unless earlier.parameters.size == 1 && later.parameters.size == 2 &&
              earlier.layout.result.source.context.entries.size == 1 &&
              later.layout.result.source.context.entries.size == 2 &&
              (earlier.arguments[0]?.bind id).map (·.value) == some left.value &&
              (later.arguments[0]?.bind id).map (·.value) == some right.value do
            throwError "input-result execution merged original and later source argument planes"
          discard <| checkCompletion kernel consumer request response.root
    finally
      owners.close owner.generation
      kernel.close
  finally setEnv original

-- The independent registered group-kernel declaration fixes the inclusion's ambient to
-- the input arrow's source. Its other fields still require a provider. These opaque native
-- interfaces supply no computed group-theoretic answer; only the existing source selection
-- and the absence of a whole-result realization are under test.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let sign ← Elab.Term.elabTermAndSynthesize
      (← `(CasCatalogue.Algebra.FiniteGroups.sign 3)) none
    let signArrow ← mkAppM ``CategoryTheory.Arrow.mk #[sign]
    let object ← mkAppM ``CategoryTheory.Arrow.left #[signArrow]
    let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[object]
    let receiver ← mkAppM ``CategoryTheory.Arrow.mk #[identity]
    let receiverRole ← SourceLayout.ofTerm (← context.close receiver)
    let receiverRecord ← RecordLayout.ofSource receiverRole
    let #[leftField, rightField, homField] :=
        receiverRecord.fields.filter (·.field.wireIndex.isSome)
      | throwError "the group-kernel input changed its native computational fields"
    unless ← isDefEq (← leftField.layout.source.inContext context)
        (← rightField.layout.source.inContext context) do
      throwError "the group-kernel control requires equal native endpoint terms"
    let family ← SourceFamily.forReference (.functor ⟨"fun.arrows_groups.kernel"⟩)
    let declaration := family.source.family.instantiateLevelParams family.universeParams
      (family.universeParams.map fun _ => Level.zero)
    let callableSource ← mkProjection declaration `obj
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let owner ← owners.spawn { cmd := "/bin/cat" }
    try
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let produced ← kernel.ledger.allocate
      let left ← producer.stage
        { program, occurrence := produced, role := leftField.layout, parameters := #[] }
        (.closure program #[])
      let right ← producer.stage
        { program, occurrence := produced, role := rightField.layout, parameters := #[] }
        (.closure program #[])
      let hom ← producer.stage
        { program, occurrence := produced, role := homField.layout, parameters := #[] }
        (.closure program #[])
      let input ← producer.stage
        { program, occurrence := produced, role := receiverRole, parameters := #[] }
        (.product #[left, right, hom])
      let lazyInput ← producer.stage
        { program, occurrence := produced, role := receiverRole, parameters := #[] }
        (.ownedExport owner "unpublished lazy group arrow" #[])
      -- Obtain the actual delayed published family through the production lowerer.
      let callable ← kernel.run producer context {} callableSource none
      let application ← prepare kernel producer program context callable #[receiver] #[input]
      let resultRecord ← RecordLayout.ofSource application.source
      let some underlying := resultRecord.fields.find? (·.field.wireIndex == some 0)
        | throwError "the group-kernel result lost its native underlying arrow"
      let arrowRecord ← RecordLayout.ofSource underlying.layout
      let some ambient := arrowRecord.fields.find? (·.field.wireIndex == some 1)
        | throwError "the group-kernel inclusion lost its native ambient field"
      let resultArrow ← producer.stage (← application.originFor underlying.layout)
        (.ownedExport owner "unpublished kernel inclusion arrow" #[])
      let .ok _ ← producer.commit
        | throwError "the registered group-kernel input interfaces could not publish"

      let projectedCell ← CellTransaction.begin kernel.ledger
      let projection ← PreparedRequest.forProjection owners.identities program
        (← kernel.ledger.allocate) context (← projectedCell.view) resultArrow
        ambient.field.sourceIndex #[]
      let selected ← demand kernel projectedCell projection
      unless selected.root.value == left.value && selected.root.value != right.value do
        throwError "the registered fixed ambient selected a different equal-valued input endpoint"
      unless selected.root.projectionAccesses.any (fun (parent, path) =>
          parent.value == input.value && path == #[leftField.field.projection]) &&
          selected.root.projectionAccesses.any (fun (parent, path) =>
            parent.value == resultArrow.value && path == #[ambient.field.projection]) do
        throwError "the fixed ambient lost its original input or current output access"
      let published ← checkCompletion kernel projectedCell projection selected.root

      -- A lazy input would require its unpublished owner's projection interface if forced.
      -- The whole kernel result is not input-fixed: coverage discovery must leave that input
      -- untouched and reach the ordinary missing-realization failure for the target family.
      let incomplete ← CellTransaction.begin kernel.ledger
      let retainedCallable ← markValue kernel.marks callable callableSource
      let retainedInput ← markValue kernel.marks lazyInput receiver
      let failure : Option Exception ← try
        discard <| kernel.run incomplete context {} (mkApp retainedCallable retainedInput) none
        pure none
      catch error => pure (some error)
      let some failure := failure
        | throwError "a partially input-fixed group-kernel result bypassed its required provider"
      unless CasCatalogue.Exception.stratum? failure == some .noImplementation do throw failure
      if ((← failure.toMessageData.toString).splitOn "fun.arrows_groups.kernel").length == 1 then
        throw failure
      unless (← incomplete.activeGraph).isNone &&
          (← SessionSnapshot.current).id == published.id &&
          (← kernel.dispatches.get).isEmpty do
        throwError "incomplete input-result coverage published or dispatched a partial result"
    finally
      owners.close owner.generation
      kernel.close
  finally setEnv original

-- Native id preserves its complete input; Prod.fst selects a declared native field. A descriptor
-- carries the whole Prod value but no stored field identities. These controls use only those
-- native structural rules: the ordinary result below is produced by Kernel.run on Prod.mk,
-- not supplied by a mathematical backend or recovered from the descriptor's packet.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 11]
    let pairRole ← SourceLayout.ofTerm (← context.close pairTerm)
    let identityTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => p)) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let program ← owners.identities.fresh .program
      let produced ← kernel.ledger.allocate
      let .ok payload := ValuePayload.descriptor
          (.arr #[toJson (7 : Nat), toJson (11 : Nat)]) #[]
        | throwError "the native descriptor control has an invalid packet"
      let input ← producer.stage
        { program, occurrence := produced, role := pairRole, parameters := #[] } payload
      let identity ← kernel.run producer context {} identityTerm none
      let producerGraph ← producer.view
      let some inputNode := producerGraph.find input.value
        | throwError "the descriptor control lost its original input"
      unless inputNode.payload.data.storedFields?.isNone do
        throwError "the descriptor control already has stored native field data"
      let .error _ := producerGraph.project input 0
        | throwError "the descriptor control fabricated a native field reference"
      let .ok _ ← producer.commit
        | throwError "the descriptor control could not publish its original input"

      let executionCalls ← IO.mkRef (0 : Nat)
      let resolutionCalls ← IO.mkRef (0 : Nat)
      let executor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
        fun request transaction => do
          executionCalls.modify (· + 1)
          kernel.executor request transaction
      let rejectResolution : FixedInput → MetaM ValueBinding := fun _ => do
        resolutionCalls.modify (· + 1)
        throwError "descriptor input routing invoked a fabricated lazy field resolver"
      let wholeCell ← CellTransaction.begin kernel.ledger
      let whole ← prepare kernel wholeCell program context identity #[pairTerm] #[input]
      let wholeResult ← Execute.run executor
        (PFunctor.FreeM.lift (P := OperationalSignature) whole) wholeCell
        (some rejectResolution)
      unless wholeResult.root.value == input.value && (← executionCalls.get) == 0 &&
          (← resolutionCalls.get) == 0 do
        throwError "whole descriptor identity changed its node or executed a demand"
      let wholeGraph ← wholeCell.view
      let some wholeNode := wholeGraph.find wholeResult.root.value
        | throwError "whole descriptor identity lost its retained node"
      unless wholeNode.payload.data.storedFields?.isNone do
        throwError "whole descriptor identity fabricated a stored native record"
      discard <| checkCompletion kernel wholeCell whole wholeResult.root

      -- The identity's retained application supplies a real fixed-source path to the same
      -- descriptor. Its absent field table must prevent that path from becoming coverage.
      let fieldCell ← CellTransaction.begin kernel.ledger
      let fieldGraph ← fieldCell.view
      let field ← PreparedRequest.forProjection owners.identities program
        (← kernel.ledger.allocate) context fieldGraph wholeResult.root 0 #[]
      unless field.origin.application.isSome do
        throwError "the descriptor projection control lost its source application provenance"
      let beforeDispatches := (← kernel.dispatches.get).size
      let beforeCodes := (← kernel.codes.get).size
      let beforeMarks := (← kernel.marks.get).size
      let .none ← field.fixedInputFor fieldGraph field.source
        | throwError "the descriptor's native schema fabricated a fixed input field"
      let .none ← field.inputResultPlan fieldGraph
        | throwError "the descriptor's absent field table supplied complete result coverage"
      let afterPreparation ← fieldCell.view
      unless afterPreparation.sameRevision fieldGraph &&
          (← kernel.dispatches.get).size == beforeDispatches &&
          (← kernel.codes.get).size == beforeCodes &&
          (← kernel.marks.get).size == beforeMarks &&
          (← kernel.ledger.isFresh field.occurrence) &&
          (← kernel.ledger.pendingFor field.occurrence fieldCell.id).isNone do
        throwError "fixed-source preparation executed or staged a descriptor field demand"
      let .ok none := afterPreparation.projected? wholeResult.root #[``Prod.fst]
        | throwError "fixed-source preparation fabricated a published descriptor field"
      let computed : IO.Ref (Option ValueBinding) ← IO.mkRef none
      let fieldExecutor : PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
        fun request transaction => do
          executionCalls.modify (· + 1)
          let .project operand selected := request.action
            | throwError "the descriptor field control reached a different action"
          unless operand.value == input.value && selected.projection == ``Prod.fst do
            throwError "the descriptor field demand changed its exact operand or projection"
          let value ← kernel.run transaction context {} (mkProj ``Prod 0 pairTerm) none
          computed.set (some value)
          let response ← kernelCompletion request transaction value (some rejectResolution)
          return (response, transaction)
      let fieldResult ← Execute.run fieldExecutor
        (PFunctor.FreeM.lift (P := OperationalSignature) field) fieldCell
        (some rejectResolution)
      let some computed ← computed.get
        | throwError "the descriptor field was not produced by the ordinary executor"
      unless (← executionCalls.get) == 1 && (← resolutionCalls.get) == 0 &&
          fieldResult.root.value == computed.value && fieldResult.root.value != input.value do
        throwError "descriptor field admission fabricated an input identity or bypassed execution"
      discard <| checkCompletion kernel fieldCell field fieldResult.root
    finally kernel.close
  finally setEnv original

-- One lazy runtime record has one first field, even when two result positions select it.
-- The stored source is only a native Prod constructor. Both projections run through the
-- production native evaluator and its ordinary fixed-input resolver; no provider or fixture
-- executor supplies a field value. The two output roles may differ, but their node must not.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 11]
    let pairSource ← context.close pairTerm
    let pairRole ← SourceLayout.ofTerm pairSource
    let duplicateTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : Nat × Nat) => (p.1, p.1))) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let code ← owners.identities.fresh .program
      kernel.codes.modify (·.insert code (.term pairSource))
      let produced ← kernel.ledger.allocate
      let input ← producer.stage
        { program := code, occurrence := produced, role := pairRole, parameters := #[] }
        (.closure code #[])
      let duplicate ← kernel.run producer context {} duplicateTerm none
      let producerGraph ← producer.view
      let some inputNode := producerGraph.find input.value
        | throwError "the lazy duplicate control lost its original record"
      unless inputNode.payload.data.storedFields?.isNone do
        throwError "the lazy duplicate control already has stored field identities"
      let .error _ := producerGraph.project input 0
        | throwError "the lazy duplicate control already exposes its first field"
      let .ok _ ← producer.commit
        | throwError "the lazy duplicate control could not publish its original record"

      let consumer ← CellTransaction.begin kernel.ledger
      try
        let function ← markValue kernel.marks duplicate duplicateTerm
        let argument ← markValue kernel.marks input pairTerm
        -- Kernel.run installs the production fixed-input resolver. This is one
        -- application to the same retained record, not two callable applications.
        let result ← kernel.run consumer context {} (mkApp function argument) none
        let graph ← consumer.view
        let .ok first := graph.project result 0
          | throwError "the lazy duplicate result lost its first field"
        let .ok second := graph.project result 1
          | throwError "the lazy duplicate result lost its second field"
        for field in #[first, second] do
          unless field.projectionAccesses.any (fun (parent, path) =>
              parent.value == input.value && parent.associationIds == input.associationIds &&
                path == #[``Prod.fst]) do
            throwError "the lazy duplicate result did not select the same original record field"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the native lazy duplicate control dispatched a provider"
        unless first.value == second.value do
          throwError "one lazy input field was realized as two different nodes"
      finally discard <| consumer.abort
    finally kernel.close
  finally setEnv original

-- A deeper selection may occur before its shared prefix. Retain the intermediate field,
-- while equal source terms at another parent or native path remain distinct selections.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 11]
    let inputTerm ← mkAppM ``Prod.mk #[pairTerm, pairTerm]
    let inputSource ← context.close inputTerm
    let inputRole ← SourceLayout.ofTerm inputSource
    let selectTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p q : (Nat × Nat) × (Nat × Nat)) =>
        (p.1.1, (p.1, (p.2, q.1))))) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let code ← owners.identities.fresh .program
      kernel.codes.modify (·.insert code (.term inputSource))
      let produced ← kernel.ledger.allocate
      let stage := producer.stage
        { program := code, occurrence := produced, role := inputRole, parameters := #[] }
        (.closure code #[])
      let input ← stage
      let other ← stage
      unless input.value != other.value do
        throwError "the lazy overlap control merged its original parent nodes"
      let selected ← kernel.run producer context {} selectTerm none
      let graph ← producer.view
      for parent in #[input, other] do
        let .error _ := graph.project parent 0
          | throwError "the lazy overlap control already has stored field identities"
      let .ok _ ← producer.commit
        | throwError "the lazy overlap control could not publish its original records"

      let consumer ← CellTransaction.begin kernel.ledger
      try
        let function ← markValue kernel.marks selected selectTerm
        let left ← markValue kernel.marks input inputTerm
        let right ← markValue kernel.marks other inputTerm
        let result ← kernel.run consumer context {} (mkAppN function #[left, right]) none
        let graph ← consumer.view
        let project := fun parent index => IO.ofExcept <|
          (graph.project parent index).mapError IO.userError
        let deep ← project result 0
        let rest ← project result 1
        let first ← project rest 0
        let rest ← project rest 1
        let second ← project rest 0
        let otherFirst ← project rest 1
        let fromFirst ← project first 0
        unless deep.value == fromFirst.value do
          throwError "a deeper lazy input selection recreated its shared prefix field"
        unless first.value != second.value && first.value != otherFirst.value &&
            second.value != otherFirst.value do
          throwError "lazy input reuse merged distinct parent or native path identities"
        for (field, parent, path) in #[
            (deep, input, #[``Prod.fst, ``Prod.fst]),
            (first, input, #[``Prod.fst]),
            (second, input, #[``Prod.snd]),
            (otherFirst, other, #[``Prod.fst])] do
          unless field.projectionAccesses.any (fun (actual, selectedPath) =>
              actual.value == parent.value && actual.associationIds == parent.associationIds &&
                selectedPath == path) do
            throwError "lazy input reuse changed an original selected parent or native path"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the native lazy overlap control dispatched a provider"
      finally discard <| consumer.abort
    finally kernel.close
  finally setEnv original

-- A lazy native prefix may expose a symbolic descriptor. Discovering its unavailable field
-- preserves the ordinary projection failure, without replaying the prefix or inventing data.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 11]
    let pairRole ← SourceLayout.ofTerm (← context.close pairTerm)
    let selectTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : (Nat × Nat) × Nat) => p.1.1)) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let code ← owners.identities.fresh .program
      let produced ← kernel.ledger.allocate
      let .ok descriptorPayload := ValuePayload.descriptor .null #[]
        | throwError "the lazy descriptor control could not prepare its symbolic value"
      let descriptor ← producer.stage
        { program := code, occurrence := produced, role := pairRole, parameters := #[] }
        descriptorPayload
      let retained ← markValue kernel.marks descriptor pairTerm
      let inputTerm ← mkAppM ``Prod.mk #[retained, mkNatLit 13]
      let inputSource ← context.close inputTerm
      kernel.codes.modify (·.insert code (.term inputSource))
      let input ← producer.stage
        { program := code, occurrence := produced,
          role := ← SourceLayout.ofTerm inputSource, parameters := #[] }
        (.closure code #[descriptor])
      let selected ← kernel.run producer context {} selectTerm none
      let graph ← producer.view
      for parent in #[descriptor, input] do
        let .error _ := graph.project parent 0
          | throwError "the lazy descriptor control already has stored native fields"
      let .ok _ ← producer.commit
        | throwError "the lazy descriptor control could not publish its original values"

      let consumer ← CellTransaction.begin kernel.ledger
      try
        let function ← markValue kernel.marks selected selectTerm
        let argument ← markValue kernel.marks input inputTerm
        let failure : Option Exception ← try
          discard <| kernel.run consumer context {} (mkApp function argument) none
          pure none
        catch error => pure (some error)
        let some failure := failure
          | throwError "a lazy descriptor prefix fabricated its absent native field"
        unless CasCatalogue.Exception.stratum? failure == some .noImplementation do
          throw failure
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the native lazy descriptor control dispatched a provider"
      finally discard <| consumer.abort
    finally kernel.close
  finally setEnv original

-- Fresh projection requests reuse the published field of one exact lazy parent. Equal
-- fields at another path or parent are independent, and an older snapshot sees no new data.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
    let pairSource ← context.close pairTerm
    let pairRole ← SourceLayout.ofTerm pairSource
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let code ← owners.identities.fresh .program
      kernel.codes.modify (·.insert code (.term pairSource))
      let produced ← kernel.ledger.allocate
      let stage := producer.stage
        { program := code, occurrence := produced, role := pairRole, parameters := #[] }
        (.closure code #[])
      let input ← stage
      let other ← stage
      unless input.value != other.value do
        throwError "the published lazy projection control merged its original parents"
      let .ok _ ← producer.commit
        | throwError "the published lazy projection control could not publish its parents"
      let project (transaction : CellTransaction) (parent : ValueBinding) (index : Nat) :
          MetaM ValueBinding := do
        let source ← markValue kernel.marks parent pairTerm
        kernel.run transaction context {} (.proj ``Prod index source) none
      -- These cells begin at the same snapshot. Only the first one's graph is published.
      let stale ← CellTransaction.begin kernel.ledger
      let firstCell ← CellTransaction.begin kernel.ledger
      try
        let before ← stale.view
        let first ← project firstCell input 0
        let again ← project firstCell input 0
        let sibling ← project firstCell input 1
        let otherFirst ← project firstCell other 0
        unless (before.find first.value).isNone &&
            !(before.requiredOwners #[first]).isOk do
          throwError "a tentative lazy projection escaped into an older visible graph"
        let .ok published ← firstCell.commit
          | throwError "the published lazy projection control could not commit its first reads"
        let laterCell ← CellTransaction.begin kernel.ledger
        try
          let later ← project laterCell input 0
          let .ok latest ← laterCell.commit
            | throwError "the published lazy projection control could not commit its later read"
          unless latest.id != published.id do
            throwError "the published lazy projection control did not enter a new snapshot"
          for (value, parent, path) in #[
              (first, input, #[``Prod.fst]),
              (again, input, #[``Prod.fst]),
              (later, input, #[``Prod.fst]),
              (sibling, input, #[``Prod.snd]),
              (otherFirst, other, #[``Prod.fst])] do
            unless value.projectionAccesses.any (fun (actual, selectedPath) =>
                actual.value == parent.value && actual.associationIds == parent.associationIds &&
                  selectedPath == path) do
              throwError "a fresh projection request changed its original parent or field path"
          unless first.value != sibling.value && first.value != otherFirst.value &&
              sibling.value != otherFirst.value do
            throwError "published projection reuse merged distinct parent or native path identities"
          let staleValue ← project stale input 0
          let staleGraph ← stale.view
          unless staleValue.value != first.value && (staleGraph.find first.value).isNone &&
              (latest.graph.find staleValue.value).isNone do
            throwError "published projection reuse crossed an immutable snapshot boundary"
          let .error .staleSnapshot ← stale.commit
            | throwError "an older lazy projection cell published over a newer snapshot"
          unless (← SessionSnapshot.current).id == latest.id do
            throwError "an older lazy projection cell changed the current snapshot"
          unless (← kernel.dispatches.get).isEmpty do
            throwError "the native published projection control dispatched a provider"
          unless first.value == again.value && first.value == later.value do
            throwError "one lazy input field changed node across fresh requests or committed cells"
        finally discard <| laterCell.abort
      finally
        discard <| firstCell.abort
        discard <| stale.abort
    finally kernel.close
  finally setEnv original

-- An actual lazy inner record is first accessed through its enriched projection view.
-- Later plan preparation reaches that same record through the exact original input baseline.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← getEnv
  try
    let context ← ContextTelescope.capture #[]
    let pairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 11]
    let pairSource ← context.close pairTerm
    let pairRole ← SourceLayout.ofTerm pairSource
    let selectTerm ← Elab.Term.elabTermAndSynthesize
      (← `(fun (p : (Nat × Nat) × Nat) => (p.1.1, p.1))) none
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    try
      let producer ← CellTransaction.begin kernel.ledger
      let innerCode ← owners.identities.fresh .program
      kernel.codes.modify (·.insert innerCode (.term pairSource))
      let inner ← producer.stage
        { program := innerCode, occurrence := ← kernel.ledger.allocate,
          role := pairRole, parameters := #[] }
        (.closure innerCode #[])
      let markedInner ← markValue kernel.marks inner pairTerm
      let outerTerm ← mkAppM ``Prod.mk #[markedInner, mkNatLit 13]
      let outerSource ← context.close outerTerm
      let outerCode ← owners.identities.fresh .program
      kernel.codes.modify (·.insert outerCode (.term outerSource))
      let outer ← producer.stage
        { program := outerCode, occurrence := ← kernel.ledger.allocate,
          role := ← SourceLayout.ofTerm outerSource, parameters := #[] }
        (.closure outerCode #[inner])
      let selected ← kernel.run producer context {} selectTerm none
      let graph ← producer.view
      for parent in #[outer, inner] do
        let .error _ := graph.project parent 0
          | throwError "the lazy intermediate control already has stored field identities"
      let .ok _ ← producer.commit
        | throwError "the lazy intermediate control could not publish its original records"

      let consumer ← CellTransaction.begin kernel.ledger
      try
        let markedOuter ← markValue kernel.marks outer outerTerm
        let innerProjection := mkProj ``Prod 0 markedOuter
        let accessedInner ← kernel.run consumer context {} innerProjection none
        unless accessedInner.value == inner.value &&
            accessedInner.associationIds != inner.associationIds &&
            accessedInner.projectionAccesses.any (fun (parent, path) =>
              parent.value == outer.value && parent.associationIds == outer.associationIds &&
                path == #[``Prod.fst]) do
          throwError "the lazy intermediate control did not retain its enriched parent view"
        let markedAccess ← markValue kernel.marks accessedInner innerProjection
        let first ← kernel.run consumer context {} (mkProj ``Prod 0 markedAccess) none
        unless first.projectionAccesses.any (fun (parent, path) =>
            parent.value == accessedInner.value &&
              parent.associationIds == accessedInner.associationIds &&
              path == #[``Prod.fst]) do
          throwError "the lazy intermediate field lost its actual first access parent"

        let request ← prepare kernel consumer (← owners.identities.fresh .program) context
          selected #[outerTerm] #[outer]
        let some plan ← request.inputResultPlan (← consumer.view)
          | throwError "the retained lazy intermediate did not supply complete result coverage"
        -- No resolver is supplied: both selections must already be visible graph relations.
        let resolved ← plan.resolve (liftM (m := IO) consumer.view)
        let some planned := resolved.selections.find? (·.path == #[``Prod.fst])
          | throwError "the lazy intermediate plan lost its deeper selected field"
        unless planned.value.value == first.value && planned.input.parent.value == outer.value &&
            planned.input.parent.associationIds == outer.associationIds &&
            planned.input.path == #[``Prod.fst, ``Prod.fst] do
          throwError "plan preparation changed the retained lazy intermediate field or source path"
        let function ← markValue kernel.marks selected selectTerm
        let result ← kernel.run consumer context {} (mkApp function markedOuter) none
        let graph ← consumer.view
        let .ok deep := graph.project result 0
          | throwError "the lazy intermediate result lost its deeper field"
        let .ok retained := graph.project result 1
          | throwError "the lazy intermediate result lost its original inner record"
        unless deep.value == first.value && retained.value == inner.value do
          throwError "the input result recreated an already retained lazy intermediate selection"
        for (value, path) in #[
            (deep, #[``Prod.fst, ``Prod.fst]), (retained, #[``Prod.fst])] do
          unless value.projectionAccesses.any (fun (parent, selectedPath) =>
              parent.value == outer.value && parent.associationIds == outer.associationIds &&
                selectedPath == path) do
            throwError "the lazy intermediate result lost its complete original access path"
        unless (← kernel.dispatches.get).isEmpty do
          throwError "the native lazy intermediate control dispatched a provider"
      finally discard <| consumer.abort
    finally kernel.close
  finally setEnv original

end CasRuntime.InputResultTests
