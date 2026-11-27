module

public import CasRuntime.Limit
public import CasCompiler.RecordAction

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend




opaque Kernel.stageUniversal (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (program : RuntimeId .program)
    (captures : Array ValueBinding) : MetaM ValueBinding := do
  let .primitive (.limitUniversal family owner) universes := request.action
    | throwError "a universal producer requires its original native family"
  let cone ← request.universalCone
  let graph ← transaction.view
  let some node := graph.find cone.value
    | throwError "the universal family lost its actual completed cone"
  let some completion ← transaction.completionFor? node.origin.occurrence
    | throwError "the universal family lost its cone's original completion"
  let original := completion.request
  let .primitive (.limit presentation originalOwner) originalUniverses := original.action
    | throwError "the universal family requires an original raw-cone completion"
  unless (SelectedApplicationFamily.limit presentation).exactlyMatches (.limit family.presentation) &&
      originalUniverses == universes do
    throwError "the universal family changed its original presentation or universes"
  let selectedConstruction ← withSourceScope request fun context _ => do
    let parameters := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
    let selected ← family.presentation.ownerAt (← owner.mapM (·.inContext context))
      (← parameters.mapM (·.inContext context))
    pure selected.source.construction
  let originalConstruction ← withSourceScope original fun context _ => do
    let parameters := original.application.map (·.arguments.map (·.source.source)) |>.getD #[]
    let selected ← presentation.ownerAt (← originalOwner.mapM (·.inContext context))
      (← parameters.mapM (·.inContext context))
    pure selected.source.construction
  unless selectedConstruction == originalConstruction do
    throwError "the universal family changed its original retained construction owner"
  unless completion.response.root.value == cone.value &&
      completion.response.root.associationIds.toList.isPrefixOf cone.associationIds.toList do
    throwError "the universal family changed its actual completed cone occurrence"
  let declared := request.origin.application.map (·.arguments) |>.getD #[]
  let supplied := original.origin.application.map (·.arguments) |>.getD #[]
  unless declared.size == supplied.size && (declared.zip supplied).all (fun pair =>
      match pair with
      | (none, none) => true
      | (some left, some right) =>
        left.value == right.value && left.associationIds == right.associationIds
      | _ => false) do
    throwError "the universal family changed its cone's original parameter occurrences"
  unless captures.size == request.scope.size &&
      (captures.zip request.scope).all (fun (left, right) =>
        left.value == right.value && left.associationIds == right.associationIds) do
    throwError "the universal family changed its complete original captures"
  let .container complete := node.payload.data
    | throwError "the universal family requires the complete actual cone packet"
  unless complete.originalPacket.isSome && complete.fields.isSome do
    throwError "the universal family cannot capture an incomplete native cone"
  discard <| request.admitInputs graph
  let some parent := request.nativeParent
    | throwError "the universal family lost its complete native presentation layout"
  let #[coneField, universalField] := parent.fields.filter (·.field.wireIndex.isSome)
    | throwError "the original presentation changed its complete computational field schema"
  unless coneField.field.projection == family.presentation.coneProjection &&
      universalField.field.projection == family.projection do
    throwError "the original presentation changed its cone/universal field order"
  let draft ← transaction.draft
  let nativePrefixState ← RecordPrefix.prepare kernel.ledger.owners.identities request.program
    request.occurrence parent draft.view request.environment.bound
  let (draft, nativePrefixState, _) ← liftM (m := IO) <| draft.bindField nativePrefixState cone
  let nativePrefix ← nativePrefixState.currentField
  let origin ← nativePrefix.attachOrigin
    (← request.originFor request.source (some draft.view)) draft.view
  let (draft, value) ← liftM (m := IO) <| draft.stage origin (.closure program captures)


  match ← transaction.installDraft draft with
  | .ok () => return value
  | .error failure => transactionFailure failure




opaque Kernel.universalPredecessors (kernel : Kernel) (family : PreparedRequest)
    (transaction : CellTransaction) (inputs : Array RecordActionInput) :
    MetaM (Array (Nat × ValueBinding)) := do
  let _ := kernel
  let .primitive (.limitUniversal selected _) _ := family.action
    | throwError "native predecessor inputs require the original universal subfamily"
  let some completion ← transaction.completionFor? family.occurrence
    | throwError "the universal action lost its original completed family"
  family.requirePreparation completion.request.roles.scope
  let graph ← transaction.view
  let some node := graph.find completion.response.root.value
    | throwError "the universal action lost its original producing value"
  let some nativePrefix := node.origin.fieldPrefix
    | throwError "the universal action lost its original native predecessor frame"
  discard <| IO.ofExcept <|
    (nativePrefix.requireOrigin family.program family.occurrence family.source).mapError IO.userError
  let #[frame] := nativePrefix.frames
    | throwError "the universal action changed its original whole-presentation frame"
  unless frame.field.projection == selected.projection do
    throwError "the universal action selected another native presentation field"
  inputs.mapM fun input => do
    let some field := frame.association.layout.fields[input.sourceIndex]?
      | throwError "a universal input is outside its original native predecessor slots"
    unless field.field.projection == input.projection do
      throwError "a universal input changed its original native projection"
    let some value := frame.preceding[input.sourceIndex]?.bind id
      | throwError "a universal input has no actual original predecessor value"
    discard <| IO.ofExcept <| (graph.requiredOwners #[value]).mapError IO.userError
    return (input.sourceIndex, value)

end CasRuntime
