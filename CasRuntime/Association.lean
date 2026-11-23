module

public import CasRuntime.PreparedRequest
public import CasRuntime.Transaction

public section

namespace CasRuntime

open Lean Meta CasCompiler

/-- Reuse exact nodes under the new application's native roles and actual dependencies.
Stored projections receive separate field views, so unrelated owners do not leak between fields.
Reuse: originFor, RecordPrefix and immutable CellDraft association extensions. -/
partial def PreparedRequest.associateResult (request : PreparedRequest) (supply : IdentitySupply)
    (source : SourceLayout) (draft : CellDraft) (value : ValueBinding) :
    MetaM (CellDraft × ValueBinding) := do
  let candidate ← request.environment.checkResult draft.view source value
  if request.origin.application.isNone && request.origin.access.isNone then
    return (← liftM (m := IO) <| draft.retain candidate.root, candidate.root)
  let some node := draft.view.find candidate.root.value
    | throwError "the reused result is outside its isolated graph"
  let stored := match node.payload.data with
    | .product _ | .container _ => true
    | _ => false
  let mut draft := draft
  let mut selected := #[]
  if source.kind == .record && stored then
    let layout ← RecordLayout.ofSource source
    let mut record ← liftM (m := IO) <|
      RecordPrefix.begin supply request.program request.occurrence layout
    for prepared in layout.fields do
      if let some index := prepared.field.wireIndex then
        let actual ← IO.ofExcept <|
          (draft.view.project candidate.root index).mapError IO.userError
        let (nextDraft, binding) ← request.associateResult supply prepared.layout draft actual
        let (nextDraft, nextRecord, binding) ← liftM (m := IO) <|
          nextDraft.bindField record binding
        draft := nextDraft
        record := nextRecord
        selected := selected.push binding
    discard <| IO.ofExcept <| record.finish.mapError IO.userError
  let origin ← request.originFor source
  if origin.access.isSome then
    liftM (m := IO) <| draft.bindProjection origin candidate.root selected
  else if origin.application.isSome then
    liftM (m := IO) <| draft.bindApplication origin candidate.root selected
  else
    return (← liftM (m := IO) <| draft.retain candidate.root, candidate.root)

end CasRuntime
