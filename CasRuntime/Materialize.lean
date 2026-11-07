module

public import CasCompiler.Program
public import CasRuntime.Reply
public import CasRuntime.Transaction

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue.Backend

private def stageResult (request : PreparedRequest) (source : SourceLayout)
    (draft : CellDraft) (payload : ValuePayload) : MetaM (CellDraft × ValueBinding) := do
  let origin ← request.environment.origin request.program request.occurrence source
  let (draft, binding) ← liftM (m := IO) <| draft.stage origin payload
  let candidate ← request.environment.checkResult draft.view source binding
  return (draft, candidate.root)

/-- Follow the released record/envelope encoding and native source-ordered field metadata.
Reuse: CasContract.Port computational packets, SourceLayout, RecordPrefix and ValueContainer.
Only prepared fields receive new roles; references preserve their original scope bindings. -/
private partial def materializeValue (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (source : SourceLayout) (value : Json)
    (path : Array InputPathStep) (draft : CellDraft) : MetaM (CellDraft × ValueBinding) := do
  if let some reference := reply.references.find? (·.path == path) then
    let candidate ← request.environment.checkResult draft.view source reference.binding
    return (draft, candidate.root)
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "valueData" || tag == some "opaqueData" then
    let .ok envelope := ComputationalValue.decode value
      | throwError "the parsed reply lost its computational value envelope"
    match envelope with
    | .inline data =>
      return ← materializeValue reply request connection supply source data
        (path ++ #[.field "args", .index 0]) draft
    | .opaque token =>
      let some declaration := reply.exports.find? (·.token == token)
        | throwError "the parsed reply lost its native export declaration"
      unless declaration.owner == connection.generation do
        throwError "the native export belongs to a different supplying connection"
      return ← stageResult request source draft
        (.ownedExport connection token declaration.captures)
  match source.kind with
  | .proof => throwError "a source proof has no computational reply position"
  | .function =>
    throwError "inline callable materialization requires its prepared executable representation"
  | .record =>
    let layout ← RecordLayout.ofSource source
    let fields := layout.fields.filter (·.field.wireIndex.isSome)
    let positions : Array (Array InputPathStep × Json) ← if fields.size == 1 then
        pure #[(#[], value)]
      else do
        let .ok values := value.getArr?
          | throwError "the reply record requires its complete ordered data fields"
        unless values.size == fields.size do
          throwError "the reply record has a different prepared data-field arity"
        pure <| values.mapIdx fun index value => (#[.index index], value)
    let mut draft := draft
    let mut record ← liftM (m := IO) <|
      RecordPrefix.begin supply request.program request.occurrence layout
    let mut slots : Array ContainerSlot := #[]
    let mut selected : Array ValueBinding := #[]
    for prepared in fields, position in positions do
      let (next, binding) ← materializeValue reply request connection supply prepared.layout
        position.2 (path ++ position.1) draft
      draft := next
      let (next, binding) ← liftM (m := IO) <| record.bind draft.view binding
      record := next
      slots := slots.push { path := position.1, binding }
      selected := selected.push binding
    let .ok _ := record.finish
      | throwError "the materialized record has an incomplete formal field prefix"
    let .ok payload := ValuePayload.container value slots selected none
      | throwError "the materialized record has an invalid literal reference layout"
    stageResult request source draft payload
  | .data | .typeValue =>
    let slots := reply.references.filterMap fun reference =>
      if path.toList.isPrefixOf reference.path.toList then
        some ({ path := reference.path.extract path.size reference.path.size,
          binding := reference.binding } : ContainerSlot)
      else none
    let .ok payload := ValuePayload.container value slots #[] none
      | throwError "the reply has native or control data outside a prepared typed position"
    stageResult request source draft payload

/-- Materialize a parsed immediate reply into an isolated draft with native prepared roles.
Reuse: active RequestScope authority, CellDraft isolation and the source-native result checks.
This storage step creates neither a completion witness nor a published result. -/
opaque ImmediateReply.materialize (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (scope : RequestScope) (connection : Connection) :
    MetaM (CellDraft × CandidateResponse request.source) := do
  unless reply.scopeId == scope.id && scope.reservation.transaction == transaction.id &&
      scope.reservation.occurrence == request.occurrence &&
      scope.reservation.connection == connection.generation do
    throwError "reply materialization changed its prepared invocation or scope"
  let draft ← liftM (m := IO) transaction.draft
  discard <| liftM (m := IO) <|
    scope.resolveMany scope.reservation draft.view scope.wireId #[]
  let (draft, binding) ← materializeValue reply request connection transaction.owners.identities
    request.source reply.value #[] draft
  let candidate ← request.environment.checkResult draft.view request.source binding
  return (draft, candidate)

end CasRuntime
