module

public import CasRuntime.PreparedRequest
public import CasRuntime.Reply
public import CasRuntime.Transaction
public import CasRuntime.Literal
public import CasRuntime.Association
public import CasRuntime.FixedInput
public import CasRuntime.FixedValue

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue.Backend

private def stageResult (request : PreparedRequest) (source : SourceLayout)
    (draft : CellDraft) (payload : ValuePayload) : MetaM (CellDraft × ValueBinding) := do
  let origin ← request.originFor source
  let (draft, binding) ← liftM (m := IO) <| draft.stage origin payload
  let candidate ← request.environment.checkResult draft.view source binding
  return (draft, candidate.root)

/-- The released complete record packet, including single-data-field collapse. -/
private def recordReplyPositions (count : Nat) (value : Json) :
    MetaM (Array (Array InputPathStep × Json)) := do
  if count == 1 then return #[(#[], value)]
  let .ok values := value.getArr?
    | throwError "the reply record requires its complete ordered data fields"
  unless values.size == count do
    throwError "the reply record has a different prepared data-field arity"
  return values.mapIdx fun index value => (#[.index index], value)

/-- Resolve fixed source inputs before taking an isolated draft. Inline positions follow the
same record/envelope grammar as materialization; references reuse stored-field preflight.
Reuse: resolveFixedResults, fixedInputFor and prepared native result projection paths. -/
private partial def preflightFixedResults (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (resolve : Option (FixedInput → MetaM ValueBinding))
    (source : SourceLayout) (value : Json) (path : Array InputPathStep) :
    MetaM (Array FixedResult) := do
  if let some reference := reply.references.find? (·.path == path) then
    return ← request.resolveFixedResults transaction source reference.binding resolve
  let graph ← liftM (m := IO) transaction.view
  if let some input ← request.fixedInputFor graph source then
    let value ← input.resolveValue (liftM (m := IO) transaction.view) resolve
    return #[{ path := ← request.source.projectionPathTo source, input, value }]
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "valueData" || tag == some "opaqueData" then
    let .ok envelope := ComputationalValue.decode value
      | throwError "the parsed reply lost its computational value envelope"
    match envelope with
    | .inline data =>
      return ← preflightFixedResults reply request transaction resolve source data
        (path ++ #[.field "args", .index 0])
    | .opaque _ => return #[]
  if source.kind != .record then return #[]
  let layout ← RecordLayout.ofSource source
  let fields := layout.fields.filter (·.field.wireIndex.isSome)
  let positions ← recordReplyPositions fields.size value
  let mut fixed := #[]
  for prepared in fields, position in positions do
    fixed := fixed ++ (← preflightFixedResults reply request transaction resolve prepared.layout
      position.2 (path ++ position.1))
  return fixed

/-- Follow the released record/envelope encoding and native source-ordered field metadata.
Reuse: CasContract.Port computational packets, SourceLayout, RecordPrefix and ValueContainer.
Only prepared fields receive new roles; references preserve their original scope bindings. -/
private partial def materializeValue (reply : ImmediateReply) (request : PreparedRequest)
    (connection : Connection) (supply : IdentitySupply) (source : SourceLayout) (value : Json)
    (path : Array InputPathStep) (fixed : Array FixedResult) (draft : CellDraft) :
    MetaM (CellDraft × ValueBinding) := do
  let resultPath ← request.source.projectionPathTo source
  if let some selected := fixed.find? (·.path == resultPath) then
    let retained ← match reply.retainsValue draft.view connection value path selected.value with
      | .ok retained => pure retained
      | .error reason =>
        CasCatalogue.throwStratum .malformed
          m!"{reason}: the reply changed a fixed source input"
    unless retained do
      CasCatalogue.throwStratum .malformed "the reply changed a fixed source input"
    return ← request.associateResult supply source draft selected.value fixed (complete := true)
  if let some reference := reply.references.find? (·.path == path) then
    return ← request.associateResult supply source draft reference.binding fixed (complete := true)
  let tag := (value.getObjValAs? String "ctor").toOption
  if tag == some "valueData" || tag == some "opaqueData" then
    let .ok envelope := ComputationalValue.decode value
      | throwError "the parsed reply lost its computational value envelope"
    match envelope with
    | .inline data =>
      return ← materializeValue reply request connection supply source data
        (path ++ #[.field "args", .index 0]) fixed draft
    | .opaque token =>
      let some declaration := reply.exports.find? (·.token == token)
        | throwError "the parsed reply lost its native export declaration"
      unless declaration.owner == connection.generation do
        throwError "the native export belongs to a different supplying connection"
      return ← stageResult request source draft
        (.ownedExport connection token declaration.captures)
  discard <| ScalarLiteral.check source value
  match source.kind with
  | .proof => throwError "a source proof has no computational reply position"
  | .function =>
    throwError "inline callable materialization requires its prepared executable representation"
  | .record =>
    let layout ← RecordLayout.ofSource source
    let fields := layout.fields.filter (·.field.wireIndex.isSome)
    let positions ← recordReplyPositions fields.size value
    let mut draft := draft
    let mut record ← liftM (m := IO) <|
      RecordPrefix.begin supply request.program request.occurrence layout
    let mut slots : Array ContainerSlot := #[]
    let mut selected : Array ValueBinding := #[]
    for prepared in fields, position in positions do
      let (next, binding) ← materializeValue reply request connection supply prepared.layout
        position.2 (path ++ position.1) fixed draft
      draft := next
      let (nextDraft, nextRecord, binding) ← liftM (m := IO) <| draft.bindField record binding
      draft := nextDraft
      record := nextRecord
      slots := slots.push { path := position.1, binding, fieldIndex := prepared.field.wireIndex }
      selected := selected.push binding
    let .ok _ := record.finish
      | throwError "the materialized record has an incomplete formal field prefix"
    let .ok payload := ValuePayload.container value slots selected none
      | throwError "the materialized record has an invalid literal reference layout"
    stageResult request source draft payload
  | .data | .typeValue =>
    let slots := reply.references.filterMap fun reference =>
      if path.toList.isPrefixOf reference.path.toList then
        some ({
          path := reference.path.extract path.size reference.path.size
          binding := reference.binding
          fieldIndex := none } : ContainerSlot)
      else none
    let .ok payload := ValuePayload.container value slots #[] none
      | throwError "the reply has native or control data outside a prepared typed position"
    stageResult request source draft payload

/-- Materialize a parsed immediate reply into an isolated draft with native prepared roles.
Reuse: active RequestScope authority, CellDraft isolation and the source-native result checks.
This storage step creates neither a completion witness nor a published result. -/
opaque ImmediateReply.materialize (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (scope : RequestScope) (connection : Connection)
    (resolveFixed : Option (FixedInput → MetaM ValueBinding) := none) :
    MetaM (CellDraft × PreparedResponse request) := do
  unless reply.scopeId == scope.id && scope.reservation.transaction == transaction.id &&
      scope.reservation.occurrence == request.occurrence &&
      scope.reservation.connection == connection.generation do
    throwError "reply materialization changed its prepared invocation or scope"
  let graph ← liftM (m := IO) transaction.view
  discard <| liftM (m := IO) <|
    scope.resolveMany scope.reservation graph scope.wireId #[]
  let fixed ← preflightFixedResults reply request transaction resolveFixed request.source
    reply.value #[]
  let draft ← liftM (m := IO) transaction.draft
  discard <| liftM (m := IO) <|
    scope.resolveMany scope.reservation draft.view scope.wireId #[]
  let (draft, binding) ← materializeValue reply request connection transaction.owners.identities
    request.source reply.value #[] fixed draft
  let candidate ← request.admitResult draft.view binding
  return (draft, candidate)

/-- Admit and install a complete immediate reply with its exact transaction-local completion.
Publication remains the whole-cell commit transition. -/
opaque ImmediateReply.stageCompletion (reply : ImmediateReply) (request : PreparedRequest)
    (transaction : CellTransaction) (scope : RequestScope) (connection : Connection)
    (resolveFixed : Option (FixedInput → MetaM ValueBinding) := none) :
    MetaM (Except TransactionFailure CompletionAssociation) := do
  let (draft, response) ← reply.materialize request transaction scope connection resolveFixed
  transaction.completeReply draft request response scope reply

end CasRuntime
