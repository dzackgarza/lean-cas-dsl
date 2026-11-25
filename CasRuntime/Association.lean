module

public import CasRuntime.PreparedRequest
public import CasRuntime.Transaction
public import CasRuntime.FixedInput

public section

namespace CasRuntime

open Lean Meta CasCompiler

private def fixedResultAt (request : PreparedRequest) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding) (fixed : Array FixedResult) (complete : Bool) :
    MetaM (Option FixedResult) := do
  let path ← request.source.projectionPathTo source
  if let some retained := fixed.find? (fun entry => entry.path.toList.isPrefixOf path.toList) then
    let suffix := path.extract retained.path.size path.size
    let selected := { retained.input with parent := retained.value, path := suffix }
    return some ⟨path, { retained.input with path := retained.input.path ++ suffix },
      ← selected.storedValue graph⟩
  if complete then return none
  let some input ← request.fixedInputFor graph source | return none
  let selected ← match ← input.storedValue? graph with
    | some selected => pure selected
    | none =>
      match ← IO.ofExcept <| (graph.projectionBasis value input.parent input.path).mapError IO.userError with
      | some selected => pure selected
      | none => input.storedValue graph
  return some ⟨path, input, selected⟩

/-- Resolve the materialized portion of an existing result before opening a reply draft.
Lazy record descendants remain demands. The resolver is used only for lazy source-selected
inputs, with a fresh graph after each demand; stored inputs keep their original bindings. -/
partial def PreparedRequest.resolveFixedResults (request : PreparedRequest)
    (transaction : CellTransaction) (source : SourceLayout) (value : ValueBinding)
    (resolve : Option (FixedInput → MetaM ValueBinding) := none) :
    MetaM (Array FixedResult) := do
  let select := fun (input : FixedInput) => do
    input.resolveValue (liftM (m := IO) transaction.view) resolve
  let graph ← transaction.view
  let input ← request.fixedInputFor graph source
  if let some input := input then
    let selected ← match ← input.storedValue? (← transaction.view) with
      | some selected => pure selected
      | none =>
        let graph ← transaction.view
        match ← IO.ofExcept <| (graph.projectionBasis value input.parent input.path).mapError IO.userError with
        | some selected => pure selected
        | none => select input
    -- Existing replies must preserve the exact input before later fields are checked.
    -- Reuse the same baseline guard as association, without staging or changing a path.
    unless value.value == selected.value &&
        selected.associationIds.toList.isPrefixOf value.associationIds.toList do
      CasCatalogue.throwStratum .malformed "the reply changed a fixed source input"
    return #[⟨← request.source.projectionPathTo source, input, selected⟩]
  let graph ← transaction.view
  let some node := graph.find value.value
    | throwError "the reused result is outside its isolated graph"
  let stored := node.payload.data.storedFields?.isSome
  if source.kind != .record || !stored then return #[]
  let mut fixed := #[]
  for prepared in (← RecordLayout.ofSource source).fields do
    if let some index := prepared.field.wireIndex then
      let graph ← transaction.view
      let actual ← IO.ofExcept <| (graph.project value index).mapError IO.userError
      fixed := fixed ++ (← request.resolveFixedResults transaction prepared.layout actual resolve)
  return fixed

/-- Associate the descendants of one already fully checked candidate. Recursive validation
has checked every stored field before this private routine adds any consuming association. -/
private partial def associateCheckedResult (request : PreparedRequest) (supply : IdentitySupply)
    (source : SourceLayout) (draft : CellDraft) (candidate : CandidateResponse source)
    (fixed : Array FixedResult) (complete : Bool) :
    MetaM (CellDraft × ValueBinding) := do
  let retained ← fixedResultAt request draft.view source candidate.root fixed complete
  let mut draft := draft
  if let some retained := retained then
    unless candidate.root.value == retained.value.value &&
        retained.value.associationIds.toList.isPrefixOf candidate.root.associationIds.toList do
      CasCatalogue.throwStratum .malformed "the reply changed a fixed source input"
    let input := retained.input
    if !input.path.isEmpty && (← IO.ofExcept <|
        (draft.view.projectedAccess? input.parent input.path).mapError IO.userError).isNone then
      -- Publish the original native input access before an output field can become the
      -- first full-path view. The saved baseline never acquires output associations.
      let currentDraft := draft
      draft ← input.source.withOpen fun bindings _ => do
        unless input.parameters.size == bindings.size do
          throwError "a fixed input lost its original complete source context"
        let context ← ContextTelescope.capture bindings
        let mut parameters := #[]
        for (binding, value) in bindings.zip input.parameters do
          if let some value := value then
            let .ok parameter := RuntimeParameter.ofValue currentDraft.view binding.id value
              | throwError "a fixed input parameter is outside its original graph"
            parameters := parameters.push parameter
        let sourceParameters := parameters
        let publishSource := fun (projection : PreparedRequest) (sourceDraft : CellDraft)
            (baseline : ValueBinding) => do
          let projection := projection.withSourceSnapshot request.observation.sourceSnapshot
          let .project parent field := projection.action
            | throwError "a fixed input lost its prepared native projection"
          let checked ← projection.environment.checkProjectionResult sourceDraft.view
            projection.source baseline parent field
          let (nextDraft, access) ← associateCheckedResult projection supply
            projection.source sourceDraft checked #[] true
          discard <| projection.admitResult nextDraft.view access
          return (nextDraft, access)
        let prepareField := fun (sourceDraft : CellDraft) (parent : ValueBinding)
            (projection : Name) => do
          let some index := parent.role.fields.findIdx? (·.projection == projection)
            | throwError "a fixed input lost its original native field position"
          PreparedRequest.forProjection supply request.program (← supply.fresh .occurrence)
            context sourceDraft.view parent index sourceParameters
        let frontier ← IO.ofExcept <|
          (currentDraft.view.projectionFrontier input.parent input.path).mapError IO.userError
        let some (parent, remaining) := frontier
          | throwError "a fixed input has no available native field interface"
        if !remaining.isEmpty then
          unless remaining.size == 1 do
            throwError "a fixed input has no independently available intermediate parent"
          let some _ ← IO.ofExcept <|
              (currentDraft.view.projectionBasis retained.value input.parent input.path).mapError IO.userError
            | throwError "a fixed input lost its exact original pending projection"
        let mut sourceDraft := currentDraft
        if input.path.size > 1 && !remaining.isEmpty then
          let sourcePrefix := input.path.extract 0 (input.path.size - 1)
          let projection ← PreparedRequest.forStoredProjection supply request.program
            (← supply.fresh .occurrence) context sourceDraft.view input.parent sourcePrefix sourceParameters
          let (nextDraft, parentAccess) ← publishSource projection sourceDraft parent
          sourceDraft := nextDraft
          let some last := input.path.back?
            | throwError "a fixed input lost its original final field"
          let projection ← prepareField sourceDraft parentAccess last
          let (nextDraft, _) ← publishSource projection sourceDraft retained.value
          sourceDraft := nextDraft
        let projection ← if input.path.size == 1 then do
            let some field := input.path[0]?
              | throwError "a fixed input lost its original native field"
            prepareField sourceDraft input.parent field
          else
            PreparedRequest.forStoredProjection supply request.program
              (← supply.fresh .occurrence) context sourceDraft.view input.parent input.path sourceParameters
        let (completedDraft, _) ← publishSource projection sourceDraft retained.value
        return completedDraft
  if request.origin.application.isNone && request.origin.access.isNone && retained.isNone then
    return (← liftM (m := IO) <| draft.retain candidate.root, candidate.root)
  let some node := draft.view.find candidate.root.value
    | throwError "the reused result is outside its isolated graph"
  let stored := node.payload.data.storedFields?.isSome
  let mut selected := #[]
  if source.kind == .record && stored then
    let layout ← RecordLayout.ofSource source
    let mut record ← RecordPrefix.prepare supply request.program request.occurrence layout
      draft.view request.environment.sourceMarks
    for prepared in layout.fields do
      if let some index := prepared.field.wireIndex then
        let actual ← IO.ofExcept <|
          (draft.view.project candidate.root index).mapError IO.userError
        let candidate ← IO.ofExcept <|
          (CandidateResponse.ofValue prepared.layout draft.view actual).mapError IO.userError
        let (nextDraft, binding) ← associateCheckedResult request supply prepared.layout draft
          candidate fixed complete
        let (nextDraft, nextRecord, binding) ← liftM (m := IO) <|
          nextDraft.bindField record binding
        draft := nextDraft
        record := nextRecord
        selected := selected.push binding
    discard <| IO.ofExcept <| record.finish.mapError IO.userError
  let origin ← request.originFor source (some draft.view)
  let mut value := candidate.root
  if let some retained := retained then
    if !retained.input.path.isEmpty then
      let original ← IO.ofExcept <|
        (draft.view.applicationOrigin retained.input.parent).mapError IO.userError
      let mut application := original
      for projection in retained.input.path do
        application ← application.mapM (·.forProjection projection)
      let inputOrigin : ValueOrigin := { origin with
        application := application
        access := some retained.input.parent
        accessPath := retained.input.path }
      let (next, selectedValue) ← draft.bindProjection inputOrigin value selected
      draft := next
      value := selectedValue
  if origin.access.isSome then
    draft.bindProjection origin value selected
  else if origin.application.isSome then
    liftM (m := IO) <| draft.bindApplication origin value selected
  else
    return (← liftM (m := IO) <| draft.retain value, value)

/-- Reuse exact nodes under the new application's native roles and actual dependencies.
The actual projection request supplies its one pending edge only during complete candidate
validation. Stored descendants are then associated in this isolated reply; ordinary result
admission rechecks their published paths before installation.
Reuse: originFor, RecordPrefix and immutable CellDraft association extensions. -/
def PreparedRequest.associateResult (request : PreparedRequest) (supply : IdentitySupply)
    (source : SourceLayout) (draft : CellDraft) (value : ValueBinding)
    (fixed : Array FixedResult := #[]) (complete : Bool := false) :
    MetaM (CellDraft × ValueBinding) := do
  let candidate ← match request.action with
    | .project operand field =>
      if source.address == request.source.address then
        request.environment.checkProjectionResult draft.view source value operand field
      else request.environment.checkResult draft.view source value
    | .primitive (.limitUniversal _ _) _ => do
      let fieldPrefix ← request.resultFieldPrefix draft.view value
      request.environment.checkResult draft.view source value fieldPrefix
    | .apply .. | .primitive .. => request.environment.checkResult draft.view source value
  associateCheckedResult request supply source draft candidate fixed complete

/-- Carry the authenticated source access into an assembled input result while its sealed
selection and the graph's projection cache retain the original baseline. A stored source
path without an earlier access is admitted through the ordinary original projection. -/
private def selectedInputView (request : PreparedRequest) (supply : IdentitySupply)
    (selected : FixedResult) (draft : CellDraft) : MetaM (CellDraft × ValueBinding) := do
  let input := selected.input
  if input.path.isEmpty then return (draft, selected.value)
  let existing ← IO.ofExcept <|
    (draft.view.projectedAccess? input.parent input.path).mapError IO.userError
  let (draft, access) ← match existing with
    | some access => pure (draft, access)
    | none => input.source.withOpen fun bindings _ => do
      unless input.parameters.size == bindings.size do
        throwError "a fixed input lost its original complete source context"
      let context ← ContextTelescope.capture bindings
      let mut parameters := #[]
      for (binding, value) in bindings.zip input.parameters do
        if let some value := value then
          let parameter ← IO.ofExcept <|
            (RuntimeParameter.ofValue draft.view binding.id value).mapError IO.userError
          parameters := parameters.push parameter
      let projection ← PreparedRequest.forStoredProjection supply request.program
        (← supply.fresh .occurrence) context draft.view input.parent input.path parameters
      let projection := projection.withSourceSnapshot request.observation.sourceSnapshot
      let (draft, access) ← projection.associateResult supply projection.source draft
        selected.value #[] (complete := true)
      discard <| projection.admitResult draft.view access
      return (draft, access)
  let some baseline ← IO.ofExcept <|
      (draft.view.projectionBasis access input.parent input.path).mapError IO.userError
    | throwError "an assembled input lost its exact original source access"
  unless baseline.value == selected.value.value &&
      baseline.associationIds.toList.isPrefixOf selected.value.associationIds.toList &&
      selected.value.value == access.value &&
      selected.value.associationIds.toList.isPrefixOf access.associationIds.toList do
    throwError "an assembled input access changed its original selected occurrence"
  return (draft, access)

private partial def assembleInputResult (request : PreparedRequest) (source : SourceLayout)
    (supply : IdentitySupply) (fixed : Array FixedResult) (draft : CellDraft) :
    MetaM (CellDraft × ValueBinding) := do
  let path ← request.source.projectionPathTo source
  if let some selected := fixed.find? (·.path == path) then
    return ← selectedInputView request supply selected draft
  unless source.kind == .record do
    throwError "the complete input result lost a prepared computational field"
  let layout ← RecordLayout.ofSource source
  let mut draft := draft
  let mut fields := #[]
  for prepared in layout.fields do
    if prepared.field.wireIndex.isNone then continue
    let (nextDraft, value) ← assembleInputResult request prepared.layout supply fixed draft
    draft := nextDraft
    fields := fields.push value
  -- The original views are checked against the complete actual result prefix first.
  -- associateCheckedResult alone adds the result's new consuming field associations.
  liftM (m := IO) <| draft.stage (← request.originFor source (some draft.view)) (.product fields)

/-- Assemble the complete source-selected result after all selected lazy inputs have settled.
Validate its stored fields together with their actual native prefixes before adding consuming
associations. The isolated draft remains unpublished until the complete result is admitted.
Reuse: RecordPrefix, whole-result associateResult and the sealed input-result admission check. -/
def ResolvedInputResult.assemble (resolved : ResolvedInputResult request)
    (transaction : CellTransaction) : MetaM (CellDraft × InputResultCompletion request) := do
  let traced := (request.source.source.expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  let draft ← transaction.draft
  if traced then dbg_trace "[inclusion.stage] assembly {repr request.occurrence}: before raw tree"
  let (draft, value) ← assembleInputResult request request.source transaction.owners.identities
    resolved.selections draft
  if traced then dbg_trace "[inclusion.stage] assembly {repr request.occurrence}: before whole association"
  let (draft, value) ← request.associateResult transaction.owners.identities
    request.source draft value resolved.selections (complete := true)
  if traced then dbg_trace "[inclusion.stage] assembly {repr request.occurrence}: before result admission"
  let response ← request.admitResult draft.view value
  if traced then dbg_trace "[inclusion.stage] assembly {repr request.occurrence}: result admitted"
  let completed ← IO.ofExcept <| (resolved.admit draft.view response).mapError IO.userError
  return (draft, completed)

end CasRuntime
