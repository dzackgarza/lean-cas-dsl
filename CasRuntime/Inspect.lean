module

public import CasRuntime.Session
public import CasCompiler.SourceSnapshot
public import CasCompiler.SourceMethod
public import CasCompiler.OperationFamily
public import CasCompiler.SourceMember
public import CasCompiler.ReadMember
public import CasCompiler.ReadProjection
public import CasCompiler.ReadDispatch

public section

namespace CasRuntime.Inspect

open Lean Meta Elab Term CasCompiler CasCatalogue CasTools

/-- A declaration observation is prepared from the actual retained source binding,
not from the carrier or the name of a resulting Lean expression. Its data are
inert and may be shared by all committed observations of one source scope. -/
structure BindingObservation where
  binding : BindingId
  name : String
  type : String
  details : Json
  members : Array String

private def contextDocument (source : SourceContextObservation) : Json := Id.run do
  let build : StateM NativeExpression.Builder (List (String × Json) × Array Nat) := do
    let context ← ContextSnapshot.contextJson source.context
    let categories ← source.context.entries.mapM fun entry =>
      (source.categoryFor entry.id).mapM SourceSnapshot.categoryJson
    let ringVariables ← source.context.entries.mapM fun entry =>
      SourceSnapshot.ringVariablesJson (source.ringsFor entry.id)
    let declarations ← source.context.nativeDeclarations.constants.mapM
      (NativeExpression.constantInfoJson NativeExpression.Builder.add)
    let roots ← source.context.entries.mapM fun entry =>
      NativeExpression.Builder.add entry.type
    return ([
      ("context", context), ("instances", ContextSnapshot.instancesJson source.context),
      ("categories", toJson categories), ("ringVariables", toJson ringVariables),
      ("declarations", toJson declarations),
      ("descriptions", toJson source.descriptions),
      ("spans", toJson (source.spans.map SourceSnapshot.spanJson))], roots)
  let ((fields, roots), builder) := build.run {}
  return Json.mkObj (fields ++ [("nativeExpressions", builder.finish roots)])

/-- Exact registration information, not an inferred name for a backend routine.
The executable configuration is retained separately from any actual routine
observations returned during negotiation-authorized execution. -/
private def registrationDocument (kernel : Kernel) (identity : DispatchIdentity) : Json :=
  let registration := identity.registration
  let backend := kernel.manifest.backends.find? (·.name == registration.backend)
  Json.mkObj [
    ("operation", toJson registration.operation), ("input", toJson registration.input),
    ("backend", toJson registration.backend),
    ("manifestSha256", toJson identity.manifestDigest),
    ("profileSha256", toJson identity.profileDigest),
    ("command", toJson (backend.map (·.command))),
    ("arguments", toJson (backend.map (·.args)))]

private def ownerDocument (owner : ConnectionGeneration) : Json :=
  Json.mkObj [("worker", toJson owner.worker), ("serial", toJson owner.serial)]

private def producerDocument (kernel : Kernel) (producer : CompletionProducer) : Json :=
  match producer with
  | .kernel => Json.mkObj [("kind", "kernel")]
  | .invocation dispatch scope requestId =>
    let target := match dispatch.selected with
      | .primitive identity => registrationDocument kernel identity
      | .native value _ => Json.mkObj [("nativeValue", Observation.identityJson value)]
    Json.mkObj [
      ("kind", "invocation"), ("target", target),
      ("connection", ownerDocument dispatch.connection),
      ("scope", Observation.identityJson scope), ("requestId", toJson requestId),
      ("occurrence", Observation.identityJson dispatch.occurrence),
      ("transaction", Observation.identityJson dispatch.transaction)]

private def completionDocument (kernel : Kernel) (association : CompletionAssociation) : Json :=
  let observation := association.request.observation
  Json.mkObj [
    ("producer", producerDocument kernel association.producer),
    ("routines", toJson (association.routines.map fun frame => Json.mkObj [
      ("connection", ownerDocument frame.connection),
      ("scope", Observation.identityJson frame.scope),
      ("requestId", toJson frame.requestId),
      ("occurrence", Observation.identityJson frame.occurrence),
      ("observations", toJson frame.observations)])),
    ("native", observation.native), ("readable", observation.readable),
    ("selection", toJson observation.selection),
    ("sourceSnapshot", toJson observation.sourceSnapshot),
    ("result", Observation.identityJson association.response.root.value)]

/-- The graph's actual source role and exact supplying occurrence are observed
without forcing a field, reconstructing a closure, or asking any provider.
Availability at preparation is explicitly distinct from the immutable
mathematical data and exact owner dependency identities. -/
private def retainedValue (session : KernelSession) (transaction : CellTransaction)
    (graph : ValueGraph) (binding : ValueBinding) : IO Json := do
  let some node := graph.find binding.value
    | throw (IO.userError "the retained source binding has no actual value node")
  let owners ← IO.ofExcept ((graph.requiredOwners #[binding]).mapError IO.userError)
  let available ← session.kernel.ledger.owners.allAlive owners
  let completion ← transaction.completionFor? node.origin.occurrence
  let occurrences := (#[node.origin.occurrence] ++
    binding.applications.map (·.association.occurrence) ++
    binding.instantiations.map (·.association.occurrence)).toList.eraseDups.toArray
  let completions ← occurrences.filterMapM fun occurrence => do
    return (← transaction.completionFor? occurrence).map (completionDocument session.kernel)
  -- Inspect only the stored packet representation, never an exported token or
  -- a delayed program. The original native role is retained separately.
  let packet ← IO.ofExcept ((graph.packet? binding).mapError IO.userError)
  return Json.mkObj [
    ("reference", Observation.identityJson binding.value),
    ("occurrence", Observation.identityJson node.origin.occurrence),
    ("program", Observation.identityJson node.origin.program),
    ("associations", toJson (binding.associationIds.map Observation.identityJson)),
    ("owners", toJson (owners.map ownerDocument)),
    ("availableAtPreparation", toJson available),
    ("hasPacket", toJson packet.isSome), ("packet", toJson packet),
    ("completion", toJson (completion.map (completionDocument session.kernel))),
    ("completions", toJson completions)]

/-- List the frozen registration forms permitted for an independently selected
source family. This is an inventory of forms, not a claim that an arbitrary
future operand matches a form or that a provider is currently live. -/
private def permittedForms (kernel : Kernel) (state : SemanticState)
    (target : ProfileTarget) : MetaM (Array Json) := do
  let selected ← kernel.manifest.registrations.filterM fun row => do
    if !kernel.profile.allowsRegistration target row then return false
    match target with
    | .computation reference => return (← publishedFamily? state row.operation) == some reference
    | .application id => return !applicationAddressConflict state row.operation &&
        (publishedApplication? state row.operation).any (·.id == id)
    | .property id => return (publishedProperty? state row.operation).any (·.id == id)
    | .presentation id => return (publishedPresentation? state row.operation).any (·.id == id)
    | .lift id => return (← publishedLift? state row.operation).any (·.1.id == id)
  return selected.map fun row =>
    Json.mkObj [("operation", toJson row.operation), ("input", toJson row.input),
      ("backend", toJson row.backend)]

/-- Close an already chosen category interface, including its dependent carrier and
limit data, in the exact original native scope. None of these expressions is evaluated. -/
private def closeSelection (context : OpenContext) (category : NativeSourceCategory) :
    MetaM (StateM NativeExpression.Builder Json) := do
  let bundle ← context.close category.bundle
  let carrier ← category.carrier.mapM fun carrier => do
    let actions ← carrier.actions.mapM context.close
    let comparisons ← carrier.comparisons.mapM context.close
    return (⟨carrier.refs, carrier.target, carrier.identifications, actions, comparisons⟩ :
      SourceCarrierSelection)
  let limit ← category.limit.mapM fun limit => do
    let cone ← context.close limit.cone
    let bundle ← context.close limit.bundle
    let presentation ← context.close limit.presentation
    let diagram ← context.close limit.diagram
    let interface ← limit.interface.mapM context.close
    return (⟨limit.row, limit.declaration, cone, limit.colimit, limit.category, bundle,
      presentation, diagram, interface⟩ : SourceLimitSelection)
  return do
    let bundle ← ContextSnapshot.closedTermJson bundle
    let carrier ← carrier.mapM SourceSnapshot.carrierJson
    let limit ← limit.mapM SourceSnapshot.limitJson
    return Json.mkObj [
      ("role", toJson <| match category.role with
        | .object => "object" | .morphism => "morphism"),
      ("expression", toJson (reprStr category.expression)),
      ("bundle", bundle), ("carrier", toJson carrier), ("limit", toJson limit)]

/-- Freeze an actual checked judgement, retaining both its complete native type
and its selected mathematical interface, in the same expression graph. -/
private def judgementDocument (context : OpenContext)
    (judgement : NativeSourceJudgement) : TermElabM Json := do
  let term ← context.close judgement.value
  let selection ← judgement.category.mapM (fun selected => liftM (closeSelection context selected))
  let build : StateM NativeExpression.Builder (Json × Option Json × Array Nat) := do
    let native ← ContextSnapshot.closedTermJson term
    let category ← selection.mapM id
    let expression ← NativeExpression.Builder.add term.expression
    let type ← NativeExpression.Builder.add term.type
    return (native, category, #[expression, type])
  let ((native, category, roots), builder) := build.run {}
  return Json.mkObj [
    ("type", toJson (← ppExpr (← inferType judgement.value)).pretty),
    ("native", native), ("category", toJson category),
    ("nativeExpressions", builder.finish roots)]

/-- Freeze an actual typed operation family before its additional operands are supplied.
The independent source row fixes the registration address; it does not select a provider. -/
private def candidateDocument (kernel : Kernel) (state : SemanticState)
    (context : OpenContext) (kind name id : String) (target : ProfileTarget)
    (route : Option Route) (expression : Expr) : TermElabM Json := do
  let document ← judgementDocument context ⟨expression, none⟩
  return document
    |>.setObjVal! "kind" (toJson kind)
    |>.setObjVal! "name" (toJson name)
    |>.setObjVal! "id" (toJson id)
    |>.setObjVal! "route" (toJson (route.map fun route => reprStr route.refs))
    |>.setObjVal! "status" (toJson "typed_candidate")
    |>.setObjVal! "permittedRegistrationForms" (toJson (← permittedForms kernel state target))

private def memberCandidateDocument (kernel : Kernel) (state : SemanticState)
    (context : OpenContext) (name : String) (choice : SourceMemberChoice SourceReader.MemberEvidence) :
    TermElabM Json := do
  let (kind, id, target) : String × Option String × Option ProfileTarget :=
    match choice.evidence with
    | .projection => ("projection", none, none)
    | .image => ("image", none, none)
    | .method choice =>
      let entry := choice.evidence.family.entry
      ("method", some entry.id.raw, some (.computation (.method entry.id)))
    | .family row _ => ("morphism", some row.id.raw, some (.computation (.morphism row.id)))
    | .property choice =>
      let entry := choice.evidence.family.entry
      ("property", some entry.id.raw, some (.property entry.id))
    | .element row => ("element", some row.id.raw, some (.computation (.morphism row.id)))
  let document ← judgementDocument context choice.judgement
  let route ← choice.path.route?
  return document
    |>.setObjVal! "kind" (toJson kind)
    |>.setObjVal! "name" (toJson name)
    |>.setObjVal! "id" (toJson id)
    |>.setObjVal! "route" (toJson (route.map fun route => reprStr route.refs))
    |>.setObjVal! "status" (toJson "typed_candidate")
    |>.setObjVal! "permittedRegistrationForms"
      (toJson ((← target.mapM (fun target => liftM (permittedForms kernel state target))) |>.getD #[]))

/-- Prepare the same zero-additional-argument member that source syntax would select.
The retained receiver is passed directly, never reparsed or reread. An ambiguous
member retains its original typed alternatives but contributes no completion name. -/
private def observeMember (kernel : Kernel) (state : SemanticState)
    (context : OpenContext) (receiver : NativeSourceJudgement)
    (name : String) : TermElabM (Option (Json × Bool)) := do
  let saved ← saveState
  let reader : ReadContext := {
    categoryOf := fun _ => pure none
    source := ⟨← getRef⟩
    expected := none
    qualification := none
    expectedCategory := none
    project := readProjection
    read := fun _ _ _ _ _ => throwError "observation cannot read additional source"
  }
  try
    let candidates ← SourceReader.memberChoicesAtReceiver reader receiver name #[] none
    let baseline ← saveState
    let alternatives ← candidates.choices.mapM fun choice => do
      choice.nativeState.restore
      memberCandidateDocument kernel state context name choice
    baseline.restore
    if alternatives.isEmpty && candidates.mismatches.isEmpty then
      discard <| sourceMemberPreference name candidates.considered #[]
      return none
    let result : Except Outcome Json ← try
        match ← SourceReader.completeMemberChoices reader (checkReadJudgementApplicable reader)
            name #[] candidates.considered candidates.choices candidates.mismatches with
        | .ok judgement =>
          pure (.ok (← judgementDocument context judgement))
        | .error message =>
          pure (.error (.invalid (← message.toString)))
      catch error =>
        pure (.error (← Outcome.ofException error))
    let base := Json.mkObj [("kind", "member"), ("name", toJson name),
      ("alternatives", toJson alternatives)]
    match result with
    | .ok selected =>
      return some (base.setObjVal! "status" (toJson "applicable")
        |>.setObjVal! "selected" selected, true)
    | .error failure =>
      return some (base.setObjVal! "status" (toJson "unresolved")
        |>.setObjVal! "outcome" (toJson failure.kind)
        |>.setObjVal! "stratum" (toJson failure.stratum?)
        |>.setObjVal! "diagnostic" (toJson failure.detail), false)
  finally
    saved.restore

/-- Specialize only the rigid source-object slot of the whole independently
registered operation. All other arguments and dependent binder types remain
native lambda data; no numeral, operand or selected structure is fabricated. -/
private partial def specializeObject (family : Expr) (index : Nat)
    (object : Expr) : MetaM Expr := do
  let .lam name type body info := family
    | throwError "the discovered operation lost its original object slot"
  if index == 0 then
    unless ← isDefEq (← inferType object) type do
      throwError "the discovered operation has a different complete source object type"
    return body.instantiate1 object
  withLocalDecl name info type fun argument => do
    mkLambdaFVars #[argument] (← specializeObject (body.instantiate1 argument) (index - 1) object)

private def observeOperation (kernel : Kernel) (state : SemanticState)
    (context : OpenContext) (receiver : NativeSourceJudgement)
    (name : String) : TermElabM (Array Json) := do
  let some category := receiver.category | return #[]
  unless category.role == .object do return #[]
  let query ← SourceRoutes.forOperation category.expression name
  let some routes ← query.finiteRoutes
    | throwUnsupportedSource "operation discovery requires the uniform source route comparison"
  let original ← saveState
  try
    let mut result := #[]
    for route in routes do
      for row in state.operationBindings route.target name do
        original.restore
        let family ← nativeOwnedFamily state category.expression category.bundle route
          row.declaration
          (fun binders => if binders.size > row.numerals then
            some (binders.size - 1 - row.numerals) else none)
          (some (``OperationEntry, row.id.raw))
        let expression ← specializeObject family.value family.objectIndex receiver.value
        discard <| levelMVarToParam (← instantiateMVars expression)
        let expression ← instantiateMVars expression
        let candidate ← candidateDocument kernel state context "operation" name row.id.raw
          (.computation (.operation row.id)) (some route) expression
        result := result.push (candidate.setObjVal! "arity" (toJson row.arity))
    return result
  finally
    original.restore

/-- Enumerate actual member competition and independently typed operation families.
Projection spellings come from the source reader; they are advertised only when
that reader selects an actual typed value. An operation still requiring an operand
is a typed family, not a promise of applicability to an invented argument. -/
private def discover (kernel : Kernel) (context : OpenContext)
    (receiver : NativeSourceJudgement) : TermElabM (Array Json × Array String) := do
  let state ← semanticState
  let mut rows := #[]
  let mut names := #[]
  let saved ← saveState
  try
    let members := state.methods.map (·.name) ++ state.properties.map (·.name) ++
      state.morphisms.map (·.name) ++ #["obj", "hom", "forward", "backward", "image"]
    for name in members.toList.eraseDups do
      saved.restore
      Core.checkSystem "source member discovery"
      try
        if let some (document, applicable) ← observeMember kernel state context receiver name then
          rows := rows.push document
          if applicable then names := names.push name
      catch error =>
        let failure ← Outcome.ofException error
        rows := rows.push (Json.mkObj [
          ("kind", "member"), ("name", toJson name), ("status", "unresolved"),
          ("outcome", toJson failure.kind), ("stratum", toJson failure.stratum?),
          ("diagnostic", toJson failure.detail)])
    if receiver.category.any (·.role == .object) then
      for name in (state.operations.map (·.name)).toList.eraseDups do
        saved.restore
        Core.checkSystem "source operation discovery"
        try
          rows := rows ++ (← observeOperation kernel state context receiver name)
        catch error =>
          let failure ← Outcome.ofException error
          rows := rows.push (Json.mkObj [
            ("kind", "operation"), ("name", toJson name), ("status", "unresolved"),
            ("outcome", toJson failure.kind), ("stratum", toJson failure.stratum?),
            ("diagnostic", toJson failure.detail)])
    return (rows, names)
  finally
    saved.restore

/-- Display only the actual new source bindings and their retained values.
The native type determines whether a packet has a scalar display convention;
an arbitrary two-slot record is never interpreted as a rational. -/
def newBindings (before after : KernelSession) (transaction : CellTransaction) :
    TermElabM (Array Json) := do
  let previous := before.source.observation.context.entries
  let frozen := after.source.observation
  let graph ← transaction.view
  let document := contextDocument frozen
  frozen.context.withOpen fun bindings => do
    let mut result := #[]
    for entry in frozen.context.entries, index in [:frozen.context.entries.size] do
      if previous.any (·.id == entry.id) then continue
      let some binding := bindings[index]?
        | throwError "the display scope lost its retained declaration"
      unless binding.id == entry.id do
        throwError "the display scope changed its retained declaration identity"
      let type ← inferType binding.expression
      let shown := frozen.descriptions[index]?.getD ""
      let shown ← if shown.isEmpty then pure (← ppExpr type).pretty else pure shown
      let nativeType ← whnf (← zetaReduce type)
      let scalar := if nativeType.isConstOf ``Rat then "rational"
        else if nativeType.isConstOf ``Nat then "natural"
        else if nativeType.isConstOf ``Int then "integer"
        else "native"
      let runtime ← (after.value? entry.id).mapM fun value =>
        liftM (m := IO) (retainedValue after transaction graph value)
      result := result.push (Json.mkObj [
        ("binding", ContextSnapshot.bindingJson entry.id), ("index", toJson index),
        ("name", toJson entry.userName.toString), ("type", toJson shown),
        ("scalarConvention", toJson scalar), ("runtime", toJson runtime),
        ("source", document)])
    return result

/-- Prepare all declarations from the actual candidate source/graph before
publication. Query code receives only these immutable JSON records; it never
reopens the source scope or reads a transaction. -/
def prepare (session : KernelSession) (transaction : CellTransaction) :
    TermElabM (Array BindingObservation) := do
  let frozen := session.source.observation
  let document := contextDocument frozen
  let graph ← transaction.view
  frozen.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let mut result := #[]
    for entry in frozen.context.entries, index in [:frozen.context.entries.size] do
      let some binding := bindings[index]?
        | throwError "the inspection scope lost its retained declaration"
      unless binding.id == entry.id do
        throwError "the inspection scope changed its retained declaration identity"
      let type ← inferType binding.expression
      let shown := frozen.descriptions[index]?.getD ""
      let shown ← if shown.isEmpty then pure (← ppExpr type).pretty else pure shown
      let runtime ← (session.value? entry.id).mapM fun value =>
        liftM (m := IO) (retainedValue session transaction graph value)
      let category ← session.source.openCategory context binding.expression.fvarId!
      let (candidates, members) ← discover session.kernel context ⟨binding.expression, category⟩
      let details := Json.mkObj [
        ("binding", ContextSnapshot.bindingJson entry.id), ("index", toJson index),
        ("source", document), ("runtime", toJson runtime),
        ("candidates", toJson candidates)]
      result := result.push ⟨entry.id, entry.userName.toString, shown, details, members⟩
    return result

end CasRuntime.Inspect
