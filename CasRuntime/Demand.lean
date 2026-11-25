module

public import CasRuntime.Invocation
public import CasRuntime.LimitUniversal
public import CasCompiler.CreationSource
public import CasCompiler.SourceReference
public import CasCompiler.SelectedField
public import CasCompiler.RecordAction

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Input addresses of this exact invocation: the complete-request form, and the exact form and
category of each argument that is a registered named object. -/
def inputForms (family : String) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM (Array String) := do
  let state ← semanticState
  -- Named morphisms publish their own raw complete-declaration request address.
  let own := if state.morphisms.any (·.id.raw == family) then family else s!"{family}#input"
  let mut forms := #[own]
  for argument in arguments do
    if let some (id, _) ← sourceObjectReference? (← argument.inContext context) then
      if let some entry := state.objects.find? (·.id == id) then
        forms := forms ++ #[entry.id.raw, entry.category.raw]
  return forms

/-- Retain a published family, or one more selected field of it, as a delayed demand. -/
def Kernel.delay (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (captures : Array ValueBinding) : MetaM (PreparedResponse request) := do
  let program ← kernel.ledger.owners.identities.fresh .program
  kernel.codes.modify (·.insert program (.family family path))
  let value ← if family.action matches .primitive (.limitUniversal _ _) _ then do
      if path.isEmpty && request.occurrence == family.occurrence then
        kernel.stageUniversal request transaction program captures
      else
        transaction.stage (← request.originFor request.source) (.closure program captures)
    else
      transaction.stage (← request.originFor request.source) (.closure program captures)
  kernelCompletion request transaction value
    (some (kernel.resolveFixedInput evaluateSource transaction request.program))

/-- Evaluate a checked source term for a claimed demand and complete that demand. -/
private def evaluateRequest (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction)
    (build : OpenContext → MetaM Expr) : MetaM (PreparedResponse request) := do
  let value ← withSourceScope request fun context bound => do
    evaluateSource transaction request.program context bound
      (← build context)
  kernelCompletion request transaction value
    (some (kernel.resolveFixedInput evaluateSource transaction request.program))

/-- Prepare record invocation inputs from the exact retained family result. Only the
source compiler determines their native slots and applications. The original completion
is selected by occurrence and preparation identity, never by expression or type. -/
private def Kernel.prepareRecordAction (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (boundary : ProgramBoundary)
    (universes : List Level) (path : Array FieldLayout) (arguments : Array ClosedTerm) :
    MetaM RecordAction := do
  withSourceScope request fun context bound => do
    let _ := bound
    let mut parent ← family.source.source.inContext context
    if !path.isEmpty then
      let some completion ← transaction.completionFor? family.occurrence
        | throwError "the delayed record lost its original completed family"
      family.requirePreparation completion.request.roles.scope
      parent ← markValue kernel.marks completion.response.root parent
    let formal := family.application.map (·.arguments.map (·.source.source)) |>.getD #[]
    let supplied := family.origin.application.map (·.arguments) |>.getD #[]
    unless formal.size == supplied.size do
      throwError "the record family lost its original complete parameter references"
    let mut parameters := #[]
    for parameter in formal, index in [:formal.size] do
      let source ← parameter.inContext context
      parameters := parameters.push (← match supplied[index]?.bind id with
        | some value => markValue kernel.marks value source
        | none => pure source)
    let values := match request.action with
      | .apply _ _ values => values
      | _ => #[]
    let mut actual := #[]
    for argument in arguments, index in [:arguments.size] do
      let source ← argument.inContext context
      actual := actual.push (← match values[index]?.bind id with
        | some value => markValue kernel.marks value source
        | none => pure source)
    RecordAction.prepare boundary universes context family.source parent path parameters actual
      family.selection

/-- Materialize only the source-prepared invocation slots, after realization selection.
The same path handles ordinary records and released record packets. -/
private def Kernel.recordInputs (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request family : PreparedRequest) (transaction : CellTransaction) (action : RecordAction) :
    MetaM (Array (Nat × ValueBinding)) := do
  let predecessors ← if action.predecessors.isEmpty then pure #[]
    else kernel.universalPredecessors family transaction action.predecessors
  let inputs ← withSourceScope request fun context bound => do
    action.inputs.mapM fun input => do
      let source ← input.source.inContext context
      return (input.sourceIndex,
        ← evaluateSource transaction request.program context bound source)
  return predecessors ++ inputs

/-- Dispatch a delayed family demand whose action has reached its actual arguments.
The selected registration receives the family parameters and the action arguments.
A selected derivation is the checked plan at those same parameters, fields and arguments. -/
partial def Kernel.reach (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (path : Array FieldLayout)
    (parameters : Array ValueBinding) (arguments : Array ClosedTerm) :
    MetaM (PreparedResponse request) := do
  let .primitive boundary universes := family.action
    | throwError "internal: a delayed family demand lost its published boundary"
  if let .limit selected _ := boundary then
    unless path.isEmpty && request.occurrence == family.occurrence do
      throwError "a raw construction changed its original complete request boundary"
    let invocation ← PreparedLimitInvocation.prepare kernel evaluateSource request transaction
    let registration ← selectLift kernel.profile kernel.manifest (.limit selected.entry.id)
      selected.operation invocation.forms
    return ← kernel.invokeLimit evaluateSource request transaction registration invocation
  if let .creation selected := boundary then
    unless path.isEmpty && request.occurrence == family.occurrence do
      throwError "a creation changed its original complete fixed request boundary"
    let invocation ← PreparedCreationInvocation.prepare kernel evaluateSource request transaction
    let registration ← selectLift kernel.profile kernel.manifest (.lift selected.family.entry.id)
      selected.operation invocation.forms
    return ← kernel.invokeCreation evaluateSource request transaction registration invocation
  if let .point selected := boundary then
    let invocation ← if selected.invocation then do
        unless path.isEmpty && request.occurrence == family.occurrence do
          throwError "a complete categorical request changed its original whole boundary"
        PreparedPointInvocation.prepare kernel request transaction
      else do
        let some invocation ← PreparedPointInvocation.prepare? kernel evaluateSource
            request family path transaction
          | throwStratum .noImplementation "the categorical field has no original scalar point interface"
        pure invocation
    let realization ← match selected.owner with
      | .named (.morphism entry) => do
        kernel.profile.select kernel.manifest
          (.morphism entry.id) invocation.operation invocation.forms
      | .action (.functor id) => do
        kernel.profile.select kernel.manifest
          (.functor id) invocation.operation invocation.forms
      | owner => do
        let target := match owner with
          | .named (.application entry) => ProfileTarget.application entry.id
          | .component entry _ _ => .component entry.id
          | .cartesian entry => .cartesian entry.id
          | .binder entry => .binder entry.id
          | .action edge => .edge ("action:" ++ (edgeImageDescriptor edge).compress)
          | .named (.morphism entry) => .computation (.morphism entry.id)
        Realization.registration <$>
          selectLift kernel.profile kernel.manifest target invocation.operation invocation.forms
    match realization with
    | .registration registration =>
      return ← kernel.invokePoint evaluateSource request transaction registration invocation
    | .derivation checked =>
      return ← evaluateRequest kernel evaluateSource request transaction fun context => do
        let (actual, _) ← family.markedArguments kernel.marks context selected.parameterCount
        let plan ← checked.instantiate universes
        let replacement := plan.betaRev
          (actual.extract 0 selected.declarationParameterCount).reverse (preserveMData := true)
        let mut arrow ← selected.realizedArrow universes actual replacement
        if selected.invocation then
          let formal := family.application.map (·.arguments.map (·.source.source)) |>.getD #[]
          let some originalDomain := formal[selected.parameterCount]?
            | throwError "the categorical derivation lost its original domain position"
          let some originalPoint := formal[selected.parameterCount + 1]?
            | throwError "the categorical derivation lost its original point position"
          let domain ← markValue kernel.marks invocation.domain
            (← originalDomain.inContext context)
          let point ← markValue kernel.marks invocation.argument
            (← originalPoint.inContext context)
          return ← selected.resultAt universes actual arrow domain point
        for field in path do arrow ← projectTerm arrow field
        let values := match request.action with | .apply _ _ values => values | _ => #[]
        let mut applied := #[]
        for argument in arguments, index in [:arguments.size] do
          let source ← argument.inContext context
          applied := applied.push (← match values[index]?.bind id with
            | some value => markValue kernel.marks value source
            | none => pure source)
        return arrow.betaRev applied.reverse (preserveMData := true)
  if let .objectAction selected := boundary then
    unless path.isEmpty && request.occurrence == family.occurrence do
      throwError "an object action changed its original complete request boundary"
    let invocation ← PreparedObjectAction.prepare kernel request (← transaction.view)
    let realization ← match selected.edge with
      | .functor id => do
        kernel.profile.select kernel.manifest (.functor id)
          invocation.operation invocation.forms
      | _ => do
        Realization.registration <$>
          selectLift kernel.profile kernel.manifest (.edge selected.operation)
            invocation.operation invocation.forms
    match realization with
    | .registration registration =>
      return ← kernel.invokeObjectAction evaluateSource request transaction registration invocation
    | .derivation checked =>
      return ← evaluateRequest kernel evaluateSource request transaction fun context => do
        let (actual, _) ← family.markedArguments kernel.marks context (selected.parameterCount + 1)
        let plan ← checked.instantiate universes
        let parameters := actual.extract 0 selected.parameterCount
        let replacement := plan.betaRev parameters.reverse (preserveMData := true)
        selected.realized universes parameters actual[selected.parameterCount]! replacement
  if let .property _ := boundary then
    unless path.isEmpty && parameters.isEmpty && request.occurrence == family.occurrence do
      throwError "a property observation lost its complete original primitive request"
    let route ← PreparedPropertyRoute.prepare kernel (← transaction.view) request
    let selected ← route.select kernel.profile kernel.manifest
    let invocation ← selected.materialize kernel evaluateSource request transaction
    return ← kernel.invokeProperty evaluateSource request transaction invocation
  if let .routedMethod _ := boundary then
    let route ← PreparedMethodRoute.prepare kernel (← transaction.view)
      request family path parameters
    let selection ← route.select kernel.profile kernel.manifest
    let selected ← selection.materialize kernel evaluateSource request transaction
    return ← match selection.realization with
      | .registration _ => do
        let invocation ← selected.invocation kernel evaluateSource request transaction
        kernel.invokeMethod evaluateSource request transaction invocation
      | .derivation _ =>
        selected.derivation kernel evaluateSource request transaction
  let selectedPath : Array Name := match boundary with
    | .limitUniversal selected _ =>
      selected.path ++ path.map (fun (field : FieldLayout) => field.projection)
    | _ => path.map (fun (field : FieldLayout) => field.projection)
  let role := "/".intercalate (selectedPath.map Name.toString).toList
  if let .presentation selected := boundary then
    let invocation ← PreparedPresentationInvocation.prepare request family path (← transaction.view)
      (← kernel.codes.get) (← kernel.marks.get)
    let registration ← selectLift kernel.profile kernel.manifest (.presentation selected.entry.id)
      invocation.operation invocation.forms
    return ← kernel.invokePresentation evaluateSource request transaction registration invocation
  if let .application selected := boundary then
    let .application entry := selected.owner
      | throwError "the delayed object application changed its exact owner kind"
    let some invocation ← PreparedPointInvocation.prepare? kernel evaluateSource request family path transaction
      | throwError "the object application lost its complete original point interface"
    let registration ← selectLift kernel.profile kernel.manifest (.application entry.id)
      invocation.operation invocation.forms
    return ← kernel.invokePoint evaluateSource request transaction registration invocation
  let action ← kernel.prepareRecordAction request transaction family boundary universes path arguments
  let point ← PreparedPointInvocation.prepare? kernel evaluateSource request family path transaction
  let address := point.map (·.operation) |>.getD action.address
  let forms ← match point with
    | some point => pure point.forms
    | none => withSourceScope request fun context _ => do
      return (← inputForms action.familyAddress context arguments)
  let realization : Realization ← match action.owner with
    | .computation reference => kernel.profile.select kernel.manifest reference address forms
    | .lift id =>
      pure (.registration (← selectLift kernel.profile kernel.manifest (.lift id) address forms))
    | .limit id =>
      pure (.registration (← selectLift kernel.profile kernel.manifest (.limit id) address forms))
  match realization with
  | .registration registration =>
    match point with
    | some point => kernel.invokePoint evaluateSource request transaction registration point
    | none => do
      let inputs ← kernel.recordInputs evaluateSource request family transaction action
      let parameters := match boundary with
        | .limitUniversal _ _ =>
          (family.origin.application.map (·.arguments.filterMap id)).getD #[]
        | _ => parameters
      kernel.invokeRegistration evaluateSource request transaction registration role parameters inputs
  | .derivation checked =>
    evaluateRequest kernel evaluateSource request transaction fun context => do
      let plan ← checked.instantiate universes
      let formal : Array ClosedTerm := match family.application with
        | none => #[]
        | some application => application.arguments.map (·.source.source)
      let supplied := family.origin.application.map (·.arguments) |>.getD #[]
      unless formal.size == supplied.size do
        throwError "the source derivation lost its original complete parameter references"
      let mut parameters := #[]
      for parameter in formal, index in [:formal.size] do
        let source ← parameter.inContext context
        parameters := parameters.push (← match supplied[index]?.bind id with
          | some value => markValue kernel.marks value source
          | none => pure source)
      let mut term := plan.betaRev parameters.reverse (preserveMData := true)
      for field in path do term ← projectTerm term field
      let values := match request.action with
        | .apply _ _ values => values
        | _ => #[]
      let mut actual := #[]
      for argument in arguments, index in [:arguments.size] do
        let source ← argument.inContext context
        actual := actual.push (← match values[index]?.bind id with
          | some value => markValue kernel.marks value source
          | none => pure source)
      return term.betaRev actual.reverse (preserveMData := true)

/-- A concrete field demand completes this exact formal construction once. The original
producer's owner envelope supplies its whole native request; the actual operand remains
the receiver-scoped key. An equal descriptor or source expression cannot select a cone. -/
private def Kernel.limitProjection? (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request : PreparedRequest) (transaction : CellTransaction) (operand : ValueBinding)
    (field : FieldLayout) (creation : Option PreparedCreationFamily := none) :
    MetaM (Option ValueBinding) := do
  let graph ← transaction.view
  let some node := graph.find operand.value
    | throwError "the construction receiver is outside its original graph"
  withSourceScope request fun context bound => do
    let original ← node.origin.role.source.inContext context
    let some selected ← NativeLimitSelection.ofExpr? original | return none
    let family ← LimitFamily.forId ⟨selected.source.row⟩
    let cached ← match ← transaction.selectedAt selected.source.construction
        family.coneProjection operand with
      | .ok value => pure value
      | .error failure => transactionFailure failure
    let cone ← match cached with
      | some value => pure value
      | none => do
        let whole ← match creation with
          | some prepared => do
            unless prepared.construction == selected.source.construction &&
                prepared.target.entry.id.raw == selected.source.row do
              throwError "the created object changed its original source preparation"
            let owner ← markValue kernel.marks operand original
            prepared.coneSource context owner
          | none => do
            let some whole ← LimitFamily.wholeFrom original
              | throwError "the original construction lost its whole native request"
            pure whole
        let value ← evaluateSource transaction request.program context bound whole
        let graph ← transaction.view
        let some completed := graph.find value.value
          | throwError "the completed construction has no actual result node"
        match completed.payload.data with
        | .container packet =>
          unless packet.originalPacket.isSome && packet.fields.isSome do
            throwError "the construction cannot publish an incomplete native cone"
        | .ownedToken .. =>
          unless creation.isSome do
            throwError "the raw construction requires its whole original native data ports"
        | _ => throwError "the completed construction lost its whole original native cone"
        match ← transaction.bindSelectedAt selected.source.construction family.coneProjection
            operand value with
        | .ok () => pure value
        | .error failure => transactionFailure failure
    let coneSource ← markValue kernel.marks cone (← cone.role.source.inContext context)
    let apexSource ← mkAppM family.apexProjection #[coneSource]
    let apex ← evaluateSource transaction request.program context bound apexSource
    let actual ← markValue kernel.marks apex apexSource
    return some (← evaluateSource transaction request.program context bound
      (← projectTerm actual field))

/-- The kernel-owned concrete executor of prepared demands (T013).
A published family whose value is a callable or a record is retained as a delayed demand.
A field of retained code extends that demand or lowers the source field. An application
dispatches the delayed family on its selected realization, evaluates retained source code at
the actual arguments, or invokes the native export on its original connection. -/
partial def Kernel.execute (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (PreparedResponse request) := do
  let graph ← transaction.view
  match request.action with
  | .primitive boundary _ =>
    let immediate := match boundary with
      | .point family => family.invocation
      | .objectAction _ | .limit _ _ | .creation _ => true
      | _ => false
    if immediate then
      let arguments := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
      return ← kernel.reach evaluateSource request transaction request #[] #[] arguments
    if request.source.kind == .function || request.source.kind == .record then
      return ← kernel.delay evaluateSource request transaction request #[] request.scope
    let arguments : Array ClosedTerm := match request.application with
      | none => #[]
      | some application => application.arguments.map (·.source.source)
    kernel.reach evaluateSource request transaction request #[] #[] arguments
  | .project operand field =>
    let some node := graph.find operand.value
      | throwError "internal: the projected value is outside the active graph"
    match node.payload.data with
    | .closure program captures =>
      match (← kernel.codes.get)[program]? with
      | some (.family family path) =>
        if request.source.kind == .function || request.source.kind == .record then
          kernel.delay evaluateSource request transaction family (path.push field) captures
        else
          kernel.reach evaluateSource request transaction family (path.push field) captures #[]
      | some (.term source) | some (.formalLeg source _) =>
        evaluateRequest kernel evaluateSource request transaction fun context => do
          projectTerm (← source.inContext context) field
      | some (.creationOwner source) => do
        let some value ← kernel.limitProjection? evaluateSource request transaction
            operand field (some source)
          | throwError "the created object lost its original native construction"
        kernelCompletion request transaction value
          (some (kernel.resolveFixedInput evaluateSource transaction request.program))
      | some (.retainedPoint ..) =>
        throwError "the retained scalar carrier cannot supply another record field"
      | some (.constructionLeg ..) =>
        throwError "a native cone component function cannot supply another record field"
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. =>
      kernel.invokeExport evaluateSource request transaction operand s!"project:{field.projection}"
    | .container container =>
      if container.fields.isSome then
        throwError "internal: a stored field reached the executor"
      if let some value ← kernel.limitProjection? evaluateSource request transaction operand field then
        return ← kernelCompletion request transaction value
          (some (kernel.resolveFixedInput evaluateSource transaction request.program))
      throwStratum .noImplementation
        m!"the retained descriptor supplies no native data for {field.projection}"
    | _ => throwError "internal: a stored field reached the executor"
  | .apply callable arguments values =>
    let code ← IO.ofExcept <| (graph.callable callable).mapError IO.userError
    let some node := graph.find code.value
      | throwError "internal: the applied value is outside the active graph"
    match node.payload.data with
    | .closure program captures =>
      match (← kernel.codes.get)[program]? with
      | some (.family family path) =>
        kernel.reach evaluateSource request transaction family path captures arguments
      | some (.creationOwner _) =>
        throwError "a created object requires its declared native field before application"
      | some (.retainedPoint original registration parameters source target packet path) => do
        let invocation ← PreparedPointInvocation.retained kernel evaluateSource request transaction
          original registration parameters source target packet path captures
        kernel.invokePoint evaluateSource request transaction registration invocation
      | some (.constructionLeg original registration diagram packet ports path retained) =>
        kernel.constructionLeg request transaction original registration diagram packet ports
          path retained captures
      | some (.term source) | some (.formalLeg source _) =>
        evaluateRequest kernel evaluateSource request transaction fun context => do
          let mut actual := #[]
          for argument in arguments, index in [:arguments.size] do
            let term ← argument.inContext context
            actual := actual.push (← match values[index]?.bind id with
              | some value => markValue kernel.marks value term
              | none => pure term)
          return (mkAppN (← source.inContext context) actual).headBeta
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. => kernel.invokeExport evaluateSource request transaction callable "apply"
    | .container container =>
      if container.callableData then
        throwStratum .noImplementation
          "the retained callable data have no accepted native application continuation"
      throwError "internal: the applied container has no retained callable interface"
    | _ => throwError "internal: the applied value has no code or native export"

end CasRuntime
