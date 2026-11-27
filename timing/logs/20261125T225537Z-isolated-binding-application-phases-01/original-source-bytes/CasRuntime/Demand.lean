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
def inputForms (action : RecordAction) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (arguments : Array ClosedTerm) : MetaM (Array String) := do
  -- Named morphisms publish their own raw complete-declaration request address.
  let own := match action.owner with
    | .computation (.morphism _) => action.familyAddress
    | _ => s!"{action.familyAddress}#input"
  let mut forms := #[own]
  for argument in arguments do
    if let some (entry, _) ← sourceObjectSelection? context selections
        (← argument.inContext context) then
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
        transaction.stage request.origin (.closure program captures)
    else
      -- This is the exact whole source whose complete origin preparation already fixed.
      -- Stage and result admission still check it against the current graph and request.
      transaction.stage request.origin (.closure program captures)
  kernelCompletion request transaction value
    (some (kernel.resolveFixedInput evaluateSource transaction request.program))

/-- Evaluate a checked source term for a claimed demand and complete that demand. -/
private def evaluateRequest (kernel : Kernel) (evaluateSource : SourceEvaluation) (request : PreparedRequest)
    (transaction : CellTransaction)
    (build : OpenContext → Std.HashMap BindingId ValueBinding → MetaM ValueBinding) : MetaM (PreparedResponse request) := do
  let value ← withSourceScope request build
  kernelCompletion request transaction value
    (some (kernel.resolveFixedInput evaluateSource transaction request.program))

/-- A native record action closed over the exact environment that owns its typed operands. -/
private structure ScopedRecordAction where
  action : RecordAction
  environment : RuntimeEnvironment

/-- Prepare record invocation inputs from the exact retained family result. Only the
source compiler determines their native slots and applications. The original completion
is selected by occurrence and preparation identity, never by expression or type. -/
private def Kernel.prepareRecordAction (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) (family : PreparedRequest) (boundary : ProgramBoundary)
    (universes : List Level) (path : Array FieldLayout) (arguments : Array ClosedTerm) :
    MetaM ScopedRecordAction := do
  withSourceScope request fun context bound => do
    let count := family.application.map (·.arguments.size) |>.getD 0
    family.withArguments kernel.ledger.owners.identities context bound count
        fun context bound parameters _ => do
      request.withArguments kernel.ledger.owners.identities context bound arguments.size
          fun context bound actual _ => do
        let finish := fun context bound parent => do
          let action ← RecordAction.prepare boundary universes context family.source parent path
            parameters actual family.selection
          let selections ← SourceSelectionScope.merge
            (← family.environment.selections.inContext context)
            (← family.source.selections.inContext context)
          let selections ← selections.merge (← request.source.selections.inContext context)
          let environment ← RuntimeEnvironment.captureBound request.environment.worker
            context bound (← transaction.view) (some request.environment) selections
          return (⟨action, environment⟩ : ScopedRecordAction)
        let parent ← family.source.source.inContext context
        if path.isEmpty then return ← finish context bound parent
        let some completion ← transaction.completionFor? family.occurrence
          | throwError "the delayed record lost its original completed family"
        family.requirePreparation completion.request.roles.scope
        withBoundValue kernel.ledger.owners.identities context bound parent
          completion.response.root finish

/-- Materialize only the source-prepared invocation slots, after realization selection.
The same path handles ordinary records and released record packets. -/
private def Kernel.recordInputs (kernel : Kernel) (evaluateSource : SourceEvaluation)
    (request family : PreparedRequest) (transaction : CellTransaction) (prepared : ScopedRecordAction) :
    MetaM (Array (Nat × ValueBinding)) := do
  let action := prepared.action
  let predecessors ← if action.predecessors.isEmpty then pure #[]
    else kernel.universalPredecessors family transaction action.predecessors
  let inputs ← prepared.environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    action.inputs.mapM fun input => do
      let source ← input.source.inContext context
      let evaluate := fun context selections source =>
        prepared.environment.evaluateSource evaluateSource transaction request.program
          context prepared.environment.bound source selections
      let selections ← prepared.environment.selections.inContext context
      let value ← match input.selectedField with
        | none => evaluate context selections source
        | some field => do
          let field ← field.mapM (fun term => term.inContext context)
          selections.withBinding kernel.ledger.owners.identities context
            { value := source, field := some field } evaluate
      return (input.sourceIndex, value)
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
      return ← evaluateRequest kernel evaluateSource request transaction fun context bound => do
        let count := selected.parameterCount + (if selected.invocation then 2 else 0)
        family.withArguments kernel.ledger.owners.identities context bound count
            fun context bound supplied _ => do
          let actual := supplied.extract 0 selected.parameterCount
          let selections ← SourceSelectionScope.merge
            (← request.environment.selections.inContext context)
            (← family.environment.selections.inContext context)
          checked.instantiate universes kernel.ledger.owners.identities context selections
              fun context selections plan => do
            let replacement := plan.betaRev
              (actual.extract 0 selected.declarationParameterCount).reverse
            let mut arrow ← selected.realizedArrow universes actual replacement
            if selected.invocation then
              let some domain := supplied[selected.parameterCount]?
                | throwError "the categorical derivation lost its original domain position"
              let some point := supplied[selected.parameterCount + 1]?
                | throwError "the categorical derivation lost its original point position"
              return ← request.environment.evaluateSource evaluateSource transaction request.program
                context bound (← selected.resultAt universes actual arrow domain point) selections
            for field in path do arrow ← projectTerm arrow field
            request.withArguments kernel.ledger.owners.identities context bound arguments.size
                fun context bound applied _ =>
              request.environment.evaluateSource evaluateSource transaction request.program
                context bound (arrow.betaRev applied.reverse) selections
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
      return ← evaluateRequest kernel evaluateSource request transaction fun context bound => do
        family.withArguments kernel.ledger.owners.identities context bound (selected.parameterCount + 1)
            fun context bound actual _ => do
          let selections ← SourceSelectionScope.merge
            (← request.environment.selections.inContext context)
            (← family.environment.selections.inContext context)
          checked.instantiate universes kernel.ledger.owners.identities context selections
              fun context selections plan => do
            let parameters := actual.extract 0 selected.parameterCount
            let replacement := plan.betaRev parameters.reverse
            request.environment.evaluateSource evaluateSource transaction request.program context bound
              (← selected.realized universes parameters actual[selected.parameterCount]! replacement)
              selections
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
      (← kernel.codes.get)
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
  let prepared ← kernel.prepareRecordAction request transaction family boundary universes path arguments
  let action := prepared.action
  let point ← PreparedPointInvocation.prepare? kernel evaluateSource request family path transaction
  let address := point.map (·.operation) |>.getD action.address
  let forms ← match point with
    | some point => pure point.forms
    | none => withSourceScope request fun context _ => do
      return (← inputForms action context
        (← request.environment.selections.inContext context) arguments)
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
      let inputs ← kernel.recordInputs evaluateSource request family transaction prepared
      let parameters := match boundary with
        | .limitUniversal _ _ =>
          (family.origin.application.map (·.arguments.filterMap id)).getD #[]
        | _ => parameters
      kernel.invokeRegistration evaluateSource request transaction registration role parameters inputs
  | .derivation checked =>
    evaluateRequest kernel evaluateSource request transaction fun context bound => do
      checked.instantiate universes kernel.ledger.owners.identities context
          (← request.environment.selections.inContext context) fun context selections plan => do
        let count := family.application.map (·.arguments.size) |>.getD 0
        family.withArguments kernel.ledger.owners.identities context bound count
            fun context bound parameters _ => do
          let selections ← SourceSelectionScope.merge selections
            (← family.environment.selections.inContext context)
          let mut term := plan.betaRev parameters.reverse
          for field in path do term ← projectTerm term field
          request.withArguments kernel.ledger.owners.identities context bound arguments.size
              fun context bound actual _ =>
            request.environment.evaluateSource evaluateSource transaction request.program
              context bound (term.betaRev actual.reverse) selections

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
    withBindingContext graph context bound operand fun context bound => do
      let some originalSelection ← operand.role.selected? context | return none
      let some selected := originalSelection.limit | return none
      let family : LimitFamily ← match originalSelection.application.map
          (fun (application : SelectedSourceApplication Expr) => application.family) with
        | some (.limit family) => pure family
        | some (.limitUniversal family) => pure family.presentation
        | some (.creation _ target) => pure target
        | _ =>
          match originalSelection.creationOwner with
          | some (_, target) => pure target
          | none =>
            let some family := originalSelection.limitFamily
              | throwError "the construction lost its complete original selected limit family"
            pure family
      if let some retained := originalSelection.limitFamily then
        unless (SelectedApplicationFamily.limit family).exactlyMatches (.limit retained) do
          throwError "the construction changed its complete original selected limit family"
      if let some (.limit entry) := originalSelection.reference.orElse
          (fun _ => originalSelection.observation) then
        unless (SelectedSourceReference.limit family.entry).exactlyMatches (.limit entry) do
          throwError "the construction changed its complete original selected limit row"
      unless family.entry.id.raw == selected.source.row do
        throwError "the construction changed its original selected presentation"
      let selections ← SourceSelectionScope.merge
        (← request.environment.selections.inContext context)
        (← operand.role.selections.inContext context)
      let original ← operand.selectedSource context
      let cached ← match ← transaction.selectedAt selected.source.construction
          family.coneProjection operand with
        | .ok value => pure value
        | .error failure => transactionFailure failure
      let finish := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
          (selections : SourceSelectionScope Expr) (cone : ValueBinding) => do
        withBindingContext (← transaction.view) context bound cone fun context bound => do
          withBoundValue kernel.ledger.owners.identities context bound
              (← cone.selectedSource context) cone fun context bound coneSource => do
            let apexSource ← mkAppM family.apexProjection #[coneSource]
            let apex ← request.environment.evaluateSource evaluateSource transaction request.program
              context bound apexSource selections
            withBoundValue kernel.ledger.owners.identities context bound apexSource apex
                fun context bound actual => do
              return some (← request.environment.evaluateSource evaluateSource transaction request.program
                context bound (← projectTerm actual field) selections)
      if let some value := cached then return ← finish context bound selections value
      let complete := fun (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
          (selections : SourceSelectionScope Expr) (whole : Expr) => do
        let value ← request.environment.evaluateSource evaluateSource transaction request.program
          context bound whole selections
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
        match ← transaction.bindSelectedAt selected.source.construction family.coneProjection operand value with
        | .ok () => finish context bound selections value
        | .error failure => transactionFailure failure
      match creation with
      | some prepared =>
        unless prepared.construction == selected.source.construction &&
            prepared.target.entry.id.raw == selected.source.row do
          throwError "the created object changed its original source preparation"
        withBoundValue kernel.ledger.owners.identities context bound original operand
            fun context bound owner =>
          prepared.coneSource kernel.ledger.owners.identities context selections owner
            fun context selections whole => complete context bound selections whole
      | none =>
        withBoundValue kernel.ledger.owners.identities context bound original operand
            fun context bound owner =>
          limitConeSource kernel.ledger.owners.identities context selections owner originalSelection
            fun context selections whole => do
              let some whole := whole
                | throwError "the original construction lost its whole native request"
              complete context bound selections whole

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
      | some (.term source retainedSelections) | some (.formalLeg source _ retainedSelections) =>
        evaluateRequest kernel evaluateSource request transaction fun context bound => do
          withBindingContext graph context bound operand fun context bound => do
            let selections ← retainedSelections.inContext context
            request.environment.evaluateSource evaluateSource transaction request.program context bound
              (← projectTerm (← source.inContext context) field) selections
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
  | .apply callable arguments _ =>
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
      | some (.term source retainedSelections) | some (.formalLeg source _ retainedSelections) =>
        evaluateRequest kernel evaluateSource request transaction fun context bound => do
          withBindingContext graph context bound callable fun context bound => do
            request.withArguments kernel.ledger.owners.identities context bound arguments.size
                fun context bound actual _ => do
              request.environment.evaluateSource evaluateSource transaction request.program context bound
                (mkAppN (← source.inContext context) actual).headBeta
                (← retainedSelections.inContext context)
      | none => throwError "internal: a retained closure has no code"
    | .ownedToken .. => kernel.invokeExport evaluateSource request transaction callable "apply"
    | .container container =>
      if container.callableData then
        throwStratum .noImplementation
          "the retained callable data have no accepted native application continuation"
      throwError "internal: the applied container has no retained callable interface"
    | _ => throwError "internal: the applied value has no code or native export"

end CasRuntime
