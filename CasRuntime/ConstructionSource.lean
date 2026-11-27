module

public import CasRuntime.ExecutionContext
public import CasRuntime.NativeMapEndpoints
public import CasCompiler.ConstructionEndpoint
public import CasCompiler.PreparedCreationFamily

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

private def sameConstructionOccurrence (original actual : ValueBinding) : Bool :=
  original.value == actual.value &&
    original.associationIds.toList.isPrefixOf actual.associationIds.toList



private partial def constructionParameterPath? (graph : ValueGraph)
    (original actual : ValueBinding) : MetaM (Option (Array Name)) := do
  if original.value == actual.value && original.associationIds == actual.associationIds then
    return some #[]
  let some (_, parent, path) ← IO.ofExcept <|
      (graph.projectionSelection actual).mapError IO.userError | return none
  let some earlier ← constructionParameterPath? graph original parent | return none
  return some (earlier ++ path)



private partial def constructionCompletion (transaction : CellTransaction) (graph : ValueGraph)
    (cone current : ValueBinding) (path : Array Name := #[]) :
    MetaM CompletionAssociation := do
  let some node := graph.find current.value
    | throwError "the construction leg lost its original visible cone"
  if let some completion ← transaction.completionFor? node.origin.occurrence then
    if sameConstructionOccurrence completion.response.root current then
      match completion.request.action with
      | .primitive (.limit ..) _ =>
        unless path.isEmpty do
          throwError "the raw construction leg changed its original complete cone root"
        return completion
      | .primitive (.creation _) _ =>
        unless path == #[``CategoryTheory.LiftsToLimit.toLiftableCone,
            ``CategoryTheory.LiftableCone.liftedCone] do
          throwError "the created construction leg changed its exact lifted source cone path"
        let some _ ← IO.ofExcept <|
            (graph.projectionBasis cone current path).mapError IO.userError
          | throwError "the created source cone lost its actual complete-result parent"
        return completion
      | _ => pure ()
  let some (_, parent, previous) ← IO.ofExcept <|
      (graph.projectionSelection current).mapError IO.userError
    | throwError "the construction leg lost its original producing completion"
  constructionCompletion transaction graph cone parent (previous ++ path)



private structure RetainedConstructionSource where
  request : PreparedRequest
  owner : Expr
  ownerFamily : SelectedLimitOwner Expr
  parameters : Array Expr
  values : Array (Option ValueBinding)
  selection : NativeLimitSelection

private def retainedConstructionSource (kernel : Kernel) (transaction : CellTransaction)
    (graph : ValueGraph) (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (cone : ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding → RetainedConstructionSource →
      MetaM α) : MetaM α := do
  unless ← graph.isAvailable kernel.ledger.owners cone do transactionFailure .staleOwner
  let completion ← constructionCompletion transaction graph cone cone
  unless ← graph.isAvailable kernel.ledger.owners completion.response.root do
    transactionFailure .staleOwner
  let request := completion.request
  let inputs ← request.admitInputs graph
  discard <| IO.ofExcept <| (inputs.arguments graph).mapError IO.userError
  let some node := graph.find cone.value
    | throwError "the construction leg lost its original visible native fields"
  match node.payload.data with
  | .container complete =>
    unless complete.originalPacket.isSome && complete.fields.isSome do
      throwError "the construction leg cannot use an incomplete native cone"
  | .ownedToken .. =>
    unless request.action matches .primitive (.creation _) _ do
      throwError "the raw construction leg requires its complete native data ports"
  | _ => throwError "the construction leg lost its complete returned native cone"
  request.environment.withContext context bound fun context bound => do
    match request.action with
    | .primitive (.limit family owner) _ =>
      let ownerFamily ← owner.mapM (·.inContext context)
      let owner ← family.ownerFamily ownerFamily
      let source := request.application.map (·.arguments.map (·.source.source)) |>.getD #[]
      let values := request.origin.application.map (·.arguments) |>.getD #[]
      unless source.size == family.parameterCount && values.size == source.size do
        throwError "the construction leg lost its complete original parameter table"
      let parameters ← source.mapM (·.inContext context)
      let selection ← family.ownerAt ownerFamily parameters
      return ← action context bound { request, owner, ownerFamily, parameters, values, selection }
    | .primitive (.creation prepared) _ =>
      let owner ← prepared.owner.inContext context
      let ownerFamily ← prepared.sourceOwner.mapM (·.inContext context)
      let parameters ← prepared.sourceArguments.mapM (·.inContext context)
      let selection ← prepared.selection context
      let environment ← request.environment.withGraph (some graph)
      let mut values : Array (Option ValueBinding) := #[]
      for parameter in parameters do
        let selected ← if ← isProof parameter then pure none
          else environment.endpointValue? context graph parameter
        if let some value := selected then
          environment.checkDeclaredInput context graph parameter value
        values := values.push selected
      return ← action context bound { request, owner, ownerFamily, parameters, values, selection }
    | _ => throwError "the construction leg has no original raw or created source preparation"




opaque Kernel.retainedRawConstructionCone (kernel : Kernel) (transaction : CellTransaction)
    (graph : ValueGraph) (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (cone : ValueBinding)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      (PreparedRequest × Expr × NativeLimitSelection × Expr) → MetaM α) : MetaM α := do
  retainedConstructionSource kernel transaction graph context bound cone fun context bound original => do
    unless original.request.action matches .primitive (.limit ..) _ do
      throwError "the creation target is not its original complete raw construction"
    withBindingContext graph context bound cone fun context bound => do
      withBoundValue kernel.ledger.owners.identities context bound
          (← cone.role.source.inContext context) cone fun context bound coneSource =>
        action context bound (original.request, original.owner, original.selection, coneSource)





opaque Kernel.retainedConstructionCone (kernel : Kernel) (transaction : CellTransaction)
    (graph : ValueGraph) (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (retained : Json → MetaM (Option ValueBinding)) (packet : Json)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      Option (Expr × NativeLimitSelection × Expr) → MetaM α) : MetaM α := do
  let some cone ← retained packet | return ← action context bound none
  retainedConstructionSource kernel transaction graph context bound cone fun context bound original => do
    let finish (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
        (selected : NativeLimitSelection) : MetaM α :=
      withBindingContext graph context bound cone fun context bound => do
        withBoundValue kernel.ledger.owners.identities context bound
            (← cone.role.source.inContext context) cone fun context bound coneSource =>
          action context bound (some (original.owner, selected, coneSource))
    match original.request.action with
    | .primitive (.limit family _) _ =>
      original.request.withArguments kernel.ledger.owners.identities context bound family.parameterCount
        fun context bound parameters _ => do
          finish context bound (← family.ownerAt original.ownerFamily parameters)
    | .primitive (.creation _) _ => finish context bound original.selection
    | _ => throwError "the construction leg changed its original source preparation"




private partial def abstractConstructionIndex (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (original : RetainedConstructionSource)
    (formals : Array Expr) (expression : Expr) : MetaM Expr := do
  if let some selected ← environment.endpointValue? context graph expression then
    let mut positions : Array Nat := #[]
    for value in original.values, index in [:original.values.size] do
      let some value := value | continue
      unless value.value == selected.value && value.associationIds == selected.associationIds do
        continue
      let some parameter := original.parameters[index]?
        | throwError "the construction index lost an original source position"
      if parameter.equal expression then positions := positions.push index
    if let #[position] := positions then
      let some formal := formals[position]?
        | throwError "the construction index lost an original formal position"
      return formal


    unless positions.isEmpty do return expression
  let recur := abstractConstructionIndex environment context graph original formals
  match expression with
  | .mdata data body => return .mdata data (← recur body)
  | .app function argument => return .app (← recur function) (← recur argument)
  | .lam name type body info => return .lam name (← recur type) (← recur body) info
  | .forallE name type body info => return .forallE name (← recur type) (← recur body) info
  | .letE name type value body nonDependent =>
    return .letE name (← recur type) (← recur value) (← recur body) nonDependent
  | .proj owner index body => return .proj owner index (← recur body)
  | expression => return expression




opaque Kernel.checkConstructionEndpoint (kernel : Kernel) (transaction : CellTransaction)
    (graph : ValueGraph) (context : OpenContext) (environment : RuntimeEnvironment)
    (leg : NativeConstructionLeg) (target : Bool) (candidate : Expr) : MetaM Bool := do
  if target == leg.selection.source.colimit then return false
  let some supplied ← environment.endpointValue? context graph candidate | return false
  let some cone ← environment.endpointValue? context graph leg.cone
    | throwError "the construction endpoint lost its exact retained native cone"
  retainedConstructionSource kernel transaction graph context environment.bound cone
      fun context _ original => do
    unless leg.owner.equal original.owner &&
        leg.selection.source.construction == original.selection.source.construction &&
        leg.selection.source.row == original.selection.source.row &&
        leg.selection.source.declaration == original.selection.source.declaration &&
        leg.selection.source.colimit == original.selection.source.colimit do
      throwError "the construction endpoint changed its original complete source owner"
    let mut positions : Array (Nat × Array Name) := #[]
    for value in original.values, index in [:original.values.size] do
      let some value := value | continue
      if let some path ← constructionParameterPath? graph value supplied then
        positions := positions.push (index, path)
    let some (position, path) := positions[0]? | return false
    let indexFamily ← withConstructionParameters original.ownerFamily
        original.selection.source.construction original.parameters.size fun formals _ => do
      let index ← abstractConstructionIndex environment context graph original formals leg.index
      mkLambdaFVars formals index (usedOnly := false) (usedLetOnly := false)
    checkConstructionLegEndpointAt original.ownerFamily original.selection original.parameters
      indexFamily leg.index target position path (positions.extract 1 positions.size)
    return true




opaque Kernel.retainedCreationOwner (kernel : Kernel) (graph : ValueGraph)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (retained : Json → MetaM (Option ValueBinding)) (packet : Json)
    (action : OpenContext → Std.HashMap BindingId ValueBinding →
      Option (NativeLimitSelection × Expr) → MetaM α) : MetaM α := do
  let some value ← retained packet | return ← action context bound none
  unless ← graph.isAvailable kernel.ledger.owners value do
    transactionFailure .staleOwner
  let some node := graph.find value.value
    | throwError "the creation request lost its original visible owner"
  withBindingContext graph context bound value fun context bound => do
    let source ← value.selectedSource context
    let some original ← value.role.selected? context | return ← action context bound none
    let some selected := original.limit | return ← action context bound none
    unless selected.source.creation.isSome do return ← action context bound none
    withBoundValue kernel.ledger.owners.identities context bound source value fun context bound owner =>
      action context bound (some (selected, owner))

end CasRuntime
