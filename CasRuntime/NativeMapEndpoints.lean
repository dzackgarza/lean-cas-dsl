module

public import CasRuntime.ResultCodec
public import CasRuntime.Association

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue



private partial def nativeEndpointReference? (environment : RuntimeEnvironment)
    (context : OpenContext) (source : Expr) (path : Array Name := #[]) :
    MetaM (Option (ValueBinding × Array Name)) := do
  if let .mdata data body := source then
    return ← nativeEndpointReference? environment context body path
  if let .fvar id := source then
    let some original := context.bindings.find? (·.expression.fvarId! == id)
      | throwError "a native endpoint is outside its original complete source context"
    let value ← IO.ofExcept <| (environment.lookup original.id).mapError IO.userError
    if value.isNone && original.role == .selectedStructure &&
        !environment.selections.contains original.id then
      throwError "the source lost its retained typed selection"
    if value.isNone && original.role == .result then
      throwError "the source lost a retained runtime binding"
    return value.map (fun value => (value, path))
  if let some selected ← SourceProjection.ofExpr? source then
    return ← nativeEndpointReference? environment context selected.parent
      (#[selected.declaration] ++ path)
  return none




opaque RuntimeEnvironment.endpointValue? (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (source : Expr) :
    MetaM (Option ValueBinding) := do
  let some (parent, path) ← nativeEndpointReference? environment context source | return none
  discard <| IO.ofExcept <| (graph.requiredOwners #[parent]).mapError IO.userError
  if path.isEmpty then return some parent
  let some access ← IO.ofExcept <|
      (graph.projectedAccess? parent path).mapError IO.userError | return none
  let some baseline ← IO.ofExcept <|
      (graph.projectionBasis access parent path).mapError IO.userError
    | throwError "an original endpoint access lost its exact native parent/path"
  unless baseline.value == access.value &&
      baseline.associationIds.toList.isPrefixOf access.associationIds.toList do
    throwError "an original endpoint access changed its retained value occurrence"
  return some access




private def retainNativeEndpoint (request : PreparedRequest) (environment : RuntimeEnvironment)
    (context : OpenContext) (supply : IdentitySupply) (parent : ValueBinding) (path : Array Name)
    (draft : CellDraft) : MetaM (CellDraft × ValueBinding) := do
  discard <| IO.ofExcept <| (draft.view.requiredOwners #[parent]).mapError IO.userError
  if path.isEmpty then return (draft, parent)
  if let some access ← IO.ofExcept <|
      (draft.view.projectedAccess? parent path).mapError IO.userError then
    return (draft, access)
  let some (baseline, remaining) ← IO.ofExcept <|
      (draft.view.projectionFrontier parent path).mapError IO.userError
    | throwStratum .noImplementation "the original native endpoint has no stored field interface"
  unless remaining.isEmpty do
    throwStratum .noImplementation "the original native endpoint requires its retained field demand"
  let mut parameters := #[]
  for entry in environment.context.entries, value in environment.values do
    if let some value := value then
      parameters := parameters.push (← IO.ofExcept <|
        (RuntimeParameter.ofValue draft.view entry.id value).mapError IO.userError)
  let projection ← PreparedRequest.forStoredProjection supply request.program
    (← supply.fresh .occurrence) context draft.view parent path parameters (some environment)
    (selections := ← environment.selections.inContext context)
  let projection := projection.withSourceSnapshot request.observation.sourceSnapshot
  let (draft, access) ← projection.associateResult supply projection.source draft
    baseline #[] (complete := true)
  discard <| projection.admitResult draft.view access
  let some retained ← IO.ofExcept <|
      (draft.view.projectionBasis access parent path).mapError IO.userError
    | throwError "the native endpoint lost its original stored projection basis"
  unless retained.value == baseline.value &&
      retained.associationIds == baseline.associationIds &&
      access.value == baseline.value &&
      baseline.associationIds.toList.isPrefixOf access.associationIds.toList do
    throwError "native endpoint admission changed its original field occurrence"
  return (draft, access)





opaque nativeFunctionEndpoints? (request : PreparedRequest)
    (environment : RuntimeEnvironment) (native : SourceLayout) (supply : IdentitySupply)
    (draft : CellDraft) (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × Option ValueBinding × Option ValueBinding) := do
  unless native.kind == .function do
    throwError "function endpoint preparation requires its original native function role"
  let environment ← environment.withGraph (some draft.view)
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    native.source.context.withInContext context fun context => do
      let inspect := fun (context : OpenContext) (type : Expr)
          (bound : Std.HashMap BindingId ValueBinding) => do
        let selections ← SourceSelectionScope.merge (← environment.selections.inContext context)
          (← native.selections.inContext context)
        let current ← RuntimeEnvironment.captureBound environment.worker context bound draft.view
          (selections := selections)
        let (source, target) ← nativeFunctionEndpointTypes type
        let retain := fun (endpoint : Expr) (draft : CellDraft) => do
          let some (parent, path) ← nativeEndpointReference? current context endpoint
            | return (draft, none)
          let (draft, value) ← retainNativeEndpoint request current context supply parent path draft
          let retained ← match fieldPrefix with
            | some nativePrefix =>
              nativePrefix.checkEndpoint current context draft.view endpoint value
            | none => pure false
          unless retained do
            current.checkDeclaredInput context draft.view endpoint value
          return (draft, some value)
        let (draft, source) ← retain source draft
        let (draft, target) ← match target with
          | some target => retain target draft
          | none => pure (draft, none)
        return (draft, source, target)
      match fieldPrefix with
      | some nativePrefix =>
        discard <| IO.ofExcept <|
          (nativePrefix.requireOrigin request.program request.occurrence native).mapError IO.userError
        nativePrefix.withBoundType context draft.view environment.bound inspect
      | none =>
        let expression ← native.source.inContext context
        inspect context (← inferType expression) environment.bound




opaque PreparedMapResult.fromNative (request : PreparedRequest)
    (environment : RuntimeEnvironment) (native : SourceLayout) (supply : IdentitySupply)
    (draft : CellDraft) (checkSymbolic : Option PreparedSymbolicCheck := none)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × PreparedMapResult) := do
  let environment ← environment.withGraph (some draft.view)
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    native.source.context.withInContext context fun context => do
      let inspect := fun (context : OpenContext) (expression : Expr)
          (bound : Std.HashMap BindingId ValueBinding) => do
        let selections ← SourceSelectionScope.merge (← environment.selections.inContext context)
          (← native.selections.inContext context)
        let current ← RuntimeEnvironment.captureBound environment.worker context bound draft.view
          (selections := selections)
        let (source, target) ← nativeMapEndpoints expression
        let some (sourceParent, sourcePath) ← nativeEndpointReference? current context source
          | throwStratum .noImplementation "the native map source has no retained original supplier"
        let some (targetParent, targetPath) ← nativeEndpointReference? current context target
          | throwStratum .noImplementation "the native map target has no retained original supplier"
        let (draft, source) ← retainNativeEndpoint request current context supply sourceParent
          sourcePath draft
        let (draft, target) ← retainNativeEndpoint request current context supply targetParent
          targetPath draft
        let prepared ← PreparedMapResult.forSource current native draft.view source target
          none none none #[] checkSymbolic (fieldPrefix := fieldPrefix)
        return (draft, prepared)
      match fieldPrefix with
      | none => inspect context (← native.source.inContext context) environment.bound
      | some nativePrefix =>
        discard <| IO.ofExcept <|
          (nativePrefix.requireOrigin request.program request.occurrence native).mapError IO.userError
        nativePrefix.withBoundType context draft.view environment.bound fun context type bound =>
          withLocalDeclD `nativeMap type fun expression => inspect context expression bound

end CasRuntime
