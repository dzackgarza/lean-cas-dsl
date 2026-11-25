module

public import CasRuntime.ResultCodec
public import CasRuntime.Association

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue

/-- An endpoint supplier is read only from this original native endpoint's explicit value
mark, context BindingId, or syntactic native projection spine. No expression/type search
selects a computational value, and no source definition or matcher is evaluated here. -/
private partial def nativeEndpointReference? (environment : RuntimeEnvironment)
    (context : OpenContext) (source : Expr) (path : Array Name := #[]) :
    MetaM (Option (ValueBinding × Array Name)) := do
  if let .mdata data body := source then
    if let some key := markedKey? data then
      let some (_, value) := environment.sourceMarks.find? (·.1 == key)
        | throwError "a native endpoint lost its original retained value mark"
      return some (value, path)
    return ← nativeEndpointReference? environment context body path
  if let .fvar id := source then
    let some original := context.bindings.find? (·.expression.fvarId! == id)
      | throwError "a native endpoint is outside its original complete source context"
    let value ← IO.ofExcept <| (environment.lookup original.id).mapError IO.userError
    return value.map (fun value => (value, path))
  if let some selected ← SourceProjection.ofExpr? source then
    return ← nativeEndpointReference? environment context selected.parent
      (#[selected.declaration] ++ path)
  return none

/-- Read only an explicit original endpoint supplier or an already authenticated native
projection access. A source expression such as a new functor image has no binding here;
its native dependency constraints remain with the caller's transient interface check. -/
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

/-- Reuse an original stored native endpoint path. Publishing its access uses the ordinary
intrinsic projection preparation/association boundary, as fixed-input result assembly does.
The original baseline stays unchanged; lazy fields are not executed during reply admission. -/
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

/-- Retain each independently supplied endpoint of this original native function. A known
domain remains fixed when the target is absent or depends on the argument. Absence means
only that the source grammar supplied no value; malformed marks, changed parents and failed
native admission remain errors. No finite inventory or source value is reconstructed. -/
opaque nativeFunctionEndpoints? (request : PreparedRequest)
    (environment : RuntimeEnvironment) (native : SourceLayout) (supply : IdentitySupply)
    (draft : CellDraft) (marks : Array ValueBinding := #[])
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × Option ValueBinding × Option ValueBinding) := do
  unless native.kind == .function do
    throwError "function endpoint preparation requires its original native function role"
  let available ← IO.ofExcept <|
    (mergeSourceMarks environment.sourceMarks
      (marks.mapIdx fun index value => (index, value))).mapError IO.userError
  let captured ← IO.ofExcept <| (retainedSourceMarks available native.source).mapError IO.userError
  let environment ← environment.withSourceMarks captured (some draft.view)
  let inspect := fun (context : OpenContext) (type : Expr)
      (captured : Array (Nat × ValueBinding)) => do
    let environment ← environment.withSourceMarks captured (some draft.view)
    let (source, target) ← nativeFunctionEndpointTypes type
    let retain := fun (endpoint : Expr) (draft : CellDraft) => do
      let some (parent, path) ← nativeEndpointReference? environment context endpoint
        | return (draft, none)
      let (draft, value) ← retainNativeEndpoint request environment context supply parent path draft
      let retained ← match fieldPrefix with
        | some nativePrefix => nativePrefix.checkEndpoint environment context draft.view marks endpoint value
        | none => pure false
      unless retained do
        environment.checkDeclaredInput context draft.view marks endpoint value
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
    nativePrefix.withMarkedType draft.view environment.sourceMarks inspect (minimumKey := marks.size)
  | none => native.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    inspect context (← inferType expression) environment.sourceMarks

/-- The actual suppliers of this independently selected native Hom's endpoint slots.
Constructor ports supply their prefix environment; nested maps supply their own native role.
This is a source-directed read of exact retained positions, never endpoint reconstruction. -/
opaque PreparedMapResult.fromNative (request : PreparedRequest)
    (environment : RuntimeEnvironment) (native : SourceLayout) (supply : IdentitySupply)
    (draft : CellDraft) (marks : Array ValueBinding := #[])
    (checkSymbolic : Option PreparedSymbolicCheck := none)
    (fieldPrefix : Option NativeFieldPrefix := none) :
    MetaM (CellDraft × PreparedMapResult) := do
  let available ← IO.ofExcept <|
    (mergeSourceMarks environment.sourceMarks
      (marks.mapIdx fun index value => (index, value))).mapError IO.userError
  let captured ← IO.ofExcept <| (retainedSourceMarks available native.source).mapError IO.userError
  let environment ← environment.withSourceMarks captured (some draft.view)
  let inspect := fun (context : OpenContext) (expression : Expr)
      (captured : Array (Nat × ValueBinding)) => do
    let current ← environment.withSourceMarks captured (some draft.view)
    let (source, target) ← nativeMapEndpoints expression
    let some (sourceParent, sourcePath) ← nativeEndpointReference? current context source
      | throwStratum .noImplementation "the native map source has no retained original supplier"
    let some (targetParent, targetPath) ← nativeEndpointReference? current context target
      | throwStratum .noImplementation "the native map target has no retained original supplier"
    let (draft, source) ← retainNativeEndpoint request current context supply sourceParent
      sourcePath draft
    let (draft, target) ← retainNativeEndpoint request current context supply targetParent
      targetPath draft
    let prepared ← PreparedMapResult.forSource environment native draft.view source target
      marks none none none #[] checkSymbolic (fieldPrefix := fieldPrefix)
    return (draft, prepared)
  match fieldPrefix with
  | none => native.source.withOpen fun bindings expression => do
    inspect (← ContextTelescope.capture bindings) expression environment.sourceMarks
  | some nativePrefix =>
    discard <| IO.ofExcept <|
      (nativePrefix.requireOrigin request.program request.occurrence native).mapError IO.userError
    nativePrefix.withMarkedType draft.view environment.sourceMarks (fun context type captured =>
      withLocalDeclD `nativeMap type fun expression => inspect context expression captured)
      (minimumKey := marks.size)

end CasRuntime
