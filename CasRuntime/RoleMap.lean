module

public import CasCompiler.Roles
public import CasRuntime.Environment

public section

namespace CasRuntime

open Lean Meta CasCompiler

/-- Input and capture sources name positions, independently of value or expression equality. -/
inductive InputRoleSource
  | argument (position : Nat)
  | capture (position : Nat)
  deriving BEq, Repr

structure InputRoleBinding where
  private mk ::
  role : RoleId
  source : InputRoleSource
  value : ValueBinding

/-- A total map for this request's declared computational arguments and captures.
The map contains references and source roles, never completed payload storage. -/
structure InputRoleMap where
  private mk ::
  telescope : RoleTelescope
  private bindings : Std.HashMap RoleId InputRoleBinding

/-- Admit every declared wire argument and capture in its source position.
Reuse: native RuntimeEnvironment checks and immutable graph visibility. Proof positions stay
in the telescope without a runtime payload. This is input-map admission, not result admission. -/
opaque InputRoleMap.admit (telescope : RoleTelescope) (environment : RuntimeEnvironment)
    (graph : ValueGraph) (arguments : Array (Option ValueBinding)) (captures : Array ValueBinding) :
    MetaM InputRoleMap := do
  unless graph.worker == telescope.scope.program.worker && graph.worker == environment.worker do
    throwError "the computational input map belongs to a different worker"
  unless arguments.size == telescope.arguments.size && captures.size == telescope.captures.size do
    throwError "the computational input map has a different source telescope"
  let mut bindings : Std.HashMap RoleId InputRoleBinding := {}
  for declared in telescope.arguments, index in [:telescope.arguments.size] do
    let some supplied := arguments[index]?
      | throwError "a computational argument is outside its complete source table"
    if declared.wireIndex.isSome then
      let some value := supplied
        | throwError "a demanded computational argument role has no actual binding"
      let .ok argument := RuntimeArgument.ofValue graph index value
        | throwError "a computational argument is outside the visible graph"
      let value ← environment.checkArgument declared.role.source argument
      bindings := bindings.insert declared.role.id ⟨declared.role.id, .argument index, value⟩
    else
      if supplied.isSome then throwError "a formal proof role has a runtime payload"
  for declared in telescope.captures, index in [:telescope.captures.size] do
    let some value := captures[index]?
      | throwError "a demanded capture role has no actual binding"
    let candidate ← environment.checkResult graph declared.layout value
    bindings := bindings.insert declared.role.id ⟨declared.role.id, .capture index, candidate.root⟩
  return ⟨telescope, bindings⟩

private def InputRoleMap.checkVisibility (map : InputRoleMap) (graph : ValueGraph) :
    Except String Unit := do
  unless graph.worker == map.telescope.scope.program.worker do
    throw "the computational input map belongs to a different worker"
  discard <| graph.requiredOwners (map.bindings.toArray.map (·.2.value))

private def InputRoleMap.requireBinding (map : InputRoleMap) (role : RoleId) :
    Except String InputRoleBinding := do
  unless role.scope == map.telescope.scope do
    throw "the computational role belongs to a different scope"
  let some binding := map.bindings[role]?
    | throw "the computational role has no input binding"
  return binding

/-- Role identity includes its scope. Recheck all input visibility in the caller's snapshot. -/
opaque InputRoleMap.lookup (map : InputRoleMap) (graph : ValueGraph) (role : RoleId) :
    Except String InputRoleBinding := do
  map.checkVisibility graph
  map.requireBinding role

/-- Source-ordered wire values; aliases keep each of their distinct role positions. -/
opaque InputRoleMap.arguments (map : InputRoleMap) (graph : ValueGraph) :
    Except String (Array ValueBinding) := do
  map.checkVisibility graph
  let mut values := #[]
  for argument in map.telescope.arguments do
    if argument.wireIndex.isSome then
      values := values.push (← map.requireBinding argument.role.id).value
  return values

end CasRuntime
