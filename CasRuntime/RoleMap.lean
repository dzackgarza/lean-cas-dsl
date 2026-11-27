module

public import CasCompiler.InputCoverage
public import CasRuntime.Environment

public section

namespace CasRuntime

open Lean Meta CasCompiler


inductive InputRoleSource
  | argument (position : Nat)
  | capture (position : Nat)
  deriving BEq, Repr

structure InputRoleBinding where
  private mk ::
  role : RoleId
  source : InputRoleSource
  value : ValueBinding





structure InputRoleMap where
  private mk ::
  telescope : RoleTelescope
  private bindings : Std.HashMap RoleId InputRoleBinding

private def admitInputRoles (telescope : RoleTelescope) (environment : RuntimeEnvironment)
    (graph : ValueGraph) (arguments : Array (Option ValueBinding)) (captures : Array ValueBinding)
    (actual : Array RuntimeArgument) (coverage : Option (InputResultSourceCoverage telescope)) :
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
      if supplied.isNone && coverage.any (fun selected => !selected.arguments.contains index) then
        continue
      let some value := supplied
        | throwError (MessageData.tagged `CasRuntime.InputRoleMap.missingArgument
            "a demanded computational argument role has no actual binding")
      let .ok _ := graph.requiredOwners #[value]
        | throwError "a computational argument is outside the visible graph"
      let argument ← if let some retained := actual.find? (·.index == index) then do
          unless retained.value.value == value.value &&
              retained.value.associationIds == value.associationIds do
            throwError "a computational argument changed its prepared source occurrence"
          pure retained
        else do
          let .ok argument := RuntimeArgument.ofValue graph index value
            | throwError "a computational argument is outside the visible graph"
          pure argument
      let value ← environment.checkArgument declared.role.source argument
      bindings := bindings.insert declared.role.id ⟨declared.role.id, .argument index, value⟩
    else
      if supplied.isSome then throwError "a formal proof role has a runtime payload"
  for declared in telescope.captures, index in [:telescope.captures.size] do
    let some value := captures[index]?
      | throwError "a demanded capture role has no actual binding"
    let candidate ← environment.checkOperand graph declared.layout value
    bindings := bindings.insert declared.role.id ⟨declared.role.id, .capture index, candidate.root⟩
  return ⟨telescope, bindings⟩




opaque InputRoleMap.admit (telescope : RoleTelescope) (environment : RuntimeEnvironment)
    (graph : ValueGraph) (arguments : Array (Option ValueBinding)) (captures : Array ValueBinding)
    (actual : Array RuntimeArgument := #[]) : MetaM InputRoleMap :=
  admitInputRoles telescope environment graph arguments captures actual none





opaque InputRoleMap.admitInputResult (telescope : RoleTelescope)
    (coverage : InputResultSourceCoverage telescope) (environment : RuntimeEnvironment)
    (graph : ValueGraph) (arguments : Array (Option ValueBinding)) (captures : Array ValueBinding)
    (actual : Array RuntimeArgument := #[]) : MetaM InputRoleMap :=
  admitInputRoles telescope environment graph arguments captures actual (some coverage)

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


opaque InputRoleMap.lookup (map : InputRoleMap) (graph : ValueGraph) (role : RoleId) :
    Except String InputRoleBinding := do
  map.checkVisibility graph
  map.requireBinding role


opaque InputRoleMap.arguments (map : InputRoleMap) (graph : ValueGraph) :
    Except String (Array ValueBinding) := do
  map.checkVisibility graph
  let mut values := #[]
  for argument in map.telescope.arguments do
    if argument.wireIndex.isSome then
      values := values.push (← map.requireBinding argument.role.id).value
  return values



structure ResultRoleMap where
  private mk ::
  telescope : RoleTelescope
  root : ValueBinding
  private bindings : Std.HashMap RoleId ValueBinding

def InputRoleMap.references (map : InputRoleMap) : Array ValueBinding :=
  map.bindings.toArray.map (·.2.value)

def ResultRoleMap.references (map : ResultRoleMap) : Array ValueBinding :=
  map.bindings.toArray.map (·.2)





opaque ResultRoleMap.admit (telescope : RoleTelescope) (environment : RuntimeEnvironment)
    (graph : ValueGraph) (value : ValueBinding)
    (projectionContext : Option (ValueBinding × FieldLayout) := none)
    (fieldPrefix : Option NativeFieldPrefix := none) : MetaM ResultRoleMap := do
  unless graph.worker == telescope.scope.program.worker do
    throwError "the result role map belongs to a different worker"
  let bindings ← IO.mkRef ({} : Std.HashMap RoleId ValueBinding)
  let sameSource := fun (left right : ClosedTerm) =>
    left.context.exactlyMatches right.context && left.expression.equal right.expression &&
      left.type.equal right.type && left.universeParams == right.universeParams &&
      left.nativeDeclarations.exactlyMatches right.nativeDeclarations
  let admitted : Array Nat → ValueBinding → MetaM Unit := fun path actual => do
    for declared in telescope.results do
      unless declared.wirePath == some path do continue
      unless actual.role.address == declared.layout.address &&
          actual.role.kind == declared.layout.kind &&
          sameSource actual.role.source declared.layout.source &&
          actual.role.selectionBinding == declared.layout.selectionBinding &&
          SourceSelectionScope.exactlyMatches sameSource
            actual.role.selections declared.layout.selections do
        throwError "an admitted result changed its original declared source position"


      bindings.modify (·.insert declared.role.id actual)
  let candidate ← match projectionContext with
    | some (operand, field) =>
      environment.checkProjectionResult graph telescope.source value operand field admitted
    | none => environment.checkResult graph telescope.source value fieldPrefix admitted
  return ⟨telescope, candidate.root, ← bindings.get⟩


opaque ResultRoleMap.lookup (map : ResultRoleMap) (graph : ValueGraph) (role : RoleId) :
    Except String ValueBinding := do
  unless graph.worker == map.telescope.scope.program.worker do
    throw "the result role map belongs to a different worker"
  unless role.scope == map.telescope.scope do
    throw "the result role belongs to a different scope"
  discard <| graph.requiredOwners #[map.root]
  let some value := map.bindings[role]?
    | throw "the result role has no materialized binding"
  discard <| graph.requiredOwners #[value]
  return value

end CasRuntime
