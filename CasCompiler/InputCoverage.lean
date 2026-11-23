module

public import CasCompiler.Roles

public section

namespace CasCompiler

open Lean Meta

private partial def selectedArguments (application : ApplicationLayout) (source : SourceLayout)
    (contextInputs : Array BindingId) : MetaM (Option (Array Nat)) := do
  let path ← application.result.projectionPathTo source
  let dependencies ← application.dependenciesFor source
  if let some (.projection selected) ←
      application.inputProjectionThrough #[] path contextInputs then
    return some (dependencies.arguments ++ match selected.target with
      | .argument index => #[index]
      | .context _ => #[])
  if source.kind != .record then return none
  let mut required := dependencies.arguments
  for field in (← RecordLayout.ofSource source).fields do
    if field.field.wireIndex.isNone then continue
    let some selected ← selectedArguments application field.layout contextInputs | return none
    required := required ++ selected
  return some required

/-- Source-only whole-result coverage for argument preparation. Every computational result
field must select an original argument/context reference through the existing native tracer.
Required data include all selected fields' type dependencies and their transitive formal
prefix dependencies. This reader neither supplies values nor authorizes an execution.
Reuse: inputProjectionThrough, dependenciesFor and ArgumentLayout.precedingDependencies. -/
opaque ApplicationLayout.inputResultArguments (application : ApplicationLayout)
    (contextInputs : Array BindingId := #[]) : MetaM (Option (Array Nat)) := do
  let some selected ← selectedArguments application application.result contextInputs | return none
  let mut required := selected
  for index in (List.range application.arguments.size).reverse do
    unless required.contains index do continue
    let some argument := application.arguments[index]?
      | throwError "source input coverage lost an original argument slot"
    for previous in argument.precedingDependencies do
      unless previous < index do
        throwError "source input coverage changed its native dependent prefix"
      required := required.push previous
  unless required.all (· < application.arguments.size) do
    throwError "source input coverage selected an absent formal argument"
  return some ((Array.range application.arguments.size).filter required.contains)

private def sameClosedSource (first second : ClosedTerm) : Bool :=
  first.expression == second.expression && first.type == second.type &&
    first.universeParams == second.universeParams &&
    first.context.entries.size == second.context.entries.size &&
    (first.context.entries.zip second.context.entries).all (fun (left, right) =>
      left.id == right.id && left.role == right.role && left.userName == right.userName &&
      left.binderInfo == right.binderInfo && left.type == right.type &&
      left.value == right.value && left.nondep == right.nondep) &&
    first.context.instances.size == second.context.instances.size &&
    (first.context.instances.zip second.context.instances).all (fun (left, right) =>
      left.className == right.className && left.binding == right.binding)

/-- A complete source-coverage witness for this exact prepared role telescope. The native
formal application and its complete context are checked before this private constructor is
available; callers cannot replace required argument positions with an arbitrary subset. -/
structure InputResultSourceCoverage (roles : RoleTelescope) where
  private mk ::
  private required : Array Nat

def InputResultSourceCoverage.arguments (coverage : InputResultSourceCoverage roles) :
    Array Nat := coverage.required

/-- Seal source coverage only for the exact prepared result and complete original formal
application. Native expression equality here checks certificate ownership; it never selects
an actual runtime binding or treats definitionally equal inputs as the same occurrence. -/
opaque RoleTelescope.inputResultCoverage (roles : RoleTelescope)
    (application : ApplicationLayout) (contextInputs : Array BindingId := #[]) :
    MetaM (Option (InputResultSourceCoverage roles)) := do
  unless sameClosedSource roles.source.source application.result.source &&
      roles.arguments.size == application.arguments.size do return none
  let some result := roles.results[0]? | return none
  unless sameClosedSource result.role.typeFamily application.resultTypeFamily do return none
  for role in roles.arguments, argument in application.arguments,
      index in [:application.arguments.size] do
    unless argument.sourceIndex == index && role.wireIndex == argument.wireIndex &&
        sameClosedSource role.role.source argument.source.source &&
        sameClosedSource role.role.typeFamily argument.typeFamily do return none
  let some required ← application.inputResultArguments contextInputs | return none
  return some ⟨required⟩

end CasCompiler
