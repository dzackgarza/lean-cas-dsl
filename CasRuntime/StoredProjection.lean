module

public import CasRuntime.Value

public section

namespace CasRuntime

open Lean

/-- Follow an exact native field path through actual stored or already published projections.
Return its remaining path at a lazy frontier; a descriptor without field data gives none.
Only graph references are read. No provider runs and no intermediate result is completed.
Reuse: the existing FixedInput.storedFrontier traversal and ValueGraph.projected?/project. -/
opaque ValueGraph.projectionFrontier (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : Except String (Option (ValueBinding × Array Name)) := do
  discard <| graph.requiredOwners #[parent]
  let mut value := parent
  for projection in path, offset in [:path.size] do
    let some field := value.role.fields.find? (·.projection == projection)
      | throw "a native field path lost its actual record interface"
    let some index := field.wireIndex
      | throw "a computational field path selected a proof field"
    let some node := graph.find value.value
      | throw "the selected value is outside the visible graph"
    if node.payload.data.storedFields?.isNone then
      if let some retained ← graph.projected? value #[projection] then
        value := retained
        continue
    match node.payload.data with
    | .closure .. | .ownedToken .. => return some (value, path.extract offset path.size)
    | .container container =>
      if container.fields.isNone then return none
      value ← graph.project value index
    | .product .. => value ← graph.project value index
    | .portable .. => throw "the selected value has no native record access interface"
  return some (value, #[])

end CasRuntime
