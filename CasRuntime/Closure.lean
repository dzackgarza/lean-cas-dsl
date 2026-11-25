module

public import CasRuntime.PreparedRequest
public import CasCompiler.PointPath

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend

/-- Operational code of a kernel closure. The value node retains the actual captures.
Source: data model §5, ComputationalClosure, lean-cas-dsl#66 comment 6664275536. -/
inductive ClosureCode
  /-- A checked source term. A field or application demand lowers that eliminator on it. -/
  | term (source : ClosedTerm)
  /-- A formal selected leg keeps its native continuation and, for a direct construction,
  its unchanged released named packet. Formation does not demand a whole cone. A created
  source leg has no target-row packet and retains only its scoped native continuation. -/
  | formalLeg (source : ClosedTerm) (packet : Option ValueContainer)
  /-- A published family at its prepared parameters, with the fields already selected.
  Its realization is selected when an action reaches actual arguments
  (execution contract v2 §5.2, lean-cas-dsl#69 comment 6664277464). -/
  | family (request : PreparedRequest) (path : Array FieldLayout)
  /-- A formal created object retains its complete source preparation and actual original
  inputs. Its native field demand completes the fixed creation against this exact owner. -/
  | creationOwner (source : PreparedCreationFamily)
  /-- An actual returned map with its originally selected provider and native carrier path. -/
  | retainedPoint (request : PreparedRequest) (registration : Registration)
      (parameters : ValueContainer) (source target : ValueBinding) (packet : ValueContainer)
      (path : NativePointPath request.source)
  /-- Components of an actual completed cone retain its whole original data packet. -/
  | constructionLeg (request : PreparedRequest) (registration : Registration)
      (diagram packet : ValueContainer) (ports : Array (Option ValueBinding))
      (path : Array Name) (retained : Array ValueBinding)

/-- Authenticate a supplied family from the actual callable's retained code. The code table
fixes the original preparation, native field path and captures; equality of native types or
source expressions cannot select another family. -/
opaque PreparedRequest.requireFamily (request family : PreparedRequest)
    (path : Array FieldLayout) (graph : ValueGraph)
    (codes : Std.HashMap (RuntimeId .program) ClosureCode) : MetaM Unit := do
  let .apply callable _ _ := request.action
    | throwError "a prepared family invocation requires its actual callable"
  let code ← IO.ofExcept <| (graph.callable callable).mapError IO.userError
  let some node := graph.find code.value
    | throwError "the family callable is outside its visible graph"
  let .closure program captures := node.payload.data
    | throwError "the family callable has no retained native code"
  let some (.family original selected) := codes[program]?
    | throwError "the family callable lost its original prepared family"
  family.requirePreparation original.roles.scope
  unless path.map (·.projection) == selected.map (·.projection) do
    throwError "the family invocation changed its actual callable's native field path"
  unless captures.size == family.scope.size &&
      (captures.zip family.scope).all (fun (left, right) =>
        left.value == right.value && left.associationIds == right.associationIds) do
    throwError "the family invocation changed its actual callable's complete captures"

end CasRuntime
