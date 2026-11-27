module

public import CasRuntime.PreparedRequest
public import CasCompiler.PointPath
public import CasCompiler.SelectionScope

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue CasCatalogue.Backend



inductive ClosureCode

  | term (source : ClosedTerm) (selections : SourceSelectionScope ClosedTerm := {})



  | formalLeg (source : ClosedTerm) (packet : Option ValueContainer)
      (selections : SourceSelectionScope ClosedTerm := {})



  | family (request : PreparedRequest) (path : Array FieldLayout)


  | creationOwner (source : PreparedCreationFamily)

  | retainedPoint (request : PreparedRequest) (registration : Registration)
      (parameters : ValueContainer) (source target : ValueBinding) (packet : ValueContainer)
      (path : NativePointPath request.source)

  | constructionLeg (request : PreparedRequest) (registration : Registration)
      (diagram packet : ValueContainer) (ports : Array (Option ValueBinding))
      (path : Array Name) (retained : Array ValueBinding)




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
