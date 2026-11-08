module

public import CasCompiler.Surface
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

-- Match the complete native diagram, including its category structure, before
-- projecting any field. Reuse: LimitEntry and the native LimitCone/ColimitCocone family.
private def limitPresentation (row : LimitEntry) (diagram : Expr) :
    TermElabM (Option Expr) := do
  discard <| checkedDeclaration row.declaration
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (parameters, _, result) ← forallMetaTelescopeReducing (← inferType declaration)
  let result ← whnfR result
  let constructor := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
    else ``CategoryTheory.Limits.LimitCone
  unless result.isAppOf constructor do
    throwError "the registered universal presentation has a different native result family"
  let expected ← mkAppM constructor #[diagram]
  unless ← isDefEq result expected do return none
  let presentation ← instantiateMVars (mkAppN declaration parameters)
  if presentation.hasMVar || presentation.hasLevelMVar then
    throwError "the registered universal presentation requires its complete declaration parameters"
  return some (sourceReference ``LimitEntry row.id.raw row.declaration presentation)

/-- Form the declared binary presentation at the original complete source objects.
Reuse: Limits.pair, LimitEntry and the accepted native cone/cocone projections.
The category bundle fixes the diagram's chosen structure and dependent parameters. -/
opaque sourceBinaryLimit (left right : NativeSourceJudgement) (colimit : Bool) :
    TermElabM NativeSourceJudgement := do
  let left ← if left.category.isSome then pure left else sourceSetJudgement .object left.value
  let right ← if right.category.isSome then pure right else sourceSetJudgement .object right.value
  let some source := left.category
    | throwError "the source binary construction requires its selected category"
  let some target := right.category
    | throwError "the source binary construction requires its selected category"
  unless source.role == .object && target.role == .object do
    throwError "source binary construction requires objects"
  unless source.expression.syntacticEq target.expression &&
      (← isDefEq source.bundle target.bundle) do
    throwError "source binary construction has different complete selected categories"
  let state ← semanticState
  let #[category] := state.categories.filter (·.expression.syntacticEq source.expression)
    | throwUnsupportedSource "source binary construction requires its declared complete category"
  discard <| checkedDeclaration category.declaration
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[source.bundle]
  let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[source.bundle]
  let diagram ← mkAppOptM ``CategoryTheory.Limits.pair
    #[some carrier, some categoryInstance, some left.value, some right.value]
  let shape := if colimit then "coproduct" else "product"
  let mut candidates := #[]
  for row in state.limits do
    unless row.category == category.id && row.colimit == colimit && row.shape == shape do continue
    let applicable ← withoutModifyingState do
      return (← limitPresentation row diagram).isSome
    if applicable then candidates := candidates.push row
  let #[row] := candidates
    | if candidates.isEmpty then
        throwUnsupportedSource
          "source binary construction has no applicable declared universal presentation"
      else
        throwSemanticAmbiguity
          "source binary construction requires its selected universal presentation"
  let some presentation ← limitPresentation row diagram
    | throwError "the selected universal presentation changed its complete diagram"
  let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  unless ← isDefEq (← inferType apex) carrier do
    throwError "the universal presentation changed its complete selected category"
  return ⟨apex, some ⟨.object, source.expression, source.bundle, none⟩⟩

end CasCompiler
