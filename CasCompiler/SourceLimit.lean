module

public import CasCompiler.SourceCarrier
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
  return some presentation

/-- Form the declared binary presentation at the original complete source objects.
Reuse: Limits.pair, LimitEntry and the accepted native cone/cocone projections.
The category bundle fixes the diagram's chosen structure and dependent parameters. -/
opaque sourceBinaryLimit (left right : NativeSourceJudgement) (colimit : Bool) :
    TermElabM NativeSourceJudgement := do
  let left ← if left.category.isSome then pure left else sourceSetJudgement .object left.value
  let right ← if right.category.isSome then pure right else sourceSetJudgement .object right.value
  -- Objects of different selected categories meet in sets: each operand is its carrier, read
  -- through its whole structural carrier route (`Fin(2) × ℤ/3`).
  let (left, right) ← match left.category, right.category with
    | some source, some target =>
      if source.expression.syntacticEq target.expression then pure (left, right)
      else pure (← sourceCarrier left, ← sourceCarrier right)
    | _, _ => pure (left, right)
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
  -- The apex is the registered limit's named object at its diagram, as for a limit named by
  -- its shape: the lowerer sends it as that row's descriptor, not the presentation record.
  return ⟨sourceReference ``LimitEntry row.id.raw row.declaration apex,
    some ⟨.object, source.expression, source.bundle, none⟩⟩

/-- The limit of shape `shape` of the maps `maps` of a category that only creates it: the
registered limit of the image diagram along the structural step `U` of a registered creation lift
(LiftKind.createsLimits), transported to the image of the source diagram (Mathlib
`diagramIsoCospan`, `IsLimit.postcomposeInvEquiv`) and lifted back along `U` (Mathlib
`liftLimit`). Reference: the original reader's `Semantic.limit` and `liftedLimitCone`. -/
private def createdLimit (shape : String) (selected : NativeSourceCategory)
    (maps : Array NativeSourceJudgement) : TermElabM (Option NativeSourceJudgement) := do
  let state ← semanticState
  for lift in state.lifts do
    unless lift.kind == .createsLimits shape do continue
    let some edge := state.structuralEdge? lift.edge | continue
    unless edge.source.syntacticEq selected.expression do continue
    let some target := state.categories.find? (·.expression.syntacticEq edge.target) | continue
    let some row := state.limits.find? fun limit =>
        !limit.colimit && limit.category == target.id && limit.shape == shape
      | continue
    let #[left, right] := maps
      | throwUnsupportedSource m!"a created {shape} takes the two maps of its cospan"
    unless shape == "pullback" do
      throwUnsupportedSource m!"the created {shape} has no diagram constructor in the reader"
    let some steps := state.routeEdges? selected.expression target.expression #[lift.edge]
      | throwError "the creation lift {lift.id.raw} is not a route of its own step"
    let routed ← nativeRouteFunctor state
      { source := selected.expression, target := target.expression, steps } selected.bundle
    let functor ← exprToSyntax routed.functor
    discard <| checkedDeclaration lift.evidence
    let evidence ← exprToSyntax (← mkConstWithFreshMVarLevels lift.evidence)
    discard <| checkedDeclaration row.declaration
    let declaration ← exprToSyntax (← mkConstWithFreshMVarLevels row.declaration)
    let (f, g) := (← exprToSyntax left.value, ← exprToSyntax right.value)
    let apex ← elabTermAndSynthesize (← `(
      letI : CategoryTheory.CreatesLimit (CategoryTheory.Limits.cospan $f $g) $functor :=
        (($evidence : CategoryTheory.CreatesLimitsOfShape CategoryTheory.Limits.WalkingCospan
          $functor).CreatesLimit (K := CategoryTheory.Limits.cospan $f $g))
      (CategoryTheory.liftLimit (K := CategoryTheory.Limits.cospan $f $g) (F := $functor)
        ((CategoryTheory.Limits.IsLimit.postcomposeInvEquiv
            (CategoryTheory.Limits.diagramIsoCospan
              (CategoryTheory.Functor.comp (CategoryTheory.Limits.cospan $f $g) $functor))
            ($declaration (CategoryTheory.Functor.map $functor $f) (CategoryTheory.Functor.map $functor $g)).cone).symm
          ($declaration (CategoryTheory.Functor.map $functor $f) (CategoryTheory.Functor.map $functor $g)).isLimit)).pt)) none
    let apex ← instantiateMVars apex
    if apex.hasMVar || apex.hasLevelMVar then
      throwError "the created {shape} has undetermined parameters"
    return some ⟨sourceReference ``LimitEntry row.id.raw row.declaration apex,
      some ⟨.object, selected.expression, selected.bundle, none⟩⟩
  return none

/-- A registered limit or colimit named by its shape and applied to the maps of its diagram
(`pullback(f, g)`, `cokernel(m)`): the apex of the declared cone or cocone at those maps, in the
category of the maps. Reuse: LimitEntry and the native LimitCone/ColimitCocone family. A row
whose declaration does not accept the maps is not a candidate; several accepting rows are a
semantic ambiguity. -/
opaque sourceNamedLimit (shape : String) (maps : Array NativeSourceJudgement) :
    TermElabM (Option NativeSourceJudgement) := do
  let state ← semanticState
  let rows := state.limits.filter (·.shape == shape)
  if rows.isEmpty then return none
  let some selected := maps[0]?.bind (·.category)
    | throwError "the universal construction {shape} requires maps of a selected category"
  unless maps.all (·.category.any (·.role == .morphism)) do
    throwError "the universal construction {shape} is applied to the maps of its diagram"
  let present := fun (row : LimitEntry) => do
    discard <| checkedDeclaration row.declaration
    let declaration ← mkConstWithFreshMVarLevels row.declaration
    let value ← elabAppArgs declaration #[] (maps.map (Arg.expr ·.value)) none false false
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the presentation of {shape} has undetermined parameters"
    return value
  let mut candidates := #[]
  for row in rows do
    -- Applicability is the declaration's own typing at the actual maps.
    let accepts ← withoutModifyingState do
      try discard <| present row; pure true
      catch _ => pure false
    if accepts then candidates := candidates.push row
  if candidates.isEmpty then
    if let some created ← createdLimit shape selected maps then return some created
  let #[row] := candidates
    | if candidates.isEmpty then
        throwUnsupportedSource m!"no registered {shape} accepts these maps"
      else throwSemanticAmbiguity s!"several registered presentations of {shape} accept these maps"
  let presentation ← present row
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  return some ⟨sourceReference ``LimitEntry row.id.raw row.declaration apex,
    some ⟨.object, selected.expression, selected.bundle, none⟩⟩

end CasCompiler
