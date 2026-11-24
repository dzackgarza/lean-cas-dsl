module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import CasCompiler.Elaborate
import CasCompiler.SourceCarrier

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
  let interface ← prepareLimitInterface row presentation
  let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  unless ← isDefEq (← inferType apex) carrier do
    throwError "the universal presentation changed its complete selected category"
  -- The apex is the registered limit's named object at its diagram, as for a limit named by
  -- its shape: the lowerer sends it as that row's descriptor, not the presentation record.
  let value ← sourceReferenceAt ``LimitEntry row.id.raw row.declaration presentation apex
  let cone ← retainSourceApplication row.declaration presentation cone
  return ⟨value,
    some ⟨.object, source.expression, source.bundle, none,
      some ⟨row.id.raw, row.declaration, cone, colimit, source.expression, source.bundle,
        presentation, diagram, interface⟩⟩⟩

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
    let diagram ← mkAppM ``CategoryTheory.Limits.cospan #[left.value, right.value]
    let mappedDiagram ← mkAppM ``CategoryTheory.Functor.comp #[diagram, routed.functor]
    let leftImage ← mkAppM ``CategoryTheory.Functor.map #[routed.functor, left.value]
    let rightImage ← mkAppM ``CategoryTheory.Functor.map #[routed.functor, right.value]
    discard <| checkedDeclaration row.declaration
    let targetPresentation ← mkAppM row.declaration #[leftImage, rightImage]
    let interface ← prepareLimitInterface row targetPresentation (some mappedDiagram)
    let some comparison := interface.standardization
      | throwUnsupportedSource "the created limit requires its declared diagram standardization"
    let comparison ← exprToSyntax comparison
    let declaredPresentation := targetPresentation
    let targetPresentation ← exprToSyntax targetPresentation
    let (f, g) := (← exprToSyntax left.value, ← exprToSyntax right.value)
    let presentation ← elabTermAndSynthesize (← `(
      letI : CategoryTheory.CreatesLimit (CategoryTheory.Limits.cospan $f $g) $functor :=
        (($evidence : CategoryTheory.CreatesLimitsOfShape CategoryTheory.Limits.WalkingCospan
          $functor).CreatesLimit (K := CategoryTheory.Limits.cospan $f $g))
      let universal :=
        (CategoryTheory.Limits.IsLimit.postcomposeInvEquiv $comparison
          ($targetPresentation).cone).symm ($targetPresentation).isLimit
      (⟨CategoryTheory.liftLimit (K := CategoryTheory.Limits.cospan $f $g) (F := $functor)
          universal,
        CategoryTheory.liftedLimitIsLimit
          (K := CategoryTheory.Limits.cospan $f $g) (F := $functor) universal⟩ :
        CategoryTheory.Limits.LimitCone (CategoryTheory.Limits.cospan $f $g)))) none
    let presentation ← instantiateMVars presentation
    if presentation.hasMVar || presentation.hasLevelMVar then
      throwError "the created {shape} has undetermined parameters"
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    let value ← sourceReferenceAt ``LimitEntry row.id.raw row.declaration declaredPresentation apex
    let cone ← retainSourceApplication row.declaration declaredPresentation cone
    return some ⟨value,
      some ⟨.object, selected.expression, selected.bundle, none,
        some ⟨row.id.raw, row.declaration, cone, false,
          selected.expression, selected.bundle, presentation, diagram, interface⟩⟩⟩
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
  let references := Array.replicate maps.size (← getRef)
  let present (row : LimitEntry) : TermElabM (Option Expr) := do
    discard <| checkedDeclaration row.declaration
    let declaration ← mkConstWithFreshMVarLevels row.declaration
    let explicitCount ← withoutModifyingState do
      let (_, binders, result) ← forallMetaTelescopeReducing (← inferType declaration)
      let constructor := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
        else ``CategoryTheory.Limits.LimitCone
      unless (← whnfR result).isAppOf constructor do
        throwError "the registered universal presentation has a different native result family"
      return (binders.filter (·.isExplicit)).size
    unless maps.size == explicitCount do return none
    let applied ← elabSourceApplicationApplicable declaration references none fun index _ => do
      let some map := maps[index]?
        | throwError "the universal presentation lost an original map"
      return .ok map.value
    let .ok (value, _) := applied | return none
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the presentation of {shape} has undetermined parameters"
    return some value
  let mut candidates := #[]
  for row in rows do
    -- Applicability is the declaration's own typing at the actual maps.
    let accepts ← withoutModifyingState do
      return (← present row).isSome
    if accepts then candidates := candidates.push row
  if candidates.isEmpty then
    if let some created ← createdLimit shape selected maps then return some created
  let #[row] := candidates
    | if candidates.isEmpty then
        throwUnsupportedSource m!"no registered {shape} accepts these maps"
      else throwSemanticAmbiguity s!"several registered presentations of {shape} accept these maps"
  let some presentation ← present row
    | throwError "the selected universal presentation no longer accepts its original maps"
  let interface ← prepareLimitInterface row presentation
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  let value ← sourceReferenceAt ``LimitEntry row.id.raw row.declaration presentation apex
  let cone ← retainSourceApplication row.declaration presentation cone
  return some ⟨value,
    some ⟨.object, selected.expression, selected.bundle, none,
      some ⟨row.id.raw, row.declaration, cone, row.colimit,
        selected.expression, selected.bundle, presentation, interface.diagram, interface⟩⟩⟩

/-- The object of a diagram's index type that the ordinal `ordinal` names: the number itself in
`ℕ`, `⟨ordinal, _⟩` in `Fin n` when it is below `n`, else the `ordinal`-th constructor of a closed
enumeration. A native Discrete index wraps that same underlying selection by Discrete.mk.
Any other index, or an ordinal outside it, is invalid.
Reference: the original reader's `constructionIndex` (CasCatalogue/Language.lean). -/
private partial def constructionIndex (indexType : Expr) (ordinal : Nat) : TermElabM Expr := do
  let indexType ← instantiateMVars (← whnfR indexType)
  if indexType.hasMVar || indexType.hasLevelMVar then
    throwStratum .invalid m!"the construction index type is not determined"
  if indexType.isAppOfArity ``CategoryTheory.Discrete 1 then
    let selected ← constructionIndex indexType.appArg! ordinal
    let index ← mkAppOptM ``CategoryTheory.Discrete.mk
      #[some indexType.appArg!, some selected]
    unless ← isDefEq (← inferType index) indexType do
      throwStratum .invalid m!"the index constructor does not inhabit {indexType}"
    return index
  if indexType.isConstOf ``Nat then return mkNatLit ordinal
  if indexType.isAppOfArity ``Fin 1 then
    let bound := indexType.appArg!
    let below ← mkAppM ``LT.lt #[mkNatLit ordinal, bound]
    let proof ← try mkDecideProof below
      catch _ => throwStratum .invalid m!"the construction index {ordinal} is outside {indexType}"
    return mkApp3 (mkConst ``Fin.mk) bound (mkNatLit ordinal) proof
  let some name := indexType.getAppFn.constName?
    | throwStratum .invalid m!"the construction index {indexType} is not a closed enumeration"
  let .inductInfo info ← getConstInfo name
    | throwStratum .invalid m!"the construction index {indexType} is not an enumeration"
  for constructor in info.ctors do
    let .ctorInfo constructorInfo ← getConstInfo constructor | unreachable!
    unless constructorInfo.numFields == 0 do
      throwStratum .invalid m!"an ordinal cannot select a constructor with fields of {indexType}"
  let some constructor := info.ctors[ordinal]?
    | throwStratum .invalid m!"the construction index {ordinal} is outside {indexType}"
  let index ← mkAppOptM constructor (indexType.getAppArgs.map some)
  unless ← isDefEq (← inferType index) indexType do
    throwStratum .invalid m!"the index constructor does not inhabit {indexType}"
  return index

/-- `K.leg(j)`: the defining leg of the registered limit or colimit `K` at the object of its shape
that the ordinal `j` names (constitution C7: a universal construction supplies its defining maps).
The row and the cone or cocone are the selection that the formation of `K` retained in its
judgement (constitution C23); a receiver with no such selection is not a limit. The leg is the
cone's `π` or the cocone's `ι` at that object, marked with the limit's row and the ordinal, so
that it is sent as the limit's named leg and not unfolded (C22). Reference: the original reader's
`constructionLeg` (CasCatalogue/Language.lean). -/
def sourceLimitLeg? (receiver : NativeSourceJudgement) (ordinal : Nat) :
    TermElabM (Option NativeSourceJudgement) := do
  let some category := receiver.category | return none
  let some selection := category.limit | return none
  let cone := selection.cone
  let some presentation ← sourceApplication? selection.declaration cone
    | throwError "the selected construction lost its original registered application"
  let colimit := selection.colimit
  let leg ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.ι
    else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[leg]
  let .forallE _ indexType _ _ ← whnf (← inferType component)
    | throwError "the defining leg has no shape index"
  let hom := mkApp component (← constructionIndex indexType ordinal)
  check hom
  -- The component belongs to this cone, while its apex is the actual selected source
  -- occurrence. Preserve that occurrence in the native hom type before a functor action
  -- reads its implicit endpoints. The other endpoint remains the original diagram object.
  let homType ← inferType hom
  let homType ← if homType.isAppOfArity ``Quiver.Hom 4 then pure homType else whnfR homType
  unless homType.isAppOfArity ``Quiver.Hom 4 do
    throwError "the defining leg lost its complete native morphism type"
  let endpoints := homType.getAppArgs.set! (if colimit then 3 else 2) receiver.value
  let hom ← mkExpectedTypeHint hom (mkAppN homType.getAppFn endpoints)
  check hom
  let .mdata data body ←
      sourceReferenceAt ``LimitEntry selection.row selection.declaration presentation hom
    | throwError "internal: a source reference is not an annotation"
  -- The diagram endpoint is a projection of this actual selected leg, just as the
  -- endpoint of a named map is a projection of that map. In particular, a functor
  -- action must not have to execute the diagram's object selector to reconstruct it.
  -- The selected apex remains its original binding in the Arrow constructor. The
  -- selection identity also makes the endpoint and the map share the same leg occurrence.
  let hom ← selectMorphism (.mdata (data.setNat `CasCompiler.source.leg ordinal) body)
  return some ⟨hom, some ⟨.morphism, selection.category, selection.bundle, none, none⟩⟩

end CasCompiler
