module

public import CasCompiler.Surface
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The complete native meaning of an explicitly selected registered comparison.
The actual edge actions are retained for constructor coherence; their composites alone
cannot supply the expansion comparisons required by the released component interface. -/
structure NativeSourceCell where
  entry : CellEntry
  application : Expr
  inverse : Bool
  constructors : Array ConstructorId := #[]
  source : CategoryExpr
  sourceBundle : Expr
  target : CategoryExpr
  targetBundle : Expr
  left : NativeRouteFunctor
  right : NativeRouteFunctor
  transformation : Expr
  isomorphism : Option Expr

private def checkNativeCell (source target left right transformation : Expr) : MetaM Unit := do
  let (leftSource, leftTarget) ← functorCategoryBundles left
  let (rightSource, rightTarget) ← functorCategoryBundles right
  unless ← isDefEq leftSource source <&&> isDefEq rightSource source <&&>
      isDefEq leftTarget target <&&> isDefEq rightTarget target do
    throwError "the selected cell has different complete native categories"
  let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
  unless ← isDefEq (← inferType transformation) expected do
    throwError "the selected cell has different complete native functor endpoints"

/-- Check the already applied declaration against its exact registered routes. Selection
comes from the row supplied by the reader; neither the receiver's carrier nor a provider
chooses a cell. The receiver later fixes any ordinary application metavariables. -/
def nativeSourceCell (entry : CellEntry) (application : Expr) (inverse : Bool := false) :
    MetaM NativeSourceCell := do
  let state ← semanticState
  let #[original] := state.cells.filter (·.id == entry.id)
    | throwError "a source cell requires its unique registered declaration"
  unless original.declaration == entry.declaration && original.invertible == entry.invertible &&
      original.source.syntacticEq entry.source && original.target.syntacticEq entry.target &&
      original.left == entry.left && original.right == entry.right do
    throwError "the selected cell changed its accepted registration"
  if inverse && !entry.invertible then
    throwStratum .invalid "the source cell has no registered inverse"
  discard <| checkedDeclaration entry.declaration
  let application ← instantiateMVars application
  unless application.consumeMData.getAppFn.isConstOf entry.declaration do
    throwError "the selected cell lost its original declaration application"
  let application := sourceReference ``CellEntry entry.id.raw entry.declaration application
  let transformation ← if entry.invertible then
      mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[application]
    else pure application
  let type ← whnfR (← inferType transformation)
  let declaredLeft ← if type.isAppOfArity ``Quiver.Hom 4 then
      pure type.getAppArgs[2]!
    else if type.isAppOfArity ``CategoryTheory.NatTrans 6 then
      pure type.getAppArgs[4]!
    else throwError "the applied cell has no complete native transformation interface"
  let (source, target) ← functorCategoryBundles declaredLeft
  let left ← nativeEdgePathFunctor state entry.left source
  let right ← nativeEdgePathFunctor state entry.right source
  let (left, right) := if inverse then (right, left) else (left, right)
  checkNativeCell source target left.functor right.functor transformation
  let isomorphism ← if entry.invertible then do
      let directed ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[application]
        else pure application
      pure (some directed)
    else pure none
  return {
    entry := entry
    application := application
    inverse := inverse
    source := entry.source
    sourceBundle := source
    target := entry.target
    targetBundle := target
    left := left
    right := right
    transformation := transformation
    isomorphism := isomorphism }

private def selectedConstructorApplication (entry : ConstructorEntry) (field : Name)
    (categories arguments : Array Expr) : MetaM Expr := do
  discard <| checkedDeclaration field
  let value ← applyConstructorInterface field categories arguments
  let kind := if field == entry.semantics then ``ConstructorEntry
    else if entry.functorialAction == some field then ``ConstructorEntry.functorialAction
    else if entry.comparisonAction == some field then ``ConstructorEntry.comparisonAction
    else if entry.identityComparison == some field then ``ConstructorEntry.identityComparison
    else ``ConstructorEntry.compositionComparison
  return sourceReference kind entry.id.raw field value

private def checkNativeIso (left right value : Expr) : MetaM Unit := do
  let expected ← mkAppM ``CategoryTheory.Iso #[left, right]
  unless ← isDefEq (← inferType value) expected do
    throwError "the selected constructor comparison changed its complete native endpoints"

/-- Expand a constructor's action on this exact route with its accepted identity and
composition comparisons. The result is the composite of the individually mapped actions,
with an actual isomorphism from the action on the original complete composite. -/
private def mapCellRoute (entry : ConstructorEntry) (source : Expr)
    (route : NativeRouteFunctor) : MetaM (NativeRouteFunctor × Expr) := do
  let some action := entry.functorialAction
    | throwStratum .invalid "the selected constructor has no declared functor action"
  let some identity := entry.identityComparison
    | throwStratum .invalid "the selected constructor has no declared identity comparison"
  let some composition := entry.compositionComparison
    | throwStratum .invalid "the selected constructor has no declared composition comparison"
  let mappedSource ← selectedConstructorApplication entry entry.semantics #[source] #[source]
  let mappedTarget ← selectedConstructorApplication entry entry.semantics
    #[route.target] #[route.target]
  let whole ← selectedConstructorApplication entry action #[source, route.target] #[route.functor]
  if route.actions.isEmpty then
    let result ← categoryIdentity mappedSource
    let comparison ← selectedConstructorApplication entry identity #[source] #[source]
    checkNativeIso whole result comparison
    return (⟨result, mappedTarget, #[]⟩, comparison)
  let first := route.actions[0]!
  let (firstSource, firstTarget) ← functorCategoryBundles first
  unless ← isDefEq firstSource source do
    throwError "the selected cell route lost its original starting category"
  let mapped ← selectedConstructorApplication entry action #[source, firstTarget] #[first]
  let mut original := first
  let mut originalTarget := firstTarget
  let mut expanded := mapped
  let mut actions := #[mapped]
  let mut comparison ← mkAppM ``CategoryTheory.Iso.refl #[mapped]
  for next in route.actions.extract 1 route.actions.size do
    let (nextSource, nextTarget) ← functorCategoryBundles next
    unless ← isDefEq nextSource originalTarget do
      throwError "the selected cell route lost an original intermediate category"
    let mappedNext ← selectedConstructorApplication entry action
      #[originalTarget, nextTarget] #[next]
    let step ← selectedConstructorApplication entry composition
      #[source, originalTarget, nextTarget] #[original, next]
    let carried ← mkAppM ``CategoryTheory.Functor.isoWhiskerRight #[comparison, mappedNext]
    comparison ← mkAppM ``CategoryTheory.Iso.trans #[step, carried]
    original ← mkFunctorComp original next
    originalTarget := nextTarget
    expanded ← mkFunctorComp expanded mappedNext
    actions := actions.push mappedNext
  checkNativeIso whole expanded comparison
  return (⟨expanded, mappedTarget, actions⟩, comparison)

/-- Apply one accepted unary constructor to an invertible cell, retaining both route
expansion comparisons. This is precisely the constructor-induced component contract. -/
def NativeSourceCell.construct (cell : NativeSourceCell) (id : ConstructorId) :
    MetaM NativeSourceCell := do
  let some entry := (← semanticState).constructor? id
    | throwStratum .invalid "the source comparison constructor is absent"
  unless entry.signature == #[.category] do
    throwStratum .invalid "the source comparison constructor does not have a unary category interface"
  let some action := entry.comparisonAction
    | throwStratum .invalid "the source comparison constructor has no declared comparison action"
  let some original := cell.isomorphism
    | throwStratum .invalid "the source constructor comparison requires an invertible cell"
  let source ← selectedConstructorApplication entry entry.semantics
    #[cell.sourceBundle] #[cell.sourceBundle]
  let target ← selectedConstructorApplication entry entry.semantics
    #[cell.targetBundle] #[cell.targetBundle]
  let (left, leftExpansion) ← mapCellRoute entry cell.sourceBundle cell.left
  let (right, rightExpansion) ← mapCellRoute entry cell.sourceBundle cell.right
  let mapped ← selectedConstructorApplication entry action
    #[cell.sourceBundle, cell.targetBundle] #[original]
  let reverseLeft ← mkAppM ``CategoryTheory.Iso.symm #[leftExpansion]
  let comparison ← mkAppM ``CategoryTheory.Iso.trans #[reverseLeft, mapped]
  let comparison ← mkAppM ``CategoryTheory.Iso.trans #[comparison, rightExpansion]
  checkNativeIso left.functor right.functor comparison
  let transformation ← mkAppM ``CategoryTheory.Iso.hom #[comparison]
  checkNativeCell source target left.functor right.functor transformation
  return { cell with
    constructors := #[id] ++ cell.constructors
    source := .construct id #[.category cell.source]
    sourceBundle := source
    target := .construct id #[.category cell.target]
    targetBundle := target
    left := left
    right := right
    transformation := transformation
    isomorphism := some comparison }

/-- Form the component at the independently read receiver. A constructor path, when supplied,
is outermost first and is applied inside out to the whole retained comparison. -/
def NativeSourceCell.component (cell : NativeSourceCell) (receiver : NativeSourceJudgement) :
    MetaM NativeSourceJudgement := do
  if let some category := receiver.category then
    unless category.role == .object && category.expression.syntacticEq cell.source do
      throwStratum .invalid "the source cell receiver has a different selected category"
    unless ← isDefEq category.bundle cell.sourceBundle do
      throwStratum .invalid "the source cell receiver has different complete native category parameters"
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[cell.sourceBundle]
  unless ← isDefEq (← inferType receiver.value) carrier do
    throwStratum .invalid "the source cell receiver is outside its complete declared domain"
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[cell.transformation, receiver.value]
  let component ← selectMorphism component
  let inputs := #[receiver.value, cell.sourceBundle, cell.targetBundle,
    cell.left.functor, cell.right.functor, cell.transformation] ++ cell.isomorphism.toArray ++
    cell.left.actions ++ cell.right.actions ++ #[cell.application.consumeMData]
  let mut retained := component
  for input in inputs do
    retained ← mkAppM ``Function.const #[← inferType input, retained, input]
  -- The final typed witness is the exact original declaration application. This keeps
  -- sourceApplication? valid outside the selected morphism's expected-type hint.
  let constructors := toJson (cell.constructors.map (·.raw))
  let metadata := KVMap.empty
    |>.setName `CasCompiler.source.kind ``CellEntry
    |>.setString `CasCompiler.source.id cell.entry.id.raw
    |>.setName `CasCompiler.source.declaration cell.entry.declaration
    |>.setName `CasCompiler.source.application cell.entry.declaration
    |>.setBool `CasCompiler.source.cell.component true
    |>.setBool `CasCompiler.source.cell.inverse cell.inverse
    |>.setBool `CasCompiler.source.cell.isomorphism cell.isomorphism.isSome
    |>.setNat `CasCompiler.source.cell.leftActions cell.left.actions.size
    |>.setNat `CasCompiler.source.cell.rightActions cell.right.actions.size
    |>.setString `CasCompiler.source.cell.constructors constructors.compress
  return ⟨.mdata metadata retained,
    some ⟨.morphism, cell.target, ← instantiateMVars cell.targetBundle, none, none⟩⟩

/-- The exact component retained at formation, together with its whole directed cell and
original receiver. Native source closure transports every field in the same telescope. -/
structure NativeSourceCellComponent where
  private mk ::
  cell : NativeSourceCell
  receiver : Expr
  value : Expr

/-- Read only the typed cell envelope emitted by component formation and its original native
aliases. No declaration occurrence, equal carrier or endpoint supplies missing cell data. -/
partial def sourceCellComponent? (value : Expr) : MetaM (Option NativeSourceCellComponent) := do
  let expression ← instantiateMVars value
  match expression with
  | .mdata data body =>
    if !data.getBool `CasCompiler.source.cell.component then return ← sourceCellComponent? body
    let id := data.getString `CasCompiler.source.id
    let #[entry] := (← semanticState).cells.filter (·.id.raw == id)
      | throwError "the retained source cell lost its exact accepted row"
    unless data.getName `CasCompiler.source.kind == ``CellEntry &&
        data.getName `CasCompiler.source.declaration == entry.declaration &&
        data.getName `CasCompiler.source.application == entry.declaration do
      throwError "the retained source cell changed its declaration witness"
    let inverse := data.getBool `CasCompiler.source.cell.inverse
    let hasIso := data.getBool `CasCompiler.source.cell.isomorphism
    unless hasIso == entry.invertible && (!inverse || entry.invertible) do
      throwError "the retained source cell changed its available orientation"
    let encoded := data.getString `CasCompiler.source.cell.constructors
    let .ok parsed := Json.parse encoded
      | throwError "the retained source cell lost its constructor path"
    let .ok names := fromJson? (α := Array String) parsed
      | throwError "the retained source cell has a malformed constructor path"
    unless (toJson names).compress == encoded do
      throwError "the retained source cell has a noncanonical constructor path"
    let constructors := names.map ConstructorId.mk
    let leftCount := data.getNat `CasCompiler.source.cell.leftActions
    let rightCount := data.getNat `CasCompiler.source.cell.rightActions
    let count := 7 + (if hasIso then 1 else 0) + leftCount + rightCount
    let mut current := body
    let mut reversedFields := #[]
    for _ in [:count] do
      unless current.isAppOfArity ``Function.const 4 do
        throwError "the retained source cell lost a complete native interface field"
      reversedFields := reversedFields.push current.getAppArgs[3]!
      current := current.getAppArgs[2]!
    let fields := reversedFields.reverse
    let application := fields.back!
    unless application.consumeMData.getAppFn.isConstOf entry.declaration do
      throwError "the retained source cell has a different original application"
    let receiver := fields[0]!
    let sourceBundle := fields[1]!
    let targetBundle := fields[2]!
    let leftFunctor := fields[3]!
    let rightFunctor := fields[4]!
    let transformation := fields[5]!
    let isomorphism := if hasIso then some fields[6]! else none
    let start := 6 + (if hasIso then 1 else 0)
    let left := NativeRouteFunctor.mk leftFunctor targetBundle (fields.extract start (start + leftCount))
    let right := NativeRouteFunctor.mk rightFunctor targetBundle
      (fields.extract (start + leftCount) (start + leftCount + rightCount))
    let mut source := entry.source
    let mut target := entry.target
    for constructor in constructors.reverse do
      let some original := (← semanticState).constructor? constructor
        | throwError "the retained source cell lost an original constructor"
      unless original.signature == #[.category] && original.functorialAction.isSome &&
          original.comparisonAction.isSome && original.identityComparison.isSome &&
          original.compositionComparison.isSome do
        throwError "the retained source cell constructor lost its complete comparison interface"
      source := .construct constructor #[.category source]
      target := .construct constructor #[.category target]
    checkNativeCell sourceBundle targetBundle leftFunctor rightFunctor transformation
    if let some isomorphism := isomorphism then checkNativeIso leftFunctor rightFunctor isomorphism
    let expected ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, receiver]
    unless ← isDefEq current expected do
      throwError "the retained source cell changed its original native component"
    let cell : NativeSourceCell := {
      entry := entry
      application := application
      inverse := inverse
      constructors := constructors
      source := source
      sourceBundle := sourceBundle
      target := target
      targetBundle := targetBundle
      left := left
      right := right
      transformation := transformation
      isomorphism := isomorphism }
    return some ⟨cell, receiver, value⟩
  | .fvar id =>
    match (← id.getDecl).value? with
    | some original => sourceCellComponent? original
    | none => pure none
  | .letE _ _ original body _ => sourceCellComponent? (body.instantiate1 original)
  | _ =>
    if expression.isAppOfArity ``id 2 then
      sourceCellComponent? expression.getAppArgs[1]!
    else pure none

end CasCompiler
