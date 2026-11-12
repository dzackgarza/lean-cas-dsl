module

public import CasCompiler.Surface

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- A registered power object at its actual base object. -/
structure NativePowerObject where
  row : PowerObjectEntry
  base : Expr

/-- The registered power object whose object at some base is the native type `type`.
Source: Registry.Entry.PowerObjectEntry; `𝒫(X)` is the object family of the row at `X`.
Two power objects with the same native type remain distinct, so several matches are ambiguous. -/
def sourcePowerObject? (type : Expr) : TermElabM (Option NativePowerObject) := do
  let state ← semanticState
  let mut found := #[]
  for row in state.powerObjects do
    let some object := state.objects.find? (·.id == row.object)
      | throwError "the registered power object {row.id.raw} has no object family"
    discard <| checkedDeclaration object.declaration
    let family ← mkConstWithFreshMVarLevels object.declaration
    let base ← mkFreshExprMVar none
    let applicable ← withoutModifyingState do
      let object ← elabAppArgs family #[] #[Arg.expr base] none false false
      isDefEq object type
    unless applicable do continue
    let object ← elabAppArgs family #[] #[Arg.expr base] none false false
    discard <| isDefEq object type
    let base ← instantiateMVars base
    if base.hasMVar || base.hasLevelMVar then
      throwError "the registered power object is not determined by its native type"
    found := found.push ⟨row, base⟩
  match found with
  | #[] => return none
  | #[selected] => return some selected
  | _ => throwSemanticAmbiguity "the native type is the object of several registered power objects"

/-- The registered power object at the base `base`: the rows whose object family accepts it. -/
def sourcePowerObjectAt (base : Expr) : TermElabM NativePowerObject := do
  let state ← semanticState
  let mut found := #[]
  for row in state.powerObjects do
    let some object := state.objects.find? (·.id == row.object)
      | throwError "the registered power object {row.id.raw} has no object family"
    discard <| checkedDeclaration object.declaration
    let family ← mkConstWithFreshMVarLevels object.declaration
    let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
    let some parameter := parameters[0]?
      | throwError "the registered power object {row.id.raw} has no base parameter"
    if ← withoutModifyingState (isDefEq (← inferType parameter) (← inferType base)) then
      found := found.push (⟨row, base⟩ : NativePowerObject)
  match found with
  | #[selected] => return selected
  | #[] => throwUnsupportedSource "no registered power object accepts this base object"
  | _ => throwSemanticAmbiguity "several registered power objects accept this base object"

/-- Apply a declaration of the power object at its base, then at the remaining arguments. -/
private def atBase (power : NativePowerObject) (declaration : Name) (arguments : Array Expr) :
    TermElabM Expr := do
  discard <| checkedDeclaration declaration
  let function ← mkConstWithFreshMVarLevels declaration
  elabAppArgs function #[] ((#[power.base] ++ arguments).map Arg.expr) none false false

/-- The value of a global element `1 ⟶ Y` at the power object's registered point.
Source: PowerObjectEntry.point, the declaration consumers use to extract a value from a global
element. -/
def sourceGlobalValue (power : NativePowerObject) (element : Expr) (expected : Option Expr) :
    TermElabM Expr := do
  discard <| checkedDeclaration power.row.point
  let point ← mkConstWithFreshMVarLevels power.row.point
  let function ← sourceSetFunction element
  elabAppArgs function #[] #[Arg.expr point] expected false false

/-- The subset `{a₁, …, aₙ} ⊆ X`, through the registered subset-literal form of the power object.
The literal is the Finset of the elements, formed by the quotient map `List.toFinset` that the
literal form's normal form names; its denotation is the registered global element of `𝒫(X)`.
Source: Registry.Entry.SubsetLiteralEntry and lit.sets.finite_subsets. -/
def sourceSubsetLiteral (power : NativePowerObject) (elements : Array Expr) (expected : Expr) :
    TermElabM Expr := do
  let rows := (← semanticState).subsetLiterals.filter (·.powerObject == power.row.id)
  let #[row] := rows
    | if rows.isEmpty then
        throwUnsupportedSource "the selected power object has no registered subset-literal form"
      else throwSemanticAmbiguity "the selected power object has several subset-literal forms"
  unless row.type == ``Finset do
    throwUnsupportedSource m!"the subset-literal form {row.id.raw} has an unread literal type"
  let list ← mkListLit power.base elements.toList
  let literal ← mkAppM ``List.toFinset #[list]
  let element ← atBase power row.denotation #[literal]
  let value ← sourceGlobalValue power element (some expected)
  return sourceReference ``SubsetLiteralEntry row.id.raw row.denotation value

/-- A subset `A ⊆ X` used as an object is the set of its members, through the registered extent
of its power object. The global element of `𝒫(X)` at the point is the constant map with value
`A`, since the point's source is the terminal object.
Source: PowerObjectEntry.extent; the original reader's rule that a subset names its extent. -/
def sourceExtent? (judgement : NativeSourceJudgement) : TermElabM (Option NativeSourceJudgement) := do
  if judgement.category.isSome then return none
  let some power ← sourcePowerObject? (← instantiateMVars (← inferType judgement.value))
    | return none
  discard <| checkedDeclaration power.row.extent
  let extent ← mkConstWithFreshMVarLevels power.row.extent
  let element ← mkFreshExprMVar none
  discard <| elabAppArgs extent #[] #[Arg.expr power.base, Arg.expr element] none false false
  let elementType ← instantiateMVars (← inferType element)
  let constant ← withLocalDeclD `point (← mkFreshTypeMVar) fun point => do
    mkLambdaFVars #[point] judgement.value
  let global ← elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom) #[]
    #[Arg.expr constant] (some elementType) false false
  let object ← elabAppArgs extent #[] #[Arg.expr power.base, Arg.expr global] none false false
  return some (← sourceSetJudgement .object object)

/-- `x ∈ A` for a subset `A` of `X`: the registered membership `X × 𝒫 X → Ω` at the pair. -/
def sourceMembership (power : NativePowerObject) (element container : Expr) : TermElabM Expr := do
  let member ← atBase power power.row.member #[]
  let function ← sourceSetFunction member
  let pair ← mkAppM ``Prod.mk #[element, container]
  elabAppArgs function #[] #[Arg.expr pair] none false false

/-- `{t ∈ X | P}`: the subset that the predicate `t ↦ P : X → Ω` classifies, through the
registered transpose. `predicate` is the native function into the truth values. -/
def sourceComprehension (power : NativePowerObject) (predicate : Expr) (expected : Option Expr) :
    TermElabM Expr := do
  let transpose ← mkConstWithFreshMVarLevels power.row.transpose
  discard <| checkedDeclaration power.row.transpose
  let classifier ← mkFreshExprMVar none
  discard <| elabAppArgs transpose #[] #[Arg.expr power.base, Arg.expr classifier] none false false
  let classifierType ← instantiateMVars (← inferType classifier)
  let classifierValue ← elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom) #[]
    #[Arg.expr predicate] (some classifierType) false false
  let element ← atBase power power.row.transpose #[classifierValue]
  sourceGlobalValue power element expected

/-- `{e | t ∈ X}`: the image of the whole map `t ↦ e : X → Y` in `𝒫(Y)`, through the registered
image of the power object of `Y`. `target` is the power object at `Y`. -/
def sourceImage (target : NativePowerObject) (domain function : Expr) (expected : Option Expr) :
    TermElabM Expr := do
  let image ← mkConstWithFreshMVarLevels target.row.image
  discard <| checkedDeclaration target.row.image
  let arrow ← mkFreshExprMVar none
  discard <| elabAppArgs image #[] #[Arg.expr domain, Arg.expr target.base, Arg.expr arrow]
    none false false
  let arrowType ← instantiateMVars (← inferType arrow)
  let arrowValue ← elabAppArgs (← mkConstWithFreshMVarLevels ``TypeCat.ofHom) #[]
    #[Arg.expr function] (some arrowType) false false
  let element ← elabAppArgs image #[] #[Arg.expr domain, Arg.expr target.base, Arg.expr arrowValue]
    none false false
  sourceGlobalValue target element expected

end CasCompiler
