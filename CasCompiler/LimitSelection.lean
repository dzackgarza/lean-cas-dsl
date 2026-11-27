module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData
public import CasCompiler.SourceTypeOrigin

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue


opaque SelectedLimitOwner.ofBinding (context : OpenContext)
    (scope : SourceSelectionScope Expr) (value : Expr) : MetaM (SelectedLimitOwner Expr) := do
  let some selected := scope.findAt? context value.getAppFn
    | throwError "the construction lost its exact selected owner-template binding"
  let actual := value.getAppArgs
  unless actual.size ≤ selected.formalBindings.size do
    throwError "the construction changed its selected owner-template formal positions"
  let selected ← selected.mapM fun field => do
    let applied := mkAppN field actual
    check applied
    return applied.headBeta
  let some selection := selected.limit
    | throwError "the construction lost its original typed owner template"
  unless selected.value.equal selection.receiver do
    throwError "the owner template changed its original native receiver family"
  return ⟨selection, selected.formalBindings.drop actual.size⟩



def SelectedLimitOwner.bind (owner : SelectedLimitOwner Expr) (family : LimitFamily)
    (creationOwner : Option (CreationFamily × LimitFamily) := none) : SourceReadM Expr :=
  fun _ scope finish => do
    let parameters ← scope.formals.filterM fun binding => do
      return !(← binding.expression.fvarId!.getDecl).isLet
    let owner ← owner.mapM fun field =>
      mkLambdaFVars (scope.formals.map (·.expression)) field
        (usedOnly := false) (usedLetOnly := false)
    let selection : SourceSelection Expr := {
      value := owner.selection.receiver,
      formalBindings := parameters.map (·.id) ++ owner.formalBindings,
      limit := some owner.selection, limitFamily := some family, creationOwner }
    scope.selections.withBinding scope.identities scope.context selection
      (fun context selections value =>
        finish (mkAppN value (parameters.map (·.expression))) { scope with context, selections })


opaque NativeLimitSelection.ofSource (source : NativeSourceLimitSelection) (receiver : Expr) :
    MetaM NativeLimitSelection := do
  unless !source.construction.isAnonymous do
    throwError "the original construction has no shared selection identity"
  check receiver
  unless ← isDefEq (← inferType receiver)
      (← mkAppM ``CategoryTheory.Bundled.α #[source.bundle]) do
    throwError "the construction receiver has a different complete native category"
  return ⟨source, receiver⟩


opaque retainLimitConstruction (judgement : NativeSourceJudgement) :
    SourceReadM NativeSourceJudgement := do
  let some category := judgement.category
    | liftM (m := TermElabM) <| throwError "a selected construction requires its original category"
  let some source := category.limit
    | liftM (m := TermElabM) <| throwError "a selected construction requires its original interface"
  let some selected ← SourceReadM.selection? judgement.value
    | liftM (m := TermElabM) <| throwError "a selected construction requires its original source reference"
  let some (.limit row) := selected.reference
    | liftM (m := TermElabM) <| throwError "the construction changed its original source reference"
  let some family := selected.limitFamily
    | liftM (m := TermElabM) <| throwError "the construction lost its complete original limit family"
  unless (SelectedSourceReference.limit row).exactlyMatches (.limit family.entry) do
    liftM (m := TermElabM) <| throwError "the construction changed its complete original limit family"
  unless row.declaration == source.declaration && row.id.raw == source.row do
    liftM (m := TermElabM) <| throwError "the construction changed its original source reference"
  let some _ ← sourceApplication? source.declaration selected
    | liftM (m := TermElabM) <| throwError "the construction lost its original registered application"
  let owner ← NativeLimitSelection.ofSource source judgement.value
  let value ← SourceReadM.select { selected with
    value := judgement.value
    category := some category
    limit := some owner }
  return { judgement with value }


opaque retainLimitLeg (category : NativeSourceCategory) (receiver index value : Expr)
    (declaredType : Option Expr := none) : SourceReadM Expr := do
  let some source := category.limit
    | liftM (m := TermElabM) <| throwError "a selected leg requires its receiver's original construction"
  let some retained ← SourceReadM.selection? receiver
    | liftM (m := TermElabM) <| throwError "a selected leg lost its receiver's original selection"
  let some construction := retained.limit
    | liftM (m := TermElabM) <| throwError "a selected leg lost its original construction"
  let some family := retained.limitFamily
    | liftM (m := TermElabM) <| throwError "a selected leg lost its complete original limit family"
  unless !source.construction.isAnonymous &&
      source.construction == construction.source.construction do
    liftM (m := TermElabM) <| throwError "the receiver belongs to a different original construction selection"
  let construction ← NativeLimitSelection.ofSource construction.source receiver
  SourceReadM.select {
    value, leg := some ⟨construction, index, value⟩, limitFamily := some family } declaredType


opaque NativeLimitLegSelection.ofExpr? (context : OpenContext)
    (scope : SourceSelectionScope Expr) (value : Expr) :
    MetaM (Option NativeLimitLegSelection) := do
  let some selected := scope.findAt? context value.getAppFn | return none
  return (← selected.specialize value.getAppArgs).leg




opaque NativeLimitSelection.legAt (selection : NativeLimitSelection) (cone index : Expr) :
    MetaM Expr := do
  unless ← isDefEq (← inferType cone) (← inferType selection.source.cone) do
    throwError "the retained cone has a different complete native interface"
  let transformation ← mkAppM (if selection.source.colimit then
    ``CategoryTheory.Limits.Cocone.ι else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation]
  let value := mkApp component index
  check value
  return value

end CasCompiler
