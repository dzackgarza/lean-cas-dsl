module

public import CasCompiler.SelectedField
public import Mathlib.CategoryTheory.Comma.Arrow

public section

namespace CasCompiler

open Lean Meta

/-- The declared endpoint carried by this explicit native Arrow projection.
Source interpretation can inspect its domain without forgetting the retained runtime arrow. -/
def selectedEndpoint? (value : Expr) : Option Expr := do
  let .mdata data body := value | none
  let .ofString selector ← data.find `CasCompiler.endpoint | none
  let projection ← if selector == "source" then some ``CategoryTheory.Arrow.left
    else if selector == "target" then some ``CategoryTheory.Arrow.right else none
  if !body.getAppFn.isConstOf projection then none else do
    let arrow ← body.getAppArgs.back?
    if !arrow.getAppFn.isConstOf ``CategoryTheory.Arrow.mk then none else do
      let arguments := arrow.getAppArgs
      arguments[arguments.size - (if selector == "source" then 3 else 2)]?

/-- The declared end that a stated end of a selected map retains; any other expression is
returned as it is. Instance synthesis and matching against registered objects take this end. -/
def declaredEndpoint (stated : Expr) : MetaM Expr := do
  let stated ← instantiateMVars stated
  return (selectedEndpoint? stated).getD stated

/-- Retain the source and target projections of this actual selected arrow.
Reuse: Mathlib's Arrow.mk, Arrow.left and Arrow.right. The type hint is definitionally
the original morphism type; the metadata preserves its computational occurrence. -/
def selectMorphism (value : Expr) : MetaM Expr := do
  let reference := match value with | .mdata data _ => data | _ => KVMap.empty
  let type ← whnfR (← inferType value)
  unless type.isAppOfArity ``Quiver.Hom 4 do
    throwError "a selected morphism must have its declared source and target"
  let selection ← mkFreshUserName `selectedMorphism
  let selected := selectedField selection ``CategoryTheory.Arrow.hom value
  let arrow ← mkAppM ``CategoryTheory.Arrow.mk #[selected]
  let endpoint := fun projection selector => do
    let value ← mkAppM projection #[arrow]
    return Expr.mdata (KVMap.empty.setString `CasCompiler.endpoint selector) value
  let source ← endpoint ``CategoryTheory.Arrow.left "source"
  let target ← endpoint ``CategoryTheory.Arrow.right "target"
  let stated := mkAppN type.getAppFn
    #[type.getAppArgs[0]!, type.getAppArgs[1]!, source, target]
  let value ← mkExpectedTypeHint value stated
  check value
  return .mdata (reference.setName `CasCompiler.selection selection
    |>.setName `CasCompiler.selection.field ``CategoryTheory.Arrow.hom) value

end CasCompiler
