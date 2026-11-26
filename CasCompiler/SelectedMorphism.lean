module

public import CasCompiler.SelectionScope
public import CasCompiler.Layout
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled

public section

namespace CasCompiler

open Lean Meta



def selectedEndpoint? (context : OpenContext) (scope : SourceSelectionScope Expr)
    (value : Expr) : Option Expr := do
  let selected ← scope.findAt? context value
  return (← selected.endpoint).value








def declaredEndpoint (stated : Expr) : MetaM Expr := do
  let stated ← instantiateMVars stated
  let body := stated.consumeMData
  let native ← SourceProjection.ofExpr? body
  for (projection, canonical, fromEnd) in
      [(``CategoryTheory.Arrow.left, ``CategoryTheory.Comma.left, 3),
        (``CategoryTheory.Arrow.right, ``CategoryTheory.Comma.right, 2)] do
    let arrow? := if body.getAppFn.isConstOf projection then body.getAppArgs.back?
      else match native with
        | some selected =>
          if selected.declaration == canonical then some selected.parent else none
        | none => none
    if let some arrow := arrow? then
      let arrow := arrow.consumeMData
      if arrow.getAppFn.isConstOf ``CategoryTheory.Arrow.mk then
        let arguments := arrow.getAppArgs
        if let some declared := arguments[arguments.size - fromEnd]? then return declared
  return stated




def selectMorphism [Monad m] [MonadLiftT MetaM m] (selection : SourceSelection Expr)
    (select : SourceSelection Expr → Option Expr → m Expr)
    (category : Option Expr := none)
    (declaredCategory : Option Expr := none) : m Expr := do
  let selected ← select selection none
  let (type, arrow) ← liftM (m := MetaM) do
    let inferred ← inferType selected
    let type ← if inferred.isAppOfArity ``Quiver.Hom 4 then pure inferred else whnfR inferred
    unless type.isAppOfArity ``Quiver.Hom 4 do
      throwError "a selected morphism must have its declared source and target"
    let arrow ← match category with
      | none => mkAppM ``CategoryTheory.Arrow.mk #[selected]
      | some bundle => do
        let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
        let instanceValue ← mkAppM ``CategoryTheory.Bundled.str #[bundle]
        mkAppOptM ``CategoryTheory.Arrow.mk
          #[some carrier, some instanceValue, some type.getAppArgs[2]!,
            some type.getAppArgs[3]!, some selected]
    let arguments := arrow.getAppArgs
    unless arguments.size >= 3 do
      throwError "the selected morphism lost its native Arrow constructor endpoints"
    let arguments := (arguments.set! (arguments.size - 3) type.getAppArgs[2]!).set!
      (arguments.size - 2) type.getAppArgs[3]!
    let retained := mkAppN arrow.getAppFn (arguments.set! (arguments.size - 1) selected)
    check retained
    unless ← isDefEq retained arrow do
      throwError "the selected morphism changed its native Arrow constructor"
    pure (type, retained)
  let declaredBoundary ← liftM (m := MetaM) <| declaredCategory.mapM fun bundle => do
    return (← mkAppM ``CategoryTheory.Bundled.α #[bundle],
      ← mkAppM ``CategoryTheory.Bundled.str #[bundle])
  let sourceValue ← liftM (m := MetaM) <| mkAppM ``CategoryTheory.Arrow.left #[arrow]
  let source ← select { value := sourceValue, endpoint := some {
    arrow := selected, side := .source, value := type.getAppArgs[2]! } }
    (declaredBoundary.map Prod.fst)
  let targetValue ← liftM (m := MetaM) <| mkAppM ``CategoryTheory.Arrow.right #[arrow]
  let target ← select { value := targetValue, endpoint := some {
    arrow := selected, side := .target, value := type.getAppArgs[3]! } }
    (declaredBoundary.map Prod.fst)
  let stated ← liftM (m := MetaM) <| match declaredBoundary with
    | none => pure <| mkAppN type.getAppFn
        #[type.getAppArgs[0]!, type.getAppArgs[1]!, source, target]
    | some (carrier, instanceValue) => do
      let constructor ← mkAppOptM ``CategoryTheory.Arrow.mk
        #[some carrier, some instanceValue, some source, some target]
      let .forallE _ domain _ _ ← whnfR (← inferType constructor)
        | throwError "the selected morphism lost its declared native Hom interface"
      pure domain
  select { selection with value := selected } (some stated)

end CasCompiler
