module

public import CasCompiler.SelectionScope
public import CasCompiler.Layout
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.ConcreteCategory.Bundled

public section

namespace CasCompiler

open Lean Meta

/-- The declared endpoint carried by this explicit native Arrow projection.
Source interpretation can inspect its domain without forgetting the retained runtime arrow. -/
def selectedEndpoint? (context : OpenContext) (scope : SourceSelectionScope Expr)
    (value : Expr) : Option Expr := do
  let selected ← scope.findAt? context value
  return (← selected.endpoint).value

/-- The declared end that a stated end of a selected map retains; any other expression is
returned as it is. A stated end is `(Arrow.mk f).left` or `(Arrow.mk f).right`; the declared end
is the corresponding argument of `Arrow.mk`, which is that projection by definition. Unification
can drop the endpoint annotation and expose the canonical Comma projection. Native projection
metadata identifies that field in either expression syntax; no field ordinal selects an endpoint.
Instance synthesis,
the shape of a source set and matching against registered objects take the declared end. -/
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

/-- Bind the actual arrow once, then retain both native endpoint projections in the same
scope. The final typed alias keeps the complete original selection and names that arrow;
the supplied binder checks its stated dependent type using original-source correspondence. -/
def selectMorphism [Monad m] [MonadLiftT MetaM m] (selection : SourceSelection Expr)
    (select : SourceSelection Expr → Option Expr → m Expr)
    (category : Option Expr := none) : m Expr := do
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
  let sourceValue ← liftM (m := MetaM) <| mkAppM ``CategoryTheory.Arrow.left #[arrow]
  let source ← select { value := sourceValue, endpoint := some {
    arrow := selected, side := .source, value := type.getAppArgs[2]! } } none
  let targetValue ← liftM (m := MetaM) <| mkAppM ``CategoryTheory.Arrow.right #[arrow]
  let target ← select { value := targetValue, endpoint := some {
    arrow := selected, side := .target, value := type.getAppArgs[3]! } } none
  let stated := mkAppN type.getAppFn
    #[type.getAppArgs[0]!, type.getAppArgs[1]!, source, target]
  select { selection with value := selected } (some stated)

end CasCompiler
