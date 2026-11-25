module

public import CasCompiler.Declaration
public import LeanCategories.Catalogue.Registry.Entry
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Lean.Meta.AbstractMVars

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- A selected universal presentation and its accepted computational interface.
The diagram is the presentation's own diagram. A creation lift separately retains its source
diagram and source presentation. The data constructor retains its complete dependent telescope,
including formal proof arguments; its non-Prop arguments are the computational data ports. -/
structure LimitInterface (term : Type) where
  presentation : term
  diagram : term
  standardization : Option term
  dataConstructor : Option term

abbrev NativeLimitInterface := LimitInterface Expr

/-- Transport all parts of one interface through the same checked source context. -/
def LimitInterface.mapM [Monad m] (interface : LimitInterface α) (f : α → m β) :
    m (LimitInterface β) := do
  return {
    presentation := ← f interface.presentation
    diagram := ← f interface.diagram
    standardization := ← interface.standardization.mapM f
    dataConstructor := ← interface.dataConstructor.mapM f }

private def resolved (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars value
  if value.hasExprMVar || value.hasLevelMVar || value.hasLooseBVars then
    throwError "a selected limit interface requires its complete source parameters"
  check value
  return value

/-- Restore the declared binder annotations after native metavariable abstraction.
Lean.Meta.abstractMVars preserves dependency order but creates explicit local binders. -/
private def restoreBinders : List BinderInfo → Expr → MetaM Expr
  | [], value => pure value
  | info :: rest, .lam name type body _ => do
    return .lam name type (← restoreBinders rest body) info
  | _, _ => throwError "the limit data constructor lost a declared argument"

/-- Specialize only the constructor parameters fixed by the complete declared diagram.
Reuse: Registry.validateLimit, Lean's native telescope and abstractMVars at v4.33.0.
Every remaining argument, including proofs and implicit object ports, stays in declaration
order. The accepted constructor supplies the dependencies; no cone field is guessed. -/
private def prepareDataConstructor (row : LimitEntry) (diagram : Expr) (name : Name) :
    MetaM Expr := withNewMCtxDepth do
  discard <| checkedDeclaration name
  let constructor ← mkConstWithFreshMVarLevels name
  let (parameters, binders, conclusion) ← forallMetaTelescopeReducing (← inferType constructor)
  let expected ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone
    else ``CategoryTheory.Limits.Cone) #[diagram]
  unless ← withTransparency .all <| isDefEq conclusion expected do
    throwError "limit {row.id.raw}: its data constructor changes the selected diagram"
  let applied ← instantiateMVars (mkAppN constructor parameters)
  let abstracted ← abstractMVars applied
  let mut retainedBinders := #[]
  let mut previous : Option Nat := none
  for parameter in abstracted.mvars do
    let some index := parameters.findIdx? (· == parameter)
      | throwError "limit {row.id.raw}: its data constructor has an undeclared argument"
    if let some prior := previous then
      unless prior < index do
        throwError "limit {row.id.raw}: its data constructor changed argument order"
    let some binder := binders[index]?
      | throwError "limit {row.id.raw}: its data constructor lost an argument annotation"
    retainedBinders := retainedBinders.push binder
    previous := some index
  let value ← restoreBinders retainedBinders.toList abstracted.expr
  -- Universes that the diagram does not fix remain rigid parameters of this interface.
  -- Fresh names avoid identifying them with universes of another selected interface.
  let levels ← abstracted.paramNames.mapM fun _ => do
    return Level.param (← mkFreshUserName `limitDataUniverse)
  let value ← resolved (value.instantiateLevelParamsArray abstracted.paramNames levels)
  forallTelescope (← inferType value) fun _ result => do
    unless ← withTransparency .all <| isDefEq result expected do
      throwError "limit {row.id.raw}: its data constructor lost the fixed result diagram"
  return value

private def prepareStandardization (row : LimitEntry) (diagram requested : Expr) :
    MetaM (Option Expr) := do
  match row.standardization with
  | none =>
    unless ← withTransparency .all <| isDefEq requested diagram do
      throwError "limit {row.id.raw}: the requested diagram needs a declared standardization"
    return none
  | some name =>
    discard <| checkedDeclaration name
    let comparison ← mkAppM name #[requested]
    let expected ← mkAppM ``CategoryTheory.Iso #[requested, diagram]
    unless ← withTransparency .all <| isDefEq (← inferType comparison) expected do
      throwError "limit {row.id.raw}: its standardization changes the selected diagram"
    return some (← resolved comparison)

/-- Reuse the already prepared native data constructor at the original selected target
presentation. A creation lift supplies its mapped source diagram only to the independently
accepted standardization; no constructor telescope or rigid universe is prepared again. -/
def NativeLimitInterface.withRequestedDiagram (interface : NativeLimitInterface)
    (row : LimitEntry) (requested : Expr) : MetaM NativeLimitInterface := do
  discard <| checkedDeclaration row.declaration
  unless interface.presentation.consumeMData.getAppFn.isConstOf row.declaration do
    throwError "limit {row.id.raw}: the retained interface changed its declaration"
  let type ← whnfR (← inferType interface.presentation)
  let family := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
    else ``CategoryTheory.Limits.LimitCone
  unless type.isAppOf family do
    throwError "limit {row.id.raw}: the retained interface changed its result family"
  let some diagram := type.getAppArgs.back?
    | throwError "limit {row.id.raw}: the retained interface lost its declared diagram"
  unless ← withTransparency .all <| isDefEq diagram interface.diagram do
    throwError "limit {row.id.raw}: the retained interface changed its complete diagram"
  return { interface with standardization :=
    ← prepareStandardization row interface.diagram (← resolved requested) }

/-- Prepare the interface at the exact presentation selected by source formation.
`requestedDiagram` is the diagram before the accepted standardization; for creation it is
the image of the source diagram under the selected creation functor. The result retains the
presentation application itself, with every original implicit and explicit argument.

Source: LimitEntry and Registry.validateLimit at lean-categories
8c35703b104aca1700b9fb40d1af4164ca31a55d. These declarations determine the interface;
the helper neither evaluates the presentation nor obtains a computational cone. -/
def prepareLimitInterface (row : LimitEntry) (presentation : Expr)
    (requestedDiagram : Option Expr := none) : MetaM NativeLimitInterface := do
  discard <| checkedDeclaration row.declaration
  let presentation ← resolved presentation
  unless presentation.consumeMData.getAppFn.isConstOf row.declaration do
    throwError "limit {row.id.raw}: the selected presentation changed its declaration"
  let type ← whnfR (← inferType presentation)
  let family := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
    else ``CategoryTheory.Limits.LimitCone
  unless type.isAppOf family do
    throwError "limit {row.id.raw}: its presentation has a different result family"
  let some diagram := type.getAppArgs.back?
    | throwError "limit {row.id.raw}: its presentation has no diagram"
  let diagram ← resolved diagram
  let requested ← resolved (requestedDiagram.getD diagram)
  let standardization ← prepareStandardization row diagram requested
  let dataConstructor ← row.dataConstructor.mapM (prepareDataConstructor row diagram)
  return { presentation, diagram, standardization, dataConstructor }

end CasCompiler
