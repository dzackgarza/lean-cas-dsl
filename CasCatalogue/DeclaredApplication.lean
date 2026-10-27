/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.CategoryContext
public import CasCatalogue.FunctorActionData

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.DeclaredApplication

/-- Recover the complete application of one independently selected declaration.
Literal arguments retain priority; aliases must agree in their full type and
whole value. Every parameter is fixed before the generic kernel equality check.
No registry search, equal-carrier choice or computational input is involved. -/
def completeProjected? (declaration : Name) (value : Expr)
    (project : Expr → TermElabM Expr) (literal? : Option Expr := none) :
    TermElabM (Option (Expr × Array Expr)) :=
    withoutModifyingState do
  let value ← instantiateMVars value
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return none
  let literal := literal?.getD value
  let application ← if literal.getAppFn.constName? == some declaration then pure literal
    else instantiateFresh declaration
  let compared ← project application
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType compared) (← inferType value) <&&> isDefEq compared value) do
    CategoryContext.exposeStructureParameters application
  unless ← withTransparency .all <|
      isDefEq (← inferType compared) (← inferType value) <&&> isDefEq compared value do
    return none
  let application ← instantiateMVars application
  let compared ← instantiateMVars compared
  unless FunctorActionData.closedParameter application && (← isTypeCorrect application) do
    return none
  let infos ← forallTelescopeReducing (← inferType application.getAppFn) fun fields _ =>
    fields.mapM (·.fvarId!.getBinderInfo)
  unless application.getAppNumArgs == infos.size do return none
  unless ← Decide.kernelAccepts (← mkEq compared value) (← mkEqRefl compared) do
    throwError "the complete declaration presentation failed its original kernel check"
  return some (application, (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none)

/-- The existing ordinary/functor application interface. Its stripping order,
full equality checks and closed-parameter requirements are unchanged. -/
def complete? (declaration : Name) (value : Expr)
    (asFunctor : Bool := false) : TermElabM (Option (Expr × Array Expr)) :=
    withoutModifyingState do
  let value ← instantiateMVars value
  unless FunctorActionData.closedParameter value && (← isTypeCorrect value) do return none
  let mut literal := value.consumeMData
  while literal.isAppOfArity ``id 2 ||
      (asFunctor && literal.isAppOf ``CategoryTheory.Cat.Hom.toFunctor) do
    literal := literal.appArg!.consumeMData
  completeProjected? declaration value
    (fun application => if asFunctor then Semantic.asFunctor application else pure application)
    (some literal)

end CasCatalogue.DeclaredApplication
