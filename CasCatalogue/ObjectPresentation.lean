/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.ObjectPresentation

/-- Public object fields select existing accepted declarations. The two presentation
selectors use the same complete parameter family and opposite projections of its
accepted isomorphism; they do not register another comparison or infer one from carriers. -/
def fieldDeclaration (entry : ObjectEntry) (field : String) : Option Name :=
  match field with
  | "inclusion" => entry.inclusion
  | "constants" => entry.constants
  | "presentation" | "inversePresentation" =>
      entry.functorPresentation.map (·.identification)
  | _ => none

/-- Project a public map from the fully instantiated declaration that owns it. -/
def fieldValue (field : String) (application : Expr) : TermElabM Expr := do
  match field with
  | "presentation" => mkAppM ``CategoryTheory.Iso.hom #[application]
  | "inversePresentation" => mkAppM ``CategoryTheory.Iso.inv #[application]
  | _ => pure application

def applyParameters (declaration : Name) (parameters : Array Expr) : TermElabM Expr := do
  elabTermAndSynthesize
    (← `($(mkCIdent declaration) $(← parameters.mapM exprToSyntax)*)) none

/-- A declared field, with its selected parameters and direction retained in the trace. -/
def field (entry : ObjectEntry) (selector : String) (parameters : Array Expr)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let some declaration := fieldDeclaration entry selector
    | throwError "the registered object has no {selector} field"
  let application ← applyParameters declaration parameters
  let value ← instantiateMVars (← fieldValue selector application)
  if value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars then
    throwError "the public object field has unresolved complete parameters"
  Trace.record trace? value (.objectField entry.id selector entry.category parameters)
  return value

/-- The existing registered construction and its complete accepted comparison. This
plan contains only formal catalogue data; a computed result never supplies its laws. -/
structure Plan where
  argument : Expr
  action : Expr
  image : Expr
  object : Expr
  route : Array EdgeRef
  applications : Array Expr
  identification : Expr

def plan (entry : ObjectEntry) (parameters : Array Expr)
    (trace? : Option Trace := none) : TermElabM (Option Plan) := do
  let some presentation := entry.functorPresentation | return none
  let state ← registryState
  let some functor := state.functor? presentation.functor
    | throwError "the object presentation names an unregistered functor"
  let object ← Semantic.object entry (← parameters.mapM exprToSyntax) trace?
  let argument ← applyParameters presentation.argument parameters
  let action ← Semantic.edgeFunctor state (.functor functor.id)
  let mut image ← Semantic.objOf action argument
  let mut applications := #[]
  for step in presentation.route do
    let action ← Semantic.edgeFunctor state step
    image ← Semantic.objOf action image
    applications := applications.push action
  let identification ← applyParameters presentation.identification parameters
  unless ← withTransparency .all <| isDefEq (← inferType identification)
      (← mkAppM ``CategoryTheory.Iso #[image, object]) do
    throwError "the object presentation changes its complete selected endpoints"
  let argument ← instantiateMVars argument
  let action ← instantiateMVars action
  image ← instantiateMVars image
  let identification ← instantiateMVars identification
  applications ← applications.mapM instantiateMVars
  if (#[argument, action, image, object, identification] ++ applications).any
      (fun value => value.hasMVar || value.hasLevelMVar || value.hasFVar || value.hasLooseBVars) then
    throwError "the object presentation lost a complete selected parameter"
  return some {
    argument := argument, action := action, image := image, object := object
    route := presentation.route, applications := applications, identification := identification }

end CasCatalogue.ObjectPresentation
