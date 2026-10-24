/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.DirectConstruction

/-- An application of an existing declaration at its complete dependent telescope.
Only elaboration state is assembled here; mathematical data come from the declaration. -/
structure Application where
  value : Expr
  arguments : Array Expr
  explicit : Array Expr

/-- Supply explicit arguments in declaration order, leaving only signature inference open. -/
def instantiate (declaration : Name) (parameters : Array Term) : TermElabM Application := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit := (arguments.zip infos).filterMap fun (argument, info) =>
    if info.isExplicit then some argument else none
  unless parameters.size <= explicit.size do
    throwStratum .invalid m!"{declaration} has too many explicit arguments"
  for (parameter, argument) in parameters.zip explicit do
    let supplied ← elabTerm parameter (some (← instantiateMVars (← inferType argument)))
    unless ← isDefEq argument supplied do
      throwStratum .invalid m!"a supplied declaration argument has a different complete type"
  return { value := mkAppN constant arguments, arguments, explicit }

/-- Close only declared class and proposition obligations. Data are never defaulted. -/
def close (application : Application) : TermElabM Application := do
  for argument in application.arguments do
    if (← instantiateMVars argument).isMVar then
      let type ← instantiateMVars (← inferType argument)
      if (← isClass? type).isSome then
        if let some instanceValue := (← trySynthInstance type).toOption then
          discard <| isDefEq argument instanceValue
      else if !type.hasMVar && (← isProp type) then
        if let some proof ← Decide.decisionProof type then
          discard <| isDefEq argument proof
  let value ← instantiateMVars application.value
  if value.hasMVar || value.hasLevelMVar || value.hasLooseBVars then
    throwStratum .invalid "the selected declaration requires further complete typed arguments"
  unless ← isTypeCorrect value do
    throwStratum .invalid "the selected declaration is outside its complete dependent signature"
  return {
    value
    arguments := (← application.arguments.mapM instantiateMVars)
    explicit := (← application.explicit.mapM instantiateMVars) }

/-- Explicit data parameters omit propositions, which remain exclusively formal inputs. -/
def dataArguments (parameters : Array Expr) : MetaM (Array Expr) :=
  parameters.filterM fun parameter => return !(← isProp (← inferType parameter))

structure Action where
  entry : ConstructionEntry
  parameters : Array Expr
  functor : Expr
  source : Expr
  target : CategoryContext

/-- Instantiate the actual dependent construction. The receiver fixes its full source category;
the registered target is checked independently of any computational representation. -/
def select (entry : ConstructionEntry) (parameters : Array Term) (receiver : Expr) :
    TermElabM Action := do
  let application ← instantiate entry.declaration parameters
  let functor ← Semantic.asFunctor application.value
  discard <| Semantic.objOf functor receiver
  let application ← close application
  let functor ← instantiateMVars (← Semantic.asFunctor application.value)
  let type ← whnfR (← inferType functor)
  unless type.isAppOf ``CategoryTheory.Functor do
    throwStratum .invalid "the registered construction does not retain a functor"
  let (_, targetBundle) ← functorCategoryBundles functor
  let target : CategoryContext := { expression := entry.target, bundle := targetBundle }
  let image ← Semantic.objOf functor receiver
  unless ← withTransparency .all <| isDefEq (← inferType image)
      (← mkAppM ``CategoryTheory.Bundled.α #[targetBundle]) do
    throwStratum .invalid "the construction changed its complete registered target"
  return {
    entry
    parameters := application.explicit
    functor
    source := type.getAppArgs[0]!
    target }

/-- Object action of the single accepted dependent construction. -/
def obj (action : Action) (receiver : Expr) : TermElabM Expr := do
  unless ← withTransparency .all <| isDefEq (← inferType receiver) action.source do
    throwStratum .invalid "the construction receiver has a different complete source category"
  Semantic.objOf action.functor receiver

/-- A Hom type at the actual category dictionary selected by the functor. -/
def homAt (action : Action) (targetCategory : Bool) (source target : Expr) : TermElabM Expr := do
  let type ← whnfR (← inferType action.functor)
  let arguments := type.getAppArgs
  let offset := if targetCategory then 2 else 0
  let category := arguments[offset]!
  let dictionary := arguments[offset + 1]!
  let categoryStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some category, some dictionary]
  let quiver ← mkAppOptM ``CategoryTheory.CategoryStruct.toQuiver #[some category, some categoryStruct]
  mkAppOptM ``Quiver.Hom #[some category, some quiver, some source, some target]

/-- Map action preserves both exact endpoints and the actual selected source morphism. -/
def map (action : Action) (source target morphism : Expr) : TermElabM Expr := do
  unless ← withTransparency .all <| isDefEq (← inferType source) action.source <&&>
      isDefEq (← inferType target) action.source do
    throwStratum .invalid "the construction map has a different complete source category"
  let expected ← homAt action false source target
  unless ← withTransparency .all <| isDefEq (← inferType morphism) expected do
    throwStratum .invalid "the construction map changed a selected source endpoint"
  let result ← Semantic.mapOf action.functor morphism
  let expected ← homAt action true (← obj action source) (← obj action target)
  unless ← withTransparency .all <| isDefEq (← inferType result) expected do
    throwStratum .invalid "the construction map has incompatible declared result endpoints"
  return ← instantiateMVars result

end CasCatalogue.DirectConstruction
