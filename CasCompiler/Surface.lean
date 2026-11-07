module

public import CasCompiler.Elaborate
public import LeanCategories.Catalogue.Registry.Semantic
public import CasCatalogue.InterpretationFailure
import Lean.Elab.App

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- Exact registered source selection and its applied native category and value. -/
structure SourceObject where
  private mk ::
  entry : ObjectEntry
  categoryEntry : NamedCategoryEntry
  category : SourceTerm
  value : SourceTerm

opaque selectCategory (state : SemanticState) (name : String) : TermElabM NamedCategoryEntry := do
  match state.categories.filter (·.name == name) with
  | #[entry] => pure entry
  | #[] => throwError "unregistered source category: {name}"
  | _ => throwSemanticAmbiguity m!"source category {name} has several registrations"

opaque selectObject (name : String) (category : Option String) :
    TermElabM (ObjectEntry × NamedCategoryEntry) := do
    let state ← semanticState
    let qualified ← category.mapM (selectCategory state)
    let entries := state.objects.filter fun entry =>
      entry.name == name && match qualified with
        | some category => entry.category == category.id
        | none => entry.refines.isNone
    let entry ← match entries with
      | #[entry] => pure entry
      | #[] => throwError "unregistered source object: {name}"
      | _ => throwSemanticAmbiguity m!"source object {name} requires a category qualification"
    let #[categoryEntry] := state.categories.filter (·.id == entry.category)
      | throwError "the source object requires one registered category"
    return (entry, categoryEntry)

opaque objectExpressions (entry : ObjectEntry) (categoryEntry : NamedCategoryEntry)
    (application : Expr → Option Expr → TermElabM Expr) : TermElabM (Expr × Expr) := do
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration categoryEntry.declaration
  let family ← mkConstWithFreshMVarLevels categoryEntry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let category := mkAppN family parameters
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
  let function ← mkConstWithFreshMVarLevels entry.declaration
  let value ← application function (some carrier)
  unless ← isDefEq (← inferType value) carrier do
    throwError "the source object does not inhabit its registered category"
  return (category, value)

/-- A direct registered view before closing its complete native expressions. -/
structure NativeSourceView where
  private mk ::
  reference : FunctorId ⊕ ClassifierId
  declaration : Name
  target : CategoryExpr
  functor : Expr
  targetBundle : Expr

/-- Select an actual direct source action by its exact published identity. -/
opaque selectView (id : String) : TermElabM (FunctorEntry ⊕ ClassifierEntry) := do
  let state ← semanticState
  match state.functors.filter (·.id.raw == id), state.classifiers.filter (·.id.raw == id) with
  | #[entry], #[] => return .inl entry
  | #[], #[entry] => return .inr entry
  | #[], #[] => throwError "unregistered source view: {id}"
  | _, _ => throwSemanticAmbiguity m!"source view {id} has several declared actions"

/-- Apply the selected declaration and retain its complete native functor boundary.
An existing receiver category stays fixed. Otherwise the explicitly selected action supplies
its source context, which native object application must check. Explicit functor use admits
each registered role. Reuse: SourceSession.namedFunctor, classifierForgetInstance and
functorCategoryBundles; source: #66, comment 6664276482 §4. -/
opaque viewExpressions (entry : FunctorEntry ⊕ ClassifierEntry)
    (source : Option (CategoryExpr × Expr))
    (application : Expr → TermElabM Expr) : TermElabM NativeSourceView := do
  let (symbolic, target, declaration, reference) := match entry with
    | .inl entry => (entry.source, entry.target, entry.declaration, Sum.inl entry.id)
    | .inr entry => (.classifierTotal entry.id, entry.host, entry.declaration, Sum.inr entry.id)
  if let some (selected, _) := source then
    unless symbolic.syntacticEq selected do
      throwError "the selected source action has a different complete symbolic source category"
  discard <| checkedDeclaration declaration
  let value ← application (← mkConstWithFreshMVarLevels declaration)
  let functor ← match entry with
    | .inl _ =>
      if (← whnf (← inferType value)).isAppOf ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[value]
      else pure value
    | .inr _ => do
      let type ← whnf (← inferType value)
      let classifier ← if type.isAppOf ``LeanCategories.PropertyClassifier then
          mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[value]
        else if type.isAppOf ``LeanCategories.StructureClassifier then
          mkAppM ``LeanCategories.StructureClassifier.toClassifier #[value]
        else if type.isAppOf ``LeanCategories.Classifier then pure value
        else throwError "the selected classifier requires its complete declaration arguments"
      mkAppM ``CategoryTheory.Cat.Hom.toFunctor
        #[← mkAppM ``LeanCategories.Classifier.forget #[classifier]]
  let (domain, targetBundle) ← functorCategoryBundles functor
  if let some (_, selected) := source then
    unless ← isDefEq domain selected do
      throwError "the selected source action has a different complete native source category"
  return ⟨reference, declaration, target, functor, targetBundle⟩

/-- Apply the actual native functor to its actual object and check its complete target type.
Reuse: Functor.toPrefunctor/Prefunctor.obj, shared with the retained source functor API. -/
opaque functorObject (functor object target : Expr) : MetaM Expr := do
  let (domain, _) ← functorCategoryBundles functor
  let inputType ← mkAppM ``CategoryTheory.Bundled.α #[domain]
  unless ← withTransparency .all <| isDefEq (← inferType object) inputType do
    throwError "the source object does not inhabit the selected functor's native domain"
  let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
  let value ← mkAppM ``Prefunctor.obj #[prefunctor, object]
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[target]
  unless ← isDefEq (← inferType value) carrier do
    throwError "the source image does not belong to its complete native target category"
  return value

/-- Select a registered source family, then let native application elaborate its arguments.
Reuse: semanticState and the independently owned declaration telescopes; Lean.elabAppArgs
accepts retained expressions and synthesizes native implicits and selected instances. -/
opaque SourceSession.namedObject (session : SourceSession) (reference : Syntax) (name : String)
    (category : Option String) (arguments : Array SourceTerm) : TermElabM SourceObject :=
  withRef reference do
    let (entry, categoryEntry) ← selectObject name category
    let #[category, value] ← session.elaborateMany reference fun context => do
        let arguments ← arguments.mapM fun argument => do
          return Arg.expr (← argument.source.inContext context)
        let (category, value) ← objectExpressions entry categoryEntry fun function expected =>
          elabAppArgs function #[] arguments expected false false
        return #[category, value]
      | throwError "registered source formation returned an invalid number of expressions"
    return ⟨entry, categoryEntry, category,
      ← value.inCategory categoryEntry.expression category⟩

end CasCompiler
