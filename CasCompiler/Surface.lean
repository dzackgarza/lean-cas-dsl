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

opaque selectObject (name : String) (category : Option String) :
    TermElabM (ObjectEntry × NamedCategoryEntry) := do
    let state ← semanticState
    let qualified ← category.mapM fun name => do
      match state.categories.filter (·.name == name) with
      | #[entry] => pure entry
      | #[] => throwError "unregistered source category: {name}"
      | _ => throwSemanticAmbiguity m!"source category {name} has several registrations"
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
    (arguments : Array Arg) : TermElabM (Expr × Expr) := do
  discard <| checkedDeclaration entry.declaration
  discard <| checkedDeclaration categoryEntry.declaration
  let family ← mkConstWithFreshMVarLevels categoryEntry.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  let category := mkAppN family parameters
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
  let function ← mkConstWithFreshMVarLevels entry.declaration
  let value ← elabAppArgs function #[] arguments (some carrier) false false
  unless ← isDefEq (← inferType value) carrier do
    throwError "the source object does not inhabit its registered category"
  return (category, value)

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
        let (category, value) ← objectExpressions entry categoryEntry arguments
        return #[category, value]
      | throwError "registered source formation returned an invalid number of expressions"
    return ⟨entry, categoryEntry, category, value⟩

end CasCompiler
