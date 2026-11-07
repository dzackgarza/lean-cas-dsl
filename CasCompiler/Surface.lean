module

public import CasCompiler.Elaborate
public import LeanCategories.Catalogue.Registry.Semantic
public import CasCatalogue.InterpretationFailure
import Lean.Elab.App
public meta import Lean.Elab.App

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

private def selectObject (name : String) (category : Option String) :
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

private def objectExpressions (entry : ObjectEntry) (categoryEntry : NamedCategoryEntry)
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

syntax (name := sourceExpression) "cas_source% " cas_term : term

private def sourceArgument (stx : TSyntax `cas_term) : TermElabM Arg := withRef stx do
  return .stx (← `(term| cas_source% $stx:cas_term))

/-- Native application supplies the dependent expected type of each source argument.
Only original source syntax is embedded; retained expressions never return to syntax. -/
@[term_elab sourceExpression] meta def elabSourceExpression : TermElab := fun stx expected => do
  let source : TSyntax `cas_term := ⟨stx[1]⟩
  let registered := fun (name : Ident) (category : Option String)
      (arguments : Array (TSyntax `cas_term)) => do
    let (entry, categoryEntry) ← selectObject name.getId.toString category
    let (_, value) ← objectExpressions entry categoryEntry (← arguments.mapM sourceArgument)
    return value
  let value ← withRef source do
    match source with
    | `(cas_term| ($inner:cas_term)) =>
      elabTerm (← `(term| cas_source% $inner:cas_term)) expected
    | `(cas_term| $number:num) =>
      unless expected.isSome do
        throwError "a source numeral requires its independently declared parameter type"
      elabTermEnsuringType (← `(term| $number:num)) expected
    | `(cas_term| $name:ident) =>
      if let some declaration := (← getLCtx).findFromUserName? name.getId then
        pure (mkFVar declaration.fvarId)
      else registered name none #[]
    | `(cas_term| $name:ident($arguments:cas_term,*)) =>
      registered name none arguments.getElems
    | `(cas_term| $name:ident($arguments:cas_term,*) in $category:ident) =>
      registered name (some category.getId.toString) arguments.getElems
    | `(cas_term| $name:ident in $category:ident) =>
      registered name (some category.getId.toString) #[]
    | _ => throwError "source translation is not implemented for this expression form"
  if let some expected := expected then
    unless ← isDefEq (← inferType value) expected do
      throwError "the source expression does not have its independently declared parameter type"
  return value

/-- Read public source syntax directly in the retained native context.
Reuse: Lean's term elaborator supplies dependent parameter types and local bindings. -/
opaque SourceSession.read (session : SourceSession) (stx : TSyntax `cas_term)
    (expected : Option ClosedTerm := none) : TermElabM SourceTerm :=
  session.elaborate stx fun context => do
    let expected ← expected.mapM (·.inContext context)
    elabTermEnsuringType (← `(term| cas_source% $stx:cas_term)) expected

end CasCompiler
