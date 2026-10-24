/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.CategoryContext

/-- A named schema is optional; derived contexts do not manufacture registry rows. -/
def named? (state : RegistryState) (expression : CategoryExpr) : Option NamedCategoryEntry := do
  if let some row := state.categories.find? (·.expression.syntacticEq expression) then
    return row
  let .familyApp family _ := expression | none
  let candidates := state.categories.filter fun row => match row.expression with
    | .familyApp other _ => other == family
    | _ => false
  let #[row] := candidates | none
  return row

def carrier (context : CategoryContext) : MetaM Expr :=
  mkAppM ``CategoryTheory.Bundled.α #[context.bundle]

def dictionary (context : CategoryContext) : MetaM Expr :=
  mkAppM ``CategoryTheory.Bundled.str #[context.bundle]

/-- Present the very same full bundle by its accepted category expression. This
comparison includes the complete category dictionary, never just its carrier. -/
def presented (context : CategoryContext) : TermElabM CategoryContext := do
  let state ← registryState
  let declaration ← if let some row := named? state context.expression then pure row.declaration
    else match context.expression with
      | .construct id _ =>
          let some row := state.constructor? id
            | throwStratum .invalid "the derived context names an absent constructor"
          pure row.semantics
      | _ => throwStratum .invalid "the selected category has no accepted complete expression"
  let bundle ← instantiateFresh declaration
  unless ← withTransparency .all <| isDefEq bundle context.bundle do
    throwStratum .invalid "the category expression differs from its actual complete bundle"
  return { context with bundle := (← instantiateMVars bundle) }

/-- Full hom type at the actual accepted category dictionary. -/
def hom (context : CategoryContext) (source target : Expr) : TermElabM Expr := do
  let carrier ← carrier context
  let category ← dictionary context
  let categoryStruct ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
    #[some carrier, some category]
  let quiver ← mkAppOptM ``CategoryTheory.CategoryStruct.toQuiver
    #[some carrier, some categoryStruct]
  mkAppOptM ``Quiver.Hom #[some carrier, some quiver, some source, some target]

def checkObject (context : CategoryContext) (object : Expr) : TermElabM Unit := do
  unless ← withTransparency .all <| isDefEq (← inferType object) (← carrier context) do
    throwStratum .invalid "the derived object changed its complete selected category"
  unless ← isTypeCorrect context.bundle do
    throwStratum .invalid "the retained category bundle is not a typed accepted context"

def checkMorphism (context : CategoryContext) (value source target : Expr) : TermElabM Unit := do
  checkObject context source
  checkObject context target
  unless ← withTransparency .all <| isDefEq (← inferType value) (← hom context source target) do
    throwStratum .invalid "the derived morphism changed its full selected category or endpoints"

/-- The explicit chosen row, with parameters fixed by this object's own type. -/
def ofNamed (entry : NamedCategoryEntry) (object : Expr) : TermElabM CategoryContext := do
  let bundle ← instantiateFresh entry.declaration
  let context := { expression := entry.expression, bundle : CategoryContext }
  checkObject context object
  let bundle ← instantiateMVars bundle
  if bundle.hasMVar || bundle.hasLevelMVar then
    throwStratum .invalid "the selected category context requires complete typed parameters"
  return { context with bundle }

/-- Constructor action consumes the full accepted bundle, without carrier reconstruction. -/
def construct (context : CategoryContext) (constructor : ConstructorId) :
    TermElabM CategoryContext := do
  let some row := (← registryState).constructor? constructor
    | throwStratum .invalid "the selected category constructor is not registered"
  unless row.signature == #[ConstructorArgKind.category] do
    throwStratum .invalid "this category action requires its declared additional parameters"
  let bundle ← applyConstructorInterface row.semantics #[context.bundle] #[context.bundle]
  return {
    expression := .construct constructor #[.category context.expression]
    bundle := (← instantiateMVars bundle) }

end CasCatalogue.CategoryContext
