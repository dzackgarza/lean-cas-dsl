/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public import CasCatalogue.LimitCall
public import Mathlib.CategoryTheory.Limits.Creates

@[expose] public section

/-!
# The semantic reading of the language (`specs/architecture.md`, "The one-way workflow")

What a statement means is decided from `lean-categories`' catalogue alone, before and without any
realization: each construct elaborates to its mathematics, and a statement that does not is
invalid, whichever leaves are installed. Only then is it decided through realizations (the
realized reading), where a missing realization is a gap.

* A named object is its declaration at its parameters.
* A morphism `f : a ⟶ b` is `f` elaborated at `a ⟶ b` in the category.
* A limit or colimit is the registered presentation of its shape at the diagram, returned along the
  registered creation lift when it is computed in another category (`liftedLimitCone`).
* A method call is the method's functor after the structural route it resolves along.
* A property query is `Classifier.Holds` of the classifier after its route.
-/

open Lean Meta Elab Term CategoryTheory CategoryTheory.Limits

namespace CasCatalogue

universe v u v' u' w w'

/-- A limit cone of `K`, lifted from one of `K ⋙ U` along a functor creating limits of its shape
(Mathlib `liftLimit`, `liftedLimitIsLimit`). -/
noncomputable def liftedLimitCone {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {J : Type w} [Category.{w'} J] (U : C ⥤ E) [CreatesLimitsOfShape J U] {K : J ⥤ C}
    (L : LimitCone (K ⋙ U)) : LimitCone K :=
  ⟨liftLimit L.isLimit, liftedLimitIsLimit L.isLimit⟩

namespace Semantic

/-- `F.obj X`, elaborated at the current depth, so that the universe levels and parameters of `F`'s
source category are assigned by `X`'s category (a bundled category is unfolded as needed). -/
def objOf (F X : Expr) : TermElabM Expr := do
  let value ← elabTermAndSynthesize
    (← `(Prefunctor.obj (CategoryTheory.Functor.toPrefunctor $(← exprToSyntax F)) $(← exprToSyntax X)))
    none
  instantiateMVars value

/-- The registered object `entry` at the parameters `params`. -/
def object (entry : ObjectEntry) (params : Array Term) : TermElabM Expr := do
  let value ← elabTermAndSynthesize (← `($(mkCIdent entry.declaration) $params*)) none
  instantiateMVars value

/-- The morphism `f : a ⟶ b`. -/
def hom (f : Term) (a b : Expr) : TermElabM Expr := do
  let expected ← mkAppM ``Quiver.Hom #[a, b]
  let value ← elabTermEnsuringType f expected
  synthesizeSyntheticMVarsNoPostponing
  mkExpectedTypeHint (← instantiateMVars value) expected

/-- The registered limit (colimit) of `shape` at the diagram `D` of the category `category`: its
presentation, returned along the registered creation lift when it is computed elsewhere. -/
def limit (colimit : Bool) (shape : String) (D : Expr) (category : String) : TermElabM Expr := do
  let state ← registryState
  let some entry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveLimit entry.id shape colimit with
    | .ok resolution => pure resolution
    | .error message => throwStratum .invalid m!"{message}"
  let some row := state.limits.find? (·.id == resolution.limit) | unreachable!
  let family ← instantiateFresh row.declaration
  let familyDiagram := (← whnfR (← inferType family)).appArg!
  -- The presentation at the diagram `F`, identified with its standard form (as in `LimitCall`).
  let presentationAt (F : Expr) : TermElabM Expr := do
    let some isoName := standardFormIso shape
      | throwStratum .invalid m!"the shape {shape} has no standard form"
    let α ← mkAppM isoName #[F]
    let standard := (← whnfR (← inferType α)).getAppArgs.back!
    unless ← withTransparency .all <| isDefEq familyDiagram standard do
      throwStratum .invalid m!"the registered {shape} {row.id.raw} does not apply to this diagram"
    instantiateMVars (← mkAppM (if colimit then ``colimitCoconeOfIso else ``limitConeOfIso)
      #[α, family])
  match resolution.lift.bind fun id => state.lifts.find? (·.id == id) with
  | none => presentationAt D
  | some lift =>
      if colimit then
        throwStratum .invalid m!"a colimit returned along a lift is not registered"
      let U ← state.edgeFunctor lift.edge
      let L ← presentationAt (← withTransparency .all <| mkFunctorComp D U)
      let evidence ← instantiateFresh lift.evidence
      let lifted ← elabTermAndSynthesize (← `(@CasCatalogue.liftedLimitCone _ _ _ _ _ _
        $(← exprToSyntax U) $(← exprToSyntax evidence) _ $(← exprToSyntax L))) none
      instantiateMVars lifted

/-- The value of the method `name` on the object `X` of `category`, and the category it is in. -/
def method (name : String) (X : Expr) (category : NamedCategoryEntry) :
    TermElabM (Expr × NamedCategoryEntry) := do
  let state ← registryState
  let resolution ← match state.resolveMethod category.expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let some functor := state.functor? resolution.method.functor
    | throwStratum .invalid m!"`{name}` has no registered functor"
  let some target := state.category? functor.target
    | throwStratum .invalid m!"the result category of `{name}` is not a registered category"
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← state.routeFunctor (resolution.route.steps.map (·.ref))) X
  let F ← registeredFunctorInstance functor
  let input ← methodInput resolution.method image
  return (← objOf F input, target)

/-- The proposition that the property `name` holds of the object `X` of `category`. -/
def property (name : String) (X : Expr) (category : NamedCategoryEntry) : TermElabM Expr := do
  let state ← registryState
  let resolution ← match state.resolveProperty category.expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← state.routeFunctor (resolution.route.steps.map (·.ref))) X
  let classifier ← classifierInstance resolution.classifier
  let holds ← elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax image))) none
  instantiateMVars holds

end Semantic

end CasCatalogue

-- The semantic layer ends here.
