/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public import CasCatalogue.Trace
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section

/-!
# The semantic reading of the language (`specs/architecture.md`, "The one-way workflow")

What a statement means is decided from `lean-categories`' catalogue alone, before and without any
leaf: each construct elaborates to its mathematics, and a statement that does not is invalid,
whichever leaves are installed. Only then is it decided (`CasCatalogue.Realize`): in Lean where
Lean decides it, else by evaluating the same term through the admitted registrations, where a
missing registration is a gap.

* A named object is its declaration at its parameters.
* A morphism `f : a ⟶ b` is `f` elaborated at `a ⟶ b` in the category.
* A limit or colimit is the registered presentation of its shape at the diagram, returned along the
  registered creation lift when it is computed in another category (`liftedLimitCone`).
* A method call is the method's functor after the structural route it resolves along.
* A property query is `Classifier.Holds` of the classifier after its route.

Each construction records, in the trace it is given (`CasCatalogue.Trace`), the catalogue
operation that formed its value, so that the realized reading evaluates the same term.
-/

open Lean Meta Elab Term CategoryTheory CategoryTheory.Limits

namespace CasCatalogue

universe v u v' u' w w'

/-- A limit cone of `G`, transported to a diagram `F ≅ G` (`IsLimit.postcomposeInvEquiv`). -/
def limitConeOfIso {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {F G : J ⥤ C}
    (α : F ≅ G) (L : LimitCone G) : LimitCone F :=
  ⟨(Cone.postcompose α.inv).obj L.cone, (IsLimit.postcomposeInvEquiv α L.cone).symm L.isLimit⟩

/-- A colimit cocone of `G`, transported to a diagram `F ≅ G` (`IsColimit.precomposeHomEquiv`). -/
def colimitCoconeOfIso {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {F G : J ⥤ C}
    (α : F ≅ G) (L : ColimitCocone G) : ColimitCocone F :=
  ⟨(Cocone.precompose α.hom).obj L.cocone,
    (IsColimit.precomposeHomEquiv α L.cocone).symm L.isColimit⟩

/-- A limit cone of `K`, lifted from one of `K ⋙ U` along a functor creating limits of its shape
(Mathlib `liftLimit`, `liftedLimitIsLimit`). -/
noncomputable def liftedLimitCone {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {J : Type w} [Category.{w'} J] (U : C ⥤ E) [CreatesLimitsOfShape J U] {K : J ⥤ C}
    (L : LimitCone (K ⋙ U)) : LimitCone K :=
  ⟨liftLimit L.isLimit, liftedLimitIsLimit L.isLimit⟩

/-- Mathlib's identification of a diagram of a standard shape with its standard form. -/
def standardFormIso : String → Option Name
  | "pullback" => some ``CategoryTheory.Limits.diagramIsoCospan
  | "product" | "coproduct" => some ``CategoryTheory.Limits.diagramIsoPair
  | "kernel" | "cokernel" | "equalizer" | "coequalizer" =>
      some ``CategoryTheory.Limits.diagramIsoParallelPair
  | _ => none

/-- Mathlib's constructor of the cones (cocones) of a standard shape from their data: the apex
and the legs, with the commutation the legs must satisfy. A cone computed by a registration is
decoded in this form (`CasCatalogue.Realize`, CC-DECODE). -/
def standardCone (shape : String) (colimit : Bool) : Option Name :=
  match shape, colimit with
  | "product", false => some ``CategoryTheory.Limits.BinaryFan.mk
  | "coproduct", true => some ``CategoryTheory.Limits.BinaryCofan.mk
  | "pullback", false => some ``CategoryTheory.Limits.PullbackCone.mk
  | "pushout", true => some ``CategoryTheory.Limits.PushoutCocone.mk
  | "equalizer", false => some ``CategoryTheory.Limits.Fork.ofι
  | "coequalizer", true => some ``CategoryTheory.Limits.Cofork.ofπ
  | "kernel", false => some ``CategoryTheory.Limits.KernelFork.ofι
  | "cokernel", true => some ``CategoryTheory.Limits.CokernelCofork.ofπ
  | _, _ => none

/-- A declaration applied to fresh metavariables for all its arguments. -/
def instantiateFresh (declaration : Name) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  return mkAppN constant args

namespace Semantic

/-- `F.obj X`, elaborated at the current depth, so that the universe levels and parameters of `F`'s
source category are assigned by `X`'s category (a bundled category is unfolded as needed). -/
def objOf (F X : Expr) : TermElabM Expr := do
  let value ← elabTermAndSynthesize
    (← `(Prefunctor.obj (CategoryTheory.Functor.toPrefunctor $(← exprToSyntax F)) $(← exprToSyntax X)))
    none
  instantiateMVars value

/-- The registered object `entry` at the parameters `params`. Recorded with its explicit
parameters (the declaration's explicit arguments). -/
def object (entry : ObjectEntry) (params : Array Term) (trace? : Option Trace := none) :
    TermElabM Expr := do
  let value ← elabTermAndSynthesize (← `($(mkCIdent entry.declaration) $params*)) none
  let value ← instantiateMVars value
  if value.getAppFn.constName? == some entry.declaration then
    let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
      xs.mapM (·.fvarId!.getBinderInfo)
    let explicit := (value.getAppArgs.zip infos).filterMap fun (a, i) =>
      if i.isExplicit then some a else none
    Trace.record trace? value (.object entry.id explicit)
  return value

/-- The morphism `f : a ⟶ b`. -/
def hom (f : Term) (a b : Expr) : TermElabM Expr := do
  let expected ← mkAppM ``Quiver.Hom #[a, b]
  let value ← elabTermEnsuringType f expected
  synthesizeSyntheticMVarsNoPostponing
  mkExpectedTypeHint (← instantiateMVars value) expected

/-- The registered limit (colimit) of `shape` at the diagram `D` of the category `category`: its
presentation, returned along the registered creation lift when it is computed elsewhere. -/
def limit (colimit : Bool) (shape : String) (D : Expr) (category : String)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let state ← registryState
  let some entry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveLimit entry.id shape colimit with
    | .ok resolution => pure resolution
    | .error message => throwStratum .invalid m!"{message}"
  let some row := state.limits.find? (·.id == resolution.limit) | unreachable!
  let family ← instantiateFresh row.declaration
  let familyDiagram := (← whnfR (← inferType family)).appArg!
  -- The presentation at the diagram `F`, identified with its standard form.
  let presentationAt (F : Expr) : TermElabM Expr := do
    let some isoName := standardFormIso shape
      | throwStratum .invalid m!"the shape {shape} has no standard form"
    let α ← mkAppM isoName #[F]
    let standard := (← whnfR (← inferType α)).getAppArgs.back!
    unless ← withTransparency .all <| isDefEq familyDiagram standard do
      throwStratum .invalid m!"the registered {shape} {row.id.raw} does not apply to this diagram"
    instantiateMVars (← mkAppM (if colimit then ``colimitCoconeOfIso else ``limitConeOfIso)
      #[α, family])
  let presentation ← match resolution.lift.bind fun id => state.lifts.find? (·.id == id) with
    | none => presentationAt D
    | some lift => do
        if colimit then
          throwStratum .invalid m!"a colimit returned along a lift is not registered"
        let U ← state.edgeFunctor lift.edge
        let L ← presentationAt (← withTransparency .all <| mkFunctorComp D U)
        let evidence ← instantiateFresh lift.evidence
        let lifted ← elabTermAndSynthesize (← `(@CasCatalogue.liftedLimitCone _ _ _ _ _ _
          $(← exprToSyntax U) $(← exprToSyntax evidence) _ $(← exprToSyntax L))) none
        instantiateMVars lifted
  Trace.record trace? presentation (.limit row.id D resolution.lift)
  return presentation

/-- The value of the method `name` on the object `X` of `category`, and the category it is in. -/
def method (name : String) (X : Expr) (category : NamedCategoryEntry)
    (trace? : Option Trace := none) : TermElabM (Expr × NamedCategoryEntry) := do
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
  let input ← methodArgument resolution.method image
  let value ← objOf F input
  Trace.record trace? value (.method resolution.method.id resolution.route.refs X)
  return (value, target)

/-- The proposition that the property `name` holds of the object `X` of `category`. -/
def property (name : String) (X : Expr) (category : NamedCategoryEntry)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let state ← registryState
  let resolution ← match state.resolveProperty category.expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← state.routeFunctor (resolution.route.steps.map (·.ref))) X
  let classifier ← classifierInstance resolution.classifier
  let holds ← elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax image))) none
  let holds ← instantiateMVars holds
  Trace.record trace? holds (.property resolution.property.id resolution.route.refs X)
  return holds

end Semantic

end CasCatalogue
