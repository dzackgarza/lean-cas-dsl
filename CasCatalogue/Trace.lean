/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Registry.Entry
public import CasCatalogue.Resolve
public import Std.Data.HashMap

@[expose] public section

/-!
# The operation tree of a semantic reading (`specs/leaf-registration.md`, "The realized reading")

The realized reading evaluates the same term the semantic reading elaborates; there is no second
traversal of the statement. The semantic reading records, as it forms each value, the catalogue
operation that formed it, keyed by the value it produced: a named object at its parameters, a
method or property after its structural route, a registered limit at its diagram. The realized
reading walks these records bottom-up. Nothing is reverse-engineered from a printed term.
-/

open Lean

namespace CasCatalogue

/-- A local category context derived from accepted actions. The complete selected
bundle is retained even when the expression has no separately named registry row. -/
structure CategoryContext where
  expression : CategoryExpr
  bundle : Expr
  deriving Repr

/-- Accepted source presentations of one definitionally identical complete structured value.
The identity is a kernel-checkable conversion proof of the full image, never its carrier. -/
structure ParameterPresentation where
  source : ObjectId
  sourceCategory : CategoryId
  targetCategory : CategoryId
  params : Array Expr
  route : Array EdgeRef
  applications : Array Expr
  carrierRoute : Array EdgeRef
  identifications : Array Name
  object : Expr
  image : Expr
  identity : Expr
  deriving Repr

/-- One complete selected source of a routed operation. Accepted route comparisons
retain their exact constructor and whiskering contexts and the checked typed witnesses. -/
structure OperationSource where
  context : CategoryContext
  receiver : Expr
  route : Array EdgeRef
  applications : Array Expr
  comparisons : Array RouteComparison := #[]
  comparisonWitnesses : Array Expr := #[]
  deriving Repr

/-- One surviving registered binding, before any equivalence-class representative is
chosen. The complete declaration application precedes its actual supplied operands. -/
structure OperationCandidate where
  operation : OperationId
  application : Expr
  result : Expr
  sources : Array OperationSource
  deriving Repr

/-- A checked equality of universally abstracted complete routed operation families.
The indices refer to the retained candidates and their complete source witnesses.
`parameters` instantiates that shared dependent context only after the identity is checked. -/
structure OperationFamilyComparison where
  left : Nat
  right : Nat
  leftSource : Nat
  rightSource : Nat
  parameters : Array Expr
  leftFamily : Expr
  rightFamily : Expr
  leftType : Expr
  rightType : Expr
  identity : Expr
  deriving Repr

/-- How the semantic reading formed a value. -/
inductive Node
  /-- The registered object `id` at its explicit parameters (numerals, or other values). -/
  | object (id : ObjectId) (params : Array Expr)
  /-- A typed constructor parameter obtained along an accepted structural route. -/
  | parameterTransport (source : ObjectId) (sourceCategory targetCategory : CategoryId)
      (route : Array EdgeRef) (receiver : Expr)
  /-- Structural transport of an anonymous selected object, with exact source provenance. -/
  | structureTransport (sourceCategory targetCategory : CategoryId)
      (route : Array EdgeRef) (receiver : Expr)
  /-- A structural route retaining the exact full edge applications formed by the reading. -/
  | retainedRoute (sourceCategory targetCategory : CategoryId) (route : Array EdgeRef)
      (applications : Array Expr) (receiver : Expr)
  /-- Proof-only construction in an actual classifier total, retaining the complete
  original object, registered forgetful action and full-image identification. -/
  | proofRefinement (classifier : ClassifierId) (sourceCategory targetCategory : CategoryId)
      (source action identity : Expr)
  | parameterEquivalence (expectedType representative : Expr)
      (sources : Array ParameterPresentation)
  /-- A registered named morphism at its ordered explicit declaration arguments. -/
  | namedMorphism (id : MorphismId) (params : Array Expr)
  /-- A registered inclusion at its complete declared parameters and exact endpoints. -/
  | namedInclusion (id : InclusionId) (category : CategoryId) (params : Array Expr)
      (source target : Expr)
  /-- A map the object row `object` registers as its field `field` (`inclusion`: the admission
  inclusion `Mˣ ↪ M`; `constants`: `R → R[[t]]`), at its explicit parameters. -/
  | objectField (object : ObjectId) (field : String) (category : CategoryId) (params : Array Expr)
  /-- A map of the registered power object `powerObject`, its field `field` (`member`, `truth`)
  at its explicit parameters. -/
  | powerObjectMap (powerObject : PowerObjectId) (field : String) (params : Array Expr)
  /-- A callable published as a typed field of a registered owner. -/
  | namedCallable (address : String) (category : CategoryId) (params : Array Expr)
  /-- A typed callable body in its exact generalized-element domain context. -/
  | callableRecipe (category : CategoryId) (domain target body : Expr)
  /-- A formally admitted point retaining its original computational datum and endpoints. -/
  | admittedPoint (object : ObjectId) (category : CategoryId) (params : Array Expr)
      (original : Expr) (originalCategory : CategoryId) (originalSource originalTarget : Expr)
  /-- The actual checked one-data-field constructor, retaining the original point map. -/
  | constrainedPoint (constructor : Name) (category : CategoryId)
      (domain source target original : Expr)
  /-- An accepted presentation comparison, retaining declaration arguments and orientation. -/
  | presentation (id : NaturalTransformationId) (params : Array Expr) (inverse : Bool)
  | generator (id : ObjectId) (params : Array Expr)
  | presentationApply (id : NaturalTransformationId) (params : Array Expr) (inverse : Bool)
      (source target argument : Expr)
  /-- A closed selected element formed by an accepted operation, retaining all typed inputs. -/
  | operationApply (id : OperationId) (params operands : Array Expr) (target selected : Expr)
  | operationPoint (id : OperationId) (params : Array Expr)
      (comparison operation target selected : Expr)
  /-- The entire checked class of inherited operations. `chosen` is a deterministic
  serialization representative inside that class, never an operation-priority rule. -/
  | operationEquivalence (representative : Expr) (chosen : Nat)
      (candidates : Array OperationCandidate) (comparisons : Array OperationFamilyComparison)
  | elementNumeral (value : Nat) (target selected : Expr)
  /-- The value of a closed point at the registered terminal point, used as a dependent
  declaration parameter while retaining its complete selected computational source. -/
  | elementValue (point target selected : Expr)
  /-- The product mediator of independently fixed points at a retained formal product. -/
  | productMediator (category : CategoryId) (presentation domain left right : Expr)
  | morphismComposition (category : CategoryId) (first second source middle target : Expr)
  | morphismIdentity (category : CategoryId) (object : Expr)
  | contextualRoute (source target : CategoryContext) (route : Array EdgeRef)
      (applications : Array Expr) (receiver : Expr) (morphism : Bool)
  | contextualComposition (context : CategoryContext)
      (first second source middle target : Expr)
  | contextualIdentity (context : CategoryContext) (object : Expr)
  | contextualArrow (context : CategoryContext) (hom source target : Expr)
  /-- The stored map of an object of the registered arrow-category construction. -/
  | arrowProjection (receiver : Expr)
  /-- A defining leg of the exact retained universal construction. -/
  | limitProjection (receiver index : Expr)
  /-- A field of the complete accepted Arrow/subobject or universal-construction schema.
  An optional index is an actual registered data-constructor port, never a value lookup. -/
  | structuredProjection (receiver : Expr) (field : String) (index : Option Nat)
  /-- The canonical cartesian map and its endpoints, fixed by a registered family
  reindexing, its complete parameters, original base map and selected fibre object. -/
  | cartesian (id : FunctorId) (params : Array Expr) (baseMorphism receiver : Expr)
      (field : String)
  /-- Forward point identification along a checked carrier-preserving structural view. -/
  | pointView (source target : Expr) (route : Array EdgeRef)
      (applications : Array Expr) (argument : Expr)
  /-- The exact map action of an accepted structural route. -/
  | morphismTransport (sourceCategory targetCategory : CategoryId)
      (route : Array EdgeRef) (receiver : Expr)
  /-- A registered functor's object action at its typed parameters and exact receiver. -/
  | functor (id : FunctorId) (params : Array Expr) (receiver : Expr)
  /-- A directly selected registered construction, with every declaration parameter. -/
  | construction (id : ConstructionId) (params : Array Expr) (receiver : Expr)
  | constructionMap (id : ConstructionId) (params : Array Expr)
      (source target morphism : Expr)
  | categoryParameter (id : CategoryId) (params : Array Expr)
  | functorParameter (id : FunctorId) (params : Array Expr)
  /-- The actual registered core construction retains its underlying complete object. -/
  | coreObject (context : CategoryContext) (object : Expr)
  | coreIso (context : CategoryContext) (source target forward backward : Expr)
  /-- An explicitly selected lift's four fields share this exact retained application. -/
  | selectedLift (id : LiftId) (params : Array Expr) (source inclusion monic : Expr)
  | liftProjection (receiver : Expr) (field : String)
  | liftFactor (receiver baseMap cone proof : Expr)
  /-- A component of a registered cell, after its declared constructor actions. -/
  | cellComponent (id : NaturalTransformationId) (params : Array Expr)
      (constructors : Array ConstructorId) (inverse : Bool) (receiver : Expr)
  | cellEndpoint (id : NaturalTransformationId) (params : Array Expr)
      (constructors : Array ConstructorId) (inverse right : Bool) (receiver : Expr)
  /-- A binder's exact parameters, domain map and independently admitted map. -/
  | binder (id : BinderId) (params : Array Expr) (domain body admitted : Expr)
  /-- A registered arrow-category object, with its defining map and both endpoints. -/
  | arrow (category : CategoryId) (morphism source target : Expr)
  /-- The denotation of the literal `literal` of the registered literal form `form` (a morphism
  of its graph, a finite subset of its elements). -/
  | literal (form : LiteralId) (literal : Expr)
  /-- The method `id`, applied to `receiver` after the structural route `route`. -/
  | method (id : MethodId) (route : Array EdgeRef) (receiver : Expr)
  /-- A method whose result has prescribed lifts back along its route. -/
  | methodWithLifts (id : MethodId) (route : Array EdgeRef) (lifts : Array LiftId)
      (receiver : Expr)
  /-- The property `id`, decided of `receiver` after the structural route `route`. -/
  | property (id : PropertyId) (route : Array EdgeRef) (receiver : Expr)
  /-- The registered limit `id` at the diagram `diagram`, returned along the registered creation
  lift `lift` when it is computed in another category. -/
  | limit (id : LimitId) (diagram : Expr) (lift : Option LiftId)
  deriving Repr

/-- The records of one statement's semantic reading. -/
abbrev Trace := IO.Ref (Std.HashMap Expr Node)

def Trace.new : IO Trace := IO.mkRef {}

/-- Record that `value` was formed by `node`, when a trace is being kept. -/
def Trace.record (trace? : Option Trace) (value : Expr) (node : Node) : IO Unit :=
  match trace? with
  | some trace => trace.modify (·.insert value node)
  | none => pure ()

/-- Record `derived` as formed the way `value` was (the apex of a recorded limit, say). -/
def Trace.alias (trace? : Option Trace) (value derived : Expr) : IO Unit := do
  let some trace := trace? | return
  if let some node := (← trace.get)[value]? then trace.modify (·.insert derived node)

/-- How `value` was formed, if it was recorded. -/
partial def Trace.node? (trace : Trace) (value : Expr) : IO (Option Node) := do
  if let some node := (← trace.get)[value]? then return some node
  match value with
  | .mdata _ body => trace.node? body
  | _ =>
      -- Elaboration's expected-type `id` wrappers carry the same formal construction.
      -- Categorical identities and mathematical operations remain distinct trace nodes.
      if value.isAppOfArity ``id 2 then trace.node? value.appArg! else pure none

end CasCatalogue
