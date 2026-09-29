/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Syntax
public import CasCatalogue.Trust

@[expose] public section

/-!
# Registry entries

Declaration names are stored as Lean `Name` values.  JSON serialization is a
presentation concern; registration and environment lookup retain the checked
identity.
-/

namespace CasCatalogue


/-- Which lifts a registered fibration supplies. -/
inductive FibrationVariance
  /-- Cartesian lifts (`Functor.IsFibered`): reindexing is contravariant. -/
  | cartesian
  /-- Cocartesian lifts (`Functor.IsCofibered`): transport is covariant. -/
  | cocartesian
  deriving DecidableEq, Repr, Inhabited

/-- A fibration registry row (CC-FIB): a registered functor `projection : total ⥤ base`
together with `evidence`, a Lean proof that it is a cartesian (`Functor.IsFibered`) or
cocartesian (`Functor.IsCofibered`) fibration. Its fibres are the categories that vary with an
object of `base`. -/
structure FibrationEntry where
  id : FibrationId
  projection : FunctorId
  variance : FibrationVariance
  evidence : Lean.Name
  deriving Repr

/-- One step of a structural route: a registered structural functor row, or the forgetful
functor `total(c) → host(c)` of a registered classifier. -/
inductive EdgeRef
  | functor (id : FunctorId)
  | classifierForget (id : ClassifierId)
  /-- A functorial constructor applied to a structural edge: `Arr(U)`, `Core(U)`. Derived, never
  registered. -/
  | constructMap (constructor : ConstructorId) (inner : EdgeRef)
  deriving DecidableEq, Repr, Inhabited

/-- A functor action registry row (CC-ACTION): `realization` names a `RealizedAction F dC dD`,
an executable object and morphism action on realizations together with the proof that it
commutes with denotation, where `F` is (an instance of) the Mathlib functor of `edge`: a
registered functor row, or a registered classifier's forgetful functor. A composite functor's
action is the composite of its factors' actions and is never registered. -/
structure FunctorActionEntry where
  id : ActionId
  edge : EdgeRef
  realization : Lean.Name
  deriving Repr

/-- How a method's semantic functor consumes its receiver. -/
inductive MethodShape
  /-- The functor's source is the owner category itself. -/
  | object
  /-- The functor's source is `Core(owner)`: an isomorphism invariant of objects of the owner. -/
  | isoInvariant
  deriving DecidableEq, Repr, Inhabited

/-- A method presentation row (#53 §7): the surface name `name` of the registered functor
`functor`, owned at the category `owner` (its lowest generating level, #53 §5). It creates no
semantics: it names checked functor semantics. -/
structure MethodEntry where
  id : MethodId
  name : String
  owner : CategoryExpr
  functor : FunctorId
  shape : MethodShape
  /-- The result is a subobject of the receiver's image, and must be lifted back along every
  step of the route to become a subobject of the receiver itself (CC-LIFT). -/
  returnsToSource : Bool := false
  deriving Repr

/-- A lift row (CC-LIFT): `evidence` names a `MonoLift U`, lifts of subobjects along a functor
`U : C ⥤ D`; it serves the route step `edge`, which must be `U.mapArrow : Arr(C) ⥤ Arr(D)`. -/
structure LiftEntry where
  id : LiftId
  edge : EdgeRef
  evidence : Lean.Name
  deriving Repr

/-- A realizer row (CC-SEP): `denotation` names a denotation functor `R ⥤ C` whose category `C` is the
registered category `category`. A handle's category is the category of the realizer it is used
with; nothing inspects the handle to find one. `backend` names the engine that produces handles. -/
structure RealizerEntry where
  id : RealizerId
  category : CategoryId
  denotation : Lean.Name
  backend : String
  /-- A `Functor.FullyFaithful` witness for the denotation, when it is fully faithful (an induced
  realization): cells are then realized on it as preimages. -/
  fullyFaithful : Option Lean.Name := none
  deriving Repr

/-- A fused implementation row (CC-ROUTE, CC-TRUST): a backend realization of the whole composite
`method ∘ route`, keyed by that semantic composite. It is one more realization of the same
operation, never a new method, and carries its epistemic status. -/
structure ImplementationEntry where
  id : ImplementationId
  method : MethodId
  route : Array EdgeRef
  realization : Lean.Name
  backend : String
  trust : Trust
  deriving Repr

/-- A registered isomorphism between two realized objects (CC-CARRIER): `evidence` names a
an isomorphism `source ≅ target` in the handle category of the registered realizer `realizer`. -/
structure HandleIsoEntry where
  id : HandleIsoId
  realizer : RealizerId
  source : Lean.Name
  target : Lean.Name
  evidence : Lean.Name
  deriving Repr

/-- A cell row (CC-CALC, CC-COHERE): a natural transformation `declaration : L ⟶ R` (or, when `invertible`,
a natural isomorphism `L ≅ R`) between the composites `L`, `R` of the registered functors along
`left` and `right` (the identity of `source` when empty). The cell is Mathlib's; the row names it
so that it can be composed, whiskered and realized. An invertible cell between two distinct
structural routes identifies them (a comparison): a call reached along either runs on the route the
cell's direction designates, and its component carries data between the two. -/
structure CellEntry where
  id : NaturalTransformationId
  source : CategoryExpr
  target : CategoryExpr
  left : Array EdgeRef
  right : Array EdgeRef
  declaration : Lean.Name
  invertible : Bool := false
  deriving Repr

/-- A property presentation row (CC-PROP): the surface name `name` of the registered classifier
`classifier`, which alone owns the property's meaning. With `receiver := some A` it is an alias
available only on `A` (e.g. `is_abelian` on groups for commutativity of the multiplicative port,
#53 §12); it adds no meaning. -/
structure PropertyEntry where
  id : PropertyId
  name : String
  classifier : ClassifierId
  receiver : Option CategoryExpr := none
  deriving Repr

/-- A decision-procedure row (CC-PROP, CC-DECIDE): `realization` names a `Decider c d` for the
registered classifier `classifier`. A backend decides a property; it never defines one. -/
structure DeciderEntry where
  id : DeciderId
  classifier : ClassifierId
  realization : Lean.Name
  deriving Repr

/-- The kind of one argument of a typed category constructor. -/
inductive ConstructorArgKind
  | category
  | object
  | functor
  deriving DecidableEq, Repr, Inhabited

/-- A typed category constructor (#54 §1): its argument signature and the Lean definition that is
its semantics. A category whose expression is `.construct id args` must be definitionally
`semantics` applied to the registered denotations of `args`. -/
structure ConstructorEntry where
  id : ConstructorId
  signature : Array ConstructorArgKind
  semantics : Lean.Name
  /-- For a unary category constructor that is functorial, its action on functors
  (`F : C ⥤ D` to `semantics C ⥤ semantics D`), e.g. `Functor.mapArrow` for `Arr`. -/
  functorialAction : Option Lean.Name := none
  deriving Repr

/-- Named category registry row. -/
structure NamedCategoryEntry where
  id : CategoryId
  declaration : Lean.Name
  expression : CategoryExpr
  /-- Elaborated witness tying this expression to the declared category. -/
  realization : Lean.Name
  /-- Typed pullback witness required when the expression is a refinement. -/
  refinementRealization : Option Lean.Name := none
  deriving Repr, Inhabited

/--
A parameterized category family, distinct from any selected category node.

The typed realization supplies the parameter data and its category-valued fibre.
The registry records transport orientation separately.
-/
structure CategoryFamilyEntry where
  id : CategoryFamilyId
  schema : CategoryFamilySchema
  realization : Lean.Name
  transport : Lean.Name
  transportSemantics : CategoryFamilyTransportSemantics
  deriving Repr, Inhabited

/-- Classifier registry row. -/
structure ClassifierEntry where
  id : ClassifierId
  declaration : Lean.Name
  host : CategoryExpr
  realization : Lean.Name
  deriving Repr, Inhabited

/-- A typed functor declaration, with expression endpoints checked by Lean. -/
structure FunctorEntry where
  id : FunctorId
  source : CategoryExpr
  target : CategoryExpr
  declaration : Lean.Name
  realization : Lean.Name
  expression : FunctorExpr source target
  /-- Whether this functor sends an object to its *underlying* object (a forgetful functor,
  an inclusion, a fibre inclusion `ι_R : Mod_R → ∫ Mod`): the only kind of registered functor
  along which methods are inherited (#53 §8, CC-UNIFORM). Not structural: construction functors
  (base change, change of values, reindexing along a parameter morphism), which need data the
  receiver does not carry, and a fibration's projection to its base or value parameters
  (`∫ Mod → Ring`, `Bil → ∫ Mod` by values), which reads a parameter of the object rather than
  an object it *is*: a module is not a ring, so it must not inherit the ring's cardinality. -/
  structural : Bool := false
  deriving Repr

/-- Opaque category with typed structural ports. -/
structure StructuralPortEntry where
  id : OpaquePortId
  source : CategoryExpr
  target : CategoryExpr
  declaration : Lean.Name
  realization : Lean.Name
  provenance : String
  deriving Repr, Inhabited

structure OpaqueCategoryEntry where
  id : CategoryId
  declaration : Lean.Name
  realization : Lean.Name
  ports : Array StructuralPortEntry
  reason : String
  deriving Repr, Inhabited

end CasCatalogue
