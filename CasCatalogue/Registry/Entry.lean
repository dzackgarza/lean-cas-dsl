/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Syntax

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
