module

@[expose] public section

/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Stable identity types

Stable IDs are normalized mathematical identity (matching the Python semantic seed /
authored ledger). They never embed Lean universe metavariables.
-/

namespace CasCatalogue


/-- Stable category id, e.g. `cat.sets`, `cat.commutative_rings`. -/
structure CategoryId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable classifier id, e.g. `clf.magmas.commutative`. -/
structure ClassifierId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable category-family id (parameterized constructors), e.g. `fam.modules`. -/
structure CategoryFamilyId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a parameter variable in a category-family expression. -/
structure ParameterId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a morphism variable between symbolic parameters, e.g. the ring map
`φ : R ⟶ S` along which a fibration is reindexed. -/
structure ParameterMorphismId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of an operation on symbolic parameters. -/
structure ParameterOperationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a category-family parameter kind. -/
structure ParameterKindId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable identity of a category-family variance declaration. -/
structure VarianceId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable fibration id, e.g. `fib.modules`. -/
structure FibrationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable category-constructor id, e.g. `ctor.arrow`, `ctor.slice`. -/
structure ConstructorId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered functor action on realizations (CC-ACTION), e.g.
`act.modules.underlying.int_free`. -/
structure ActionId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered method presentation, e.g. `meth.cardinality`. -/
structure MethodId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered property presentation, e.g. `prop.is_commutative`. -/
structure PropertyId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered decision procedure, e.g. `dec.magmas.commutative.table`. -/
structure DeciderId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered lift of subobjects along a route step (CC-LIFT). -/
structure LiftId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered realizer (a denotation of handles into a category), CC-SEP. -/
structure RealizerId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered fused implementation of a semantic composite, CC-ROUTE. -/
structure ImplementationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered isomorphism between two realized objects, CC-CARRIER. -/
structure HandleIsoId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a registered limit presentation, e.g. `lim.sets.pullback`. -/
structure LimitId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable id of a backend's presentation of the apex of a registered limit. -/
structure LimitRealizationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable functor id. -/
structure FunctorId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-! Stable identities for natural transformations. -/

/-- Stable natural-transformation id. -/
structure NaturalTransformationId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable structural port id, e.g. `port.multiplicative`. -/
structure PortId where
  raw : String
  deriving DecidableEq, Repr, Hashable

/-- Stable opaque structural port id. -/
structure OpaquePortId where
  raw : String
  deriving DecidableEq, Repr, Hashable


instance : Inhabited CategoryId := ⟨⟨""⟩⟩
instance : Inhabited FibrationId := ⟨⟨""⟩⟩
instance : Inhabited ActionId := ⟨⟨""⟩⟩
instance : Inhabited MethodId := ⟨⟨""⟩⟩
instance : Inhabited PropertyId := ⟨⟨""⟩⟩
instance : Inhabited DeciderId := ⟨⟨""⟩⟩
instance : Inhabited LiftId := ⟨⟨""⟩⟩
instance : Inhabited RealizerId := ⟨⟨""⟩⟩
instance : Inhabited ImplementationId := ⟨⟨""⟩⟩
instance : Inhabited HandleIsoId := ⟨⟨""⟩⟩
instance : Inhabited LimitId := ⟨⟨""⟩⟩
instance : Inhabited LimitRealizationId := ⟨⟨""⟩⟩
instance : Inhabited ClassifierId := ⟨⟨""⟩⟩
instance : Inhabited CategoryFamilyId := ⟨⟨""⟩⟩
instance : Inhabited ParameterId := ⟨⟨""⟩⟩
instance : Inhabited ParameterMorphismId := ⟨⟨""⟩⟩
instance : Inhabited ParameterOperationId := ⟨⟨""⟩⟩
instance : Inhabited ParameterKindId := ⟨⟨""⟩⟩
instance : Inhabited VarianceId := ⟨⟨""⟩⟩
instance : Inhabited NaturalTransformationId := ⟨⟨""⟩⟩
instance : Inhabited PortId := ⟨⟨""⟩⟩
instance : Inhabited OpaquePortId := ⟨⟨""⟩⟩

namespace ParameterId
def r : ParameterId := ⟨"R"⟩
def s : ParameterId := ⟨"S"⟩
def w : ParameterId := ⟨"W"⟩
def wPrime : ParameterId := ⟨"W'"⟩
def n : ParameterId := ⟨"n"⟩
def i : ParameterId := ⟨"I"⟩
def domain : ParameterId := ⟨"domain"⟩
end ParameterId

namespace ParameterMorphismId
def phi : ParameterMorphismId := ⟨"phi"⟩
end ParameterMorphismId

namespace ParameterOperationId
def opposite : ParameterOperationId := ⟨"parameter.opposite"⟩
def tensorProduct : ParameterOperationId := ⟨"parameter.tensor_product"⟩
end ParameterOperationId

namespace ParameterKindId
def ringObject : ParameterKindId := ⟨"parameter-kind.ring-object"⟩
def commRingObject : ParameterKindId := ⟨"parameter-kind.comm-ring-object"⟩
def moduleObject : ParameterKindId := ⟨"parameter-kind.module-object"⟩
def nat : ParameterKindId := ⟨"parameter-kind.nat"⟩
def indexType : ParameterKindId := ⟨"parameter-kind.index-type"⟩
def domain : ParameterKindId := ⟨"parameter-kind.domain"⟩
end ParameterKindId

namespace VarianceId
def restrictionOfScalarsContravariant : VarianceId :=
  ⟨"variance.restriction-of-scalars-contravariant"⟩
def discrete : VarianceId := ⟨"variance.discrete"⟩
end VarianceId

end CasCatalogue
