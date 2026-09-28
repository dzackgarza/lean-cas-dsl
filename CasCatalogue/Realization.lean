module

public import LeanCategories.CategoryTheory.OneCat.Classifier
public import LeanCategories.CategoryTheory.OneCat.CategoricalPullback
public import CasCatalogue.Syntax
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# Typed catalogue realizations

These witnesses connect symbolic expressions to actual categories, classifiers,
families, and functors. Imported domain modules provide the witnesses locally.
-/

namespace CasCatalogue
open LeanCategories

open CategoryTheory

universe u v

namespace CategoryFamilySchema
end CategoryFamilySchema

universe uObj uHom uParam uParamHom
universe uHostParam uHostParamHom uTotalParam uTotalParamHom uParameterType uP
universe uSourceParam uSourceParamHom uTargetParam uTargetParamHom
universe uSourceObj uSourceHom uTargetObj uTargetHom

attribute [local simp] Bicategory.Strict.leftUnitor_eqToIso
  Bicategory.Strict.rightUnitor_eqToIso Bicategory.Strict.associator_eqToIso

/-- A family indexed by a discrete parameter object, with no transport beyond equality. -/
noncomputable def discreteFamilyTransport {P : Type uParam}
    (fibre : P → ObjCat.{uObj, uHom}) :
    Pseudofunctor (LocallyDiscrete (Discrete P)ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  Functor.toPseudofunctor' ((Discrete.opposite P).functor ⋙ Discrete.functor fibre)

/-- An actual parameterized family assigned to a family identifier. -/
structure CategoryFamilyRealization (identifier : CategoryFamilyId)
    (schema : CategoryFamilySchema) {P : Type uParameterType} where
  [parameterCategory : Category.{uParamHom} P]
  /-- The source category universe is independent of the fibre `Cat` universe. -/
  transport :
    Pseudofunctor (LocallyDiscrete Pᵒᵖ)
      (Cat.{uHom, max uObj uHom})
  /-- The registered semantic kind of this transport. -/
  transportSemantics : CategoryFamilyTransportSemantics

/-- The selected fibre is the pseudofunctor value at the opposite parameter. -/
def CategoryFamilyRealization.fibre {identifier : CategoryFamilyId}
    {schema : CategoryFamilySchema}
    {P : Type uParameterType}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParamHom, uParameterType}
      identifier schema (P := P))
    (parameter : P) : ObjCat.{uObj, uHom} :=
  letI := realization.parameterCategory
  realization.transport.obj (.mk (Opposite.op parameter))

/-- The canonical equality-only transport for commutative-ring fibres. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteCommRingTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam + 1, uParam + 1}
      identifier .commRing (P := Discrete (CommRingCat.{uParam}))) :
    Pseudofunctor (LocallyDiscrete (Discrete (CommRingCat.{uParam}))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, uParam + 1}
    (fun parameter => realization.fibre ⟨parameter⟩)

/-- The canonical equality-only transport for commutative-ring module fibres. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteCommRingModuleTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam + 1, uParam + 1}
      identifier .commRingModule
        (P := Discrete (Σ R : CommRingCat.{uParam}, ModuleCat.{uParam} R))) :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ R : CommRingCat.{uParam}, ModuleCat.{uParam} R))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, uParam + 1}
    (fun parameter => realization.fibre ⟨parameter⟩)

/-- The canonical equality-only transport for commutative-ring natural-number fibres. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteCommRingNatTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam + 1, uParam + 1}
      identifier .commRingNat
        (P := Discrete (Σ _R : CommRingCat.{uParam}, Nat))) :
    Pseudofunctor
      (LocallyDiscrete (Discrete (Σ _R : CommRingCat.{uParam}, Nat))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, uParam + 1}
    (fun parameter => realization.fibre ⟨parameter⟩)

/-- The canonical equality-only transport for arbitrary commutative-ring index types. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteCommRingIndexTypeTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom,
      max (uParam + 1) (v + 1), max (uParam + 1) (v + 1)}
      identifier .commRingIndexType
        (P := CategoryFamilySchema.indexTypeParameters.{uParam, v})) :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (Σ _R : CommRingCat.{uParam}, Type v))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, max (uParam + 1) (v + 1)}
    (fun parameter => realization.fibre ⟨parameter⟩)

/-- The canonical equality-only transport for domain-refined commutative-ring fibres. -/
noncomputable def CategoryFamilyRealization.canonicalDiscreteDomainTransport
    {identifier : CategoryFamilyId}
    (realization : CategoryFamilyRealization.{uObj, uHom, uParam + 1, uParam + 1}
      identifier .domain
        (P := Discrete (PSigma fun R : CommRingCat.{uParam} => IsDomain R))) :
    Pseudofunctor
      (LocallyDiscrete
        (Discrete (PSigma fun R : CommRingCat.{uParam} => IsDomain R))ᵒᵖ)
      (Cat.{uHom, max uObj uHom}) :=
  discreteFamilyTransport.{uObj, uHom, uParam + 1}
    (fun parameter => realization.fibre ⟨parameter⟩)

/- Typed evidence for one exact family application. -/
opaque CategoryFamilyParameterQuotation (schema : CategoryFamilySchema)
    (arguments : Array ParameterExpr) {P : Type uParameterType} (parameter : P) : Prop

namespace CategoryFamilyParameterQuotation

axiom ringR (R : RingCat.{u}) :
    CategoryFamilyParameterQuotation .ring #[.variable ParameterId.r] R
axiom ringS (S : RingCat.{u}) :
    CategoryFamilyParameterQuotation .ring #[.variable ParameterId.s] S
axiom commRingR (R : CommRingCat.{u}) :
    CategoryFamilyParameterQuotation .commRing #[.variable ParameterId.r]
      (Discrete.mk R : Discrete (CommRingCat.{u}))
axiom commRingS (S : CommRingCat.{u}) :
    CategoryFamilyParameterQuotation .commRing #[.variable ParameterId.s]
      (Discrete.mk S : Discrete (CommRingCat.{u}))
axiom commRingModuleRW (R : CommRingCat.{u}) (W : ModuleCat.{u} R) :
    CategoryFamilyParameterQuotation .commRingModule
      #[.variable ParameterId.r, .variable ParameterId.w]
      (Discrete.mk (⟨R, W⟩ : Σ R : CommRingCat.{u}, ModuleCat.{u} R))
axiom commRingModuleSW (S : CommRingCat.{u}) (W : ModuleCat.{u} S) :
    CategoryFamilyParameterQuotation .commRingModule
      #[.variable ParameterId.s, .variable ParameterId.w]
      (Discrete.mk (⟨S, W⟩ : Σ S : CommRingCat.{u}, ModuleCat.{u} S))
axiom commRingModuleRWPrime (R : CommRingCat.{u}) (W : ModuleCat.{u} R) :
    CategoryFamilyParameterQuotation .commRingModule
      #[.variable ParameterId.r, .variable ParameterId.wPrime]
      (Discrete.mk (⟨R, W⟩ : Σ R : CommRingCat.{u}, ModuleCat.{u} R))
axiom commRingModuleSWPrime (S : CommRingCat.{u}) (W : ModuleCat.{u} S) :
    CategoryFamilyParameterQuotation .commRingModule
      #[.variable ParameterId.s, .variable ParameterId.wPrime]
      (Discrete.mk (⟨S, W⟩ : Σ S : CommRingCat.{u}, ModuleCat.{u} S))
axiom commRingModuleTensorProduct (R S W : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup W] [Module R W] :
    CategoryFamilyParameterQuotation .commRingModule
      #[.variable ParameterId.s,
        .apply3 ParameterOperationId.tensorProduct
          (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]
      (Discrete.mk (⟨CommRingCat.of S, ModuleCat.of S (TensorProduct R S W)⟩ :
        Σ S : CommRingCat.{u}, ModuleCat.{u} S))
axiom commRingNat (R : CommRingCat.{u}) (n : Nat) :
    CategoryFamilyParameterQuotation .commRingNat
      #[.variable ParameterId.r, .variable ParameterId.n]
      (Discrete.mk (⟨R, n⟩ : Σ _R : CommRingCat.{u}, Nat))
axiom commRingIndexTypeRI (R : CommRingCat.{u}) (I : Type v) :
    CategoryFamilyParameterQuotation .commRingIndexType
      #[.variable ParameterId.r, .variable ParameterId.i]
      (Discrete.mk (⟨R, I⟩ : Σ _R : CommRingCat.{u}, Type v))
axiom domain (R : CommRingCat.{u}) (hR : IsDomain R) :
    CategoryFamilyParameterQuotation .domain
      #[.variable ParameterId.r, .variable ParameterId.domain]
      (Discrete.mk (⟨R, hR⟩ : PSigma fun _R : CommRingCat.{u} => IsDomain _R))

end CategoryFamilyParameterQuotation
structure CategoryFamilyFibreWitness (category : ObjCat.{uObj, uHom})
    {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
    {P : Type uParameterType}
    (realization : CategoryFamilyRealization identifier schema (P := P))
    {arguments : Array ParameterExpr} where
  parameter : P
  parameterQuotation : CategoryFamilyParameterQuotation schema arguments parameter
  category_eq : category = realization.fibre parameter

def CategoryFamilyFibreWitness.arguments {category : ObjCat.{uObj, uHom}}
    {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
    {P : Type uParameterType}
    {realization : CategoryFamilyRealization.{uObj, uHom, uParamHom, uParameterType}
      identifier schema (P := P)}
    {arguments : Array ParameterExpr}
    (_witness : CategoryFamilyFibreWitness category realization (arguments := arguments)) :
    Array ParameterExpr := arguments

/-- Existential package for a fibre witness with its exact realization index. -/
inductive SomeCategoryFamilyFibreWitness (category : ObjCat.{uObj, uHom}) where
  | mk {identifier : CategoryFamilyId} {schema : CategoryFamilySchema}
    {P : Type uParameterType}
      (realization : CategoryFamilyRealization.{uObj, uHom, uParamHom, uParameterType}
        identifier schema (P := P))
      {arguments : Array ParameterExpr}
      (witness : CategoryFamilyFibreWitness category realization (arguments := arguments))

/-- An actual category assigned to a symbolic category expression. -/
structure CategoryRealization (expression : CategoryExpr)
    (category : ObjCat.{uObj, uHom}) where
  familyFibre : Option
      (SomeCategoryFamilyFibreWitness.{uObj, uHom, uParamHom, uParameterType} category) := none

/-- An actual classifier assigned to a symbolic host and classifier identifier. -/
structure ClassifierRealization (host : CategoryExpr) (identifier : ClassifierId)
    (category : ObjCat.{uObj, uHom}) (classifier : Classifier category) where
  hostRealization :
    CategoryRealization.{uObj, uHom, uHostParam, uHostParamHom} host category
  totalRealization :
    CategoryRealization.{uObj, uHom, uTotalParam, uTotalParamHom}
      (.classifierTotal identifier) classifier.total

/-- A typed realization of a refinement by the actual classifier pullback. -/
structure RefinementRealization (expression : CategoryExpr)
    (category : ObjCat.{uObj, uHom}) where
  base : CategoryExpr
  classifierId : ClassifierId
  expression_eq : expression = .refine base classifierId
  baseCategory : ObjCat.{uObj, uHom}
  host : CategoryExpr
  hostCategory : ObjCat.{uObj, uHom}
  baseRealization : CategoryRealization.{uObj, uHom, uObj, uHom} base baseCategory
  classifier : Classifier hostCategory
  classifierRealization :
    ClassifierRealization.{uObj, uHom, uObj, uHom, uObj, uHom}
      host classifierId hostCategory classifier
  baseToHost : baseCategory ⟶ hostCategory
  reindexed : Reindexed baseToHost classifier
  equivalence : category ≌ reindexed.total
  baseProjection : reindexed.total ⟶ baseCategory
  baseProjection_eq : baseProjection = reindexed.baseProjection
  classifierProjection : reindexed.total ⟶ classifier.total
  classifierProjection_eq : classifierProjection = reindexed.axiomProjection

/-- An actual functor assigned to a typed symbolic functor expression. -/
structure FunctorRealization {source target : CategoryExpr}
    (expression : FunctorExpr source target)
    (sourceCategory : ObjCat.{uSourceObj, uSourceHom})
    (targetCategory : ObjCat.{uTargetObj, uTargetHom})
    (functor : sourceCategory ⥤ targetCategory) where
  sourceRealization :
    CategoryRealization.{uSourceObj, uSourceHom, uSourceParam, uSourceParamHom}
      source sourceCategory
  targetRealization :
    CategoryRealization.{uTargetObj, uTargetHom, uTargetParam, uTargetParamHom}
      target targetCategory

/-- The forgetful functor is part of the typed classifier realization.

This witness fixes both endpoint realizations and the concrete functor.  A
registry row for `classifierForget` must use this exact witness.
-/
def ClassifierRealization.forgetfulRealization
    {host : CategoryExpr} {identifier : ClassifierId}
    {category : ObjCat.{uObj, uHom}} {classifier : Classifier category}
    (realization : ClassifierRealization host identifier category classifier) :
    FunctorRealization (.classifierForget identifier host)
      classifier.total category classifier.forget.toFunctor :=
  { sourceRealization := realization.totalRealization
    targetRealization := realization.hostRealization }

end CasCatalogue
