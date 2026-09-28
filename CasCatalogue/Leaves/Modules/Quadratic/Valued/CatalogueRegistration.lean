module

public import CasCatalogue.Registry.Extension
public import LeanCategories.Modules.Mathlib
public import CasCatalogue.Leaves.Modules.CatalogueRegistration
public import LeanCategories.Modules.Quadratic.Valued.ChangeValue
public import CasCatalogue.Leaves.Modules.Quadratic.Valued.Catalogue
public import CasCatalogue.Leaves.Modules.Quadratic.Valued.Expressions
public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import LeanCategories.Modules.Quadratic.Valued.Total
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Modules.Catalogue
public meta import LeanCategories.Modules.Quadratic.Valued.ChangeValue
public meta import CasCatalogue.Leaves.Modules.Quadratic.Valued.Catalogue
public meta import CasCatalogue.Leaves.Modules.Quadratic.Valued.Expressions

@[expose] public section

namespace CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration
open LeanCategories LeanCategories.Modules LeanCategories.Modules.Quadratic LeanCategories.Modules.Quadratic.Valued

open CategoryTheory
open LeanCategories CasCatalogue
open CasCatalogue.Modules.Quadratic.Valued.Catalogue

universe u

noncomputable def quadModuleFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1}
    (P := Σ R : CommRingCat.{u}, ModuleCat.{u} R)
    (fun (parameter : Σ R : CommRingCat.{u}, ModuleCat.{u} R) =>
    letI := parameter.1.commRing
    (Cat.of (QuadModuleCat parameter.1 parameter.2) : ObjCat.{u + 1, u}))

noncomputable def quadModuleFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.quadModule .commRingModule
      (P := Discrete (Σ R : CommRingCat.{u}, ModuleCat.{u} R)) where
  transport := quadModuleFamilyTransport
  transportSemantics := .discrete

noncomputable def quadWFormFamilyTransport :=
  discreteFamilyTransport.{u + 1, u, u + 1} (P := CommRingCat.{u})
    (fun (R : CommRingCat.{u}) =>
    letI := R.commRing
    (Cat.of (QuadWFormCat R) : ObjCat.{u + 1, u}))

noncomputable def quadWFormFamilyRealization :
    CategoryFamilyRealization.{u + 1, u, u + 1, u + 1} CategoryFamilyId.quadWForm .commRing
      (P := Discrete (CommRingCat.{u})) where
  transport := quadWFormFamilyTransport
  transportSemantics := .discrete
noncomputable def quadModuleCategory (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] : ObjCat.{u + 1, u} :=
  Cat.of (QuadModuleCat R W)

noncomputable def quadWFormCategory (R : Type u) [CommRing R] : ObjCat.{u + 1, u} :=
  Cat.of (QuadWFormCat R)

noncomputable def quadModuleRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    CategoryRealization QuadModule (quadModuleCategory R W) where
  familyFibre := some (.mk quadModuleFamilyRealization {
    parameter := ⟨CommRingCat.of R, ModuleCat.of R W⟩
    parameterQuotation := .commRingModuleRW (CommRingCat.of R) (ModuleCat.of R W)
    category_eq := by rfl })

noncomputable def quadWFormRealization (R : Type u) [CommRing R] :
    CategoryRealization QuadWForm (quadWFormCategory R) where
  familyFibre := some (.mk quadWFormFamilyRealization {
    parameter := ⟨CommRingCat.of R⟩
    parameterQuotation := .commRingR (CommRingCat.of R)
    category_eq := by rfl })

noncomputable def quadModuleForgetRealization (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    FunctorRealization QuadModuleForget (quadModuleCategory R W)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Quadratic.Valued.forget R W) :=
  { sourceRealization := quadModuleRealization R W
    targetRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization (RingCat.of R) }

noncomputable def quadModuleForgetDeclaration (R : Type u) [CommRing R]
    (W : Type u) [AddCommGroup W] [Module R W] :
    quadModuleCategory R W ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Modules.Quadratic.Valued.forget R W).toCatHom

noncomputable def quadModuleChangeValueRealization (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    FunctorRealization QuadModuleChangeValue (quadModuleCategory R W)
      (quadModuleCategory R W')
      (LeanCategories.Modules.Quadratic.Valued.changeValue R W f) :=
  { sourceRealization := quadModuleRealization R W
    targetRealization :=
       { familyFibre := some (.mk quadModuleFamilyRealization {
          parameter := ⟨CommRingCat.of R, ModuleCat.of R W'⟩
          parameterQuotation := .commRingModuleRWPrime (CommRingCat.of R) (ModuleCat.of R W')
          category_eq := by rfl }) } }

noncomputable def quadWFormValueRealization (R : Type u) [CommRing R] :
    FunctorRealization QuadWFormValue (quadWFormCategory R)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Quadratic.Valued.valueProjection R) :=
  { sourceRealization := quadWFormRealization R
    targetRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization
      (RingCat.of R) }

noncomputable def quadWFormCarrierRealization (R : Type u) [CommRing R] :
    FunctorRealization QuadWFormCarrier (quadWFormCategory R)
      (Modules.Mathlib.ModulesOf (RingCat.of R))
      (LeanCategories.Modules.Quadratic.Valued.carrierProjection R) :=
  { sourceRealization := quadWFormRealization R
    targetRealization := CasCatalogue.Modules.CatalogueRegistration.modulesRealization
      (RingCat.of R) }

noncomputable def quadModuleChangeValueDeclaration (R : Type u) [CommRing R]
    (W W' : Type u) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (f : W →ₗ[R] W') :
    quadModuleCategory R W ⟶ quadModuleCategory R W' :=
  (LeanCategories.Modules.Quadratic.Valued.changeValue R W f).toCatHom

noncomputable def quadWFormValueDeclaration (R : Type u) [CommRing R] :
    quadWFormCategory R ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Modules.Quadratic.Valued.valueProjection R).toCatHom

noncomputable def quadWFormCarrierDeclaration (R : Type u) [CommRing R] :
    quadWFormCategory R ⟶ Modules.Mathlib.ModulesOf (RingCat.of R) :=
  (LeanCategories.Modules.Quadratic.Valued.carrierProjection R).toCatHom

normalized_registry .categoryFamily
  { id := CategoryFamilyId.quadModule
    schema := .commRingModule
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleFamilyRealization
    transport :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleFamilyTransport
    transportSemantics := .discrete }

normalized_registry .categoryFamily
  { id := CategoryFamilyId.quadWForm
    schema := .commRing
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormFamilyRealization
    transport :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormFamilyTransport
    transportSemantics := .discrete }

normalized_registry .category
  { id := CategoryId.quadModule
    declaration := `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleCategory
    expression := QuadModule
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleRealization}

normalized_registry .category
  { id := CategoryId.quadWForm
    declaration := `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormCategory
    expression := QuadWForm
    realization := `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormRealization}

normalized_registry .functor
  { id := FunctorId.quadModuleForget
    source := QuadModule
    target := Modules.Modules
    declaration :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleForgetDeclaration
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleForgetRealization
    expression := QuadModuleForget }

normalized_registry .functor
  { id := FunctorId.quadModuleChangeValue
    source := QuadModule
    target :=
      .familyApp CategoryFamilyId.quadModule
        #[.variable ParameterId.r, .variable ParameterId.wPrime]
    declaration :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleChangeValueDeclaration
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadModuleChangeValueRealization
    expression := QuadModuleChangeValue }

normalized_registry .functor
  { id := FunctorId.quadWFormValue
    source := QuadWForm
    target := Modules.Modules
    declaration :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormValueDeclaration
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormValueRealization
    expression := QuadWFormValue }

normalized_registry .functor
  { id := FunctorId.quadWFormCarrier
    source := QuadWForm
    target := Modules.Modules
    declaration :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormCarrierDeclaration
    realization :=
      `CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration.quadWFormCarrierRealization
    expression := QuadWFormCarrier }

end CasCatalogue.Modules.Quadratic.Valued.CatalogueRegistration
