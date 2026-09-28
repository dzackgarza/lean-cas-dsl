module

public import CasCatalogue.Leaves.Foundation.CatalogueRegistration
public import CasCatalogue.Leaves.Algebra.CatalogueRegistration
public import CasCatalogue.Leaves.Modules.CatalogueRegistration
public import CasCatalogue.Leaves.Modules.Bilinear.Valued.CatalogueRegistration
public import CasCatalogue.Leaves.Modules.Quadratic.Valued.CatalogueRegistration
public import CasCatalogue.Leaves.Lattices.Valued.CatalogueRegistration
public import CasCatalogue.Leaves.Exceptional.CatalogueRegistration
public import CasCatalogue.FibrationRegistration
public import CasCatalogue.ConstructorRegistration

@[expose] public section

namespace CasCatalogue.Catalogue.Standard
open LeanCategories

open LeanCategories CasCatalogue

/-- Stable category rows owned by the standard catalogue. -/
def expectedCategoryIds : Array CategoryId := #[
  CategoryId.additiveGroups,
  CategoryId.additiveMagmas,
  CategoryId.additiveMonoids,
  CategoryId.additiveSemigroups,
  CategoryId.bilWForm,
  CategoryId.bilinFormsOverRings,
  CategoryId.latticesOverRings,
  CategoryId.integralForms,
  CategoryId.integralLattices,
  CategoryId.bilinModule,
  CategoryId.commutativeRings,
  CategoryId.crystals,
  CategoryId.definiteLattice,
  CategoryId.fractionFieldPerfectFiniteProjectiveLattice,
  CategoryId.divisionRings,
  CategoryId.evenLattice,
  CategoryId.finiteFreeLattice,
  CategoryId.finiteProjectiveLattice,
  CategoryId.finitelyGeneratedModules,
  CategoryId.finiteRankModules,
  CategoryId.freeModules,
  CategoryId.groups,
  CategoryId.indefiniteLattice,
  CategoryId.integralLattice,
  CategoryId.lattice,
  CategoryId.magmas,
  CategoryId.magmasWithTwoOperations,
  CategoryId.modulesR,
  CategoryId.modulesTotal,
  CategoryId.modulesOverRingsExt,
  CategoryId.genFrame,
  CategoryId.basisFrame,
  CategoryId.coord,
  CategoryId.genFrameIndexed,
  CategoryId.basisFrameIndexed,
  CategoryId.coordIndexed,
  CategoryId.coordLattice,
  CategoryId.monoids,
  CategoryId.quadModule,
  CategoryId.quadWForm,
  CategoryId.rings,
  CategoryId.semigroups,
  CategoryId.sets,
  CategoryId.arrowsSets,
  CategoryId.coreSets,
  CategoryId.sliceSets,
  CategoryId.cosliceSets,
  CategoryId.subobjectsSets,
  CategoryId.modulePoints,
  CategoryId.endofunctorsSets,
  CategoryId.unimodularLattice]

/-- Stable category-family rows owned by the standard catalogue. -/
def expectedCategoryFamilyIds : Array CategoryFamilyId := #[
  CategoryFamilyId.bilWForm,
  CategoryFamilyId.bilinModule,
  CategoryFamilyId.evenLattice,
  CategoryFamilyId.fractionFieldPerfectFiniteProjectiveLattice,
  CategoryFamilyId.finiteFreeLattice,
  CategoryFamilyId.finiteProjectiveLattice,
  CategoryFamilyId.lattice,
  CategoryFamilyId.modules,
  CategoryFamilyId.genFrame,
  CategoryFamilyId.basisFrame,
  CategoryFamilyId.coord,
  CategoryFamilyId.genFrameIndexed,
  CategoryFamilyId.basisFrameIndexed,
  CategoryFamilyId.coordIndexed,
  CategoryFamilyId.coordLattice,
  CategoryFamilyId.integralLattice,
  CategoryFamilyId.quadModule,
  CategoryFamilyId.quadWForm,
  CategoryFamilyId.unimodularLattice]

/-- Stable classifier rows owned by the standard catalogue. -/
def expectedClassifierIds : Array ClassifierId := #[
  ClassifierId.ringsDivision,
  ClassifierId.magmasAdditive,
  ClassifierId.magmasAssociative,
  ClassifierId.magmasCommutative,
  ClassifierId.magmasInverse,
  ClassifierId.magmasMultiplicative,
  ClassifierId.magmasUnital,
  ClassifierId.m2oDistributive,
  ClassifierId.modulesFinitelyGenerated,
  ClassifierId.bilLattice,
  ClassifierId.bilValues,
  ClassifierId.modulesFiniteRank,
  ClassifierId.modulesFree,
  ClassifierId.setsBinaryOperation,
  ClassifierId.setsFinite,
  ClassifierId.setsGraded]

/-- Stable functor rows owned by the standard catalogue. -/
def expectedFunctorIds : Array FunctorId := #[
  FunctorId.bilWFormBaseChange,
  FunctorId.bilinModuleBaseChange,
  FunctorId.bilinModuleChangeValue,
  FunctorId.bilinModuleForget,
  FunctorId.finiteProjectiveForget,
  FunctorId.basisFrameToGenFrame,
  FunctorId.fromBasisFrame,
  FunctorId.coordForget,
  FunctorId.modulesFibreInclusion,
  FunctorId.modulesReindex,
  FunctorId.modulesUnderlying,
  FunctorId.modulesProjection,
  FunctorId.modulesExtRing,
  FunctorId.bilinFormsValues,
  FunctorId.modulesExtRegularSection,
  FunctorId.integralFormsToBil,
  FunctorId.genFrameForget,
  FunctorId.basisFrameForget,
  FunctorId.integralLatticeForget,
  FunctorId.coordLatticeToCoord,
  FunctorId.coordLatticeToIntegral,
  FunctorId.fractionFieldPerfectFiniteProjectiveForget,
  FunctorId.latticeBaseChange,
  FunctorId.latticeChangeValue,
  FunctorId.quadModuleForget,
  FunctorId.quadModuleChangeValue,
  FunctorId.quadWFormCarrier,
  FunctorId.quadWFormValue,
  FunctorId.setsIdentity,
  FunctorId.sliceSetsForget,
  FunctorId.modulePointsProjection]

/-- Stable fibration rows owned by the standard catalogue. -/
def expectedFibrationIds : Array FibrationId := #[
  FibrationId.modules,
  FibrationId.modulesExt,
  FibrationId.bilinForms]

/-- Stable category-constructor rows owned by the standard catalogue. -/
def expectedConstructorIds : Array ConstructorId := #[
  ConstructorId.arrow, ConstructorId.core, ConstructorId.slice, ConstructorId.coslice,
  ConstructorId.elements, ConstructorId.subobjects, ConstructorId.functorCategory]

/-- Stable opaque-category rows owned by the standard catalogue. -/
def expectedOpaqueCategoryIds : Array CategoryId := #[
  CategoryId.crystals,
  CategoryId.magmasWithTwoOperations]

/-- Stable opaque-port rows owned by the standard catalogue. -/
def expectedOpaquePortIds : Array OpaquePortId := #[
  ⟨"oport.crystals.sets"⟩,
  ⟨"oport.m2o.multiplicative"⟩,
  ⟨"oport.m2o.additive"⟩]

def exactStableIdSet (actual expected : Array String) : Bool :=
  actual.size == expected.size &&
    actual.all (fun id => expected.any (· == id)) &&
    expected.all (fun id => actual.any (· == id))

def validateStableIdSet (kind : String) (actual expected : Array String) :
    Except String Unit :=
  if exactStableIdSet actual expected then
    .ok ()
  else
    .error s!"standard manifest {kind} do not match the expected stable-ID set"

def rawIds {α : Type} (ids : Array α) (raw : α → String) : Array String :=
  ids.map raw

/-- Validate every retained row kind emitted by the standard registry manifest. -/
def validateStandardManifest (manifest : RegistryManifest) : Except String Unit := do
  validateStableIdSet "categories" (manifest.categories.map (·.id))
    (rawIds expectedCategoryIds (·.raw))
  validateStableIdSet "category families" (manifest.categoryFamilies.map (·.id))
    (rawIds expectedCategoryFamilyIds (·.raw))
  validateStableIdSet "classifiers" (manifest.classifiers.map (·.id))
    (rawIds expectedClassifierIds (·.raw))
  validateStableIdSet "functors" (manifest.functors.map (·.id))
    (rawIds expectedFunctorIds (·.raw))
  validateStableIdSet "constructors" (manifest.constructors.map (·.id))
    (rawIds expectedConstructorIds (·.raw))
  validateStableIdSet "fibrations" (manifest.fibrations.map (·.id))
    (rawIds expectedFibrationIds (·.raw))
  validateStableIdSet "opaque categories" (manifest.opaqueCategories.map (·.id))
    (rawIds expectedOpaqueCategoryIds (·.raw))
  validateStableIdSet "opaque ports"
    (manifest.opaqueCategories.flatMap (fun category => category.ports.map (·.id)))
    (rawIds expectedOpaquePortIds (·.raw))

/- A missing registration must fail the standard contract. -/
example : !exactStableIdSet #[CategoryId.sets.raw]
    (rawIds expectedCategoryIds (·.raw)) := by
  native_decide

end CasCatalogue.Catalogue.Standard
