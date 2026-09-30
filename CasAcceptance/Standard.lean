module

public import LeanCategories.Catalogue.Semantics
public import CasContract.Registry.Extension
public meta import LeanCategories.Catalogue.Semantics
public meta import CasContract.Registry.Extension

@[expose] public section

/-!
# The standard catalogue's stable ids

The rows the exported registry manifest (`checkedRegistryManifest`) must carry: exactly the
semantic rows `lean-categories` registers. No row of a leaf exists: a leaf is a manifest of
registrations, imported by nothing (`specs/leaf-registration.md`).
-/

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
  CategoryId.finiteProjectiveLatticesOverRings,
  CategoryId.finiteFreeLatticesOverRings,
  CategoryId.unimodularLatticesOverRings,
  CategoryId.evenIntegralLattices,
  CategoryId.quadFormsOverRings,
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
  CategoryId.freeCover,
  CategoryId.basedModule,
  CategoryId.coord,
  CategoryId.freeCoverIndexed,
  CategoryId.basedModuleIndexed,
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
  CategoryId.walkingPair,
  CategoryId.setsPairDiagrams,
  CategoryId.finiteSets,
  CategoryId.unimodularLattice,
  CategoryId.cardinals,
  CategoryId.subobjectsGroups,
  CategoryId.arrowsGroups,
  CategoryId.arrowsModules,
  CategoryId.subobjectsModules,
  CategoryId.arrowsBilinModule,
  CategoryId.subobjectsBilinModule,
  CategoryId.coreModules,
  CategoryId.coreSubobjectsSets,
  CategoryId.subsetPredicates,
  CategoryId.subsetSubsetPredicates,
  CategoryId.ideals,
  CategoryId.coreSubobjectsModules]

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
  CategoryFamilyId.freeCover,
  CategoryFamilyId.basedModule,
  CategoryFamilyId.coord,
  CategoryFamilyId.freeCoverIndexed,
  CategoryFamilyId.basedModuleIndexed,
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
  ClassifierId.bilFinite,
  ClassifierId.bilFree,
  ClassifierId.bilEven,
  ClassifierId.bilUnimodular,
  ClassifierId.bilValues,
  ClassifierId.modulesFiniteRank,
  ClassifierId.modulesFree,
  ClassifierId.setsBinaryOperation,
  ClassifierId.setsFinite,
  ClassifierId.setsGraded,
  ClassifierId.bilinModuleLattice]

/-- Stable functor rows owned by the standard catalogue. -/
def expectedFunctorIds : Array FunctorId := #[
  FunctorId.bilWFormBaseChange,
  FunctorId.bilinModuleBaseChange,
  FunctorId.bilinModuleChangeValue,
  FunctorId.bilinModuleForget,
  FunctorId.latticeFormForget,
  FunctorId.setsCardinality,
  FunctorId.ringsMultiplicative,
  FunctorId.ringsAdditive,
  FunctorId.additiveGroupsToGroups,
  FunctorId.groupsMonoid,
  FunctorId.monoidsSemigroup,
  FunctorId.subobjectsGroupsDomain,
  FunctorId.subobjectsGroupsInclusion,
  FunctorId.arrowsModulesKernel,
  FunctorId.modulesRank,
  FunctorId.finiteProjectiveForget,
  FunctorId.basedModuleToFreeCover,
  FunctorId.fromBasedModule,
  FunctorId.coordForget,
  FunctorId.modulesFibreInclusion,
  FunctorId.modulesReindex,
  FunctorId.modulesUnderlying,
  FunctorId.modulesProjection,
  FunctorId.modulesExtRing,
  FunctorId.bilinFormsValues,
  FunctorId.modulesExtRegularSection,
  FunctorId.integralFormsToBil,
  FunctorId.latticesToBil,
  FunctorId.finiteProjectiveLatticesToBil,
  FunctorId.integralLatticesToBil,
  FunctorId.quadFormsRing,
  FunctorId.freeCoverForget,
  FunctorId.basedModuleForget,
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
  FunctorId.modulePointsProjection,
  FunctorId.setsWholeSubset,
  FunctorId.subobjectsSetsDomain,
  FunctorId.subsetsPointPredicates,
  FunctorId.subsetsSubsetPredicates,
  FunctorId.subsetsContains,
  FunctorId.subsetsEquals,
  FunctorId.modulesAnnihilator,
  FunctorId.arrowsModulesImage,
  FunctorId.subobjectsModulesForget,
  FunctorId.subobjectsModulesDomain,
  FunctorId.subobjectsModulesRank,
  FunctorId.setsList,
  FunctorId.setsPairDiagonal,
  FunctorId.setsPairLimit]

/-- Stable fibration rows owned by the standard catalogue. -/
def expectedFibrationIds : Array FibrationId := #[
  FibrationId.modules,
  FibrationId.modulesExt,
  FibrationId.bilinForms,
  FibrationId.quadForms]

/-- Stable category-constructor rows owned by the standard catalogue. -/
def expectedConstructorIds : Array ConstructorId := #[
  ConstructorId.arrow, ConstructorId.core, ConstructorId.slice, ConstructorId.coslice,
  ConstructorId.elements, ConstructorId.subobjects, ConstructorId.functorCategory]

/-- Stable method-presentation rows owned by the standard catalogue (#53 §7). -/
def expectedMethodIds : Array MethodId :=
  #[⟨"meth.cardinality"⟩, ⟨"meth.inclusion"⟩, ⟨"meth.kernel"⟩, ⟨"meth.rank"⟩,
    ⟨"meth.contains"⟩, ⟨"meth.set_eq"⟩,
    ⟨"meth.annihilator"⟩,
    ⟨"meth.dim"⟩,
    ⟨"meth.arrow_ker"⟩,
    ⟨"meth.arrow_im"⟩,
    ⟨"meth.subobject_dim"⟩]

/-- Stable cell rows owned by the standard catalogue (CC-CALC). -/
def expectedCellIds : Array NaturalTransformationId := #[
  NaturalTransformationId.listUnit, NaturalTransformationId.listJoin,
  NaturalTransformationId.listReverse, ⟨"cmp.rings.carrier"⟩]

/-- Stable limit presentations (CC-UNIV). -/
def expectedLimitIds : Array LimitId := #[⟨"lim.sets.pullback"⟩, ⟨"lim.groups.kernel"⟩,
  ⟨"colim.sets.coproduct"⟩, ⟨"colim.bil_w_form.cokernel"⟩]

/-- Stable adjunction rows (CC-CALC). -/
def expectedAdjunctionIds : Array AdjunctionId := #[AdjunctionId.setsPairDiagonalLimit]

/-- Stable lift rows owned by the standard catalogue (CC-LIFT). -/
def expectedLiftIds : Array LiftId :=
  #[⟨"lift.bilin_module.restrict"⟩, LiftId.finiteSetsPullbacks]

/-- Stable property-presentation rows owned by the standard catalogue (CC-PROP). -/
def expectedPropertyIds : Array PropertyId :=
  #[⟨"prop.is_commutative"⟩, ⟨"prop.is_abelian"⟩, ⟨"prop.is_finite"⟩, ⟨"prop.is_lattice"⟩]

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

/-- Validate every row kind emitted by the standard registry manifest. -/
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
  validateStableIdSet "methods" (manifest.methods.map (·.id))
    (rawIds expectedMethodIds (·.raw))
  validateStableIdSet "properties" (manifest.properties.map (·.id))
    (rawIds expectedPropertyIds (·.raw))
  validateStableIdSet "lifts" (manifest.lifts.map (·.id))
    (rawIds expectedLiftIds (·.raw))
  validateStableIdSet "cells" (manifest.cells.map (·.id)) (rawIds expectedCellIds (·.raw))
  validateStableIdSet "limits" (manifest.limits.map (·.id)) (rawIds expectedLimitIds (·.raw))
  validateStableIdSet "adjunctions" (manifest.adjunctions.map (·.id))
    (rawIds expectedAdjunctionIds (·.raw))
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
