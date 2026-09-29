module

public import CasCatalogue.Semantics
public import CasLeaves
public meta import CasCatalogue.Semantics
public meta import CasLeaves

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
  ClassifierId.setsGraded]

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
  FunctorId.setsList]

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

/-- Stable functor-action rows owned by the standard catalogue (CC-ACTION). -/
def expectedActionIds : Array ActionId := #[
  ⟨"act.lattice.forget_form.int_gram"⟩,
  ⟨"act.bilin_module.forget.int_gram"⟩,
  ⟨"act.modules.fibre_inclusion.int_free"⟩,
  ⟨"act.modules.underlying.int_free"⟩,
  ⟨"act.sets.cardinality.presented"⟩,
  ⟨"act.groups.monoid.table"⟩,
  ⟨"act.monoids.semigroup.table"⟩,
  ⟨"act.semigroups.magma.table"⟩,
  ⟨"act.magmas.set.table"⟩,
  ⟨"act.rings.multiplicative_monoid.table"⟩,
  ⟨"act.rings.additive_group.table"⟩,
  ⟨"act.additive_groups.to_groups.table"⟩,
  ⟨"act.subobjects_groups.domain.table"⟩,
  ⟨"act.subobjects_groups.inclusion.table"⟩,
  ⟨"act.modules.rank.int_free"⟩,
  ⟨"act.modules.fibre_inclusion.cyclic_int"⟩,
  ⟨"act.modules.underlying.cyclic_int"⟩,
  ⟨"act.modules.fibre_inclusion.zmod_free"⟩,
  ⟨"act.modules.underlying.zmod_free"⟩,
  ⟨"act.sets.whole_subset.presented"⟩,
  ⟨"act.subobjects_sets.domain.presented"⟩, ⟨"act.sets.list.presented"⟩]

/-- Stable method-presentation rows owned by the standard catalogue (#53 §7). -/
def expectedMethodIds : Array MethodId :=
  #[⟨"meth.cardinality"⟩, ⟨"meth.inclusion"⟩, ⟨"meth.kernel"⟩, ⟨"meth.rank"⟩,
    ⟨"meth.contains"⟩, ⟨"meth.set_eq"⟩,
    ⟨"meth.annihilator"⟩,
    ⟨"meth.dim"⟩,
    ⟨"meth.arrow_ker"⟩,
    ⟨"meth.arrow_im"⟩,
    ⟨"meth.subobject_dim"⟩]

/-- Stable realizer rows owned by the standard catalogue (CC-SEP). -/
def expectedRealizerIds : Array RealizerId := #[
  ⟨"rz.sets.presented"⟩, ⟨"rz.core_sets.presented"⟩, ⟨"rz.cardinals.handles"⟩,
  ⟨"rz.modules.int_free"⟩, ⟨"rz.modules_total.int_free"⟩, ⟨"rz.bilin_module.int_gram"⟩,
  ⟨"rz.lattice.int_gram"⟩, ⟨"rz.core_modules.int_free"⟩, ⟨"rz.magmas.table"⟩,
  ⟨"rz.semigroups.table"⟩, ⟨"rz.monoids.table"⟩, ⟨"rz.groups.table"⟩,
  ⟨"rz.additive_groups.table"⟩,
  ⟨"rz.subobjects_groups.table"⟩, ⟨"rz.arrows_groups.table"⟩, ⟨"rz.rings.table"⟩,
  ⟨"rz.modules.cyclic_int"⟩, ⟨"rz.modules_total.cyclic_int"⟩, ⟨"rz.modules.zmod_free"⟩,
  ⟨"rz.modules_total.zmod_free"⟩, ⟨"rz.subobjects_sets.presented"⟩]

/-- Stable fused-implementation rows owned by the standard catalogue (CC-ROUTE). -/
def expectedImplementationIds : Array ImplementationId := #[
  ⟨"impl.bilin_module.cardinality.fused"⟩, ⟨"impl.bilin_module.cardinality.certified"⟩]

/-- Stable cell rows owned by the standard catalogue (CC-CALC). -/
def expectedCellIds : Array NaturalTransformationId := #[
  NaturalTransformationId.listUnit, NaturalTransformationId.listJoin,
  NaturalTransformationId.listReverse]

/-- Stable registered isomorphisms owned by the standard catalogue (CC-CARRIER). -/
def expectedHandleIsoIds : Array HandleIsoId := #[⟨"iso.f9.x_to_y_plus_2"⟩]

/-- Stable lift rows owned by the standard catalogue (CC-LIFT). -/
def expectedLiftIds : Array LiftId := #[⟨"lift.bilin_module.restrict"⟩]

/-- Stable comparison rows owned by the standard catalogue (CC-COHERE). -/
def expectedComparisonIds : Array ComparisonId := #[⟨"cmp.rings.carrier"⟩]

/-- Stable property-presentation rows owned by the standard catalogue (CC-PROP). -/
def expectedPropertyIds : Array PropertyId := #[⟨"prop.is_commutative"⟩, ⟨"prop.is_abelian"⟩]

/-- Stable decision-procedure rows owned by the standard catalogue (CC-DECIDE). -/
def expectedDeciderIds : Array DeciderId := #[⟨"dec.magmas.commutative.table"⟩]

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
  validateStableIdSet "actions" (manifest.actions.map (·.id))
    (rawIds expectedActionIds (·.raw))
  validateStableIdSet "methods" (manifest.methods.map (·.id))
    (rawIds expectedMethodIds (·.raw))
  validateStableIdSet "comparisons" (manifest.comparisons.map (·.id))
    (rawIds expectedComparisonIds (·.raw))
  validateStableIdSet "properties" (manifest.properties.map (·.id))
    (rawIds expectedPropertyIds (·.raw))
  validateStableIdSet "deciders" (manifest.deciders.map (·.id))
    (rawIds expectedDeciderIds (·.raw))
  validateStableIdSet "lifts" (manifest.lifts.map (·.id))
    (rawIds expectedLiftIds (·.raw))
  validateStableIdSet "realizers" (manifest.realizers.map (·.id))
    (rawIds expectedRealizerIds (·.raw))
  validateStableIdSet "implementations" (manifest.implementations.map (·.id))
    (rawIds expectedImplementationIds (·.raw))
  validateStableIdSet "isomorphisms" (manifest.handleIsos.map (·.id))
    (rawIds expectedHandleIsoIds (·.raw))
  validateStableIdSet "cells" (manifest.cells.map (·.id)) (rawIds expectedCellIds (·.raw))
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
