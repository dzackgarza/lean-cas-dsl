module

public import CasCatalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId
def modulesR : CategoryId := ⟨"cat.modules_r"⟩
/-- The total category of the restriction-of-scalars module fibration. -/
def modulesTotal : CategoryId := ⟨"cat.modules_total"⟩
def finitelyGeneratedModules : CategoryId := ⟨"cat.finitelygeneratedmodules"⟩
def finiteRankModules : CategoryId := ⟨"cat.finiterankmodules"⟩
def freeModules : CategoryId := ⟨"cat.freemodules"⟩
def freeCover : CategoryId := ⟨"cat.free_cover"⟩
def basedModule : CategoryId := ⟨"cat.based_module"⟩
def coord : CategoryId := ⟨"cat.coord"⟩
def freeCoverIndexed : CategoryId := ⟨"cat.free_cover_indexed"⟩
def basedModuleIndexed : CategoryId := ⟨"cat.based_module_indexed"⟩
def coordIndexed : CategoryId := ⟨"cat.coord_indexed"⟩
end CategoryId

namespace ClassifierId
def modulesFree : ClassifierId := ⟨"clf.modules_free"⟩
def modulesFinitelyGenerated : ClassifierId := ⟨"clf.modules_finitelygenerated"⟩
def modulesFiniteRank : ClassifierId := ⟨"clf.modules_finiterank"⟩
end ClassifierId

namespace CategoryFamilyId
def modules : CategoryFamilyId := ⟨"fam.modules"⟩
def freeCover : CategoryFamilyId := ⟨"fam.free_cover"⟩
def basedModule : CategoryFamilyId := ⟨"fam.based_module"⟩
def coord : CategoryFamilyId := ⟨"fam.coord"⟩
def freeCoverIndexed : CategoryFamilyId := ⟨"fam.free_cover_indexed"⟩
def basedModuleIndexed : CategoryFamilyId := ⟨"fam.based_module_indexed"⟩
def coordIndexed : CategoryFamilyId := ⟨"fam.coord_indexed"⟩

end CategoryFamilyId

namespace FunctorId
def basedModuleToFreeCover : FunctorId := ⟨"fun.based_module.to_free_cover"⟩
def fromBasedModule : FunctorId := ⟨"fun.coord.from_based_module"⟩
def coordForget : FunctorId := ⟨"fun.coord.forget"⟩
def freeCoverForget : FunctorId := ⟨"fun.free_cover.forget"⟩
def basedModuleForget : FunctorId := ⟨"fun.based_module.forget"⟩
/-- The fibre inclusion `ι_R : R-Mod ⥤ ∫ᶜ Mod`. -/
def modulesFibreInclusion : FunctorId := ⟨"fun.modules.fibre_inclusion"⟩
/-- Restriction of scalars `φ^* : S-Mod ⥤ R-Mod`, the reindexing of the module fibration. -/
def modulesReindex : FunctorId := ⟨"fun.modules.reindex"⟩
/-- The underlying-set functor `U : ∫ᶜ Mod ⥤ Sets` on the total category. -/
def modulesUnderlying : FunctorId := ⟨"fun.modules.underlying"⟩
end FunctorId

end CasCatalogue
