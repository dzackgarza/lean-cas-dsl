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
def genFrame : CategoryId := ⟨"cat.gen_frame"⟩
def basisFrame : CategoryId := ⟨"cat.basis_frame"⟩
def coord : CategoryId := ⟨"cat.coord"⟩
def genFrameIndexed : CategoryId := ⟨"cat.gen_frame_indexed"⟩
def basisFrameIndexed : CategoryId := ⟨"cat.basis_frame_indexed"⟩
def coordIndexed : CategoryId := ⟨"cat.coord_indexed"⟩
end CategoryId

namespace ClassifierId
def modulesFree : ClassifierId := ⟨"clf.modules_free"⟩
def modulesFinitelyGenerated : ClassifierId := ⟨"clf.modules_finitelygenerated"⟩
def modulesFiniteRank : ClassifierId := ⟨"clf.modules_finiterank"⟩
end ClassifierId

namespace CategoryFamilyId
def modules : CategoryFamilyId := ⟨"fam.modules"⟩
def genFrame : CategoryFamilyId := ⟨"fam.gen_frame"⟩
def basisFrame : CategoryFamilyId := ⟨"fam.basis_frame"⟩
def coord : CategoryFamilyId := ⟨"fam.coord"⟩
def genFrameIndexed : CategoryFamilyId := ⟨"fam.gen_frame_indexed"⟩
def basisFrameIndexed : CategoryFamilyId := ⟨"fam.basis_frame_indexed"⟩
def coordIndexed : CategoryFamilyId := ⟨"fam.coord_indexed"⟩

end CategoryFamilyId

namespace FunctorId
def basisFrameToGenFrame : FunctorId := ⟨"fun.basis_frame.to_gen_frame"⟩
def fromBasisFrame : FunctorId := ⟨"fun.coord.from_basis_frame"⟩
def coordForget : FunctorId := ⟨"fun.coord.forget"⟩
def genFrameForget : FunctorId := ⟨"fun.gen_frame.forget"⟩
def basisFrameForget : FunctorId := ⟨"fun.basis_frame.forget"⟩
/-- The fibre inclusion `ι_R : R-Mod ⥤ ∫ᶜ Mod`. -/
def modulesFibreInclusion : FunctorId := ⟨"fun.modules.fibre_inclusion"⟩
/-- Restriction of scalars `φ^* : S-Mod ⥤ R-Mod`, the reindexing of the module fibration. -/
def modulesReindex : FunctorId := ⟨"fun.modules.reindex"⟩
/-- The underlying-set functor `U : ∫ᶜ Mod ⥤ Sets` on the total category. -/
def modulesUnderlying : FunctorId := ⟨"fun.modules.underlying"⟩
end FunctorId

end CasCatalogue
