module

public import CasCatalogue.Syntax
public import CasCatalogue.Leaves.Modules.Catalogue
public import CasCatalogue.Leaves.Foundation.Expressions

@[expose] public section

namespace CasCatalogue.Modules


def Modules : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.variable ParameterId.r]

/-- Modules over the ring `S`: the fibre over `S`. -/
def ModulesAtS : CategoryExpr :=
  .familyApp CategoryFamilyId.modules #[.variable ParameterId.s]

/-- The total category `∫ᶜ Mod` of the module fibration (CC-FIB). -/
def ModulesTotal : CategoryExpr := .familyTotal CategoryFamilyId.modules

/-- The fibre inclusion `ι_R`. -/
def ModulesFibreInclusionExpr : FunctorExpr Modules ModulesTotal :=
  .familyFibreInclusion CategoryFamilyId.modules #[.variable ParameterId.r]

/-- Restriction of scalars along `φ : R ⟶ S`, as reindexing of the module fibration. -/
def ModulesReindexExpr : FunctorExpr ModulesAtS Modules :=
  .familyReindex CategoryFamilyId.modules ParameterMorphismId.phi
    #[.variable ParameterId.r] #[.variable ParameterId.s]

/-- The underlying-set functor on the total category of modules. -/
def ModulesUnderlyingExpr : FunctorExpr ModulesTotal Foundation.Sets :=
  .atomic FunctorId.modulesUnderlying

/-! The property categories of `R`-modules are the totals of their classifiers (CC-PROP). -/

def FreeModules : CategoryExpr := .classifierTotal ClassifierId.modulesFree

def FinitelyGeneratedModules : CategoryExpr :=
  .classifierTotal ClassifierId.modulesFinitelyGenerated

def FiniteRankModules : CategoryExpr :=
  .classifierTotal ClassifierId.modulesFiniteRank

def FreeCoverExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.freeCover
    #[.variable ParameterId.r, .variable ParameterId.n]

def BasedModuleExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.basedModule
    #[.variable ParameterId.r, .variable ParameterId.n]

def CoordExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.coord
    #[.variable ParameterId.r, .variable ParameterId.n]

def FreeCoverIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.freeCoverIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def BasedModuleIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.basedModuleIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def CoordIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.coordIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def BasedModuleToFreeCoverExpr : FunctorExpr BasedModuleExpr FreeCoverExpr :=
  .atomic FunctorId.basedModuleToFreeCover

def FromBasedModuleExpr : FunctorExpr BasedModuleExpr CoordExpr :=
  .atomic FunctorId.fromBasedModule

def CoordForgetExpr : FunctorExpr CoordExpr Modules.Modules :=
  .atomic FunctorId.coordForget

def FreeCoverForgetExpr : FunctorExpr FreeCoverIndexedExpr Modules.Modules :=
  .atomic FunctorId.freeCoverForget

def BasedModuleForgetExpr : FunctorExpr BasedModuleIndexedExpr Modules.Modules :=
  .atomic FunctorId.basedModuleForget

end CasCatalogue.Modules
