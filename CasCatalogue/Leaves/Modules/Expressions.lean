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

def FreeModules : CategoryExpr := .atom CategoryId.freeModules

def FinitelyGeneratedModules : CategoryExpr :=
  .atom CategoryId.finitelyGeneratedModules

def FiniteRankModules : CategoryExpr :=
  .atom CategoryId.finiteRankModules

def GenFrameExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.genFrame
    #[.variable ParameterId.r, .variable ParameterId.n]

def BasisFrameExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.basisFrame
    #[.variable ParameterId.r, .variable ParameterId.n]

def CoordExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.coord
    #[.variable ParameterId.r, .variable ParameterId.n]

def GenFrameIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.genFrameIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def BasisFrameIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.basisFrameIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def CoordIndexedExpr : CategoryExpr :=
  .familyApp CategoryFamilyId.coordIndexed
    #[.variable ParameterId.r, .variable ParameterId.i]

def BasisFrameToGenFrameExpr : FunctorExpr BasisFrameExpr GenFrameExpr :=
  .atomic FunctorId.basisFrameToGenFrame

def FromBasisFrameExpr : FunctorExpr BasisFrameExpr CoordExpr :=
  .atomic FunctorId.fromBasisFrame

def CoordForgetExpr : FunctorExpr CoordExpr Modules.Modules :=
  .atomic FunctorId.coordForget

def GenFrameForgetExpr : FunctorExpr GenFrameIndexedExpr Modules.Modules :=
  .atomic FunctorId.genFrameForget

def BasisFrameForgetExpr : FunctorExpr BasisFrameIndexedExpr Modules.Modules :=
  .atomic FunctorId.basisFrameForget

end CasCatalogue.Modules
