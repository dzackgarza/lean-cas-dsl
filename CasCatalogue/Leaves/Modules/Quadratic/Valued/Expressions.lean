module

public import CasCatalogue.Syntax
public import CasCatalogue.Leaves.Modules.Expressions
public import CasCatalogue.Leaves.Modules.Quadratic.Valued.Catalogue

@[expose] public section

namespace CasCatalogue.Modules.Quadratic.Valued.Catalogue


open CasCatalogue

def QuadModule : CategoryExpr :=
  .familyApp CategoryFamilyId.quadModule #[.variable ParameterId.r, .variable ParameterId.w]

def QuadWForm : CategoryExpr :=
  .familyApp CategoryFamilyId.quadWForm #[.variable ParameterId.r]

def QuadModuleForget : FunctorExpr QuadModule Modules.Modules :=
  .atomic FunctorId.quadModuleForget

def QuadModuleChangeValue : FunctorExpr QuadModule
    (.familyApp CategoryFamilyId.quadModule #[.variable ParameterId.r, .variable ParameterId.wPrime]) :=
  .atomic FunctorId.quadModuleChangeValue

def QuadWFormValue : FunctorExpr QuadWForm Modules.Modules :=
  .atomic FunctorId.quadWFormValue

def QuadWFormCarrier : FunctorExpr QuadWForm Modules.Modules :=
  .atomic FunctorId.quadWFormCarrier

end CasCatalogue.Modules.Quadratic.Valued.Catalogue
