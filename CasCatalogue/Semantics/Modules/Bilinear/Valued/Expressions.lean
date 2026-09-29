module

public import CasCatalogue.Syntax
public import CasCatalogue.Semantics.Modules.Bilinear.Valued.Catalogue
public import CasCatalogue.Semantics.Modules.Expressions

@[expose] public section

namespace CasCatalogue.Modules.Bilinear.Valued.Catalogue


open CasCatalogue

def BilinModule : CategoryExpr :=
  .familyApp CategoryFamilyId.bilinModule #[.variable ParameterId.r, .variable ParameterId.w]
def BilWForm : CategoryExpr :=
  .familyApp CategoryFamilyId.bilWForm #[.variable ParameterId.r]

def BilinModuleForget : FunctorExpr BilinModule Modules.Modules :=
  .atomic FunctorId.bilinModuleForget

def BilinModuleChangeValue : FunctorExpr BilinModule
    (.familyApp CategoryFamilyId.bilinModule
      #[.variable ParameterId.r, .variable ParameterId.wPrime]) :=
  .atomic FunctorId.bilinModuleChangeValue

def BilinModuleBaseChange : FunctorExpr BilinModule
    (.familyApp CategoryFamilyId.bilinModule
      #[.variable ParameterId.s,
        .apply3 ParameterOperationId.tensorProduct
          (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]) :=
  .atomic FunctorId.bilinModuleBaseChange

def BilWFormBaseChange : FunctorExpr BilWForm
    (.familyApp CategoryFamilyId.bilWForm #[.variable ParameterId.s]) :=
  .atomic FunctorId.bilWFormBaseChange

def BilWFormCarrier : FunctorExpr BilWForm Modules.Modules :=
  .atomic FunctorId.bilWFormCarrier

end CasCatalogue.Modules.Bilinear.Valued.Catalogue
