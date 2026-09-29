module

public import CasCatalogue.Syntax
public import CasCatalogue.Semantics.Lattices.Valued.Catalogue
public import CasCatalogue.Semantics.Modules.Expressions
public import CasCatalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

namespace CasCatalogue.Lattices.Valued.Catalogue


open CasCatalogue

def Lattice : CategoryExpr :=
  .familyApp CategoryFamilyId.lattice #[.variable ParameterId.r, .variable ParameterId.w]
def FiniteProjectiveLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.finiteProjectiveLattice
    #[.variable ParameterId.r, .variable ParameterId.w]
def FiniteFreeLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.finiteFreeLattice #[.variable ParameterId.r, .variable ParameterId.w]
def EvenLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.evenLattice #[.variable ParameterId.r]
def DefiniteLattice : CategoryExpr := .atom CategoryId.definiteLattice
def IndefiniteLattice : CategoryExpr := .atom CategoryId.indefiniteLattice
def IntegralLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.integralLattice #[.variable ParameterId.r]
def CoordLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.coordLattice
    #[.variable ParameterId.r, .variable ParameterId.n]
def FractionFieldPerfectFiniteProjectiveLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.fractionFieldPerfectFiniteProjectiveLattice
    #[.variable ParameterId.r, .variable ParameterId.domain]
def UnimodularLattice : CategoryExpr :=
  .familyApp CategoryFamilyId.unimodularLattice
    #[.variable ParameterId.r, .variable ParameterId.domain]

/-- A lattice is a formed module with a property: the full subcategory inclusion. -/
def LatticeFormForget : FunctorExpr Lattice CasCatalogue.Modules.Bilinear.Valued.Catalogue.BilinModule :=
  .atomic FunctorId.latticeFormForget

def LatticeChangeValue : FunctorExpr Lattice
    (.familyApp CategoryFamilyId.lattice
      #[.variable ParameterId.r, .variable ParameterId.wPrime]) :=
  .atomic FunctorId.latticeChangeValue

def LatticeBaseChange : FunctorExpr Lattice
    (.familyApp CategoryFamilyId.lattice
      #[.variable ParameterId.s,
        .apply3 ParameterOperationId.tensorProduct
          (.variable ParameterId.r) (.variable ParameterId.s) (.variable ParameterId.w)]) :=
  .atomic FunctorId.latticeBaseChange

def FiniteProjectiveForget : FunctorExpr FiniteProjectiveLattice Modules.Modules :=
  .atomic FunctorId.finiteProjectiveForget

def IntegralLatticeForget : FunctorExpr IntegralLattice Modules.Modules :=
  .atomic FunctorId.integralLatticeForget

def CoordLatticeToCoord : FunctorExpr CoordLattice Modules.CoordExpr :=
  .atomic FunctorId.coordLatticeToCoord

def CoordLatticeToIntegral : FunctorExpr CoordLattice IntegralLattice :=
  .atomic FunctorId.coordLatticeToIntegral

def FractionFieldPerfectFiniteProjectiveForget :
    FunctorExpr FractionFieldPerfectFiniteProjectiveLattice IntegralLattice :=
  .atomic FunctorId.fractionFieldPerfectFiniteProjectiveForget

end CasCatalogue.Lattices.Valued.Catalogue
