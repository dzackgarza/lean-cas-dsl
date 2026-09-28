module

public import CasCatalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId

def lattice : CategoryId := ⟨"cat.lattice"⟩
def finiteProjectiveLattice : CategoryId := ⟨"cat.finite_projective_lattice"⟩
def finiteFreeLattice : CategoryId := ⟨"cat.finite_free_lattice"⟩
def evenLattice : CategoryId := ⟨"cat.even_lattice"⟩
def definiteLattice : CategoryId := ⟨"cat.definite_lattice"⟩
def indefiniteLattice : CategoryId := ⟨"cat.indefinite_lattice"⟩
def integralLattice : CategoryId := ⟨"cat.integral_lattice"⟩
def coordLattice : CategoryId := ⟨"cat.coord_lattice"⟩
def fractionFieldPerfectFiniteProjectiveLattice : CategoryId :=
  ⟨"cat.fraction_field_perfect_finite_projective_lattice"⟩
def unimodularLattice : CategoryId := ⟨"cat.unimodular_lattice"⟩

end CategoryId

namespace CategoryFamilyId

def lattice : CategoryFamilyId := ⟨"fam.lattice"⟩
def finiteProjectiveLattice : CategoryFamilyId := ⟨"fam.finite_projective_lattice"⟩
def finiteFreeLattice : CategoryFamilyId := ⟨"fam.finite_free_lattice"⟩
def evenLattice : CategoryFamilyId := ⟨"fam.even_lattice"⟩
def integralLattice : CategoryFamilyId := ⟨"fam.integral_lattice"⟩
def coordLattice : CategoryFamilyId := ⟨"fam.coord_lattice"⟩
def fractionFieldPerfectFiniteProjectiveLattice : CategoryFamilyId :=
  ⟨"fam.fraction_field_perfect_finite_projective_lattice"⟩
def unimodularLattice : CategoryFamilyId := ⟨"fam.unimodular_lattice"⟩

end CategoryFamilyId

namespace FunctorId

def latticeChangeValue : FunctorId := ⟨"fun.lattice.change_value"⟩
def latticeBaseChange : FunctorId := ⟨"fun.lattice.base_change"⟩
def finiteProjectiveForget : FunctorId := ⟨"fun.finite_projective_lattice.forget"⟩
def integralLatticeForget : FunctorId := ⟨"fun.integral_lattice.forget"⟩
def coordLatticeToCoord : FunctorId := ⟨"fun.coord_lattice.to_coord"⟩
def coordLatticeToIntegral : FunctorId := ⟨"fun.coord_lattice.to_integral"⟩
def fractionFieldPerfectFiniteProjectiveForget : FunctorId :=
  ⟨"fun.fraction_field_perfect_finite_projective_lattice.forget"⟩

end FunctorId

end CasCatalogue
