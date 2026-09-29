module

public import CasCatalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId
def magmas : CategoryId := ⟨"cat.magmas"⟩
def semigroups : CategoryId := ⟨"cat.semigroups"⟩
def monoids : CategoryId := ⟨"cat.monoids"⟩
def groups : CategoryId := ⟨"cat.groups"⟩
def additiveMagmas : CategoryId := ⟨"cat.additive_magmas"⟩
def additiveSemigroups : CategoryId := ⟨"cat.additive_semigroups"⟩
def additiveMonoids : CategoryId := ⟨"cat.additive_monoids"⟩
def additiveGroups : CategoryId := ⟨"cat.additive_groups"⟩
def magmasWithTwoOperations : CategoryId := ⟨"cat.magmaswithtwooperations"⟩
def rings : CategoryId := ⟨"cat.rings"⟩
def commutativeRings : CategoryId := ⟨"cat.commutative_rings"⟩
def divisionRings : CategoryId := ⟨"cat.division_rings"⟩
end CategoryId

namespace ClassifierId
def magmasAssociative : ClassifierId := ⟨"clf.magmas.associative"⟩
def magmasCommutative : ClassifierId := ⟨"clf.magmas.commutative"⟩
def magmasUnital : ClassifierId := ⟨"clf.magmas.unital"⟩
def magmasInverse : ClassifierId := ⟨"clf.magmas.inverse"⟩
def magmasAdditive : ClassifierId := ⟨"clf.magmas.additive"⟩
def magmasMultiplicative : ClassifierId := ⟨"clf.magmas.multiplicative"⟩
def m2oDistributive : ClassifierId := ⟨"clf.magmaswithtwooperations.distributive"⟩
def ringsDivision : ClassifierId := ⟨"clf.division"⟩
end ClassifierId

namespace PortId
def additive : PortId := ⟨"port.additive"⟩
def multiplicative : PortId := ⟨"port.multiplicative"⟩
def underlyingSet : PortId := ⟨"port.underlying_set"⟩
end PortId

end CasCatalogue
