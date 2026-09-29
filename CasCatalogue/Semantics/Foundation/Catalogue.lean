module

public import CasCatalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId
def sets : CategoryId := ⟨"cat.sets"⟩
end CategoryId

namespace ClassifierId
def setsFinite : ClassifierId := ⟨"clf.sets.finite"⟩
def setsGraded : ClassifierId := ⟨"clf.sets.graded"⟩
def setsBinaryOperation : ClassifierId := ⟨"clf.sets.binary_operation"⟩
end ClassifierId

namespace FunctorId
def setsIdentity : FunctorId := ⟨"fun.sets.identity"⟩
end FunctorId

end CasCatalogue
