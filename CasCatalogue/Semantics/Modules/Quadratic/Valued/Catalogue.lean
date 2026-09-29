module

public import CasCatalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId

def quadModule : CategoryId := ⟨"cat.quad_module"⟩
def quadWForm : CategoryId := ⟨"cat.quad_wform"⟩

end CategoryId

namespace CategoryFamilyId

def quadModule : CategoryFamilyId := ⟨"fam.quad_module"⟩
def quadWForm : CategoryFamilyId := ⟨"fam.quad_wform"⟩

end CategoryFamilyId

namespace FunctorId

def quadModuleForget : FunctorId := ⟨"fun.quad_module.forget"⟩
def quadModuleChangeValue : FunctorId := ⟨"fun.quad_module.change_value"⟩
def quadWFormValue : FunctorId := ⟨"fun.quad_wform.value"⟩
def quadWFormCarrier : FunctorId := ⟨"fun.quad_wform.carrier"⟩

end FunctorId

end CasCatalogue
