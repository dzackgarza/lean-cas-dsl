module

public import CasCatalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId

def bilinModule : CategoryId := ⟨"cat.bilin_module"⟩
def bilWForm : CategoryId := ⟨"cat.bil_wform"⟩

end CategoryId

namespace CategoryFamilyId

def bilinModule : CategoryFamilyId := ⟨"fam.bilin_module"⟩
def bilWForm : CategoryFamilyId := ⟨"fam.bil_wform"⟩

end CategoryFamilyId

namespace FunctorId

def bilinModuleForget : FunctorId := ⟨"fun.bilin_module.forget"⟩
def bilWFormBaseChange : FunctorId := ⟨"fun.bil_wform.base_change"⟩
def bilWFormCarrier : FunctorId := ⟨"fun.bil_wform.carrier"⟩
def bilinModuleChangeValue : FunctorId := ⟨"fun.bilin_module.change_value"⟩
def bilinModuleBaseChange : FunctorId := ⟨"fun.bilin_module.base_change"⟩

end FunctorId

end CasCatalogue
