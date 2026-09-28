/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Syntax
public import CasCatalogue.Leaves.Foundation.Expressions
public import CasCatalogue.Leaves.Modules.Expressions

@[expose] public section

/-!
# Stable identities and expressions of the typed category constructors (#54 §1)
-/

namespace CasCatalogue


namespace ConstructorId
def arrow : ConstructorId := ⟨"ctor.arrow"⟩
def core : ConstructorId := ⟨"ctor.core"⟩
def slice : ConstructorId := ⟨"ctor.slice"⟩
def coslice : ConstructorId := ⟨"ctor.coslice"⟩
def elements : ConstructorId := ⟨"ctor.elements"⟩
def subobjects : ConstructorId := ⟨"ctor.subobjects"⟩
def functorCategory : ConstructorId := ⟨"ctor.functor_category"⟩
end ConstructorId

namespace ParameterId
/-- A symbolic object argument of a constructor. -/
def x : ParameterId := ⟨"X"⟩
end ParameterId

namespace CategoryId
def arrowsSets : CategoryId := ⟨"cat.arrows_sets"⟩
def coreSets : CategoryId := ⟨"cat.core_sets"⟩
def sliceSets : CategoryId := ⟨"cat.slice_sets"⟩
def cosliceSets : CategoryId := ⟨"cat.coslice_sets"⟩
def subobjectsSets : CategoryId := ⟨"cat.subobjects_sets"⟩
def modulePoints : CategoryId := ⟨"cat.module_points"⟩
def endofunctorsSets : CategoryId := ⟨"cat.endofunctors_sets"⟩
end CategoryId

namespace FunctorId
/-- The forgetful functor `Over X ⥤ Sets`. -/
def sliceSetsForget : FunctorId := ⟨"fun.slice_sets.forget"⟩
/-- The projection `Elements(U) ⥤ ∫ᶜ Mod` of the points of modules. -/
def modulePointsProjection : FunctorId := ⟨"fun.module_points.projection"⟩
end FunctorId

namespace Constructed

def ArrowsSets : CategoryExpr := .construct ConstructorId.arrow #[.category Foundation.Sets]
def CoreSets : CategoryExpr := .construct ConstructorId.core #[.category Foundation.Sets]
def SliceSets : CategoryExpr :=
  .construct ConstructorId.slice #[.category Foundation.Sets, .object ParameterId.x]
def CosliceSets : CategoryExpr :=
  .construct ConstructorId.coslice #[.category Foundation.Sets, .object ParameterId.x]
def SubobjectsSets : CategoryExpr :=
  .construct ConstructorId.subobjects #[.category Foundation.Sets]
/-- The points of modules: `Elements(U)` for the underlying-set functor `U` of `∫ᶜ Mod`
(CC-FIB; the typed source for element methods, spec §9 nuance 10). -/
def ModulePoints : CategoryExpr :=
  .construct ConstructorId.elements
    #[.category Modules.ModulesTotal, .functor FunctorId.modulesUnderlying]
def EndofunctorsSets : CategoryExpr :=
  .construct ConstructorId.functorCategory #[.category Foundation.Sets, .category Foundation.Sets]

def SliceSetsForgetExpr : FunctorExpr SliceSets Foundation.Sets :=
  .atomic FunctorId.sliceSetsForget
def ModulePointsProjectionExpr : FunctorExpr ModulePoints Modules.ModulesTotal :=
  .atomic FunctorId.modulePointsProjection

/-- CC-CALC: constructed categories compose with registered functors under the typed `comp`:
points of modules, to modules, to their underlying sets. -/
def ModulePointsToSetsExpr : FunctorExpr ModulePoints Foundation.Sets :=
  .comp ModulePointsProjectionExpr Modules.ModulesUnderlyingExpr

end Constructed

end CasCatalogue
