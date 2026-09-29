/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Limits.Registration
public import Mathlib.CategoryTheory.Limits.FintypeCat
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Limits returned along creation lifts (CC-LIFT, CC-UNIV)

* `cat.finite_sets`: finite sets, the total category of the classifier `clf.sets.finite`
  (`FintypeCat`, the full subcategory of finite types), whose forgetful functor to `Sets` is a
  structural step;
* `lift.finite_sets.pullbacks`: the forgetful functor `FintypeCat ⥤ Sets` creates pullbacks
  (Mathlib `FintypeCat.inclusionCreatesFiniteLimits`: finite sets are closed under finite limits).

So a pullback of finite sets is the registered pullback of sets (`lim.sets.pullback`), returned to
finite sets along the lift; `resolveLimit` names the lift it uses.
-/

open CategoryTheory Limits

namespace CasCatalogue

namespace CategoryId
def finiteSets : CategoryId := ⟨"cat.finite_sets"⟩
end CategoryId

namespace LiftId
def finiteSetsPullbacks : LiftId := ⟨"lift.finite_sets.pullbacks"⟩
end LiftId

namespace Limits.Lifts

universe u

noncomputable def finiteSetsRealization :
    CategoryRealization (.classifierTotal ClassifierId.setsFinite)
      LeanCategories.Foundation.Mathlib.FiniteSets.{u} := {}

/-- The forgetful functor of finite sets creates pullbacks. -/
noncomputable def finiteSetsCreatePullbacks :
    CreatesLimitsOfShape WalkingCospan (forget FintypeCat.{u}) :=
  inferInstance

end Limits.Lifts

normalized_registry .category
  { id := CategoryId.finiteSets
    declaration := `LeanCategories.Foundation.Mathlib.FiniteSets
    expression := .classifierTotal ClassifierId.setsFinite
    realization := `CasCatalogue.Limits.Lifts.finiteSetsRealization }

normalized_registry .lift
  { id := LiftId.finiteSetsPullbacks, edge := .classifierForget ClassifierId.setsFinite
    evidence := `CasCatalogue.Limits.Lifts.finiteSetsCreatePullbacks
    kind := .createsLimits "pullback" }

end CasCatalogue
