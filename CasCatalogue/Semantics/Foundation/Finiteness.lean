/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.Limits.Lifts
public import CasCatalogue.Refine
public meta import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Finiteness of sets (CC-PROP, CC-DECIDE)

`is_finite` is the classifier `clf.sets.finite`, whose total is `FintypeCat`, Mathlib's full
subcategory of `Type` on `Finite`. Its fibre over a set `X` is inhabited exactly when `X` is finite
(`finiteHolds_iff`), so a proved decision re-types a set into finite sets as the same set
(`CasCatalogue.refine`).
-/

open CategoryTheory

namespace CasCatalogue.Foundation.Finiteness

universe u

/-- `clf.sets.finite` is the classifier of the property `Finite` (`FintypeCat` is Mathlib's full
subcategory of finite types), so its fibre over `X` is inhabited iff `X` is finite. -/
theorem finiteHolds_iff (X : LeanCategories.Foundation.Mathlib.Sets.{u}) :
    Classifier.Holds LeanCategories.Foundation.Mathlib.finite X ↔ Finite X :=
  Classifier.holds_ofProperty (C := LeanCategories.Foundation.Mathlib.Sets.{u}) (fun X => Finite X) X

end CasCatalogue.Foundation.Finiteness

namespace CasCatalogue

normalized_registry .property
  { id := ⟨"prop.is_finite"⟩, name := "is_finite", classifier := ClassifierId.setsFinite }

end CasCatalogue
