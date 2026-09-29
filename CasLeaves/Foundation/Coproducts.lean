/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaf
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import CasLeaves.Foundation.Cardinality
public meta import CasCatalogue.Leaf
public meta import LeanCategories.Catalogue.Semantics.Limits.Registration

@[expose] public section

/-!
# Coproducts of presented finite sets

The apex of the registered coproduct `Fin m ⊕ Fin n`, presented as `Fin (m + n)`
(`finSumFinEquiv`); the coprojections and descents are the core's (`realizedColimitCocone`).
-/

open CategoryTheory Limits
open CasCatalogue.Foundation.Actions

namespace CasCatalogue.Foundation.Coproducts

/-- The apex of the coproduct of presented finite sets, with its identification. -/
def finiteCoproduct (m n : ℕ) :
    Σ a : SetHandles, setDenotation.obj a ≅
      (Limits.Registration.setsCoproduct (Fin m) (Fin n)).cocone.pt :=
  ⟨.finite (m + n), by exact finSumFinEquiv.symm.toIso⟩

end CasCatalogue.Foundation.Coproducts

namespace CasCatalogue

register_leaf
  { backend := "lean"
    contributions := [
  .limitRealization
  { id := ⟨"colimr.sets.coproduct.finite"⟩, limit := ⟨"colim.sets.coproduct"⟩
    realizer := ⟨"rz.sets.presented"⟩
    realization := `CasCatalogue.Foundation.Coproducts.finiteCoproduct }] }

end CasCatalogue
