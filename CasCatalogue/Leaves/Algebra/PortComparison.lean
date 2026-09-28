/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Leaves.Algebra.Ports
public import LeanCategories.Algebra.Concrete.RingCarrierComparison
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Leaves.Algebra.Ports

@[expose] public section

/-!
# The ring diamond is coherent at sets (CC-COHERE, #53 §9)

The multiplicative and the additive route from rings to sets are identified by
`LeanCategories.Algebra.ringCarrierComparison`, the identity natural isomorphism between their
composites. The comparison covers the whole route to `Sets`: the two ports stay distinct at
monoids and magmas, where they carry different operations.
-/

open CasCatalogue.Algebra.Catalogue.Magmas CasCatalogue.Algebra.Catalogue.Rings

namespace CasCatalogue

normalized_registry .comparison
  { id := ⟨"cmp.rings.carrier"⟩, source := Rings, target := Foundation.Sets
    left := #[.functor FunctorId.ringsMultiplicative, .functor FunctorId.monoidsSemigroup,
      .classifierForget ClassifierId.magmasAssociative, .classifierForget ClassifierId.setsBinaryOperation]
    right := #[.functor FunctorId.ringsAdditive, .functor FunctorId.additiveGroupsToGroups,
      .functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
      .classifierForget ClassifierId.magmasAssociative, .classifierForget ClassifierId.setsBinaryOperation]
    evidence := `LeanCategories.Algebra.ringCarrierComparison }

end CasCatalogue
