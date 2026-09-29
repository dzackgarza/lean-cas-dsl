/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Semantics.ConstructorRegistration
public import LeanCategories.Foundation.SectionsAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public meta import CasCatalogue.Registry.Extension
public meta import CasCatalogue.Semantics.ConstructorCatalogue

@[expose] public section

/-!
# Pair diagrams of sets and `Δ ⊣ lim` (CC-CALC, CC-UNIV)

* `cat.walking_pair`: the discrete category on two objects (Mathlib `Discrete WalkingPair`);
* `cat.sets.pair_diagrams = Fun(WalkingPair, Sets)`, a constructed category (functor category);
* `fun.sets.pair_diagonal : Sets ⥤ Fun(WalkingPair, Sets)`, `Δ = Functor.const`;
* `fun.sets.pair_limit : Fun(WalkingPair, Sets) ⥤ Sets`, the limit functor presented by sections
  (Mathlib `Functor.sectionsFunctor`);
* `adj.sets.pair.diagonal_limit : Δ ⊣ lim`, `LeanCategories.Foundation.constSectionsAdj`.

A limit functor is a right adjoint of `Δ`; any two are uniquely isomorphic (Mathlib's `lim` and
`Types.limNatIsoSectionsFunctor`). Sections is registered because its transposes reduce, and every
limit of a pair diagram is then Mathlib's `isLimitConeOfAdj` of this adjunction.
-/

open CategoryTheory Limits LeanCategories

namespace CasCatalogue

namespace CategoryId
def walkingPair : CategoryId := ⟨"cat.walking_pair"⟩
def setsPairDiagrams : CategoryId := ⟨"cat.sets.pair_diagrams"⟩
end CategoryId

namespace FunctorId
def setsPairDiagonal : FunctorId := ⟨"fun.sets.pair_diagonal"⟩
def setsPairLimit : FunctorId := ⟨"fun.sets.pair_limit"⟩
end FunctorId

namespace AdjunctionId
def setsPairDiagonalLimit : AdjunctionId := ⟨"adj.sets.pair.diagonal_limit"⟩
end AdjunctionId

namespace Foundation.PairDiagrams

universe u

def WalkingPairExpr : CategoryExpr := .atom CategoryId.walkingPair
def PairDiagramsExpr : CategoryExpr :=
  .construct ConstructorId.functorCategory #[.category WalkingPairExpr, .category Foundation.Sets]
def DiagonalExpr : FunctorExpr Foundation.Sets PairDiagramsExpr := .atomic FunctorId.setsPairDiagonal
def LimitExpr : FunctorExpr PairDiagramsExpr Foundation.Sets := .atomic FunctorId.setsPairLimit

/-- The index category of pairs. -/
def walkingPairCategory : ObjCat.{0, 0} := Cat.of (Discrete WalkingPair)
def walkingPairRealization : CategoryRealization WalkingPairExpr walkingPairCategory := {}

/-- `Fun(WalkingPair, Sets)`. -/
def pairDiagramsCategory :=
  Constructors.functorCategory.{0, 0, u + 1, u} walkingPairCategory LeanCategories.Foundation.Mathlib.Sets.{u}
def pairDiagramsRealization :
    CategoryRealization PairDiagramsExpr pairDiagramsCategory.{u} := {}

/-- `Δ : Sets ⥤ Fun(WalkingPair, Sets)`. -/
def diagonalDeclaration :
    LeanCategories.Foundation.Mathlib.Sets.{u} ⥤ pairDiagramsCategory.{u} :=
  Functor.const (Discrete WalkingPair)

/-- `lim : Fun(WalkingPair, Sets) ⥤ Sets`, presented by sections. -/
def limitDeclaration :
    pairDiagramsCategory.{u} ⥤ LeanCategories.Foundation.Mathlib.Sets.{u} :=
  Functor.sectionsFunctor (Discrete WalkingPair)

/-- `Δ ⊣ lim`. -/
def diagonalLimitAdjunction : diagonalDeclaration.{u} ⊣ limitDeclaration.{u} :=
  LeanCategories.Foundation.constSectionsAdj (Discrete WalkingPair)

noncomputable def diagonalRealization :
    FunctorRealization DiagonalExpr LeanCategories.Foundation.Mathlib.Sets.{u}
      pairDiagramsCategory.{u} diagonalDeclaration :=
  { sourceRealization := Foundation.CatalogueRegistration.setsRealization
    targetRealization := pairDiagramsRealization }

noncomputable def limitRealization :
    FunctorRealization LimitExpr pairDiagramsCategory.{u}
      LeanCategories.Foundation.Mathlib.Sets.{u} limitDeclaration :=
  { sourceRealization := pairDiagramsRealization
    targetRealization := Foundation.CatalogueRegistration.setsRealization }

end Foundation.PairDiagrams

open Foundation.PairDiagrams

normalized_registry .category
  { id := CategoryId.walkingPair
    declaration := `CasCatalogue.Foundation.PairDiagrams.walkingPairCategory
    expression := WalkingPairExpr
    realization := `CasCatalogue.Foundation.PairDiagrams.walkingPairRealization }

normalized_registry .category
  { id := CategoryId.setsPairDiagrams
    declaration := `CasCatalogue.Foundation.PairDiagrams.pairDiagramsCategory
    expression := PairDiagramsExpr
    realization := `CasCatalogue.Foundation.PairDiagrams.pairDiagramsRealization }

normalized_registry .functor
  { id := FunctorId.setsPairDiagonal
    source := Foundation.Sets
    target := PairDiagramsExpr
    declaration := `CasCatalogue.Foundation.PairDiagrams.diagonalDeclaration
    realization := `CasCatalogue.Foundation.PairDiagrams.diagonalRealization
    expression := DiagonalExpr }

normalized_registry .functor
  { id := FunctorId.setsPairLimit
    source := PairDiagramsExpr
    target := Foundation.Sets
    declaration := `CasCatalogue.Foundation.PairDiagrams.limitDeclaration
    realization := `CasCatalogue.Foundation.PairDiagrams.limitRealization
    expression := LimitExpr }

normalized_registry .adjunction
  { id := AdjunctionId.setsPairDiagonalLimit
    left := FunctorId.setsPairDiagonal
    right := FunctorId.setsPairLimit
    declaration := `CasCatalogue.Foundation.PairDiagrams.diagonalLimitAdjunction }

end CasCatalogue
