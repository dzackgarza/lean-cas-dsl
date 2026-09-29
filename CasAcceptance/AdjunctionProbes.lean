/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.ResolveSyntax
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public meta import CasAcceptance.Standard
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Acceptance for `cc-adjunctions` (CC-CALC, CC-UNIV)

The registered adjunction `adj.sets.pair.diagonal_limit : Δ ⊣ lim` on pair diagrams of sets,
realized on presented sets (`Δ` by constant diagrams, `lim` by product handles):

* a map of pair diagrams `Δ(Fin 4) ⟶ (Fin 2, Fin 3)`, i.e. a pair of maps `(g₁, g₂)`, transposes
  to the pairing `Fin 4 → Fin 2 × Fin 3`, `i ↦ (g₁ i, g₂ i)`, and the pairing transposes back to
  `(g₁, g₂)`;
* the limit of the pair diagram, computed through `Δ ⊣ lim` (Mathlib's `isLimitConeOfAdj`, realized
  by `realizedLimitConeOfAdj`), is the product handle with its projections, and the mediator of the
  competing cone `(g₁, g₂)` is the pairing;
* the adjunction row is validated as an adjunction between exactly its two functors.
-/

open CategoryTheory Limits Lean Meta Elab Term Command
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.PairDiagrams
open CasCatalogue.Foundation.PairDiagramActions

namespace CasCatalogue.AdjunctionProbes

/-- A morphism of presented finite sets. -/
def finHom {a b : ℕ} (h : Fin a → Fin b) : @Quiver.Hom SetHandles _ (.finite a) (.finite b) :=
  InducedCategory.homMk (TypeCat.ofHom h)

/-- The pair diagram `(Fin 2, Fin 3)`. -/
abbrev D : PairHandles := pair (SetHandle.finite 2 : SetHandles) (SetHandle.finite 3)

def g₁ : Fin 4 → Fin 2 := ![0, 1, 1, 0]
def g₂ : Fin 4 → Fin 3 := ![2, 0, 1, 2]

/-- The map of pair diagrams `Δ(Fin 4) ⟶ D` with components `g₁`, `g₂`. -/
def cone : diagonalAction.obj (SetHandle.finite 4) ⟶ D := mapPair (finHom g₁) (finHom g₂)

/-- The realized transpose along `Δ ⊣ lim`. -/
noncomputable def transpose : (diagonalAction.obj (SetHandle.finite 4) ⟶ D) ≃
    (@Quiver.Hom SetHandles _ (.finite 4) (limitAction.obj D)) :=
  realizedHomEquiv setDenotationFullyFaithful pairDenotationFullyFaithful
    diagonalLimitAdjunction diagonalAction limitAction _ _

/- The transpose of `(g₁, g₂)` is the pairing `i ↦ (g₁ i, g₂ i)`. -/
#guard (exec% (limitAction.obj D) : SetHandle) == .prod (.finite 2) (.finite 3)
#guard (List.finRange 4).map (fun i => (show Fin 2 × Fin 3 from (exec% (transpose cone)).hom i)) ==
  [(0, 2), (1, 0), (1, 1), (0, 2)]

/-- The pairing, written directly. -/
def pairing : @Quiver.Hom SetHandles _ (.finite 4) (.prod (.finite 2) (.finite 3)) :=
  InducedCategory.homMk (TypeCat.ofHom fun i => (g₁ i, g₂ i))

/- The pairing transposes back to `(g₁, g₂)`. -/
#guard (List.finRange 4).map (fun i =>
  (show Fin 2 from ((exec% (transpose.symm pairing)).app ⟨.left⟩).hom i)) == (List.finRange 4).map g₁
#guard (List.finRange 4).map (fun i =>
  (show Fin 3 from ((exec% (transpose.symm pairing)).app ⟨.right⟩).hom i)) == (List.finRange 4).map g₂

/-- Transposing and transposing back is the identity. -/
theorem transpose_symm_transpose : transpose.symm (transpose cone) = cone :=
  transpose.symm_apply_apply cone

/-! ### The limit of the pair diagram, through `Δ ⊣ lim` -/

noncomputable def P : LimitCone D :=
  realizedLimitConeOfAdj (J := Discrete WalkingPair) setDenotationFullyFaithful
    diagonalLimitAdjunction limitAction D

#guard (exec% P.cone.pt : SetHandle) == .prod (.finite 2) (.finite 3)
#guard (List.finRange 2).all fun a => (List.finRange 3).all fun b =>
  (show Fin 2 from (exec% (P.cone.π.app ⟨.left⟩)).hom (a, b)) == a &&
  (show Fin 3 from (exec% (P.cone.π.app ⟨.right⟩)).hom (a, b)) == b

/-- The competing cone `(g₁, g₂)` with apex `Fin 4`. -/
def s : Cone D := ⟨SetHandle.finite 4, cone⟩

/-- Its mediator. -/
noncomputable def mediator : @Quiver.Hom SetHandles _ (.finite 4) P.cone.pt := P.isLimit.lift s

/- The mediator is the pairing. -/
#guard (List.finRange 4).all fun i =>
  (show Fin 2 × Fin 3 from (exec% mediator).hom i) == (g₁ i, g₂ i)

theorem mediator_fac (j : Discrete WalkingPair) : mediator ≫ P.cone.π.app j = cone.app j :=
  P.isLimit.fac s j

/-! ### The registered row -/

run_cmd liftTermElabM do
  let state ← registryState
  let some adj := state.adjunctions.find? (·.id == AdjunctionId.setsPairDiagonalLimit)
    | throwError "adj.sets.pair.diagonal_limit is not registered"
  unless adj.left == FunctorId.setsPairDiagonal && adj.right == FunctorId.setsPairLimit do
    throwError "the adjunction names other functors"
  -- The row is an adjunction between exactly its two functors: swapped sides are rejected.
  let rejected ← try
      validateRegistryEntryDeclaration
        (.adjunction { adj with id := ⟨"adj.probe.swapped"⟩, left := adj.right, right := adj.left })
      pure false
    catch _ => pure true
  unless rejected do throwError "an adjunction with swapped sides was accepted"

end CasCatalogue.AdjunctionProbes
