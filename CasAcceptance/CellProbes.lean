/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.CellCall
public meta import CasAcceptance.Standard
public meta import CasCatalogue.CellCall

@[expose] public section

/-!
# Acceptance for `cc-cells` (CC-CALC)

Registered cells of the list monad on sets (`Semantics/Foundation/Lists.lean`): the unit
`η : 𝟭 ⟶ L`, the multiplication `μ : L ⋙ L ⟶ L` and the invertible reversal `ρ : L ≅ L`. They are
composed with Mathlib's operations, and each composite's component at a set is a morphism of the
catalogue's mathematics (`cell%`), typed by Lean:

* vertical composition, whiskering on either side and horizontal composition elaborate, between
  the composites of registered functors they are declared between;
* the inverse cell composes to the identity: `ρ ≫ ρ⁻¹` at `ℤ` is `𝟙 (L ℤ)`, a theorem about the
  registered isomorphism;
* composing cells whose endpoints do not match is rejected; inverting a cell not registered
  invertible is rejected; a cell whose declaration is not between its registered composites is
  rejected by the registry.

What a cell does to data (`ρ [v, w] = [w, v]`) is a statement of the language, decided through
the admitted registrations; no leaf supplies a cell, an action or a square.
-/

open CategoryTheory Lean Meta Elab Term Command
open CasCatalogue.Foundation.Objects

namespace CasCatalogue.CellProbes

/-- The reversal followed by its inverse is the identity at `ℤ`. -/
theorem reverse_comp_inverse :
    (cell% "cell.sets.list.reverse" ≫ "cell.sets.list.reverse"⁻¹ at (integers) in "cat.sets") =
      𝟙 _ := by
  simp

/- The composites elaborate as morphisms between the composites of registered functors. -/
run_cmd liftTermElabM do
  for term in [← `(cell% ("cell.sets.list.unit" ▷ "fun.sets.list") ≫ "cell.sets.list.join"
      at (integers) in "cat.sets"),
      ← `(cell% "fun.sets.list" ◁ "cell.sets.list.unit" at (integers) in "cat.sets"),
      ← `(cell% "cell.sets.list.unit" ◫ "cell.sets.list.unit" at (integers) in "cat.sets"),
      ← `(cell% "cell.sets.list.reverse"⁻¹ at (naturals) in "cat.sets")] do
    let e ← withoutErrToSorry (elabTerm term none)
    synthesizeSyntheticMVarsNoPostponing
    let type ← whnfR (← inferType (← instantiateMVars e))
    unless type.isAppOf ``Quiver.Hom do throwError "{term} is not a morphism: {type}"

/-- Whether elaborating `stx` fails with a message containing `fragment`. -/
def rejects (stx : Term) (fragment : String) : TermElabM Bool := do
  try
    discard <| withoutErrToSorry <| elabTerm stx none
    return false
  catch e =>
    return ((← e.toMessageData.toString).splitOn fragment).length > 1

run_cmd liftTermElabM do
  unless ← rejects (← `(cell% "cell.sets.list.join" ≫ "cell.sets.list.unit"
      at (integers) in "cat.sets")) "vertical composition" do
    throwError "a composite with mismatched endpoints was accepted"
  unless ← rejects (← `(cell% "cell.sets.list.unit"⁻¹ at (integers) in "cat.sets"))
      "not registered invertible" do
    throwError "a non-invertible cell was inverted"
  unless ← rejects (← `(cell% "cell.sets.list.reverse" at (integers) in "cat.no_such_category"))
      "no registered category" do
    throwError "a cell at an object of an unregistered category was accepted"
  -- `η` is not a cell `L ⟶ L`.
  try
    withoutModifyingEnv <| validateRegistryEntryDeclaration (.cell
      { id := ⟨"cell.probe.wrong"⟩, source := Foundation.Sets, target := Foundation.Sets
        left := #[.functor FunctorId.setsList], right := #[.functor FunctorId.setsList]
        declaration := `LeanCategories.Foundation.listUnit })
    throwError "a cell with the wrong endpoints was registered"
  catch e =>
    unless ((← e.toMessageData.toString).splitOn "is not the composite").length > 1 do
      throw e

end CasCatalogue.CellProbes
