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
# Acceptance for `cc-cells` (CC-CALC, CC-ACTION)

Registered cells of the list monad on sets (`Semantics/Foundation/Lists.lean`): the unit
`η : 𝟭 ⟶ L`, the multiplication `μ : L ⋙ L ⟶ L` and the invertible reversal `ρ : L ≅ L`. They are
composed with Mathlib's operations and run on `ℤ²` (presented as `.intPow 2`), a set that is not
enumerated: each component is a rule on `List ℤ²`, computed through the realized cell (the
preimage through the fully faithful realization of sets).

* one registered cell changes the datum: `ρ [v, w] = [w, v]`;
* two registered cells composed vertically: `(η ▷ L) ≫ μ` is the identity on data (the monad's
  unit law), and its first factor is `[v, w] ↦ [[v], [w]]`;
* whiskering on the other side, `L ◁ η : [v, w] ↦ [[v, w]]`, and horizontal composition,
  `η ◫ η : v ↦ [[v]]`;
* the inverse cell composes to the identity: `ρ ≫ ρ⁻¹` on data, and as a theorem about realized
  cells (`realizedCell_comp`, `realizedCell_id`);
* composing cells whose endpoints do not match is rejected; a backend leaf cannot register a
  cell; a cell whose declaration is not between its registered composites is rejected.
-/

open CategoryTheory Lean Meta Elab Term Command
open CasCatalogue.Foundation.Actions CasCatalogue.Foundation.ListActions

namespace CasCatalogue.CellProbes

def v : Fin 2 → ℤ := ![1, 2]
def w : Fin 2 → ℤ := ![3, -4]
def u : Fin 2 → ℤ := ![0, 7]

/-- The elements of `ℤ²`, lists of them, and lists of lists. -/
abbrev Z2 := Fin 2 → ℤ

#guard (show List Z2 from (cell% "cell.sets.list.reverse"
  at (.intPow 2) in "cat.sets").hom [v, w]) == [w, v]

#guard (show List Z2 from (cell% ("cell.sets.list.unit" ▷ "fun.sets.list") ≫ "cell.sets.list.join"
  at (.intPow 2) in "cat.sets").hom [v, w, u]) == [v, w, u]
#guard (show List (List Z2) from (cell% "cell.sets.list.unit" ▷ "fun.sets.list"
  at (.intPow 2) in "cat.sets").hom [v, w]) == [[v], [w]]
#guard (show List (List Z2) from (cell% "fun.sets.list" ◁ "cell.sets.list.unit"
  at (.intPow 2) in "cat.sets").hom [v, w]) == [[v, w]]
#guard (show List (List Z2) from (cell% "cell.sets.list.unit" ◫ "cell.sets.list.unit"
  at (.intPow 2) in "cat.sets").hom v) == [[v]]

#guard (show List Z2 from (cell% "cell.sets.list.reverse" ≫ "cell.sets.list.reverse"⁻¹
  at (.intPow 2) in "cat.sets").hom [v, w, u]) == [v, w, u]

/-- The realized reversal and its inverse compose to the identity of the realized list functor. -/
theorem reverse_comp_inverse :
    realizedCell setDenotationFullyFaithful listAction listAction
        (Foundation.Lists.listReverseCell.hom ≫ Foundation.Lists.listReverseCell.inv) =
      𝟙 listAction.action := by
  rw [Iso.hom_inv_id, realizedCell_id]

/-- Whether elaborating `stx` fails with a message containing `fragment`. -/
def rejects (stx : Term) (fragment : String) : TermElabM Bool := do
  try
    discard <| withoutErrToSorry <| elabTerm stx none
    return false
  catch e =>
    return ((← e.toMessageData.toString).splitOn fragment).length > 1

run_cmd liftTermElabM do
  unless ← rejects (← `(cell% "cell.sets.list.join" ≫ "cell.sets.list.unit"
      at (.intPow 2) in "cat.sets")) "vertical composition" do
    throwError "a composite with mismatched endpoints was accepted"
  unless ← rejects (← `(cell% "cell.sets.list.unit"⁻¹ at (.intPow 2) in "cat.sets"))
      "not registered invertible" do
    throwError "a non-invertible cell was inverted"
  let leafCell : LeafContract :=
    { backend := "probe", contributions := [.naturalTransformation
        { id := ⟨"cell.probe.leaf"⟩, source := Foundation.Sets, target := Foundation.Sets
          left := #[], right := #[.functor FunctorId.setsList]
          declaration := `LeanCategories.Foundation.listUnit }] }
  try
    registerLeaf leafCell
    throwError "a leaf registered a cell"
  catch e =>
    unless ((← e.toMessageData.toString).splitOn "natural transformation").length > 1 do
      throw e
  -- `η` is not a cell `L ⟶ L`.
  try
    withoutModifyingEnv <| addRegistryEntryChecked (.cell
      { id := ⟨"cell.probe.wrong"⟩, source := Foundation.Sets, target := Foundation.Sets
        left := #[.functor FunctorId.setsList], right := #[.functor FunctorId.setsList]
        declaration := `LeanCategories.Foundation.listUnit })
    throwError "a cell with the wrong endpoints was registered"
  catch e =>
    unless ((← e.toMessageData.toString).splitOn "is not the composite").length > 1 do
      throw e

end CasCatalogue.CellProbes
