/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import CasCatalogue.TestSuite

/-!
# Selected structure (b0-selected-structure)

Objects that share a carrier stay distinct: `(ℤ/n)^k` (`ZModPower`) and `Vec(ℤ/n, k)` are both
`Fin k → ℤ/n`, and each is recognized as itself, by its declaration, never by which transparent
alias unifies first. Before the rule, recognizing either was refused as "not a unique registered
object".
-/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language

/-- The name of the registered object of sets that `c xs` is recognized as. -/
meta def recognizedName (c : Name) (xs : Array Expr) : TermElabM String := do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets) | throwError "no sets"
  match ← (recognize state (← mkAppOptM c (xs.map some)) sets).run {} with
  | .object _ _ (some (entry, _)) _ _ => pure entry.name
  | _ => throwError "{c} is not recognized as a named object"

run_elab do
  let zmod4 := mkApp (mkConst ``ZMod) (mkNatLit 4)
  let power ← recognizedName ``CasCatalogue.Foundation.Objects.integersModPower
    #[mkNatLit 4, mkNatLit 3]
  let vectors ← recognizedName ``CasCatalogue.Algebra.LinearAlgebra.vectors #[zmod4, mkNatLit 3]
  unless power == "ZModPower" && vectors == "Vec" do
    throwError "objects sharing a carrier are not kept distinct: {power}, {vectors}"
