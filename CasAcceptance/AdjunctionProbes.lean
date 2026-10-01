/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public import CasCatalogue.Semantic
public meta import CasAcceptance.Standard
public meta import CasCatalogue.Semantic

@[expose] public section

/-!
# Acceptance for `cc-adjunctions` (CC-CALC, CC-UNIV)

The registered adjunction `adj.sets.pair.diagonal_limit : Δ ⊣ lim` on pair diagrams of sets:

* the row names exactly its two registered functors, and it is validated as an adjunction between
  them: swapped sides are rejected;
* its declaration is Mathlib's adjunction, whose `homEquiv` transposes a map of pair diagrams
  `Δ(X) ⟶ D` to a map `X ⟶ lim D` and back (`Adjunction.homEquiv`, `symm_apply_apply`).

What the transpose does to data is not a Lean term of the kernel: it is a statement of the
language, decided through the admitted registrations.
-/

open CategoryTheory Limits Lean Meta Elab Term Command

namespace CasCatalogue.AdjunctionProbes

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
  -- The registered declaration is a Mathlib adjunction: its transpose is an equivalence of homs.
  let declaration ← instantiateFresh adj.declaration
  let type ← whnfR (← inferType declaration)
  unless type.isAppOfArity ``CategoryTheory.Adjunction 6 do
    throwError "the registered declaration is not a Mathlib adjunction"
  -- The re-registered row passes.
  validateRegistryEntryDeclaration (.adjunction { adj with id := ⟨"adj.probe.control"⟩ })

end CasCatalogue.AdjunctionProbes
