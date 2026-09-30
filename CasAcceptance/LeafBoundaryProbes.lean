/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasAcceptance.Standard
public meta import CasAcceptance.Standard

@[expose] public section

/-!
# The installed leaves keep the leaf boundary (CC-ADAPTER, CC-SEP)

Every installed leaf module has only permitted direct imports (the leaf API `CasContract.Leaf`,
other leaves, Mathlib, `lean-categories`) and wrote only permitted rows; no module outside
`lean-categories` and the leaf packages wrote any row (`leafBoundaryViolations`). The refusals
themselves are the contract's, tested with it (`CasContract.Probes.LeafBoundary`).
-/

open Lean Meta Elab Command

namespace CasCatalogue.LeafBoundaryProbes

run_cmd liftTermElabM do
  let violations := leafBoundaryViolations (← getEnv)
  unless violations.isEmpty do
    throwError "leaf boundary violations: {violations.toList}"
  let leaves := (← getEnv).header.moduleNames.filter (leafRoot.isPrefixOf ·)
  unless leaves.size ≥ 10 do
    throwError "the standard universe imports only {leaves.size} leaf modules"

end CasCatalogue.LeafBoundaryProbes
