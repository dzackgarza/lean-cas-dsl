/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
# Kernel-axiom audit

Checks every declaration of the core and the probes against the standard Lean axiom budget. This
is a kernel-assumption audit only; it does not establish that a Lean statement has the intended
mathematical meaning. A leaf has no Lean declaration to audit.
-/

open Lean Elab Command

namespace CasCatalogue.Tools.AxiomAudit

/-- The standard Lean axioms permitted by the authoritative release policy. -/
def permitted : Array Name := #[
  ``propext, ``Classical.choice, ``Quot.sound]

/-- Check declarations by owning module, including imported private declarations. -/
def audit (roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) => do
    let index ← env.getModuleIdxFor? name
    let owner := env.header.moduleNames[index.toNat]!
    if roots.contains owner.getRoot then some name else none
  let mut violations : Array (Name × Array Name) := #[]
  for name in names do
    let assumptions ← collectAxioms name
    let unexpected := assumptions.filter fun assumption => !permitted.contains assumption
    if !unexpected.isEmpty then
      violations := violations.push (name, unexpected.qsort Name.lt)
  if !violations.isEmpty then
    throwError m!"nonstandard axiom dependencies: {violations.toList}"

end CasCatalogue.Tools.AxiomAudit
