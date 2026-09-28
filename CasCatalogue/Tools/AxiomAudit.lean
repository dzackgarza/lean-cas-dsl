/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
# Kernel-axiom audit

Checks every exported `CasCatalogue` declaration against the standard Lean axiom budget.
This is a kernel-assumption audit only; it does not establish that a Lean statement has
the intended mathematical meaning.
-/

open Lean Elab Command

namespace CasCatalogue.Tools.AxiomAudit

/-- The standard Lean axioms permitted by the authoritative release policy. -/
def permitted : Array Name := #[
  ``propext, ``Classical.choice, ``Quot.sound,
  -- Schema-owned quotations are opaque by design and remain non-forgeable.
  ``CasCatalogue.CategoryFamilyParameterQuotation]

/-- Reject exported CasCatalogue declarations that use nonstandard assumptions. -/
def audit : CommandElabM Unit := do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun name =>
    (`CasCatalogue).isPrefixOf name
  let mut violations : Array (Name × Array Name) := #[]
  for name in names do
    let assumptions ← collectAxioms name
    let unexpected := assumptions.filter fun assumption =>
      !permitted.contains assumption &&
        !( (`CasCatalogue.CategoryFamilyParameterQuotation).isPrefixOf assumption)
    if !unexpected.isEmpty then
      violations := violations.push (name, unexpected.qsort Name.lt)
  if !violations.isEmpty then
    throwError m!"nonstandard axiom dependencies: {violations.toList}"

run_cmd audit

/-- The audit is performed during elaboration; this executable exists for Lake and `just`. -/
def main : IO UInt32 := pure 0

end CasCatalogue.Tools.AxiomAudit
