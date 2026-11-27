module

public import CasGates.AxiomAuditRules

public section

namespace CasCompiler

open Lean Meta

/-- Read a whole declaration under the release safety and axiom policy.
Reuse: Lean.getConstInfo, Lean.collectAxioms and the existing AxiomAudit.permitted budget.
Reference: Lean/Util/CollectAxioms.lean at Lean v4.33.0. -/
opaque checkedDeclaration (name : Name) : MetaM ConstantInfo := do
  let info ← getConstInfo name
  if info.isUnsafe then throwError "source declaration {name} is unsafe"
  for assumption in ← collectAxioms name do
    unless CasCatalogue.Tools.AxiomAudit.permitted.contains assumption do
      throwError "source declaration {name} depends on {assumption}"
  return info

end CasCompiler
