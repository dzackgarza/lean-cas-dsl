module

public import CasGates.KernelPurity
import all CasAcceptance
import all CasAcceptance.ReindexExecutionProbes
import all CasAcceptance.StructuredComparisonProbes
public import CasGates.AxiomAuditRules
public meta import CasGates.AxiomAuditRules

run_cmd CasCatalogue.Tools.AxiomAudit.audit
  [`CasCatalogue, `CasCompiler, `CasRuntime, `CasContract, `CasAcceptance]

namespace CasCatalogue.Tools.AxiomAudit

/-- The audit runs during elaboration of this executable's imports. -/
def main : IO UInt32 := pure 0

end CasCatalogue.Tools.AxiomAudit
