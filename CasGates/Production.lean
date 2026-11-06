module

import all CasCompiler
import all CasCompiler.Context
import all CasCompiler.ContextTests
import all CasCompiler.Layout
import all CasCompiler.Program
import all CasCompiler.ProgramTests
import all CasRuntime
import all CasRuntime.Identity
import all CasRuntime.IdentityTests
import all CasRuntime.Owner
import all CasRuntime.OwnerTests
import all CasRuntime.Value
import all CasRuntime.ValueTests
import all CasRuntime.Occurrence
import all CasRuntime.OccurrenceTests
import all CasRuntime.Transaction
import all CasRuntime.TransactionTests
import all CasContract
import all CasContract.Failure
import all CasContract.Port
import all CasContract.Registration
public meta import CasGates.KernelPurityRules
public meta import CasGates.AxiomAuditRules

open Lean CasGates.KernelPurity

run_cmd do
  let environment ← getEnv
  let options ← getOptions
  let found ← profileitM Exception "kernel purity" options
    (Lean.Elab.Command.liftIO (violations environment productionRoots))
  unless found.isEmpty do
    throwError MessageData.joinSep (found.toList.map (m!"  {·}")) "\n"
  profileitM Exception "kernel axioms" options
    (CasCatalogue.Tools.AxiomAudit.audit productionRoots)
