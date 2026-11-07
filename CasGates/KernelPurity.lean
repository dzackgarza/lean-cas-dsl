module

import all CasCatalogue
import all CasCatalogue.Acceptance
import all CasCatalogue.AcceptanceSyntax
import all CasCatalogue.Admission
import all CasCatalogue.BinderReaderProbes
import all CasCatalogue.CellCall
import all CasCatalogue.CellSyntax
import all CasCatalogue.Codec
import all CasCatalogue.CodecConditionProbes
import all CasCatalogue.ComputationalData
import all CasCatalogue.ConstructionData
import all CasCatalogue.ConstructionDataProbes
import all CasCatalogue.ConstructionLegReaderProbes
import all CasCatalogue.ContextualSubsetProbes
import all CasCatalogue.Decide
import all CasCatalogue.ElementData
import all CasCatalogue.ElementDataProbes
import all CasCatalogue.EquationData
import all CasCatalogue.EquationDataProbes
import all CasCatalogue.EvidencePresentationProbes
import all CasCatalogue.FileItems
import all CasCatalogue.FunctorActionData
import all CasCatalogue.FunctorActionDataProbes
import all CasCatalogue.ImageFormProbes
import all CasCatalogue.InterpretationFailure
import all CasCatalogue.Language
import all CasCatalogue.LiftedSubobjectData
import all CasCatalogue.LiftedSubobjectDataProbes
import all CasCatalogue.ParameterStructureProbes
import all CasCatalogue.PresentationReaderProbes
import all CasCatalogue.ProofIdentityProbes
import all CasCatalogue.QuestionIdentity
import all CasCatalogue.QuestionProbes
import all CasCatalogue.Realize
import all CasCatalogue.Registry
import all CasCatalogue.ResolutionFailureProbes
import all CasCatalogue.Resolve
import all CasCatalogue.ResolveSyntax
import all CasCatalogue.SelectedCarrierProbes
import all CasCatalogue.Semantic
import all CasCatalogue.StructuredParameterProbes
import all CasCatalogue.StructuredReconstructionProbes
import all CasCatalogue.StructuredResult
import all CasCatalogue.StructuredResultProbes
import all CasCatalogue.TermGraphProbes
import all CasCatalogue.TestSuite
import all CasCatalogue.Trace
import all CasCompiler
import all CasCompiler.Context
import all CasCompiler.ContextTests
import all CasCompiler.Layout
import all CasCompiler.Program
import all CasCompiler.ProgramTests
import all CasCompiler.OperationalTests
import all CasCompiler.ValueRequestTests
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
import all CasRuntime.Execute
import all CasRuntime.ExecuteTests
import all CasRuntime.Scope
import all CasRuntime.ScopeTests
import all CasContract
import all CasContract.Failure
import all CasContract.Port
import all CasContract.Registration
public meta import CasGates.KernelPurityRules

open Lean CasGates.KernelPurity

run_cmd do
  let found ← violations (← getEnv) kernelRoots
  unless found.isEmpty do
    throwError MessageData.joinSep (found.toList.map (m!"  {·}")) "\n"
