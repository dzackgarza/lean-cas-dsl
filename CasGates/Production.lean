module

import all CasCompiler
import all CasCompiler.Context
import all CasCompiler.Roles
import all CasCompiler.ContextTests
import all CasCompiler.Declaration
import all CasCompiler.FormationTests
import all CasCompiler.Syntax
import all CasCompiler.Parse
import all CasCompiler.ParseTests
import all CasCompiler.ProofTests
import all CasCompiler.Elaborate
import all CasCompiler.ElaborateTests
import all CasCompiler.Surface
import all CasCompiler.SourceNumeral
import all CasCompiler.SurfaceTests
import all CasCompiler.Read
import all CasCompiler.ReadExpression
import all CasCompiler.SourceSyntaxTests
import all CasCompiler.SourceLambdaTests
import all CasCompiler.SourcePattern
import all CasCompiler.SourcePatternTests
import all CasCompiler.SourceTuple
import all CasCompiler.SourceTupleTests
import all CasCompiler.SourceOperation
import all CasCompiler.SourceOperationTests
import all CasCompiler.SourceLimit
import all CasCompiler.SourceLimitTests
import all CasCompiler.SourceMember
import all CasCompiler.SourceMemberTests
import all CasCompiler.SourceCarrier
import all CasCompiler.SourceCarrierTests
import all CasCompiler.SourceCategoryBindingTests
import all CasCompiler.SourceAtomTests
import all CasCompiler.SourceViewTests
import all CasTools.QuestionExport
import all CasTools.QuestionExportTests
import all CasTools.NativeExpressionTests
import all CasTools.SourceSnapshotTests
import all LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders
import all LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds
import all LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests
import all CasCompiler.RouteGrammar
import all CasCompiler.RouteGrammarTests
import all CasCompiler.Resolve
import all CasCompiler.ResolveTests
import all CasCompiler.NativeRouteTests
import all CasCompiler.OperationFamilyTests
import all CasCompiler.OperationRefinementTests
import all CasCompiler.Equality
import all CasCompiler.EqualityEvidenceTests
import all CasCompiler.ComparisonTests
import all CasCompiler.WhiskeringTests
import all CasCompiler.ConstructorComparisonTests
import all CasCompiler.FunctorExpressionTests
import all CasCompiler.Layout
import all CasCompiler.Program
import all CasCompiler.ProgramTests
import all CasCompiler.ApplicationArgumentTests
import all CasCompiler.OperationalTests
import all CasCompiler.ValueRequestTests
import all CasRuntime
import all CasRuntime.Identity
import all CasRuntime.IdentityTests
import all CasRuntime.Owner
import all CasRuntime.OwnerTests
import all CasRuntime.Connection
import all CasRuntime.Deadline
import all CasRuntime.Value
import all CasRuntime.ValueTests
import all CasRuntime.ContainerTests
import all CasRuntime.RecordTests
import all CasRuntime.Environment
import all CasRuntime.RoleMap
import all CasRuntime.EnvironmentTests
import all CasRuntime.ApplicationOriginTests
import all CasRuntime.EnvironmentExecutionTests
import all CasRuntime.Occurrence
import all CasRuntime.OccurrenceTests
import all CasRuntime.Transaction
import all CasRuntime.TransactionTests
import all CasRuntime.CompletionTests
import all CasRuntime.CompletionWaiterTests
import all CasRuntime.CompletionFailureTests
import all CasRuntime.Execute
import all CasRuntime.ExecuteTests
import all CasRuntime.Scope
import all CasRuntime.ScopeTests
import all CasRuntime.Encode
import all CasRuntime.EncodeTests
import all CasRuntime.Reply
import all CasRuntime.ReplyTests
import all CasRuntime.Literal
import all CasRuntime.LiteralTests
import all CasRuntime.Materialize
import all CasRuntime.MaterializeTests
import all CasRuntime.ProtocolTests
import all CasRuntime.Transport
import all CasRuntime.TransportTests
import all CasRuntime.SDKTests
import all CasRuntime.ExportCaptureTests
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
