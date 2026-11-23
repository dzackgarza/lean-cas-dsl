module

import CasRuntime.Session
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
import LeanCategories.Catalogue.Semantics.Algebra.Series
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
meta import LeanCategories.Catalogue.Semantics.Algebra.Polynomials
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals
meta import LeanCategories.Catalogue.Semantics.Foundation.Finiteness
meta import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Lattices
meta import LeanCategories.Catalogue.Semantics.Algebra.LinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.NumberSystems
meta import LeanCategories.Catalogue.Semantics.Algebra.Series

namespace CasRuntime.NativeProjectionTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue

private abbrev BindingKey := RuntimeId .value × Array (RuntimeId .association)

private def bindingKey (binding : ValueBinding) : BindingKey :=
  (binding.value, binding.associationIds)

private def sameContext (left right : ContextTelescope) : Bool :=
  left.entries.size == right.entries.size &&
    (left.entries.zip right.entries).all (fun (left, right) =>
      left.id == right.id && left.role == right.role && left.userName == right.userName &&
        left.binderInfo == right.binderInfo && left.kind == right.kind &&
        left.type == right.type && left.value == right.value && left.nondep == right.nondep) &&
    left.instances.size == right.instances.size &&
    (left.instances.zip right.instances).all (fun (left, right) =>
      left.className == right.className && left.binding == right.binding)

private def sameSource (left right : ClosedTerm) : Bool :=
  left.expression == right.expression && left.type == right.type &&
    left.universeParams == right.universeParams && sameContext left.context right.context

private structure ProjectionFrame where
  field : Name
  source : ClosedTerm
  origin : ClosedTerm
  parameters : Array (Option BindingKey)
  captures : Array BindingKey
  operand : BindingKey
  occurrence : RuntimeId .occurrence

-- A repeated source computation is detected without equating independently retained values.
-- Fresh operand/occurrence IDs are printed as evidence; they do not hide the repeated code.
private def sameProjection (left right : ProjectionFrame) : Bool :=
  left.field == right.field && sameSource left.source right.source &&
    sameSource left.origin right.origin && left.parameters == right.parameters &&
    left.captures == right.captures

private def projectionFrame? (kernel : Kernel) (request : PreparedRequest)
    (transaction : CellTransaction) : MetaM (Option ProjectionFrame) := do
  let .project operand field := request.action | return none
  let some node := (← transaction.view).find operand.value | return none
  let .closure program captures := node.payload.data | return none
  let some (.term source) := (← kernel.codes.get)[program]? | return none
  return some {
    field := field.projection
    source
    origin := node.origin.role.source
    parameters := node.origin.parameters.map (·.map bindingKey)
    captures := captures.map bindingKey
    operand := bindingKey operand
    occurrence := request.occurrence }

-- Describe the actual projection spine without expanding implicit mathematical parameters.
-- SourceProjection supplies the same native declaration and parent used by the lowerer.
-- Semantic metadata is printed before descending through it, so the boundary stays visible.
private partial def describeSpine (expression : Expr) : MetaM (Array String) := do
  if let .mdata data body := expression then
    let kind := data.getName `CasCompiler.source.kind
    let id := data.getString `CasCompiler.source.id
    let declaration := data.getName `CasCompiler.source.declaration
    let mark := markedKey? data
    let rest ← describeSpine body
    if kind.isAnonymous && id.isEmpty && declaration.isAnonymous && mark.isNone then
      return rest
    return #[s!"metadata(kind={kind}, id={id}, declaration={declaration}, mark={repr mark})"] ++ rest
  if let some projection ← SourceProjection.ofExpr? expression then
    return #[s!"projection {projection.declaration}"] ++ (← describeSpine projection.parent)
  if expression.isApp then
    return #[s!"application ({expression.getAppNumArgs} arguments)"] ++
      (← describeSpine expression.getAppFn)
  return #[match expression with
    | .const name _ => s!"constant {name}"
    | .proj owner index _ => s!"native projection {owner}[{index}]"
    | .fvar id => s!"local {repr id}"
    | .bvar index => s!"bound variable {index}"
    | .mvar id => s!"metavariable {repr id}"
    | .lam name .. => s!"lambda {name}"
    | .forallE name .. => s!"forall {name}"
    | .letE name .. => s!"let {name}"
    | .sort level => s!"sort {repr level}"
    | .lit .. => "literal"
    | .app .. | .mdata .. => "unreachable outer expression"]

private def describeProjection (frame : ProjectionFrame) : MetaM MessageData := do
  let source ← frame.source.withOpen fun _ expression => ppExpr expression
  let sourceSpine ← describeSpine frame.source.expression
  let typeSpine ← describeSpine frame.source.type
  let origin ← if sameSource frame.source frame.origin then
      pure m!"same exact closed source, type and context"
    else do
      let shown ← frame.origin.withOpen fun _ expression => ppExpr expression
      let spine ← describeSpine frame.origin.expression
      let type ← describeSpine frame.origin.type
      pure m!"{shown}\norigin spine: {repr spine}\norigin type head: {repr type}\n\
        origin context: {repr (frame.origin.context.entries.map (·.id))}"
  return m!"field: {frame.field}\noperand: {repr frame.operand}\n\
    occurrence: {repr frame.occurrence}\nsource: {source}\n\
    source spine: {repr sourceSpine}\nsource type head: {repr typeSpine}\n\
    source context: {repr (frame.source.context.entries.map (·.id))}\n\
    origin: {origin}\nparameters: {repr frame.parameters}\ncaptures: {repr frame.captures}"

private structure ProjectionGuard where
  active : IO.Ref (Array ProjectionFrame)
  demands : IO.Ref Nat

mutual

-- This is the same public composition used by Kernel.evaluateSource. The injected evaluator
-- is passed into Kernel.execute itself, so recursive source demands cannot escape the guard.
private partial def evaluateBounded (kernel : Kernel) (guard : ProjectionGuard) : SourceEvaluation :=
  fun sourceSnapshot transaction program context bound expression =>
    lowerTerm {
      ledger := kernel.ledger, transaction, codes := kernel.codes, marks := kernel.marks
      sourceSnapshot
      run := fun computation => Execute.run (executeBounded kernel guard) computation transaction
        (some (kernel.resolveFixedInput (evaluateBounded kernel guard) sourceSnapshot
          transaction program)) }
      program context bound expression

private partial def executeBounded (kernel : Kernel) (guard : ProjectionGuard) :
    PFunctor.Handler.Stateful MetaM CellTransaction OperationalSignature :=
  fun request transaction => do
    let count ← guard.demands.get
    guard.demands.set (count + 1)
    let active ← guard.active.get
    let frame ← projectionFrame? kernel request transaction
    if let some frame := frame then
      if let some prior := active.find? (sameProjection · frame) then
        throwError "a native projection re-entered its active source computation\n\
          earlier:\n{← describeProjection prior}\nrepeated:\n{← describeProjection frame}"
      guard.active.set (active.push frame)
    try
      -- This cap belongs only to the diagnostic harness, never to the kernel. It catches a
      -- cycle whose generated source changes, instead of allowing an unbounded test process.
      if count ≥ 256 then
        let detail ← match frame with
          | some frame => describeProjection frame
          | none => pure m!"the current demand is not a native term projection"
        throwError "the native projection diagnostic exceeded 256 demands\n{detail}"
      return (← kernel.execute (evaluateBounded kernel guard) request transaction, transaction)
    finally guard.active.set active

end

-- Exactly Session.underBindings: it exposes the proposition read beneath leading source lets.
private partial def underBindings : Expr → Expr
  | .letE _ _ value body _ => underBindings (body.instantiate1 value)
  | .mdata _ body => underBindings body
  | expression => expression

private def expectMissing (text operation : String) (action : MetaM ValueBinding) : MetaM Unit := do
  let failure : Option Exception ← try
    discard <| action
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "`{text}` unexpectedly computed without a leaf"
  unless failure.toMessageData.hasTag (· == Stratum.noImplementation.tag) do
    throwError "`{text}` failed before its original published boundary:\n{failure.toMessageData}"
  let detail ← failure.toMessageData.toString
  unless (detail.splitOn operation).length > 1 do
    throwError "`{text}` did not reach {operation}: {detail}"

-- These are unchanged statements and missing-operation expectations from the first block of
-- SessionComputationTests. The harness reads their actual left sides; it supplies no answers.
private def checkQuestion (source : SourceSession) (kernel : Kernel) (text operation : String)
    (evaluate : CellTransaction → OpenContext → Expr → MetaM ValueBinding) : TermElabM Unit :=
  withCurrHeartbeats <|
  withTheReader Core.Context (fun context =>
    { context with maxHeartbeats := statementHeartbeats * 1000 }) do
    let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
      | .ok statement => pure statement
      | .error error => throwError "the original projection question did not parse: {error}"
    let .question proposition ← source.readStatement ⟨statement⟩
      | throwError "the original projection question did not read as a question"
    let transaction ← CellTransaction.begin kernel.ledger
    try
      source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let asked := underBindings (← proposition.source.inContext context)
        let some (_, left, _) := asked.eq?
          | throwError "the original projection question did not read as an equality"
        expectMissing text operation (evaluate transaction context left)
    finally discard <| transaction.abort

run_cmd liftTermElabM do
  let environment ← getEnv
  try
    let owners ← OwnerRegistry.new
    let kernel ← Kernel.load owners none none 1000
    discard <| SessionSnapshot.initialize owners
    let source ← SourceSession.empty owners.identities
    let cases := #[
      ("assert |cokernel(to_dual(1))| = 2", "fun.bil_wform.carrier"),
      ("assert |Fin(2) ⊔ Fin(3)| = 5", "meth.cardinality")]
    try
      for (text, operation) in cases do
        let guard : ProjectionGuard := ⟨← IO.mkRef #[], ← IO.mkRef 0⟩
        checkQuestion source kernel text operation fun transaction context expression => do
          let program ← owners.identities.fresh .program
          evaluateBounded kernel guard none transaction program context {} expression
      -- The actual public executor must reach the same boundary after the bounded controls.
      for (text, operation) in cases do
        checkQuestion source kernel text operation fun transaction context expression =>
          kernel.run transaction context {} expression none
    finally kernel.close
  finally setEnv environment

end CasRuntime.NativeProjectionTests
