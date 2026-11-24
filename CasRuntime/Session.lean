module

public import CasRuntime.Kernel
public import CasCompiler.ReadSession
public import CasCatalogue.Evaluation
import CasCompiler.SourceCarrier

public section

namespace CasRuntime

open Lean Meta Elab Term CasCompiler CasCatalogue

/-- The outcome of one public statement. A gap and an unavailable backend are not failures of
the statement's mathematics. Source: CasContract.Failure, "Failure is stratified". -/
inductive Outcome
  | holds
  | wrong (message : String)
  | gap (reason : String)
  | unavailable (reason : String)
  | malformed (reason : String)
  | invalid (reason : String)
  | ambiguous (reason : String)
  | internal (reason : String)
  deriving Inhabited, Repr

def Outcome.kind : Outcome → String
  | .holds => "holds"
  | .wrong _ => "wrong"
  | .gap _ => "gap"
  | .unavailable _ => "unavailable"
  | .malformed _ => "malformed"
  | .invalid _ => "invalid"
  | .ambiguous _ => "ambiguous"
  | .internal _ => "internal"

def Outcome.detail : Outcome → String
  | .holds => ""
  | .wrong message | .gap message | .unavailable message | .malformed message
  | .invalid message | .ambiguous message | .internal message => message

/-- The same kind of outcome with another detail. An outcome that holds has no detail. -/
def Outcome.withDetail : Outcome → String → Outcome
  | .holds, _ => .holds
  | .wrong _, detail => .wrong detail
  | .gap _, detail => .gap detail
  | .unavailable _, detail => .unavailable detail
  | .malformed _, detail => .malformed detail
  | .invalid _, detail => .invalid detail
  | .ambiguous _, detail => .ambiguous detail
  | .internal _, detail => .internal detail

def Outcome.fails (outcome : Outcome) : Bool :=
  !(outcome matches .holds | .gap _ | .unavailable _)

/-- Classify a reader ambiguity, an unfinished source form or a stratified failure.
An exception without a stratum is an internal failure, never mathematical invalidity. -/
def Outcome.ofException (error : Exception) : MetaM Outcome := do
  let message ← error.toMessageData.toString
  if CasCatalogue.Exception.isSemanticAmbiguity error then return .ambiguous message
  if CasCatalogue.Exception.isUnsupportedSource error then return .gap message
  return match CasCatalogue.Exception.stratum? error with
    | some .invalid => .invalid message
    | some .semanticAmbiguity => .ambiguous message
    | some .noImplementation | some .ambiguousRealization => .gap message
    | some .unavailable => .unavailable message
    | some .malformed => .malformed message
    | none => .internal message

/-- One public source session over one kernel: the checked source declarations and the
committed runtime binding of each computational declaration, by stable source identity.
Source: data model §2, ContextTelescope and its separate runtime-binding map. -/
structure KernelSession where
  private mk ::
  kernel : Kernel
  source : SourceSession
  /-- Compute every question through the kernel, with no discharge in Lean. -/
  computationOnly : Bool
  private bound : Std.HashMap BindingId ValueBinding
  /-- Successful definitions whose results must be observed, because they dispatched or
  retain a delayed computation. Source dependencies carry this policy through aliases. -/
  private observed : Std.HashSet BindingId := {}
  /-- Definitions kept without a runtime value because their computation had no leaf or no
  available backend (constitution C3), and the definitions that use them. -/
  private unavailable : Array (BindingId × Name) := #[]
  /-- Definitions whose statement did not read, by declared name, with the outcome of that
  statement. A later use of such a name has the outcome of its definition. -/
  private unread : Array (String × Outcome) := #[]

/-- The installed leaves' manifest when none is named: `CAS_LEAVES`, the leaves package
directory or its manifest file, else `.lake/packages/cas_leaves`. An absent default manifest
installs no leaf. Source: api/manifest.md of the leaf contract. -/
def installedManifest : IO (Option System.FilePath) := do
  let path : System.FilePath ← match ← IO.getEnv "CAS_LEAVES" with
    | some leaves =>
      let leaves : System.FilePath := leaves
      pure (if leaves.extension == some "json" then leaves else leaves / manifestFile)
    | none => pure ((".lake" / "packages" / "cas_leaves" : System.FilePath) / manifestFile)
  return if ← path.pathExists then some path else none

/-- Start a session on the named manifest, or on the installed one. The realization profile
is the file named by `CAS_REALIZATION_PROFILE` (execution contract v2 §5.3).
The caller owns the Environment that holds the runtime snapshot. -/
opaque KernelSession.start (manifest : Option System.FilePath := none)
    (computationOnly : Bool := false) (timeoutMs : UInt32 := 600000) : MetaM KernelSession := do
  let manifest ← match manifest with
    | some path => pure (some path)
    | none => installedManifest
  let profile ← match ← IO.getEnv "CAS_REALIZATION_PROFILE" with
    | none => pure none
    | some path => do
      let json ← IO.ofExcept <| (Json.parse (← IO.FS.readFile path)).mapError IO.userError
      pure (some json)
  let owners ← OwnerRegistry.new
  discard <| SessionSnapshot.initialize owners
  return ⟨← Kernel.load owners manifest profile timeoutMs,
    ← SourceSession.empty owners.identities, computationOnly, {}, {}, #[], #[]⟩

opaque KernelSession.close (session : KernelSession) : IO Unit := session.kernel.close

/-- The retained value of a source declaration, when it has computational content. -/
def KernelSession.value? (session : KernelSession) (id : BindingId) : Option ValueBinding :=
  session.bound[id]?

private def commit (transaction : CellTransaction) : MetaM Unit := do
  match ← transaction.commit with
  | .ok _ => pure ()
  | .error failure => throwError "internal: the cell did not commit: {repr failure}"

/-- A question depending on an observed computation concerns its actual value, including
through aliases and captured definitions. Computation-only sessions use that observation path
for every proposition. Reuse: contextDependencies closes native source dependencies through
their types and values. -/
private def requiresComputedObservation (session : KernelSession) (context : OpenContext)
    (proposition : Expr) : MetaM Bool := do
  if session.computationOnly then return true
  for index in (← contextDependencies context.bindings proposition) do
    let some binding := context.bindings[index]?
      | throwError "a question dependency is outside its complete source context"
    if session.observed.contains binding.id then return true
  return false

/-- Decide an eligible closed source proposition through the existing registered literal
evaluations and kernel decision. Supplied local evidence uses the same observation policy
without requiring its proposition to be closed. -/
private def discharged (session : KernelSession) (context : OpenContext) (proposition : Expr) :
    TermElabM (Option Bool) := do
  if ← requiresComputedObservation session context proposition then return none
  let proposition ← zetaReduce proposition
  if proposition.hasFVar then return none
  Evaluation.decideEvaluated proposition

/-- The literal value of a side that is a registered literal form's denotation `denote L`.
Source: LiteralEntry, "a statement comparing a computed value with a literal compares it
with this denotation". -/
private def literalForm? (side : Expr) : MetaM (Option Expr) := do
  let side := side.consumeMData
  let .const name _ := side.getAppFn | return none
  unless (← semanticState).literals.any (·.denotation == name) do return none
  return side.getAppArgs.back?

/-- A side that the reader formed as a registered numeral (NumeralEntry). It is compared as its
own term: deciding that a computed value equals a numeral evaluates a closed proposition, which
the kernel may do; it does not compute the numeral's image as data (constitution C22). -/
private def numeralForm? (side : Expr) : Option Expr :=
  match side with
  | .mdata data body =>
    if data.getName `CasCompiler.source.kind == ``CasCatalogue.NumeralEntry then some side
    else numeralForm? body
  | _ => none

/-- Exact unsupplied formal parameters of this source, including dependencies through
native types and definitions. Hypotheses/dictionaries remain formal; no value is selected by
its name or by conversion of its carrier. -/
private def unsuppliedParameter? (session : KernelSession) (context : OpenContext)
    (expression : Expr) : MetaM (Option LocalBinding) := do
  for index in (← contextDependencies context.bindings expression) do
    let some binding := context.bindings[index]?
      | throwError "a formal dependency is outside its complete source context"
    if binding.role == .parameter && !session.bound.contains binding.id then
      return some binding
  return none

private def requireSuppliedParameters (session : KernelSession) (context : OpenContext)
    (expression : Expr) : MetaM Unit := do
  if let some binding ← unsuppliedParameter? session context expression then
    let name ← binding.expression.fvarId!.getUserName
    throwStratum .noImplementation (MessageData.tagged (missingValueTag binding.id)
      m!"the abstract parameter {name} has no supplied runtime value")

private def packetOf (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (side : Expr) : MetaM (Except String Json) := do
  let binding ← session.kernel.run transaction context session.bound side
  let graph ← transaction.view
  match ← IO.ofExcept <| (graph.packet? binding).mapError IO.userError with
  | some packet => return .ok packet
  | none => return .error "the computed value is retained by its provider and has no scalar comparison"

/-- Compare two computed candidates of one source type as retained scalar data.
The comparison reads the actual returned packets at their source type, or at the registered
literal type when one side is a literal form, and decides equality of those values in Lean's
kernel. It is an observation of candidates, not a proof. -/
private def compare (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (left right : Expr) : MetaM Outcome := do
  let literals ← #[left, right].mapM fun side => do
    if let some literal ← literalForm? side then return some literal
    return numeralForm? side
  let reading ← (literals.findSome? id).mapM fun literal => inferType literal
  let mut values := #[]
  for side in #[left, right], literal in literals do
    if let some literal := literal then
      values := values.push (literal, toString (← ppExpr literal))
      continue
    let packet ← match ← packetOf session transaction context side with
      | .ok packet => pure packet
      | .error reason => return .gap reason
    -- A candidate outside the representation of its reading type is a malformed answer.
    let value ← try
        match reading with
        | some type => ScalarLiteral.readAt type packet
        | none => ScalarLiteral.read (← SourceLayout.ofTerm (← context.close side)) packet
      catch error =>
        return .malformed s!"{packet.compress}: {← error.toMessageData.toString}"
    let some value := value
      | return .gap s!"the computed value {packet.compress} has no scalar reading at its type"
    values := values.push (value, packet.compress)
  let some (first, shown) := values[0]? | return .internal "the comparison lost its left value"
  let some (second, expected) := values[1]? | return .internal "the comparison lost its right value"
  match ← Decide.decideProp (← mkEq first second) with
  | some true => return .holds
  | some false => return .wrong s!"computed {shown}, compared with {expected}"
  | none => return .gap "equality of the computed values is not decided in Lean"

/-- Observe a question through its original native proposition. Published predicates return a
Boolean; registered properties retain their released Option Bool observation contract.
Negation applies logic to that answer, and an unknown property observation stays unknown. -/
private partial def decideComputed (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (proposition : Expr) : MetaM Outcome := do
  let logical := proposition.consumeMData
  if logical.isAppOfArity ``Not 1 then
    return match ← decideComputed session transaction context logical.appArg! with
      | .holds => .wrong "the computed predicate holds, so its negation does not"
      | .wrong _ => .holds
      | outcome => outcome
  let packet ← match ← packetOf session transaction context proposition with
    | .ok packet => pure packet
    | .error reason => return .gap reason
  if (← propertySource? proposition).isSome then
    return match PropertyObservation.decode packet with
      | .ok (some true) => .holds
      | .ok (some false) => .wrong "the computed property is false"
      | .ok none => .gap "the property observation returned no decision"
      | .error reason => .malformed s!"{packet.compress}: {reason}"
  match packet with
  | .bool true => return .holds
  | .bool false => return .wrong "the computed predicate is false"
  | other => return .malformed s!"{other.compress}: a predicate requires a Boolean answer"

/-- An equality of propositions with a truth value on one side is that proposition or its
negation (`(9 ∈ primes) = false`). -/
private def truthCase? (type left right : Expr) : MetaM (Option Expr) := do
  unless (← whnfR (← instantiateMVars type)).isProp do return none
  let truth := fun (side : Expr) => do
    let side ← whnfR (← instantiateMVars side)
    return if side.isConstOf ``True then some true
      else if side.isConstOf ``False then some false else none
  match ← truth right, ← truth left with
  | some true, _ => return some left
  | some false, _ => return some (mkNot left)
  | none, some true => return some right
  | none, some false => return some (mkNot right)
  | none, none => return none

/-- The proposition under the reader's leading bindings, such as a ring variable bound to its
registered generator. Source metadata stays attached through ordinary let substitution;
logical inspection uses a transparent view while execution retains the original source. -/
private partial def underBindings : Expr → Expr
  | .letE _ _ value body _ => underBindings (body.instantiate1 value)
  | .mdata data body => .mdata data (underBindings body)
  | expression => expression

/-- Whether a value holds a delayed published computation (a closure of a published family, as a
lift's fields are) or data owned by a provider, directly or in a field. Source-written values
remain eligible for proof discharge; their runtime retention does not depend on this test. -/
private partial def delayedComputation (codes : Std.HashMap (RuntimeId .program) ClosureCode)
    (graph : ValueGraph) (binding : ValueBinding) : Bool :=
  match graph.find binding.value with
  | none => false
  | some node => match node.payload.data with
    | .closure program _ => match codes[program]? with
      | some (.family ..) => true
      | _ => false
    | .ownedToken .. => true
    | .product fields => fields.any (delayedComputation codes graph)
    | .container value =>
      (value.slots.map (·.binding) ++ value.fields.getD #[] ++ value.callable.toArray).any
        (delayedComputation codes graph)
    | .portable _ => false

/-- An original block item observed during this cell. A missing outcome is explicitly
unpublished: `attempted` distinguishes a rolled-back stage from an unexecuted continuation.
No successful child outcome is returned as committed when its enclosing block aborts. -/
structure StatementObservation where
  item : TSyntax `cas_item
  attempted : Bool
  outcome : Option Outcome := none
  proposition : String := ""
  conclusions : Array SourceConclusion := #[]
  milliseconds : Nat := 0
  dispatches : Array Registration := #[]

/-- The result of one statement: its outcome, the session after it and, for a question,
the proposition that the reader formed. -/
structure StatementRun where
  outcome : Outcome
  session : KernelSession
  proposition : String := ""
  /-- Original terms and complete inner scopes survive lexical exit. -/
  conclusions : Array SourceConclusion := #[]
  /-- Explicit inspection output only; ordinary results remain silent about assumptions. -/
  inspectionOutput : Array String := #[]
  observations : Array StatementObservation := #[]
  published : Bool := false

/-- The heartbeat limit of one statement, in thousands. Functional work may use any heartbeat
limit that it needs (constitution C21); the limit stays finite so that a statement that does not
terminate ends in a timeout. `polynomials.factors` needs more than Lean's default 200000. -/
def statementHeartbeats : Nat := 50000000

/-- The name that a definition statement declares: the identifier after `let`. -/
private def definedName? (statement : TSyntax `cas_stmt) : Option String :=
  let arguments := statement.raw.getArgs
  match arguments[0]?, arguments[1]? with
  | some (Syntax.atom _ "let"), some name =>
    if name.isIdent then some name.getId.toString else none
  | _, _ => none

/-- A prepared statement carries its ordinary direct-statement publication policy.
A containing block can reject a non-holding child without publishing any staged child. -/
private structure StagedStatement where
  run : StatementRun
  publish : Bool

private def requiredCell (transaction : Option CellTransaction) : MetaM CellTransaction := do
  let some transaction := transaction
    | throwError "an executable statement has no owning cell transaction"
  return transaction

private partial def unobservedItems (item : TSyntax `cas_item) (statement : SourceStatement) :
    Array StatementObservation :=
  match statement with
  | .contextBlock items => items.flatMap fun (item, child) => unobservedItems item child
  | _ => #[{ item, attempted := false }]

private def unpublishedObservation (observation : StatementObservation) : StatementObservation :=
  match observation.outcome with
  | some .holds => { observation with outcome := none, conclusions := #[] }
  | _ => observation

/-- Supplied native evidence concerns its original source proposition. When that proposition
uses an observed runtime value (also through aliases/captures), or the session requests
computation only, the ordinary question path must still observe the actual candidate. -/
private def proofRequiresObservation (session : KernelSession) (proposition : SourceTerm) :
    MetaM Bool :=
  session.source.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    requiresComputedObservation session context (← proposition.source.inContext context)

private partial def executePrepared (session : KernelSession)
    (transaction : Option CellTransaction) (statement : SourceStatement) :
    TermElabM StagedStatement := do
  Core.checkSystem "source statement execution"
  match statement with
  | .assumption next =>
    -- A hypothetical source binding has no corresponding concrete runtime value.
    return ⟨{ outcome := .holds, session := { session with source := next } }, false⟩
  | .inspection scope =>
    -- Inspection consumes only frozen data. A containing block withholds this output until
    -- its outer success boundary; a direct inspection allocates no transaction or ledger ID.
    return ⟨{ outcome := .holds, session, inspectionOutput := #[scope.assumptionsText] }, false⟩
  | .proved proposition proof =>
    let conclusion ← session.source.conclusion #[proposition] (some proof)
    if ← proofRequiresObservation session proposition then
      let result ← executePrepared session transaction (.question proposition)
      return { result with run := { result.run with conclusions := #[conclusion] } }
    let shown ← proposition.source.withOpen fun _ expression => return (← ppExpr expression).pretty
    return ⟨{ outcome := .holds, session, proposition := shown, conclusions := #[conclusion] }, false⟩
  | .settled values =>
    let conclusion ← session.source.conclusion values
    let shown ← session.source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      values.mapM fun value => do
        return toString (← ppExpr (← value.source.inContext context))
    return ⟨{
      outcome := .holds
      session
      proposition := s!"settled: {" and ".intercalate shown.toList}"
      conclusions := #[conclusion] }, false⟩
  | .definition next value =>
    let transaction ← requiredCell transaction
    let conclusion ← session.source.conclusion #[value]
    let sent := (← session.kernel.dispatches.get).size
    let (binding, dependent) ← try
        next.context.withOpen fun bindings => do
          let context ← ContextTelescope.capture bindings
          let expression ← value.source.inContext context
          let dependent := context.bindings.any fun binding =>
            session.unavailable.any (·.1 == binding.id) &&
              expression.containsFVar binding.expression.fvarId!
          let type ← whnf (← inferType expression)
          if (← isProp type) || type.isSort then return (none, dependent)
          -- A definition over hypothetical parameters retains its complete native meaning;
          -- it does not turn a formal-variable descriptor into a concrete backend input.
          if (← unsuppliedParameter? session context expression).isSome then
            return (none, dependent)
          return (some (← session.kernel.run transaction context session.bound expression), dependent)
      catch error =>
        -- A direct read definition retains its source meaning on an unavailable computation.
        -- A containing block instead aborts the entire shared cell at its result boundary.
        let outcome ← Outcome.ofException error
        if outcome.fails then throw error
        let some entry := next.context.entries.back?
          | throwError "internal: a source definition added no declaration"
        let unavailable := session.unavailable.push (entry.id, entry.userName)
        return ⟨{
          outcome
          session := { session with source := next, unavailable }
          conclusions := #[conclusion] }, false⟩
    let graph ← transaction.view
    let codes ← session.kernel.codes.get
    let delayed := binding.any (delayedComputation codes graph)
    let some entry := next.context.entries.back?
      | throwError "internal: a source definition added no declaration"
    let computed := (← session.kernel.dispatches.get).size > sent || delayed
    let bound := match binding with
      | some binding => session.bound.insert entry.id binding
      | none => session.bound
    let observed := if computed then session.observed.insert entry.id else session.observed
    let unavailable := if dependent then session.unavailable.push (entry.id, entry.userName)
      else session.unavailable
    return ⟨{
      outcome := .holds
      session := { session with source := next, bound, observed, unavailable }
      conclusions := #[conclusion] }, true⟩
  | .implemented value =>
    let transaction ← requiredCell transaction
    let conclusion ← session.source.conclusion #[value]
    let shown ← session.source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let expression ← value.source.inContext context
      requireSuppliedParameters session context expression
      discard <| session.kernel.run transaction context session.bound expression
      return toString (← ppExpr expression)
    return ⟨{ outcome := .holds, session, proposition := shown, conclusions := #[conclusion] }, true⟩
  | .question proposition =>
    let transaction ← requiredCell transaction
    let conclusion ← session.source.conclusion #[proposition]
    let (outcome, shown) ← session.source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let asked ← proposition.source.inContext context
      let shown := toString (← ppExpr asked)
      let outcome ← match ← discharged session context asked with
        | some true => pure .holds
        | some false => pure (.wrong "Lean decides the negation of the statement")
        | none =>
          -- Prepare the complete question before either computed side can dispatch.
          requireSuppliedParameters session context asked
          let asked := underBindings asked
          match asked.consumeMData.eq? with
          | some (type, left, right) =>
            match ← truthCase? type left right with
            | some proposition => decideComputed session transaction context proposition
            | none => compare session transaction context left right
          | none => decideComputed session transaction context asked
      return (outcome, shown)
    -- A direct question preserves its existing commit policy for returned wrong/gap outcomes.
    return ⟨{ outcome, session, proposition := shown, conclusions := #[conclusion] }, true⟩
  | .contextBlock items =>
    discard <| requiredCell transaction
    let mut current := session
    let mut conclusions := #[]
    let mut output := #[]
    let mut observations := #[]
    let mut proposition := ""
    for (item, child) in items, index in [:items.size] do
      let start ← IO.monoMsNow
      let sent := (← session.kernel.dispatches.get).size
      let result ← try executePrepared current transaction child
        catch error =>
          -- Native interruption is not caught by this ordinary exception handler. An
          -- ordinary child failure retains its actual item and failure stratum until abort.
          let outcome ← Outcome.ofException error
          let outcome := match current.unavailable.find? (fun (id, _) => missingValueOf error id) with
            | some (_, name) => .gap s!"{name} has no computed value: {outcome.detail}"
            | none => outcome
          pure (⟨{ outcome, session := current }, false⟩ : StagedStatement)
      let milliseconds := (← IO.monoMsNow) - start
      let calls ← session.kernel.dispatches.get
      let observed : Array StatementObservation := if result.run.observations.isEmpty then
          #[{
            item
            attempted := true
            outcome := some result.run.outcome
            proposition := result.run.proposition
            conclusions := result.run.conclusions
            milliseconds
            dispatches := calls.extract sent calls.size }]
        else result.run.observations
      observations := observations ++ observed
      unless result.run.outcome matches .holds do
        let rest := (items.drop (index + 1)).flatMap fun (item, child) => unobservedItems item child
        return ⟨{ result.run with
          session
          inspectionOutput := #[]
          observations := (observations.map unpublishedObservation) ++ rest }, false⟩
      current := result.run.session
      conclusions := conclusions ++ result.run.conclusions
      output := output ++ result.run.inspectionOutput
      proposition := result.run.proposition
    -- Values/code retain their complete contexts, while no local source name, runtime
    -- binding or availability/discharge policy escapes this lexical scope.
    return ⟨{
      outcome := .holds
      session
      proposition
      conclusions
      inspectionOutput := output, observations }, true⟩

/-- Run one completely prepared public statement in one publication cell. A scoped block
reads all children before dispatch, stages them in order and commits once. Native interruption
runs the same finally-abort path and never becomes a mathematical outcome. -/
opaque KernelSession.run (session : KernelSession) (statement : TSyntax `cas_stmt) :
    TermElabM StatementRun :=
  withCurrHeartbeats <|
  withTheReader Core.Context (fun context => { context with maxHeartbeats := statementHeartbeats * 1000 }) do
  CasCompiler.setPreferredRoutes
    (session.kernel.manifest.registrations.flatMap (·.preferredRoutes))
  let saved ← saveState
  try
    let prepared ← session.source.readStatement statement
    let needsCell ← match prepared with
      | .settled _ | .assumption _ | .inspection _ => pure false
      | .proved proposition _ => proofRequiresObservation session proposition
      | _ => pure true
    if !needsCell then return (← executePrepared session none prepared).run
    let transaction ← CellTransaction.begin session.kernel.ledger
    let result ← try
        let result ← executePrepared session (some transaction) prepared
        Core.checkSystem "source statement publication"
        -- All throwing result/conclusion construction precedes the only commit.
        if result.publish then commit transaction
        pure result
      finally
        discard <| (transaction.abort : BaseIO Bool)
    unless result.publish do
      if prepared matches .contextBlock _ then saved.restore
    return { result.run with published := result.publish }
  catch error =>
    let outcome ← Outcome.ofException error
    saved.restore
    -- A use of a name whose own definition did not read has the outcome of that definition.
    if let some (name, definition) := session.unread.find? fun (name, _) =>
        CasCatalogue.Exception.isUnknownSourceName error name then
      return { outcome := definition.withDetail
                 s!"the definition of {name} did not read: {definition.detail}",
               session }
    -- A definition that did not read declares no name. Its declared name is kept with its outcome.
    let session := match definedName? statement with
      | some name => { session with unread := session.unread.push (name, outcome) }
      | none => session
    -- A statement that needs the value of a definition whose computation had no leaf has that
    -- gap, named, not an internal defect (constitution C3). The dependency check names the
    -- binding that has no value.
    if let some (_, name) := session.unavailable.find? fun (id, _) => missingValueOf error id then
      return { outcome := .gap s!"{name} has no computed value: {outcome.detail}", session }
    return { outcome, session }

end CasRuntime
