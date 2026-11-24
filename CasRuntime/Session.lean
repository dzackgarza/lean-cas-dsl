module

public import CasRuntime.Kernel
public import CasCompiler.ReadSession
public import CasCatalogue.Evaluation
public import CasCompiler.SourceSnapshot
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
  available backend (constitution C3), with the actual outcome of that computation.
  Dependent definitions keep the same cause without repeating the invocation. -/
  private unavailable : Array (BindingId × Name × Outcome) := #[]
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

/-- Start a session on the named manifest, or on the installed one. Freeze the explicit profile
configuration, or the file named by `CAS_REALIZATION_PROFILE` when it is omitted
(execution contract v2 §5.3).
The caller owns the Environment that holds the runtime snapshot. -/
opaque KernelSession.start (manifest : Option System.FilePath := none)
    (computationOnly : Bool := false) (timeoutMs : UInt32 := 600000)
    (profile : Option Json := none) : MetaM KernelSession := do
  let manifest ← match manifest with
    | some path => pure (some path)
    | none => installedManifest
  let profile ← match profile with
    | some configuration => pure (some configuration)
    | none => match ← IO.getEnv "CAS_REALIZATION_PROFILE" with
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

/-- Follow only the retained source bindings' declared dependencies. A failed computation
keeps its outcome by BindingId; later executable uses do not lower its definition again.
Mathematical questions may still be discharged from their source before this execution gate.
Reuse: contextDependencies closes dependencies through native types and definitions. -/
private def failedComputation (session : KernelSession) (context : OpenContext)
    (expression : Expr) : MetaM (Option Outcome) := do
  for index in ← contextDependencies context.bindings expression do
    let some binding := context.bindings[index]?
      | throwError "internal: a source dependency is outside its retained context"
    if let some (_, name, outcome) := session.unavailable.find? fun (id, _, _) =>
        id == binding.id then
      return some (outcome.withDetail s!"{name} has no computed value: {outcome.detail}")
  return none

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
    (context : OpenContext) (side : Expr) (sourceSnapshot : Option Json) :
    MetaM (Except String Json) := do
  let binding ← session.kernel.run transaction context session.bound side sourceSnapshot
  let graph ← transaction.view
  match ← IO.ofExcept <| (graph.packet? binding).mapError IO.userError with
  | some packet => return .ok packet
  | none => return .error "the computed value is retained by its provider and has no scalar comparison"

/-- Compare two computed candidates of one source type as retained scalar data.
The comparison reads the actual returned packets at their source type, or at the registered
literal type when one side is a literal form, and decides equality of those values in Lean's
kernel. It is an observation of candidates, not a proof. -/
private def compare (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (left right : Expr) (sourceSnapshot : Option Json) :
    MetaM Outcome := do
  let literals ← #[left, right].mapM fun side => do
    if let some literal ← literalForm? side then return some literal
    return numeralForm? side
  let reading ← (literals.findSome? id).mapM fun literal => inferType literal
  let mut values := #[]
  for side in #[left, right], literal in literals do
    if let some literal := literal then
      values := values.push (literal, toString (← ppExpr literal))
      continue
    let packet ← match ← packetOf session transaction context side sourceSnapshot with
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
    (context : OpenContext) (proposition : Expr) (sourceSnapshot : Option Json) :
    MetaM Outcome := do
  let logical := proposition.consumeMData
  if logical.isAppOfArity ``Not 1 then
    return match ← decideComputed session transaction context logical.appArg! sourceSnapshot with
      | .holds => .wrong "the computed predicate holds, so its negation does not"
      | .wrong _ => .holds
      | outcome => outcome
  let packet ← match ← packetOf session transaction context proposition sourceSnapshot with
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
Source-preflight failures have their actual outcome with `attempted := false`; reading a
typed prefix does not enter execution or establish any of its mathematical outcomes.
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
  /-- Whether prepared source entered execution. Source-preflight failures remain false. -/
  attempted : Bool := true
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

/-- The already read statement and its original source observations. A block keeps the
same typed child tree; no source syntax is replayed when execution stops or rolls back. -/
private inductive RetainedStatement where
  | statement (source : SourceStatement) (conclusions : Array SourceConclusion)
      (proposition : String)
  | contextBlock (source : SourceStatement)
      (items : Array (TSyntax `cas_item × RetainedStatement))

private def RetainedStatement.source : RetainedStatement → SourceStatement
  | .statement source _ _ | .contextBlock source _ => source

private def RetainedStatement.conclusions : RetainedStatement → Array SourceConclusion
  | .statement _ conclusions _ => conclusions
  | .contextBlock _ _ => #[]

private def RetainedStatement.proposition : RetainedStatement → String
  | .statement _ _ proposition => proposition
  | .contextBlock _ _ => ""

/-- Restore only declarations captured by the original checked source owners. Runtime
extensions remain at their restored snapshot; unread or rejected source has no such tree. -/
private partial def RetainedStatement.ensureDeclarations : RetainedStatement → MetaM Unit
  | .contextBlock _ items =>
    items.forM fun (_, child) => child.ensureDeclarations
  | .statement source conclusions _ => do
    for conclusion in conclusions do conclusion.ensureDeclarations
    match source with
    | .definition next _ | .assumption next => next.ensureDeclarations
    | .inspection scope => scope.ensureDeclarations
    | _ => pure ()

private def requiredCell (transaction : Option CellTransaction) : MetaM CellTransaction := do
  let some transaction := transaction
    | throwError "an executable statement has no owning cell transaction"
  return transaction

/-- Original unexecuted item identities, with no invented source reading. A labeled
container retains its own identity as well as the original items nested inside it. -/
partial def unreadSourceItems (item : TSyntax `cas_item) : Array StatementObservation :=
  let row : Array StatementObservation := #[{ item, attempted := false }]
  match sourceItemStatement? item with
  | none => row
  | some statement => match sourceContextItems? statement with
    | none => row
    | some items =>
      let nested := items.flatMap unreadSourceItems
      match item with
      | `(cas_item| test $_:ident $_:str : $_:cas_stmt) => row ++ nested
      | _ => nested

private partial def unobservedItems (item : TSyntax `cas_item) (statement : RetainedStatement) :
    Array StatementObservation :=
  match statement with
  | .contextBlock _ items =>
    let nested := items.flatMap fun (item, child) => unobservedItems item child
    match item with
    | `(cas_item| test $_:ident $_:str : $_:cas_stmt) =>
      #[{ item, attempted := false }] ++ nested
    | _ => nested
  | .statement _ conclusions proposition =>
    #[{ item, attempted := false, conclusions, proposition }]

private def unobservedChildren : RetainedStatement → Array StatementObservation
  | .contextBlock _ items => items.flatMap fun (item, child) => unobservedItems item child
  | .statement _ _ _ => #[]

private def unpublishedObservation (observation : StatementObservation) : StatementObservation :=
  match observation.outcome with
  -- Withhold the runtime outcome; the original typed source is independent of publication.
  | some .holds => { observation with outcome := none }
  | _ => observation

/-- Supplied native evidence concerns its original source proposition. When that proposition
uses an observed runtime value (also through aliases/captures), or the session requests
computation only, the ordinary question path must still observe the actual candidate. -/
private def proofRequiresObservation (session : KernelSession) (proposition : SourceTerm) :
    MetaM Bool :=
  session.source.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    requiresComputedObservation session context (← proposition.source.inContext context)

/-- Retain the original checked reading before its execution can throw. The same record
serves successful execution and the existing failure boundary; it asserts no runtime outcome.
Block children are retained in their actual preceding source sessions before dispatch. -/
private def preparedConclusions (session : SourceSession) (statement : SourceStatement) :
    MetaM (Array SourceConclusion) := do
  match statement with
  | .definition _ value | .question value | .implemented value =>
    return #[← session.conclusion #[value]]
  | .settled values => return #[← session.conclusion values]
  | .proved proposition proof => return #[← session.conclusion #[proposition] (some proof)]
  | .assumption _ | .inspection _ | .contextBlock _ => return #[]

/-- Freeze conclusions and their existing display in the source scopes already produced
by reading. Only the stored next-session values advance scope; this does not read or execute
any child again. Unexecuted children therefore retain exactly the same source observations. -/
private partial def retainStatement (session : SourceSession) (statement : SourceStatement) :
    MetaM RetainedStatement := do
  match statement with
  | .contextBlock items =>
    let mut current := session
    let mut retained := #[]
    for (item, child) in items do
      retained := retained.push (item, ← retainStatement current child)
      match child with
      | .definition next _ | .assumption next => current := next
      | _ => pure ()
    return .contextBlock statement retained
  | _ =>
    let conclusions ← preparedConclusions session statement
    let proposition ← match statement with
      | .question value | .implemented value =>
        session.context.withOpen fun bindings => do
          let context ← ContextTelescope.capture bindings
          return toString (← ppExpr (← value.source.inContext context))
      | .proved proposition _ =>
        proposition.source.withOpen fun _ expression => return (← ppExpr expression).pretty
      | .settled values => do
        let shown ← session.context.withOpen fun bindings => do
          let context ← ContextTelescope.capture bindings
          values.mapM fun value => do
            return toString (← ppExpr (← value.source.inContext context))
        pure s!"settled: {" and ".intercalate shown.toList}"
      | _ => pure ""
    return .statement statement conclusions proposition

/-- Freeze only the original completed source prefix. The Boolean marks the original
failed item so the existing failure boundary can attach its unchanged classified outcome
after restoring the outer session. Every item is unattempted at runtime. -/
private partial def observeReadFailure (session : SourceSession)
    (items : Array (TSyntax `cas_item × Option SourceStatementRead)) :
    MetaM (Array (Bool × StatementObservation) × Array RetainedStatement) := do
  let mut current := session
  let mut observations : Array (Bool × StatementObservation) := #[]
  let mut completed : Array RetainedStatement := #[]
  for (item, reading) in items do
    match reading with
    | none =>
      observations := observations ++ (unreadSourceItems item).map (false, ·)
    | some (.complete statement) =>
      let retained ← retainStatement current statement
      completed := completed.push retained
      observations := observations ++ (unobservedItems item retained).map (false, ·)
      match statement with
      | .definition next _ | .assumption next => current := next
      | _ => pure ()
    | some (.failed _ children) =>
      if children.isEmpty then
        observations := observations.push (true, { item, attempted := false })
      else
        match item with
        | `(cas_item| test $_:ident $_:str : $_:cas_stmt) =>
          observations := observations.push (false, { item, attempted := false })
        | _ => pure ()
        let (nested, retained) ← observeReadFailure current children
        observations := observations ++ nested
        completed := completed ++ retained
  return (observations, completed)

private partial def executePrepared (session : KernelSession)
    (transaction : Option CellTransaction) (prepared : RetainedStatement) :
    TermElabM StagedStatement := do
  Core.checkSystem "source statement execution"
  let conclusions := prepared.conclusions
  let shown := prepared.proposition
  match prepared.source with
  | .assumption next =>
    -- A hypothetical source binding has no corresponding concrete runtime value.
    return ⟨{ outcome := .holds, session := { session with source := next } }, false⟩
  | .inspection scope =>
    -- Inspection consumes only frozen data. A containing block withholds this output until
    -- its outer success boundary; a direct inspection allocates no transaction or ledger ID.
    return ⟨{ outcome := .holds, session, inspectionOutput := #[scope.assumptionsText] }, false⟩
  | .proved proposition _ =>
    if ← proofRequiresObservation session proposition then
      return ← executePrepared session transaction
        (.statement (.question proposition) conclusions shown)
    return ⟨{ outcome := .holds, session, proposition := shown, conclusions }, false⟩
  | .settled _ =>
    return ⟨{
      outcome := .holds
      session
      proposition := shown
      conclusions }, false⟩
  | .definition next value =>
    let some sourceEntry := next.context.entries.back?
      | throwError "internal: a source definition added no declaration"
    let sourceSnapshot := some (SourceSnapshot.snapshot next.observation value (some sourceEntry))
    let transaction ← requiredCell transaction
    let sent := (← session.kernel.dispatches.get).size
    let result : Except Outcome (Option ValueBinding) ← try
        next.context.withOpen fun bindings => do
          let context ← ContextTelescope.capture bindings
          let expression ← value.source.inContext context
          let type ← whnf (← inferType expression)
          if (← isProp type) || type.isSort then return .ok none
          -- A definition over hypothetical parameters retains its complete native meaning;
          -- it does not turn a formal-variable descriptor into a concrete backend input.
          if (← unsuppliedParameter? session context expression).isSome then
            return .ok none
          if let some outcome ← failedComputation session context expression then
            return .error outcome
          return .ok (some (← session.kernel.run transaction context session.bound expression
            sourceSnapshot))
      catch error =>
        -- A direct read definition retains its source meaning on an unavailable computation.
        -- A containing block instead aborts the entire shared cell at its result boundary.
        let outcome ← Outcome.ofException error
        if outcome.fails then throw error
        pure (.error outcome)
    match result with
    | .error outcome =>
        let some entry := next.context.entries.back?
          | throwError "internal: a source definition added no declaration"
        let unavailable := session.unavailable.push (entry.id, entry.userName, outcome)
        return ⟨{
          outcome
          session := { session with source := next, unavailable }
          conclusions }, false⟩
    | .ok binding =>
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
      return ⟨{
        outcome := .holds
        session := { session with source := next, bound, observed }
        conclusions }, true⟩
  | .implemented value =>
    let sourceSnapshot := some (SourceSnapshot.snapshot session.source.observation value)
    let transaction ← requiredCell transaction
    session.source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let expression ← value.source.inContext context
      if let some outcome ← failedComputation session context expression then
        return ⟨{ outcome, session, proposition := shown, conclusions }, false⟩
      requireSuppliedParameters session context expression
      discard <| session.kernel.run transaction context session.bound expression sourceSnapshot
      return ⟨{ outcome := .holds, session, proposition := shown, conclusions }, true⟩
  | .question proposition =>
    let sourceSnapshot := some (SourceSnapshot.snapshot session.source.observation proposition)
    let transaction ← requiredCell transaction
    session.source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let asked ← proposition.source.inContext context
      let settled ← discharged session context asked
      if settled.isNone then
        if let some outcome ← failedComputation session context asked then
          return ⟨{ outcome, session, proposition := shown, conclusions }, false⟩
      let outcome ← match settled with
        | some true => pure .holds
        | some false => pure (.wrong "Lean decides the negation of the statement")
        | none =>
          -- Prepare the complete question before either computed side can dispatch.
          requireSuppliedParameters session context asked
          let asked := underBindings asked
          match asked.consumeMData.eq? with
          | some (type, left, right) =>
            match ← truthCase? type left right with
            | some proposition => decideComputed session transaction context proposition sourceSnapshot
            | none => compare session transaction context left right sourceSnapshot
          | none => decideComputed session transaction context asked sourceSnapshot
      -- A direct question preserves its existing commit policy for returned wrong/gap outcomes.
      return ⟨{ outcome, session, proposition := shown, conclusions }, true⟩
  | .contextBlock _ =>
    discard <| requiredCell transaction
    let .contextBlock _ items := prepared
      | throwError "a retained context block lost its original typed children"
    let mut current := session
    let mut conclusions := #[]
    let mut output := #[]
    let mut observations := #[]
    let mut proposition := ""
    for (item, child) in items, index in [:items.size] do
      let start ← IO.monoMsNow
      let sent := (← session.kernel.dispatches.get).size
      let result ← try executePrepared current transaction child
        catch error => do
          -- Native interruption is not caught by this ordinary exception handler. An
          -- ordinary child failure retains its actual item and failure stratum until abort.
          let outcome ← Outcome.ofException error
          let outcome := match current.unavailable.find? (fun (id, _, _) => missingValueOf error id) with
            | some (_, name, definition) => definition.withDetail
                s!"{name} has no computed value: {definition.detail}"
            | none => outcome
          return (⟨{
            outcome
            session := current
            conclusions := child.conclusions
            proposition := child.proposition
          }, false⟩ : StagedStatement)
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
            dispatches := calls.extract sent calls.size }] ++
            (if result.run.outcome matches .holds then #[] else unobservedChildren child)
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
  let executionEntered ← IO.mkRef false
  let failed (error : Exception) (prepared : Option RetainedStatement)
      (prefix : Array RetainedStatement) :
      TermElabM StatementRun := do
    let outcome ← Outcome.ofException error
    saved.restore
    -- Make the checked native names present before any later source read can reuse
    -- them. The captured owners restore declarations only, never runtime state.
    for retained in prepared.toArray ++ prefix do retained.ensureDeclarations
    let attempted ← executionEntered.get
    let conclusions := (prepared.map (·.conclusions)).getD #[]
    let proposition := (prepared.map (·.proposition)).getD ""
    let observations := (prepared.map unobservedChildren).getD #[]
    -- A use of a name whose own definition did not read has the outcome of that definition.
    if let some (name, definition) := session.unread.find? fun (name, _) =>
        CasCatalogue.Exception.isUnknownSourceName error name then
      return { outcome := definition.withDetail
                 s!"the definition of {name} did not read: {definition.detail}",
               session, attempted, conclusions, proposition, observations }
    -- A definition that did not read declares no name. Its declared name is kept with its outcome.
    let session := match definedName? statement with
      | some name => { session with unread := session.unread.push (name, outcome) }
      | none => session
    -- Native dependency validation names the same stable binding. Preserve its original
    -- failure kind and cause rather than relabeling an unavailable computation as a gap.
    if let some (_, name, definition) := session.unavailable.find? fun (id, _, _) =>
        missingValueOf error id then
      return {
        outcome := definition.withDetail s!"{name} has no computed value: {definition.detail}"
        session
        attempted
        conclusions
        proposition
        observations
      }
    return { outcome, session, attempted, conclusions, proposition, observations }
  let reading ← try session.source.readStatementObserved statement
    catch error => return ← failed error none #[]
  match reading with
  | .failed error items =>
    let (observed, prefix) ← observeReadFailure session.source items
    let run ← failed error none prefix
    let observations := observed.map fun (isFailure, observation) =>
      if isFailure then { observation with outcome := some run.outcome } else observation
    return { run with
      conclusions := observations.flatMap (·.conclusions)
      observations }
  | .complete source =>
    let prepared ← try retainStatement session.source source
      catch error => return ← failed error none #[]
    try
      let needsCell ← match source with
        | .settled _ | .assumption _ | .inspection _ => pure false
        | .proved proposition _ => proofRequiresObservation session proposition
        | _ => pure true
      if !needsCell then
        executionEntered.set true
        return (← executePrepared session none prepared).run
      let transaction ← CellTransaction.begin session.kernel.ledger
      let result ← try
          executionEntered.set true
          let result ← executePrepared session (some transaction) prepared
          Core.checkSystem "source statement publication"
          -- All throwing result/conclusion construction precedes the only commit.
          if result.publish then commit transaction
          pure result
        finally
          discard <| (transaction.abort : BaseIO Bool)
      unless result.publish do
        if source matches .contextBlock _ then
          saved.restore
          prepared.ensureDeclarations
      return { result.run with published := result.publish }
    catch error =>
      failed error (some prepared) #[]

end CasRuntime
