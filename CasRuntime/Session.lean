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
  /-- Retained definitions whose actual producing/capture provenance requires observation.
  Source dependencies carry this policy through aliases independently of value retention. -/
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

private def commit (transaction : CellTransaction) : MetaM SessionSnapshot := do
  match ← transaction.commit with
  | .ok snapshot => pure snapshot
  | .error failure =>
    discard <| (transaction.abort : BaseIO Bool)
    Execute.completionFailure failure

/-- Decide the closed proposition in Lean, after substituting the session's definitions, by the
registered literal evaluations and the kernel's decision (`Evaluation.decideEvaluated`).
A statement depending on an observed computation is about its actual value, including through
aliases and captured definitions. Other retained source values remain eligible for proof.
Reuse: contextDependencies closes native source dependencies through their types and values. -/
private def discharged (session : KernelSession) (context : OpenContext) (proposition : Expr) :
    TermElabM (Option Bool) := do
  if session.computationOnly then return none
  for index in (← contextDependencies context.bindings proposition) do
    let some binding := context.bindings[index]?
      | throwError "a question dependency is outside its complete source context"
    if session.observed.contains binding.id then return none
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

/-- Decide a question that is not an equality from its computed truth value. A predicate is a
computation of the leaf that implements it (constitution C22); the kernel lowers the proposition,
reads the returned Boolean, and applies the proposition's negation, which is logic on that
answer, not a computation. -/
private partial def decideComputed (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (proposition : Expr) (sourceSnapshot : Option Json) :
    MetaM Outcome := do
  if proposition.isAppOfArity ``Not 1 then
    return match ← decideComputed session transaction context proposition.appArg!
        sourceSnapshot with
      | .holds => .wrong "the computed predicate holds, so its negation does not"
      | .wrong _ => .holds
      | outcome => outcome
  let packet ← match ← packetOf session transaction context proposition sourceSnapshot with
    | .ok packet => pure packet
    | .error reason => return .gap reason
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
registered generator. Reuse: Lean Expr.instantiate1, the substitution of one let. -/
private partial def underBindings : Expr → Expr
  | .letE _ _ value body _ => underBindings (body.instantiate1 value)
  | .mdata _ body => underBindings body
  | expression => expression

/-- Only an actual provider invocation establishes new computed data. A kernel completion
may merely return pure source data, so its receipt alone does not change that source policy. -/
private def invoked (snapshot : SessionSnapshot) (occurrence : RuntimeId .occurrence) : Bool :=
  match snapshot.receipt occurrence with
  | none => false
  | some receipt => match receipt.association.producer with
    | .invocation .. => true
    | .kernel => false

/-- Retain actual computations through aliases, stored fields, captures and selected dependent
references. Unused source-context values and unrelated access-parent fields are not dependencies.
Pure written code with no computed captures remains readable from its original definition.
Reuse: ordinary committed receipts, graph provenance and the existing field/application indices. -/
private partial def retainedComputation (codes : Std.HashMap (RuntimeId .program) ClosureCode)
    (snapshot : SessionSnapshot) (binding : ValueBinding) : Bool := Id.run do
  let some node := snapshot.graph.find binding.value | return false
  let computed := retainedComputation codes snapshot
  let selected := fun (indices : Array Nat) (values : Array (Option ValueBinding)) =>
    indices.any fun index => (values[index]?.bind id).any computed
  if invoked snapshot node.origin.occurrence then return true
  for application in binding.applications do
    if invoked snapshot application.association.occurrence then return true
    if selected application.association.contextDependencies application.applicationParameters ||
        selected application.association.dependencies application.arguments then return true
  for field in binding.instantiations do
    if invoked snapshot field.association.occurrence then return true
    if selected field.field.precedingDependencies field.preceding then return true
  let (dependencies, parameters) := match node.origin.application with
    | none => (node.origin.role.contextDependencies, node.origin.parameters)
    | some application => (application.contextDependencies, application.parameters)
  if selected dependencies parameters then return true
  if let some application := node.origin.application then
    if selected application.dependencies application.arguments then return true
  match node.payload.data with
  | .closure program captures =>
    if codes[program]? matches some (.family ..) then return true
    return captures.any computed
  | .ownedToken .. => return true
  | .product fields => return fields.any computed
  | .container value =>
    return (value.slots.map (·.binding) ++ value.fields.getD #[] ++ value.callable.toArray).any computed
  | .portable _ => return false

/-- The result of one statement: its outcome, the session after it and, for a question,
the proposition that the reader formed. -/
structure StatementRun where
  outcome : Outcome
  session : KernelSession
  proposition : String := ""

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

/-- Run one public statement through the production reader, lowerer and executor.
A definition extends the source session and retains its computed value for later statements.
A question is discharged in Lean when it is decidable there, and is otherwise computed.
Each statement is one cell: its results are published together or not at all. -/
opaque KernelSession.run (session : KernelSession) (statement : TSyntax `cas_stmt) :
    TermElabM StatementRun :=
  withCurrHeartbeats <|
  withTheReader Core.Context (fun context => { context with maxHeartbeats := statementHeartbeats * 1000 }) do
  -- The reading uses the declared preferred routes of the admitted registrations (C6).
  CasCompiler.setPreferredRoutes
    (session.kernel.manifest.registrations.flatMap (·.preferredRoutes))
  let saved ← saveState
  try
    match ← session.source.readStatement statement with
    | .definition next value =>
      let some entry := next.context.entries.back?
        | throwError "internal: a source definition added no declaration"
      let sourceSnapshot := some (SourceSnapshot.snapshot next value (some entry))
      next.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let expression ← value.source.inContext context
        let type ← whnf (← inferType expression)
        let formal := (← isProp type) || type.isSort
        unless formal do
          if let some outcome ← failedComputation session context expression then
            let unavailable := session.unavailable.push (entry.id, entry.userName, outcome)
            return { outcome, session := { session with source := next, unavailable } }
        let transaction ← CellTransaction.begin session.kernel.ledger
        let (binding, computed) ← try
            let binding ← if formal then pure none else
              pure (some (← session.kernel.run transaction context session.bound expression
                sourceSnapshot))
            let codes ← session.kernel.codes.get
            let published ← commit transaction
            pure (binding, binding.any (retainedComputation codes published))
          catch error =>
            -- A read definition keeps its meaning when its computation is a gap or unavailable
            -- at execution or commit (constitution C3); failed runtime data are never published.
            discard <| (transaction.abort : BaseIO Bool)
            let outcome ← Outcome.ofException error
            if outcome.fails then throw error
            let unavailable := session.unavailable.push (entry.id, entry.userName, outcome)
            return { outcome, session := { session with source := next, unavailable } }
        -- Every successfully produced value keeps its exact source binding for later inputs.
        -- Actual committed producer/capture provenance controls proof discharge separately.
        let bound := match binding with
          | some binding => session.bound.insert entry.id binding
          | none => session.bound
        let observed := if computed then session.observed.insert entry.id else session.observed
        return { outcome := .holds, session := { session with source := next, bound, observed } }
    | .settled values =>
      let shown ← session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        values.mapM fun value => do
          return toString (← ppExpr (← value.source.inContext context))
      return { outcome := .holds, session,
               proposition := s!"settled: {" and ".intercalate shown.toList}" }
    | .implemented value =>
      -- The value is computed in its own cell. A gap or a failed computation is the outcome.
      let sourceSnapshot := some (SourceSnapshot.snapshot session.source value)
      session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let expression ← value.source.inContext context
        let shown := toString (← ppExpr expression)
        if let some outcome ← failedComputation session context expression then
          return { outcome, session, proposition := shown }
        let transaction ← CellTransaction.begin session.kernel.ledger
        discard <| session.kernel.run transaction context session.bound expression sourceSnapshot
        discard <| commit transaction
        return { outcome := .holds, session, proposition := shown }
    | .question proposition =>
      let sourceSnapshot := some (SourceSnapshot.snapshot session.source proposition)
      session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let asked ← proposition.source.inContext context
        let shown := toString (← ppExpr asked)
        let settled ← discharged session context asked
        if settled.isNone then
          if let some outcome ← failedComputation session context asked then
            return { outcome, session, proposition := shown }
        let transaction ← CellTransaction.begin session.kernel.ledger
        let outcome ← match settled with
          | some true => pure .holds
          | some false => pure (.wrong "Lean decides the negation of the statement")
          | none =>
            let asked := underBindings asked
            match asked.eq? with
            | some (type, left, right) =>
              match ← truthCase? type left right with
              | some proposition =>
                decideComputed session transaction context proposition sourceSnapshot
              | none => compare session transaction context left right sourceSnapshot
            | none => decideComputed session transaction context asked sourceSnapshot
        discard <| commit transaction
        return { outcome, session, proposition := shown }
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
    -- Native dependency validation names the same stable binding. Preserve its original
    -- failure kind and cause rather than relabeling an unavailable computation as a gap.
    if let some (_, name, definition) := session.unavailable.find? fun (id, _, _) =>
        missingValueOf error id then
      let outcome := definition.withDetail
        s!"{name} has no computed value: {definition.detail}"
      return { outcome, session }
    return { outcome, session }

end CasRuntime
