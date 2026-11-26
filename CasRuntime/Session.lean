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
  | unsupportedSource (reason : String)
  | noImplementation (reason : String)
  | ambiguousRealization (reason : String)
  | unavailable (reason : String)
  | malformed (reason : String)
  | invalid (reason : String)
  | ambiguous (reason : String)
  | internal (reason : String)
  deriving Inhabited, Repr

def Outcome.kind : Outcome → String
  | .holds => "holds"
  | .wrong _ => "wrong"
  | .gap _ | .unsupportedSource _ | .noImplementation _ | .ambiguousRealization _ => "gap"
  | .unavailable _ => "unavailable"
  | .malformed _ => "malformed"
  | .invalid _ => "invalid"
  | .ambiguous _ => "ambiguous"
  | .internal _ => "internal"

def Outcome.detail : Outcome → String
  | .holds => ""
  | .wrong message | .gap message | .unsupportedSource message
  | .noImplementation message | .ambiguousRealization message
  | .unavailable message | .malformed message
  | .invalid message | .ambiguous message | .internal message => message

/-- The same kind of outcome with another detail. An outcome that holds has no detail. -/
def Outcome.withDetail : Outcome → String → Outcome
  | .holds, _ => .holds
  | .wrong _, detail => .wrong detail
  | .gap _, detail => .gap detail
  | .unsupportedSource _, detail => .unsupportedSource detail
  | .noImplementation _, detail => .noImplementation detail
  | .ambiguousRealization _, detail => .ambiguousRealization detail
  | .unavailable _, detail => .unavailable detail
  | .malformed _, detail => .malformed detail
  | .invalid _, detail => .invalid detail
  | .ambiguous _, detail => .ambiguous detail
  | .internal _, detail => .internal detail

def Outcome.fails (outcome : Outcome) : Bool :=
  !(outcome matches .holds | .gap _ | .noImplementation _ | .ambiguousRealization _ | .unavailable _)

/-- Preserve actual released failure strata separately from suite outcome kinds. -/
def Outcome.stratum? : Outcome → Option String
  | .unsupportedSource _ => some "unsupportedSource"
  | .invalid _ => some "invalid"
  | .ambiguous _ => some "semanticAmbiguity"
  | .noImplementation _ => some "noImplementation"
  | .ambiguousRealization _ => some "ambiguousRealization"
  | .unavailable _ => some "unavailable"
  | .malformed _ => some "malformed"
  | _ => none

/-- Classify a reader ambiguity, an unfinished source form or a stratified failure.
An exception without a stratum is an internal failure, never mathematical invalidity. -/
def Outcome.ofException (error : Exception) : MetaM Outcome := do
  let message ← error.toMessageData.toString
  if CasCatalogue.Exception.isSemanticAmbiguity error then return .ambiguous message
  if CasCatalogue.Exception.isUnsupportedSource error then return .unsupportedSource message
  return match CasCatalogue.Exception.stratum? error with
    | some .invalid => .invalid message
    | some .semanticAmbiguity => .ambiguous message
    | some .noImplementation => .noImplementation message
    | some .ambiguousRealization => .ambiguousRealization message
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

/-- Retained source declarations and the selected kernel belong to the
Environment, not a process-global name or completed-value heap. -/
private initialize sessionExtension : EnvExtension (Option KernelSession) ←
  registerEnvExtension (pure none)

private initialize activeExtension : EnvExtension (Option CellTransaction) ←
  registerEnvExtension (pure none)

def KernelSession.current? : CoreM (Option KernelSession) :=
  return sessionExtension.getState (← getEnv)

def KernelSession.install (session : KernelSession) : CoreM Unit :=
  modifyEnv (sessionExtension.setState · (some session))

def KernelSession.active? : CoreM (Option CellTransaction) :=
  return activeExtension.getState (← getEnv)

def KernelSession.setActive (transaction : Option CellTransaction) : CoreM Unit :=
  modifyEnv (activeExtension.setState · transaction)

def KernelSession.clear : CoreM Unit := do
  modifyEnv (sessionExtension.setState · none)
  KernelSession.setActive none
  SessionSnapshot.clear

def KernelSession.fork (session : KernelSession) : BaseIO KernelSession :=
  return { session with kernel := ← session.kernel.fork }

/-- The retained value of a source declaration, when it has computational content. -/
def KernelSession.value? (session : KernelSession) (id : BindingId) : Option ValueBinding :=
  session.bound[id]?

private def commit (transaction : CellTransaction) : MetaM Unit := do
  match ← transaction.commit with
  | .ok _ => pure ()
  | .error failure => throwError "internal: the cell did not commit: {repr failure}"

/-- A question depending on an observed computation concerns its actual value, including
through aliases and captured definitions. Computation-only sessions use that observation path
for every proposition. Both native declarations and their exact typed selections participate. -/
private def requiresComputedObservation (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (proposition : Expr) : MetaM Bool := do
  if session.computationOnly then return true
  for index in (← selectedContextDependencies context selections proposition) do
    let some binding := context.bindings[index]?
      | throwError "a question dependency is outside its complete source context"
    if session.observed.contains binding.id then return true
  return false

/-- Decide an eligible closed source proposition through the existing registered literal
evaluations and kernel decision. Supplied local evidence uses the same observation policy
without requiring its proposition to be closed. -/
private def discharged (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (proposition : Expr) :
    TermElabM (Option Bool) := do
  if ← requiresComputedObservation session context selections proposition then return none
  controlAt MetaM fun run =>
    context.withOriginalSources #[proposition] fun source => run do
      let proposition ← zetaReduce source[0]!
      if proposition.hasFVar then return none
      Evaluation.decideEvaluated proposition

/-- Follow only the retained source bindings' declared dependencies. A failed computation
keeps its outcome by BindingId; later executable uses do not lower its definition again.
Mathematical questions may still be discharged from their source before this execution gate.
The explicit selected records retain dependencies behind opaque source binders. -/
private def failedComputation (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (expression : Expr) : MetaM (Option Outcome) := do
  for index in ← selectedContextDependencies context selections expression do
    let some binding := context.bindings[index]?
      | throwError "internal: a source dependency is outside its retained context"
    if let some (_, name, outcome) := session.unavailable.find? fun (id, _, _) =>
        id == binding.id then
      CasTools.Diagnostics.emit "dependency.unavailable" <| Json.mkObj [
        ("binding", ContextSnapshot.bindingJson binding.id),
        ("name", toJson (name.toString (escape := false))),
        ("kind", toJson outcome.kind), ("stratum", toJson outcome.stratum?),
        ("detail", toJson outcome.detail)]
      return some (outcome.withDetail s!"{name} has no computed value: {outcome.detail}")
  return none

/-- The literal value of a side that is a registered literal form's denotation `denote L`.
Source: LiteralEntry, "a statement comparing a computed value with a literal compares it
with this denotation". -/
private def literalForm? (context : OpenContext) (selections : SourceSelectionScope Expr)
    (side : Expr) : MetaM (Option Expr) := do
  let side ← match selections.findAt? context side.getAppFn with
    | some selected =>
      let selected ← selected.specialize side.getAppArgs
      match selected.reference with
      | some (.literal _) => pure selected.value
      | _ => pure side
    | none => pure side
  let side := side.consumeMData
  let .const name _ := side.getAppFn | return none
  unless (← semanticState).literals.any (·.denotation == name) do return none
  return side.getAppArgs.back?

/-- A side that the reader formed as a registered numeral (NumeralEntry). It is compared as its
own term: deciding that a computed value equals a numeral evaluates a closed proposition, which
the kernel may do; it does not compute the numeral's image as data (constitution C22). -/
private def numeralForm? (context : OpenContext) (selections : SourceSelectionScope Expr)
    (side : Expr) : MetaM (Option Expr) := do
  let some selected := selections.findAt? context side.getAppFn | return none
  let selected ← selected.specialize side.getAppArgs
  match selected.reference with
  | some (.numeral _) => return some selected.value
  | _ => return none

/-- Exact unsupplied formal parameters of this source, including dependencies through
native types and definitions. Hypotheses/dictionaries remain formal; no value is selected by
its name or by conversion of its carrier. -/
private def unsuppliedParameter? (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (expression : Expr) : MetaM (Option LocalBinding) := do
  for index in (← selectedContextDependencies context selections expression) do
    let some binding := context.bindings[index]?
      | throwError "a formal dependency is outside its complete source context"
    if binding.role == .parameter && !session.bound.contains binding.id then
      return some binding
  return none

private def requireSuppliedParameters (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (expression : Expr) : MetaM Unit := do
  if let some binding ← unsuppliedParameter? session context selections expression then
    let name ← binding.expression.fvarId!.getUserName
    throwStratum .noImplementation (MessageData.tagged (missingValueTag binding.id)
      m!"the abstract parameter {name} has no supplied runtime value")

/-- Carry each visible source binding's actual displayed scope into the next execution.
The public source telescope remains unchanged; transient producer binders enter only this
native continuation, through their original identities and authoritative parameter tables. -/
private def KernelSession.evaluateInContext (session : KernelSession)
    (transaction : CellTransaction) (context : OpenContext) (expression : Expr)
    (sourceSnapshot : Option Json) (selections : SourceSelectionScope Expr) : MetaM ValueBinding := do
  let graph ← transaction.view
  let mut bound : Std.HashMap BindingId ValueBinding := {}
  let mut values : Array ValueBinding := #[]
  for source in context.bindings do
    if let some value := session.bound[source.id]? then
      bound := bound.insert source.id value
      values := values.push value
  let rec visit (remaining : List ValueBinding) (context : OpenContext)
      (bound : Std.HashMap BindingId ValueBinding) (selections : SourceSelectionScope Expr) :
      MetaM ValueBinding := do
    match remaining with
    | [] => session.kernel.run transaction context bound expression sourceSnapshot selections
    | value :: rest =>
      withBindingContext graph context bound value fun context bound => do
        let mut selections ← SourceSelectionScope.merge selections
          (← value.role.selections.inContext context)
        if value.admittedInterface?.isSome then
          selections ← SourceSelectionScope.merge selections
            (← value.nativeRole.selections.inContext context)
        visit rest context bound selections
  visit values.toList context bound selections

private def packetOf (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (selections : SourceSelectionScope Expr)
    (side : Expr) (sourceSnapshot : Option Json) :
    MetaM (Except String Json) := do
  let binding ← session.evaluateInContext transaction context side sourceSnapshot selections
  let graph ← transaction.view
  match ← IO.ofExcept <| (graph.packet? binding).mapError IO.userError with
  | some packet => return .ok packet
  | none => return .error "the computed value is retained by its provider and has no scalar comparison"

/-- Compare two computed candidates of one source type as retained scalar data.
The comparison reads the actual returned packets at their source type, or at the registered
literal type when one side is a literal form, and decides equality of those values in Lean's
kernel. It is an observation of candidates, not a proof. -/
private def compare (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (selections : SourceSelectionScope Expr)
    (left right : Expr) (sourceSnapshot : Option Json) :
    MetaM Outcome := do
  let literals ← #[left, right].mapM fun side => do
    if let some literal ← literalForm? context selections side then return some literal
    numeralForm? context selections side
  -- Obtain every actual result in the original operational scope. The mathematical
  -- observation below receives these packets; no source body supplies their values.
  let mut packets : Array (Option Json) := #[]
  for side in #[left, right], literal in literals do
    if literal.isSome then
      packets := packets.push none
      continue
    let packet ← match ← packetOf session transaction context selections side sourceSnapshot with
      | .ok packet => pure packet
      | .error reason => return .gap reason
    packets := packets.push (some packet)
  let sources := (#[left, right].zip literals).map fun (side, literal) => literal.getD side
  -- An observed value used as a dependent type parameter remains its actual candidate.
  -- Its mathematical definition cannot close a scalar representation on that candidate's
  -- behalf. Such an open dependent representation keeps the existing non-scalar outcome.
  for source in sources do
    for index in ← selectedContextDependencies context selections (← inferType source) do
      let some binding := context.bindings[index]?
        | return .internal "the scalar type lost an original source dependency"
      if session.observed.contains binding.id then
        return .gap "the computed value has no scalar reading at its dependent type"
  context.withOriginalSources sources fun native => do
    let mut reading : Option Expr := none
    for source in native, literal in literals do
      if literal.isSome && reading.isNone then reading := some (← inferType source)
    let mut values := #[]
    for source in native, literal in literals, packet in packets do
      if literal.isSome then
        values := values.push (source, toString (← ppExpr source))
        continue
      let some packet := packet
        | return .internal "the scalar observation lost its actual returned packet"
      -- The original native type constrains only this supplied scalar representation.
      -- Neither the mathematical source expression nor its reduction becomes its value.
      let value ← try
          let type ← match reading with
            | some type => pure type
            | none => inferType source
          ScalarLiteral.readAt type packet
        catch error =>
          return .malformed s!"{packet.compress}: {← error.toMessageData.toString}"
      let some value := value
        | return .gap s!"the computed value {packet.compress} has no scalar reading at its type"
      values := values.push (value, packet.compress)
    let some (first, shown) := values[0]? | return .internal "the comparison lost its left value"
    let some (second, expected) := values[1]? | return .internal "the comparison lost its right value"
    let proposition ← zetaReduce (← mkEq first second)
    match ← Decide.decideProp proposition with
    | some true => return .holds
    | some false => return .wrong s!"computed {shown}, compared with {expected}"
    | none => return .gap "equality of the computed values is not decided in Lean"

/-- Observe a question through its original native proposition. Published predicates return a
Boolean; registered properties retain their released Option Bool observation contract.
Negation applies logic to that answer, and an unknown property observation stays unknown. -/
private partial def decideComputed (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (selections : SourceSelectionScope Expr)
    (proposition : Expr) (sourceSnapshot : Option Json) :
    MetaM Outcome := do
  let logical := proposition.consumeMData
  if logical.isAppOfArity ``Not 1 then
    return match ← decideComputed session transaction context selections logical.appArg! sourceSnapshot with
      | .holds => .wrong "the computed predicate holds, so its negation does not"
      | .wrong _ => .holds
      | outcome => outcome
  let packet ← match ← packetOf session transaction context selections proposition sourceSnapshot with
    | .ok packet => pure packet
    | .error reason => return .gap reason
  let property := (selections.findAt? context proposition.getAppFn).any fun selection =>
    selection.application.any fun application =>
      match application.family with | .property _ => true | _ => false
  if property then
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
      | some (.family ..) | some (.formalLeg ..) | some (.creationOwner ..) | some (.retainedPoint ..)
      | some (.constructionLeg ..) => true
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
  session.source.withTerm proposition fun context selections expression =>
    requiresComputedObservation session context selections expression

/-- Encode the already retained source scope for the log, without reopening or selecting it. -/
private def sourceContextLog (source : SourceSession) : Json := Id.run do
  let build : StateM CasTools.NativeExpression.Builder Json := do
    let context ← ContextSnapshot.contextJson source.context
    let selections ← SourceSnapshot.selectionsJson source.selections
    let categories ← source.context.entries.mapM fun entry =>
      (source.categoryFor entry.id).mapM SourceSnapshot.categoryJson
    return Json.mkObj [("context", context), ("selections", selections),
      ("instances", ContextSnapshot.instancesJson source.context),
      ("categories", toJson categories),
      ("spans", toJson (source.spans.map SourceSnapshot.spanJson))]
  let (document, native) := build.run {}
  return document.setObjVal! "nativeExpressions" (native.finish #[])

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
      let reading ← match ← CasTools.Diagnostics.current? with
        | none => retainStatement current child
        | some active => do
          let entry ← active.log.write active.parents "statement.child.reading" <| Json.mkObj [
            ("source", toJson (item.raw.reprint.getD "")),
            ("position", SourceSnapshot.spanJson ⟨← getFileName,
              item.raw.getPos?, item.raw.getTailPos?⟩)]
          CasTools.Diagnostics.withScope { active with parents := active.parents.push entry } <|
            retainStatement current child
      retained := retained.push (item, reading)
      match child with
      | .definition next _ | .assumption next => current := next
      | _ => pure ()
    return .contextBlock statement retained
  | _ =>
    let conclusions ← preparedConclusions session statement
    let (kind, after) := match statement with
      | .definition next _ => ("definition", next)
      | .assumption next => ("assumption", next)
      | .question _ => ("question", session)
      | .implemented _ => ("implementation", session)
      | .proved .. => ("proof", session)
      | .settled _ => ("typing", session)
      | .inspection _ => ("inspection", session)
      | .contextBlock _ => ("context", session)
    CasTools.Diagnostics.emit "statement.read" <| Json.mkObj [
      ("kind", toJson kind), ("scope", sourceContextLog after),
      ("conclusions", toJson (conclusions.map fun conclusion => Json.mkObj [
        ("terms", toJson (conclusion.terms.map (SourceSnapshot.snapshot conclusion.context ·))),
        ("proof", toJson (conclusion.proof.map (SourceSnapshot.snapshot conclusion.context ·)))]))]
    let proposition ← match statement with
      | .question value | .implemented value =>
        value.source.withOpen fun _ expression => do
          return toString (← ppExpr expression)
      | .proved proposition _ =>
        proposition.source.withOpen fun _ expression => return (← ppExpr expression).pretty
      | .settled values => do
        let shown ← values.mapM fun value =>
          value.source.withOpen fun _ expression => do
            return toString (← ppExpr expression)
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
        session.source.withTerm value fun context selections expression => do
          let type ← whnf (← inferType expression)
          if (← isProp type) || type.isSort then return .ok none
          -- A definition over hypothetical parameters retains its complete native meaning;
          -- it does not turn a formal-variable descriptor into a concrete backend input.
          if (← unsuppliedParameter? session context selections expression).isSome then
            return .ok none
          if let some outcome ← failedComputation session context selections expression then
            return .error outcome
          return .ok (some (← session.evaluateInContext transaction context expression
            sourceSnapshot selections))
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
        CasTools.Diagnostics.emit "binding.unavailable" <| Json.mkObj [
          ("binding", ContextSnapshot.bindingJson entry.id),
          ("name", toJson (entry.userName.toString (escape := false))),
          ("kind", toJson outcome.kind), ("stratum", toJson outcome.stratum?),
          ("detail", toJson outcome.detail)]
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
      CasTools.Diagnostics.emit "binding.retained" <| Json.mkObj [
        ("binding", ContextSnapshot.bindingJson entry.id),
        ("name", toJson (entry.userName.toString (escape := false))),
        ("value", toJson (binding.map Observation.valueIdentityJson)),
        ("computed", toJson computed)]
      return ⟨{
        outcome := .holds
        session := { session with source := next, bound, observed }
        conclusions }, true⟩
  | .implemented value =>
    let sourceSnapshot := some (SourceSnapshot.snapshot session.source.observation value)
    let transaction ← requiredCell transaction
    session.source.withTerm value fun context selections expression => do
      if let some outcome ← failedComputation session context selections expression then
        return ⟨{ outcome, session, proposition := shown, conclusions }, false⟩
      requireSuppliedParameters session context selections expression
      discard <| session.evaluateInContext transaction context expression sourceSnapshot selections
      return ⟨{ outcome := .holds, session, proposition := shown, conclusions }, true⟩
  | .question proposition =>
    let sourceSnapshot := some (SourceSnapshot.snapshot session.source.observation proposition)
    let transaction ← requiredCell transaction
    session.source.withTerm proposition fun context selections asked => do
      let settled ← discharged session context selections asked
      if settled.isNone then
        if let some outcome ← failedComputation session context selections asked then
          return ⟨{ outcome, session, proposition := shown, conclusions }, false⟩
      let outcome ← match settled with
        | some true => pure .holds
        | some false => pure (.wrong "Lean decides the negation of the statement")
        | none =>
          -- Prepare the complete question before either computed side can dispatch.
          requireSuppliedParameters session context selections asked
          let asked := underBindings asked
          match asked.consumeMData.eq? with
          | some (type, left, right) =>
            match ← truthCase? type left right with
            | some proposition => decideComputed session transaction context selections proposition sourceSnapshot
            | none => compare session transaction context selections left right sourceSnapshot
          | none => decideComputed session transaction context selections asked sourceSnapshot
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
    let mut precedingSetupMilliseconds := 0
    for (item, child) in items, index in [:items.size] do
      let start ← IO.monoMsNow
      let sent := (← session.kernel.dispatches.get).size
      let log := session.kernel.log
      let parents := (← CasTools.Diagnostics.current?).map (·.parents) |>.getD #[]
      let entry ← log.write parents "statement.child.started" <| Json.mkObj [
        ("ordinal", toJson index), ("source", toJson (item.raw.reprint.getD "")),
        ("id", toJson (match item with
          | `(cas_item| test $name:ident $_:str : $_:cas_stmt) => name.getId.toString (escape := false)
          | _ => s!"(statement) {item.raw.reprint.getD ""}")),
        ("precedingSetupMilliseconds", toJson precedingSetupMilliseconds),
        ("position", SourceSnapshot.spanJson ⟨← getFileName,
          item.raw.getPos?, item.raw.getTailPos?⟩)]
      let finished ← IO.mkRef false
      let result ← CasTools.Diagnostics.withScope { log, parents := parents.push entry } do
        try
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
          CasTools.Diagnostics.emit "statement.child.finished" <| Json.mkObj [
            ("kind", toJson result.run.outcome.kind),
            ("stratum", toJson result.run.outcome.stratum?),
            ("detail", toJson result.run.outcome.detail),
            ("attempted", toJson result.run.attempted),
            ("staged", toJson result.publish),
            ("publication", toJson "pending enclosing cell"),
            ("milliseconds", toJson ((← IO.monoMsNow) - start))]
          finished.set true
          pure result
        finally
          unless ← finished.get do
            CasTools.Diagnostics.emit "statement.child.interrupted" <| Json.mkObj [
              ("milliseconds", toJson ((← IO.monoMsNow) - start))]
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
      if result.run.session.source.context.entries.size > current.source.context.entries.size then
        precedingSetupMilliseconds := precedingSetupMilliseconds + milliseconds
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
private opaque KernelSession.runCore (session : KernelSession) (statement : TSyntax `cas_stmt)
    (owningCell : Option CellTransaction := none) : TermElabM StatementRun :=
  withCurrHeartbeats <|
  withTheReader Core.Context (fun context => { context with maxHeartbeats := statementHeartbeats * 1000 }) do
  CasCompiler.setPreferredRoutes
    (session.kernel.manifest.registrations.flatMap (·.preferredRoutes))
  let saved ← saveState
  let executionEntered ← IO.mkRef false
  let failed (error : Exception) (prepared : Option RetainedStatement)
      (completedItems : Array RetainedStatement) :
      TermElabM StatementRun := do
    let outcome ← Outcome.ofException error
    saved.restore
    -- Make the checked native names present before any later source read can reuse
    -- them. The captured owners restore declarations only, never runtime state.
    for retained in prepared.toArray ++ completedItems do retained.ensureDeclarations
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
    if let some (id, name, definition) := session.unavailable.find? fun (id, _, _) =>
        missingValueOf error id then
      CasTools.Diagnostics.emit "dependency.unavailable" <| Json.mkObj [
        ("binding", ContextSnapshot.bindingJson id),
        ("name", toJson (name.toString (escape := false))),
        ("kind", toJson definition.kind), ("stratum", toJson definition.stratum?),
        ("detail", toJson definition.detail)]
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
    let (observed, completedItems) ← observeReadFailure session.source items
    let run ← failed error none completedItems
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
      -- Notebook statements stage into the already-open cell. In particular,
      -- an earlier successful command cannot commit before a later command fails.
      if let some transaction := owningCell then
        executionEntered.set true
        let result ← executePrepared session (some transaction) prepared
        Core.checkSystem "source statement staging"
        return result.run
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

/-- Log the public statement boundary, including failures before any request exists.
The recorded source position is the parser's original range; the log never changes its reading. -/
opaque KernelSession.run (session : KernelSession) (statement : TSyntax `cas_stmt)
    (owningCell : Option CellTransaction := none) : TermElabM StatementRun := do
  let started ← IO.monoMsNow
  let log := session.kernel.log
  let parents := match ← CasTools.Diagnostics.current? with
    | some active => if active.log.session == log.session then active.parents else #[]
    | none => #[]
  let entry ← log.write parents "statement.started" <| Json.mkObj [
    ("source", toJson (statement.raw.reprint.getD "")),
    ("position", SourceSnapshot.spanJson ⟨← getFileName,
      statement.raw.getPos?, statement.raw.getTailPos?⟩)]
  let finished ← IO.mkRef false
  CasTools.Diagnostics.withScope { log, parents := parents.push entry } do
    try
      let run ← session.runCore statement owningCell
      let retained := run.session.source.context.entries.filter fun binding =>
        !(session.source.context.entries.any (·.id == binding.id))
      CasTools.Diagnostics.emit "statement.finished" <| Json.mkObj [
        ("kind", toJson run.outcome.kind), ("detail", toJson run.outcome.detail),
        ("stratum", toJson run.outcome.stratum?),
        ("fails", toJson run.outcome.fails), ("attempted", toJson run.attempted),
        ("published", toJson run.published),
        ("milliseconds", toJson ((← IO.monoMsNow) - started)),
        ("retained", toJson (retained.map fun binding => Json.mkObj [
          ("binding", ContextSnapshot.bindingJson binding.id),
          ("name", toJson (binding.userName.toString (escape := false))),
          ("value", toJson ((run.session.value? binding.id).map Observation.valueIdentityJson))])),
        ("children", toJson (run.observations.map fun observation => Json.mkObj [
          ("source", toJson (observation.item.raw.reprint.getD "")),
          ("attempted", toJson observation.attempted),
          ("kind", toJson (observation.outcome.map (·.kind))),
          ("stratum", toJson (observation.outcome.bind (·.stratum?))),
          ("detail", toJson (observation.outcome.map (·.detail))),
          ("milliseconds", toJson observation.milliseconds)]))]
      finished.set true
      return run
    finally
      unless ← finished.get do
        CasTools.Diagnostics.emit "statement.interrupted" <| Json.mkObj [
          ("milliseconds", toJson ((← IO.monoMsNow) - started))]

end CasRuntime
