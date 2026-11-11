module

public import CasRuntime.Kernel
public import CasCompiler.Read
public import CasCatalogue.Decide

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
    ← SourceSession.empty owners.identities, computationOnly, {}⟩

opaque KernelSession.close (session : KernelSession) : IO Unit := session.kernel.close

/-- The retained value of a source declaration, when it has computational content. -/
def KernelSession.value? (session : KernelSession) (id : BindingId) : Option ValueBinding :=
  session.bound[id]?

private def commit (transaction : CellTransaction) : MetaM Unit := do
  match ← transaction.commit with
  | .ok _ => pure ()
  | .error failure => throwError "internal: the cell did not commit: {repr failure}"

/-- Decide the closed proposition in Lean, after substituting the session's definitions.
A statement about a declaration with a retained computed value is a statement about that
actual value, so it is compared and not discharged from the definition. -/
private def discharged (session : KernelSession) (context : OpenContext) (proposition : Expr) :
    MetaM (Option Bool) := do
  let retained := context.bindings.any fun binding =>
    (session.bound[binding.id]?).isSome && proposition.containsFVar binding.expression.fvarId!
  if retained || session.computationOnly then return none
  let proposition ← zetaReduce proposition
  if proposition.hasFVar then return none
  Decide.decideProp proposition

/-- Compare two computed candidates of one source type as retained scalar data.
The comparison reads the actual returned packets at their source type and decides equality
of those values in Lean's kernel. It is an observation of candidates, not a proof. -/
private def compare (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (left right : Expr) : MetaM Outcome := do
  let mut values := #[]
  for side in #[left, right] do
    let binding ← session.kernel.run transaction context session.bound side
    let graph ← transaction.view
    let some packet ← IO.ofExcept <| (graph.packet? binding).mapError IO.userError
      | return .gap "the computed value is retained by its provider and has no scalar comparison"
    let role ← SourceLayout.ofTerm (← context.close side)
    let some value ← ScalarLiteral.read role packet
      | return .gap s!"the computed value {packet.compress} has no scalar reading at its source type"
    values := values.push (value, packet)
  let some (first, shown) := values[0]? | return .internal "the comparison lost its left value"
  let some (second, expected) := values[1]? | return .internal "the comparison lost its right value"
  match ← Decide.decideProp (← mkEq first second) with
  | some true => return .holds
  | some false => return .wrong s!"computed {shown.compress}, compared with {expected.compress}"
  | none => return .gap "equality of the computed values is not decided in Lean"

/-- The result of one statement: its outcome, the session after it and, for a question,
the proposition that the reader formed. -/
structure StatementRun where
  outcome : Outcome
  session : KernelSession
  proposition : String := ""

/-- Run one public statement through the production reader, lowerer and executor.
A definition extends the source session and retains its computed value for later statements.
A question is discharged in Lean when it is decidable there, and is otherwise computed.
Each statement is one cell: its results are published together or not at all. -/
opaque KernelSession.run (session : KernelSession) (statement : TSyntax `cas_stmt) :
    TermElabM StatementRun := do
  let saved ← saveState
  try
    match ← session.source.readStatement statement with
    | .definition next value =>
      let transaction ← CellTransaction.begin session.kernel.ledger
      let binding ← next.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let expression ← value.source.inContext context
        let type ← whnf (← inferType expression)
        if (← isProp type) || type.isSort then return none
        return some (← session.kernel.run transaction context session.bound expression)
      commit transaction
      let some entry := next.context.entries.back?
        | throwError "internal: a source definition added no declaration"
      let bound := match binding with
        | some binding => session.bound.insert entry.id binding
        | none => session.bound
      return { outcome := .holds, session := { session with source := next, bound } }
    | .question proposition =>
      let transaction ← CellTransaction.begin session.kernel.ledger
      let (outcome, shown) ← session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let asked ← proposition.source.inContext context
        let shown := toString (← ppExpr asked)
        let outcome ← match ← discharged session context asked with
          | some true => pure .holds
          | some false => pure (.wrong "Lean decides the negation of the statement")
          | none =>
            match asked.eq? with
            | some (_, left, right) => compare session transaction context left right
            | none => pure (.gap "the statement is not an equality of computed values")
        return (outcome, shown)
      commit transaction
      return { outcome, session, proposition := shown }
  catch error =>
    let outcome ← Outcome.ofException error
    saved.restore
    return { outcome, session }

end CasRuntime
