module

public import CasRuntime.Kernel
public import CasCompiler.ReadSession
public import CasCatalogue.Evaluation
public import CasCompiler.SourceSnapshot
import CasCompiler.SourceCarrier

public section

namespace CasRuntime

open Lean Meta Elab Term CasCompiler CasCatalogue

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

def Outcome.stratum? : Outcome → Option String
  | .unsupportedSource _ => some "unsupportedSource"
  | .invalid _ => some "invalid"
  | .ambiguous _ => some "semanticAmbiguity"
  | .noImplementation _ => some "noImplementation"
  | .ambiguousRealization _ => some "ambiguousRealization"
  | .unavailable _ => some "unavailable"
  | .malformed _ => some "malformed"
  | _ => none

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

structure KernelSession where
  private mk ::
  kernel : Kernel
  source : SourceSession

  computationOnly : Bool
  private bound : Std.HashMap BindingId ValueBinding

  private observed : Std.HashSet BindingId := {}

  private unavailable : Array (BindingId × Name × Outcome) := #[]

  private unread : Array (String × Outcome) := #[]
  private cumulativeSetupMilliseconds : Nat := 0

def installedManifest : IO (Option System.FilePath) := do
  let path : System.FilePath ← match ← IO.getEnv "CAS_LEAVES" with
    | some leaves =>
      let leaves : System.FilePath := leaves
      pure (if leaves.extension == some "json" then leaves else leaves / manifestFile)
    | none => pure ((".lake" / "packages" / "cas_leaves" : System.FilePath) / manifestFile)
  return if ← path.pathExists then some path else none

opaque KernelSession.start (manifest : Option System.FilePath := none)
    (computationOnly : Bool := false) (timeoutMs : UInt32 := 600000)
    (profile : Option Json := none) (preparationStarted? : Option Nat := none) :
    MetaM KernelSession := do
  let started ← match preparationStarted? with
    | some started => pure started
    | none => IO.monoMsNow
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
  let kernel ← Kernel.load owners manifest profile timeoutMs
  let source ← SourceSession.empty owners.identities
  discard <| kernel.log.write #[] "session.prepared" <| Json.mkObj [
    ("sourceFile", toJson (← getFileName)),
    ("startedMonotonicMilliseconds", toJson started),
    ("milliseconds", toJson ((← IO.monoMsNow) - started))]
  return ⟨kernel, source, computationOnly, {}, {}, #[], #[], 0⟩

opaque KernelSession.close (session : KernelSession) : IO Unit := session.kernel.close

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

def KernelSession.value? (session : KernelSession) (id : BindingId) : Option ValueBinding :=
  session.bound[id]?

def KernelSession.setupMilliseconds (session : KernelSession) : Nat :=
  session.cumulativeSetupMilliseconds

def KernelSession.withSetupMilliseconds (session : KernelSession) (milliseconds : Nat) :
    KernelSession :=
  { session with cumulativeSetupMilliseconds := milliseconds }

def KernelSession.withComputationOnly (session : KernelSession) (enabled : Bool) : KernelSession :=
  { session with computationOnly := enabled }

private def commit (transaction : CellTransaction) : MetaM Unit := do
  match ← transaction.commit with
  | .ok _ => pure ()
  | .error failure => throwError "internal: the cell did not commit: {repr failure}"

private def requiresComputedObservation (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (proposition : Expr) : MetaM Bool := do
  if session.computationOnly then return true
  for index in (← selectedContextDependencies context selections proposition) do
    let some binding := context.bindings[index]?
      | throwError "a question dependency is outside its complete source context"
    if session.observed.contains binding.id then return true
  return false

private def discharged (session : KernelSession) (context : OpenContext)
    (selections : SourceSelectionScope Expr) (proposition : Expr) :
    TermElabM (Option Bool) := do
  if ← requiresComputedObservation session context selections proposition then return none
  controlAt MetaM fun run =>
    context.withOriginalSources #[proposition] fun source => run do
      let proposition ← zetaReduce source[0]!
      if proposition.hasFVar then return none
      Evaluation.decideEvaluated proposition

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

private def numeralForm? (context : OpenContext) (selections : SourceSelectionScope Expr)
    (side : Expr) : MetaM (Option Expr) := do
  let some selected := selections.findAt? context side.getAppFn | return none
  let selected ← selected.specialize side.getAppArgs
  match selected.reference with
  | some (.numeral _) => return some selected.value
  | _ => return none

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

private def compare (session : KernelSession) (transaction : CellTransaction)
    (context : OpenContext) (selections : SourceSelectionScope Expr)
    (left right : Expr) (sourceSnapshot : Option Json) :
    MetaM Outcome := do
  let literals ← #[left, right].mapM fun side => do
    if let some literal ← literalForm? context selections side then return some literal
    numeralForm? context selections side

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

private partial def underBindings : Expr → Expr
  | .letE _ _ value body _ => underBindings (body.instantiate1 value)
  | .mdata data body => .mdata data (underBindings body)
  | expression => expression

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

structure StatementObservation where
  item : TSyntax `cas_item
  attempted : Bool
  outcome : Option Outcome := none
  proposition : String := ""
  conclusions : Array SourceConclusion := #[]
  milliseconds : Nat := 0
  dispatches : Array Registration := #[]

structure StatementRun where
  outcome : Outcome
  session : KernelSession

  attempted : Bool := true
  proposition : String := ""

  conclusions : Array SourceConclusion := #[]

  inspectionOutput : Array String := #[]
  observations : Array StatementObservation := #[]
  published : Bool := false

def statementHeartbeats : Nat := 50000000

private def definedName? (statement : TSyntax `cas_stmt) : Option String :=
  let arguments := statement.raw.getArgs
  match arguments[0]?, arguments[1]? with
  | some (Syntax.atom _ "let"), some name =>
    if name.isIdent then some name.getId.toString else none
  | _, _ => none

private structure StagedStatement where
  run : StatementRun
  publish : Bool

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

  | some .holds => { observation with outcome := none }
  | _ => observation

private def proofRequiresObservation (session : KernelSession) (proposition : SourceTerm) :
    MetaM Bool :=
  session.source.withTerm proposition fun context selections expression =>
    requiresComputedObservation session context selections expression

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

private def preparedConclusions (session : SourceSession) (statement : SourceStatement) :
    MetaM (Array SourceConclusion) := do
  match statement with
  | .definition _ value | .question value | .implemented value =>
    return #[← session.conclusion #[value]]
  | .settled values => return #[← session.conclusion values]
  | .proved proposition proof => return #[← session.conclusion #[proposition] (some proof)]
  | .assumption _ | .inspection _ | .contextBlock _ => return #[]

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

    return ⟨{ outcome := .holds, session := { session with source := next } }, false⟩
  | .inspection scope =>

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

          if (← unsuppliedParameter? session context selections expression).isSome then
            return .ok none
          if let some outcome ← failedComputation session context selections expression then
            return .error outcome
          return .ok (some (← session.evaluateInContext transaction context expression
            sourceSnapshot selections))
      catch error =>

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

          requireSuppliedParameters session context selections asked
          let asked := underBindings asked
          match asked.consumeMData.eq? with
          | some (type, left, right) =>
            match ← truthCase? type left right with
            | some proposition => decideComputed session transaction context selections proposition sourceSnapshot
            | none => compare session transaction context selections left right sourceSnapshot
          | none => decideComputed session transaction context selections asked sourceSnapshot

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
        ("startedMonotonicMilliseconds", toJson start),
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

              let outcome ← Outcome.ofException error
              let outcome := match current.unavailable.find? (fun (id, _, _) => missingValueOf error id) with
                | some (_, name, definition) => definition.withDetail
                    s!"{name} has no computed value: {definition.detail}"
                | none => outcome
              pure (⟨{
                outcome
                session := current
                conclusions := child.conclusions
                proposition := child.proposition
              }, false⟩ : StagedStatement)
          CasTools.Diagnostics.emit "statement.child.finished" <| Json.mkObj [
            ("kind", toJson result.run.outcome.kind),
            ("fails", toJson result.run.outcome.fails),
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
        let file ← getFileName
        CasTools.Diagnostics.emit "statement.scope.stopped" <| Json.mkObj [
          ("failedChild", toJson entry), ("failedOrdinal", toJson index),
          ("skipped", toJson <| (items.drop (index + 1)).mapIdx fun offset (item, _) =>
            Json.mkObj [("ordinal", toJson (index + 1 + offset)),
              ("position", SourceSnapshot.spanJson
                ⟨file, item.raw.getPos?, item.raw.getTailPos?⟩)])]
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

    return ⟨{
      outcome := .holds
      session
      proposition
      conclusions
      inspectionOutput := output, observations }, true⟩

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

    for retained in prepared.toArray ++ completedItems do retained.ensureDeclarations
    let attempted ← executionEntered.get
    let conclusions := (prepared.map (·.conclusions)).getD #[]
    let proposition := (prepared.map (·.proposition)).getD ""
    let observations := (prepared.map unobservedChildren).getD #[]

    if let some (name, definition) := session.unread.find? fun (name, _) =>
        CasCatalogue.Exception.isUnknownSourceName error name then
      return { outcome := definition.withDetail
                 s!"the definition of {name} did not read: {definition.detail}",
               session, attempted, conclusions, proposition, observations }

    let session := match definedName? statement with
      | some name => { session with unread := session.unread.push (name, outcome) }
      | none => session

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

opaque KernelSession.run (session : KernelSession) (statement : TSyntax `cas_stmt)
    (owningCell : Option CellTransaction := none) (started? : Option Nat := none) :
    TermElabM StatementRun := do
  let started ← match started? with
    | some started => pure started
    | none => IO.monoMsNow
  let log := session.kernel.log
  let parents := match ← CasTools.Diagnostics.current? with
    | some active => if active.log.session == log.session then active.parents else #[]
    | none => #[]
  let entry ← log.write parents "statement.started" <| Json.mkObj [
    ("source", toJson (statement.raw.reprint.getD "")),
    ("startedMonotonicMilliseconds", toJson started),
    ("cumulativeSetupMilliseconds", toJson session.cumulativeSetupMilliseconds),
    ("position", SourceSnapshot.spanJson ⟨← getFileName,
      statement.raw.getPos?, statement.raw.getTailPos?⟩)]
  let finished ← IO.mkRef false
  CasTools.Diagnostics.withScope { log, parents := parents.push entry } do
    try
      let run ← session.runCore statement owningCell
      let retained := run.session.source.context.entries.filter fun binding =>
        !(session.source.context.entries.any (·.id == binding.id))
      let milliseconds := (← IO.monoMsNow) - started
      let retainsSetup := decide (run.session.source.context.entries.size > session.source.context.entries.size)
      CasTools.Diagnostics.emit "statement.finished" <| Json.mkObj [
        ("kind", toJson run.outcome.kind), ("detail", toJson run.outcome.detail),
        ("stratum", toJson run.outcome.stratum?),
        ("fails", toJson run.outcome.fails), ("attempted", toJson run.attempted),
        ("published", toJson run.published),
        ("milliseconds", toJson milliseconds),
        ("cumulativeSetupMilliseconds", toJson session.cumulativeSetupMilliseconds),
        ("retainsSetup", toJson retainsSetup),
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
      return { run with session := { run.session with
        cumulativeSetupMilliseconds := session.cumulativeSetupMilliseconds +
          (if retainsSetup then milliseconds else 0) } }
    finally
      unless ← finished.get do
        CasTools.Diagnostics.emit "statement.interrupted" <| Json.mkObj [
          ("cumulativeSetupMilliseconds", toJson session.cumulativeSetupMilliseconds),
          ("milliseconds", toJson ((← IO.monoMsNow) - started))]

end CasRuntime
