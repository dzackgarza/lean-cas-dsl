    let .forallE _ domain codomain _ := type | return none
    return some (domain, codomain)

/-- An ordinary inability to establish a fixed evidence goal can be tried under another
checked presentation. A malformed procedure result cannot authorize another attempt. -/
inductive ProcedureFailure where
  | rejected (message : String)
  | malformed (message : String)
  deriving Inhabited, Repr

def ProcedureFailure.message : ProcedureFailure → String
  | .rejected message | .malformed message => message

instance : ToMessageData ProcedureFailure where
  toMessageData failure := toMessageData failure.message

/-- The one place the kernel runs a proof procedure it did not write (`CasGates.KernelPurity`,
`evidenceRunner`): `procedure`, a `meta` procedure `TacticM Unit` of `lean-categories` registered
there and validated there, a domain's evidence registered with its admission (LC-18) or a literal
form's evaluation registered with the form, run on the goal `goal`. The result is the goals it
leaves, or, when it fails or logs an error, why. The kernel names no lemma and no tactic, and runs
no proof search of its own (`specs/architecture.md`, "What must be impossible"). A failed
procedure is not recovered into `sorry`, and its attempt leaves no message behind: its failure is
reported once, by the caller. -/
def runProcedure (procedure : Name) (goal : MVarId) :
    TermElabM (Except ProcedureFailure (List MVarId)) := do
  let procedure ← unsafe evalConst (Lean.Elab.Tactic.TacticM Unit) procedure
  let messages := (← getThe Core.State).messages
  let restore : TermElabM Unit := modifyThe Core.State fun st => { st with messages }
  let outcome ← withoutErrToSorry <| Term.withoutErrToSorry do
    try
      let remaining ← Term.withSynthesize (postpone := .no) <|
        Lean.Elab.Tactic.run goal procedure
      pure (Except.ok remaining : Except ProcedureFailure (List MVarId))
    -- Ordinary evidence rejection is returned for the caller to report. Internal
    -- failures and existing failure tags retain their identity and original stage.
    -- This runner selects no new question or procedure. Its caller may expose
    -- another checked view of this same goal after ordinary rejection only.
    catch error =>
      match error with
      | .internal .. =>
          restore
          throw error
      | .error .. =>
          if Exception.hasConflictingStrata error || Exception.isSemanticAmbiguity error ||
              (Exception.stratum? error).isSome then
            restore
            throw error
          pure (Except.error (.rejected (← error.toMessageData.toString)))
  let currentMessages := (← getThe Core.State).messages
  let newMessages := currentMessages.reportedPlusUnreported.toList.drop
    (messages.reported.size + messages.unreported.size)
  let errors := newMessages.filter (·.severity == .error)
  if let some message := errors.getLast? then
    let detail ← message.data.toString
    restore
    return .error (.malformed s!"its proof has a hole: {detail}")
  match outcome with
  | .error failure =>
      restore
      return .error failure
  | .ok remaining => return .ok remaining

/-- The evidence of the hypothesis `p` of the admission of a domain (a proposition, `IsUnit x`,
`Continuous f`, or data with at most one value, `Invertible x`, the inverse an admitted unit
keeps), established when a statement is read (LC-14) by the domain's registered evidence and by
nothing else: a `meta` proof procedure `TacticM Unit` of `lean-categories`, registered with the
domain's admission (LC-18), run through `runProcedure` on the goal `p`. The result is the closed
term the procedure built, a proof or the data, which the admission takes directly. A statement
whose obligation is not established is invalid: without the evidence, the value is not in the
domain it is used in. -/
def establish (evidence : Name) (p : Expr) (what : MessageData) : TermElabM Expr := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then
    throwStratum .invalid m!"{what}: the hypothesis {p} is not determined"
  -- Keep the supplied mathematical type as the first provider input. A stored-field
  -- view and a type-visibility view are separate, definitionally identical fallback
  -- presentations of this same obligation, never different questions or procedures.
  let attempt (presented : Expr) : TermElabM (Except String Expr) := do
    let availableEnvironment := (← getEnv).checked.get
    let outcome : Except String (Expr × Environment) ← withoutModifyingState do
      unless !presented.hasMVar && !presented.hasLevelMVar &&
          (← isTypeCorrect presented) &&
          (← withTransparency .all <| isDefEq presented p) do
        throwError "an evidence presentation changed its complete original target"
      let goal ← mkFreshExprMVar presented .syntheticOpaque
      -- Respect the procedure's conversion scope for complete implicit arguments too.
      -- Lean's legacy implicit-argument mode otherwise hides definitionally equal
      -- selected dictionaries even when the registered procedure permits unfolding.
      let result ← withOptions
        (fun options => options.setBool `backward.isDefEq.respectTransparency false) <|
        runProcedure evidence goal.mvarId!
      match result with
      | .error (.rejected message) => return .error message
      | .error (.malformed message) =>
          throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
            ({message})"
      | .ok remaining =>
          let term ← instantiateMVars goal
          -- A purported result with a hole is not ordinary rejection and is never retried.
          if !remaining.isEmpty || term.hasSorry || term.hasSyntheticSorry then
            throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
              (its term has a hole)"
          if term.hasMVar || term.hasLevelMVar then
            throwStratum .invalid m!"{what}: {p} is not established (its term is not closed: {term})"
          -- Auxiliary constants can conceal a hole or an assumption that was never
          -- available at the original question. Lean owns their transitive axiom
          -- analysis, including cached summaries of imported declarations.
          let producedKernel := (← getEnv).checked.get
          for name in term.getUsedConstants do
            if (availableEnvironment.find? name).isSome then continue
            unless (producedKernel.find? name).isSome do
              throwError "the evidence returned an unchecked auxiliary declaration"
            let assumptions ← collectAxioms name
            if assumptions.any (fun assumption => assumption == ``sorryAx ||
                (availableEnvironment.find? assumption).isNone) then
              throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
                (its auxiliary term has a hole or introduces an unprovided assumption)"
          let original ← mkExpectedTypeHint term p
          unless (← isTypeCorrect original) &&
              (← withTransparency .all <| isDefEq (← inferType original) p) do
            throwStratum .invalid m!"{what}: the evidence does not inhabit the original target {p}"
          return .ok (original, ← getEnv)
    match outcome with
    | .error message => return .error message
    | .ok (term, producedEnvironment) =>
        -- A valid proof may use a fresh auxiliary declaration. Retain the checked
        -- successful environment, but restore the caller's metavariables and messages.
        -- Recheck under that caller context before committing the environment.
        withoutModifyingState do
          setEnv producedEnvironment
          unless (← isTypeCorrect term) &&
              (← withTransparency .all <| isDefEq (← inferType term) p) do
            throwError "the evidence term depends on its discarded proof context"
        setEnv producedEnvironment
        return .ok term
  -- Restoring elaboration state does not reset the enclosing heartbeat allowance.
  -- Compute each additional view only after ordinary rejection, skipping exact duplicates.
  let originalResult ← attempt p
  if let .ok term := originalResult then return term
  let state ← registryState
  let fields ← withoutModifyingState <| evidencePresentation state p
  let fieldResult ← if fields == p then pure originalResult else attempt fields
  if let .ok term := fieldResult then return term
  let types ← withoutModifyingState <| closedTypePresentation fields
  let finalResult ← if types == fields then pure fieldResult else
    if types == p then pure originalResult else attempt types
  match finalResult with
  | .ok term => return term
  | .error message =>
      let detail := if message.length ≤ 300 then message else
        s!"{message.take 300}\n{String.intercalate "\n" ((message.splitOn "\n").reverse.take 8).reverse}"
      throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
        ({detail})"

/-- The morphism `a → b` of the registered graph literal of their category with the graph `pairs`
of numerals, each an element of the set `a` or `b` is (its registered numeral, `numeralIn`). -/
def graphOf (a b : Value) (pairs : Array (Nat × Nat)) : M Value := do
