    let .forallE _ domain codomain _ := type | return none
    return some (domain, codomain)

/-- The one place the kernel runs a proof procedure it did not write (`CasGates.KernelPurity`,
`evidenceRunner`): `procedure`, a `meta` procedure `TacticM Unit` of `lean-categories` registered
there and validated there, a domain's evidence registered with its admission (LC-18) or a literal
form's evaluation registered with the form, run on the goal `goal`. The result is the goals it
leaves, or, when it fails or logs an error, why. The kernel names no lemma and no tactic, and runs
no proof search of its own (`specs/architecture.md`, "What must be impossible"). A failed
procedure is not recovered into `sorry`, and its attempt leaves no message behind: its failure is
reported once, by the caller. -/
def runProcedure (procedure : Name) (goal : MVarId) :
    TermElabM (Except String (List MVarId)) := do
  let procedure ← unsafe evalConst (Lean.Elab.Tactic.TacticM Unit) procedure
  let messages := (← getThe Core.State).messages
  let restore : TermElabM Unit := modifyThe Core.State fun st => { st with messages }
  let outcome ← withoutErrToSorry <| Term.withoutErrToSorry do
    try
      let remaining ← Term.withSynthesize (postpone := .no) <|
        Lean.Elab.Tactic.run goal procedure
      pure (Except.ok remaining : Except String (List MVarId))
    -- Ordinary evidence rejection is returned for the caller to report. Internal
    -- failures and existing failure tags retain their identity and original stage.
    -- not a reading fallback: a rejected proof is returned, never retried
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
          pure (Except.error (← error.toMessageData.toString))
  let logged := (← getThe Core.State).messages.hasErrors && !messages.hasErrors
  match outcome with
  | .error message =>
      restore
      return .error message
  | .ok remaining =>
      if logged then
        let errors := (← getThe Core.State).messages.toList.filter (·.severity == .error)
        let detail ← match errors.getLast? with
          | some msg => msg.data.toString
          | none => pure ""
        restore
        return .error s!"its proof has a hole: {detail}"
      return .ok remaining

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
  -- Expose only definitionally identical stored fields, retaining the selected
  -- context of a forwarded same-structure projection. The registered procedure runs
  -- once on this uniform presentation, and its result must inhabit the original p.
  let presented ← evidencePresentation (← registryState) p
  let goal ← mkFreshExprMVar presented .syntheticOpaque
  -- Respect the procedure's conversion scope for complete implicit arguments too.
  -- Lean's legacy implicit-argument mode otherwise hides definitionally equal
  -- selected dictionaries even when the registered procedure permits unfolding.
  let outcome ← withOptions
    (fun options => options.setBool `backward.isDefEq.respectTransparency false) <|
    runProcedure evidence goal.mvarId!
  match outcome with
  | .error message =>
      let detail := if message.length ≤ 300 then message else
        s!"{message.take 300}\n{String.intercalate "\n" ((message.splitOn "\n").reverse.take 8).reverse}"
      throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
        ({detail})"
  | .ok remaining =>
      let term ← instantiateMVars goal
      -- Evidence with a hole is no evidence.
      if !remaining.isEmpty || term.hasSorry || term.hasSyntheticSorry then
        throwStratum .invalid m!"{what}: {p} is not established by the evidence {evidence} \
          (its term has a hole)"
      if term.hasMVar || term.hasLevelMVar then
        throwStratum .invalid m!"{what}: {p} is not established (its term is not closed: {term})"
      let original ← mkExpectedTypeHint term p
      unless ← isTypeCorrect original do
        throwStratum .invalid m!"{what}: the evidence does not inhabit the original target {p}"
      return original

/-- The morphism `a → b` of the registered graph literal of their category with the graph `pairs`
of numerals, each an element of the set `a` or `b` is (its registered numeral, `numeralIn`). -/
def graphOf (a b : Value) (pairs : Array (Nat × Nat)) : M Value := do
