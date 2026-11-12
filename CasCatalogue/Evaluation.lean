/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Codec
public import Lean.Elab.Tactic.Basic
public import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Lean discharge through the registered literal evaluations

A statement between images of literals is decided in Lean by the evaluations registered with the
literal forms (LC-18) and the kernel's decision. The kernel runs no proof procedure of its own:
`runProcedure` is the one runner of a registered procedure (`CasGates.KernelPurity`).
-/

open Lean Meta Elab Term

namespace CasCatalogue.Evaluation

open Decide

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
    -- A failed procedure is returned as its failure, which the caller reports.
    -- not a reading fallback: the failure is returned, never retried
    catch e => pure (Except.error (← e.toMessageData.toString))
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

/-- The registered evaluations that apply to the proposition `p`: the `evaluation` of each
registered literal form (a literal row's, a subset-literal row's) whose denotation occurs in `p`.
Each is a `meta` procedure of `lean-categories`, validated there with its row, which rewrites the
images of literals of its form under the catalogue's operations to literals, by the theorems of
its domain, and never closes a goal. -/
def evaluationsOf (state : SemanticState) (p : Expr) : Array Name :=
  let occurs (denotation : Name) : Bool := (p.find? (·.isConstOf denotation)).isSome
  (state.literals.filterMap fun form => if occurs form.denotation then form.evaluation else none)
    ++ (state.subsetLiterals.filterMap fun form =>
      if occurs form.denotation then form.evaluation else none)

/-- Whether Lean's kernel accepts a proof of the closed proposition `p` by the registered
evaluations `evaluations` and decision: the goal `p` is given to each evaluation in turn, through
the one sanctioned runner (`runProcedure`, LC-18). A closed remainder uses the existing
structural decision (`Codec.conditionProof`), retaining its complete declared types while
normalizing their presentation. Ordinary `mkDecideProof` remains available for a residue with
local hypotheses. The assembled proof is checked against the original `p` by Lean's kernel,
synchronously within `decideBudget`. Failure to construct or check a proof decides nothing. -/
def evaluatedDecides (evaluations : Array Name) (p : Expr) : TermElabM Bool := do
  let attempt : TermElabM Bool := do
    let goal ← mkFreshExprMVar p .syntheticOpaque
    let mut remaining := [goal.mvarId!]
    for evaluation in evaluations do
      let [current] := remaining | return false
      match ← runProcedure evaluation current with
      | .ok goals => remaining := goals
      -- not a reading fallback: an evaluation that fails decides nothing, and the claim is then
      -- realized, unchanged
      | .error _ => return false
    match remaining with
    | [] => pure ()
    | [residue] => residue.withContext do
        let condition ← instantiateMVars (← residue.getDecl).type
        let structural ← if condition.hasFVar || condition.hasMVar || condition.hasLevelMVar then
          pure none else Codec.conditionProof condition
        let proof ← match structural with
          | some proof => pure proof
          | none => mkDecideProof condition
        residue.assign proof
    | _ => return false
    let proof ← instantiateMVars goal
    if proof.hasMVar || proof.hasLevelMVar || proof.hasSorry then return false
    kernelAccepts p proof
  withCurrHeartbeats <|
    withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := decideBudget * 1000 }) <|
      -- not a reading fallback: a proposition the evaluations and decision do not settle is not
      -- decided by Lean; the claim is then realized, unchanged
      tryCatchRuntimeEx attempt fun _ => pure false

/-- The proposition `p` decided in Lean: `some true` when the kernel accepts its proof by the
registered evaluations that apply to it (`evaluationsOf`, then `extra`) and decision
(`evaluatedDecides`), `some false` when it accepts one of `¬p`, `none` otherwise. -/
def decideEvaluated (p : Expr) (extra : Array Name := #[]) : TermElabM (Option Bool) := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLevelMVar then return none
  let evaluations := extra ++ evaluationsOf (← semanticState) p
  if ← evaluatedDecides evaluations p then return some true
  if ← evaluatedDecides evaluations (mkNot p) then return some false
  return none

end CasCatalogue.Evaluation
