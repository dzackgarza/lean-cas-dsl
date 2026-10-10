# Reuse record: `gov-evidence-upstream`

`ObjectEntry.evidence` (lean-categories registry, LC-18); `establish` running only registered
evidence; `CasGates.KernelPurity` with `KernelPurityProbes`.

## Queries
- Lean `Lean.Elab.Tactic.run`, `evalConst`, `isMarkedMeta`: running a registered `meta`
  `TacticM Unit`, and checking at registration that it can be run;
- Lean `mkDecide`, `mkDecideProof`: `decide` by evaluation without tactic syntax;
- Lean `Environment.getModuleIdxFor?`, `Expr.getUsedConstants`, `Parser.parserExtension`
  (category `tactic` kinds): the module of every constant a declaration uses, and tactic kinds
  among its name literals.

## Owner
- The domain's evidence: `lean-categories` (formalization author).
- Running it, and the purity gate: the kernel (orchestrator).

## New code
The gate walks compiled declarations, because a source regex cannot see names built as strings
or syntax quotations. No Lean or Mathlib linter checks which modules a library's declarations
refer to.

## B0 admitted-point equation discharge (2026-10-10)

- Corpus queries `definitional equality decidable proof normalization` and `mkDecideProof`
  added no mathematical owner. The consumed
  `LeanCategories/Foundation/Mathlib.lean` already supplies
  `CategoryTheory.ConcreteCategory.decidableEqHom`; no new equality instance is needed.
- Reuse `Decide.decisionProof` on the original complete type before Codec normalizes its
  carrier, then retain the existing normalized structural assembly and final kernel checks.
  Keep a negated equation visible to `EquationData.prove`, whose existing proof transport
  supports both equality and its negation.
- Reuse `Codec.conditionProof` for closed residual propositions in `Realize.evaluatedDecides`.
  The assembled proof is still checked against the original assertion, and the registered-only
  execution mode still skips this discharge path.
- Admitted-point parameters reuse `Realize.realizedParameters`, including the existing
  `parameterEquivalence` reconstruction and all returned payload dependencies. Mathematical
  identities continue to come from the retained, kernel-checked parameter evidence.
