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
