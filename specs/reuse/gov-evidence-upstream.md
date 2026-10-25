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
- Corpus query `structure projection congrArg disequality` (2026-10-11), followed by the
  existing `Lean.getStructureInfo?`, `StructureInfo.fieldNames`, `Lean.Meta.mkProjection`
  and `Lean.Meta.mkCongrArg` implementations and their Mathlib uses. The core metadata and
  congruence builders already supply the required general mechanism.

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

## B0 refutation through structure projections (2026-10-11)

The current unit construction exposed a remaining generic gap: Codec's positive equation
assembly can traverse function wrappers, but its negative assembly could not. A wrapper need
not itself have a `DecidableEq` or `DFunLike` instance. Preserve the original complete equality
type, select its sole declared structure field with Lean's existing metadata, and construct its
projection using `Lean.Meta.mkProjection`. Reuse the existing solver on the field disequality;
`mkCongrArg` transports an assumed record equality to the contradiction. The final proof is
still checked against the original negation. The restriction to actual one-field structures
excludes any inference from unequal quotient representatives. No theorem, instance, admission
procedure, semantic row, or backend implementation is added.

## B0 reader-owned ambiguity (2026-10-11)

Corpus queries `file:\.lean$ MessageData.tagged`, `file:\.lean$ throwError hasTag`,
and `"semantic ambiguity"` found no existing reader-ambiguity classifier. The returned
ordinary error/attribute-tag uses and linguistic title do not supply this mechanism.
Lean Core already owns `MonadError`, `throwError`, `Exception.toMessageData`,
`MessageData.tagged`, and `MessageData.hasTag`. The two helpers in
`CasCatalogue/InterpretationFailure.lean` attach a reader-owned outer message tag and
recognize it through Core's context wrappers. They add no shared stratum, replacement
exception transport, mathematical declaration, or leaf protocol. The existing reader
outcome remains `ambiguous`; a semantic exception during execution remains an interpreter
error. Ownership follows architecture's interpretation stage and AGENTS's distinction
between ambiguity, invalidity, and backend failures.

## Transparent trace markers at the decision boundary (2026-10-25)

`Trace.operationResult` is the kernel's existing typed identity wrapper for retaining
distinct registered bindings as trace keys. `Lean.Meta.deltaExpand` already supplies
selective unfolding of that transparent definition. Reuse it only on the residual
proposition passed to the existing proof acquisition in `Realize.evaluatedDecides`.
The retained question, selected operation records, registered evaluator, and final
kernel check against the complete original proposition remain unchanged. This adds
no mathematical normalization rule, decision instance, provider retry, or budget.
