## Remaining work, from the session's end state

Readiness is defined in the procedure as: **no admitted assertion stops at a request-formation gap**. On top of that, the session's own work list (K1–K14) and the leaf-interaction items were still unfinished. Closed already: K1, K4, K6, K7, K9, K10, K11.

### 1. Kernel request formation (reachable now)

| Item | What remains |
|---|---|
| **K14 formed modules** | Two concrete defects, both diagnosed but not fixed: (a) the reader rejects destructuring maps `((a, b), (c, d)) ↦ …` with "expected end of input"; (b) `typedParameter` finds **0 route candidates** for `Vec(ℤ, 2)` at `ModuleCat ↑ℤ` across `obj.sets.vectors`, `obj.modules.vectors`, `obj.additive_monoids.vectors` — suspected coercion mismatch between ℤ as ring and as commutative ring. Then run every formed positive and its protected negative. |
| **K5 `integration.normalized`** | Performance item: reading `h(0)` inside the comprehension takes 113 s, then realization exhausts heartbeats in `whnf`. Requires the rule-4 performance route, not a functional fix. |
| **K8** | Condition met in targeted reports; needs one whole-suite CI report at or after `d838691` to close. |
| **Whole-suite report at the head** | The last full evidence is CI at `adaec09` (75 holds, 65 gaps, 12 unavailable, 1 internal; 9 request-formation gaps). The branch head is `4bcd912`, ten commits later, including the limits, `integration.at_zero`, `card_product`, `prime_factors`, `sets.eq.rev_rev`, K10, K11 and the K14 diagnostic. None of that has a whole-suite report. |
| **K13's dispatch list** | At `adaec09`, 65 gaps − 9 request-formation = **56 registration gaps**, but K13 names only 26 IDs. The leaf brief needs to be reconciled with the current registration-gap set before dispatching. |

Known remaining request-formation gaps at the head: the four `series.*` IDs and `integration.normalized`. Four of the nine at `adaec09` now form requests.

### 2. Leaf side and contract

- **K13 leaf registrations**: leaf subagent at `0030ccc` had 4 of 6 sampled IDs holding end to end (derivative, `card_power_set`, `integers.sum`, `complex.re`); the rest are open. This is leaf work, not kernel work, but K3 and K14 cannot close without it.
- **Eight undeclared answer encodings** in `lean-cas-dsl-leaf-contracts` (recorded in the leaf repo's `DEFECTS.md`): fractions/irrationals, `WithBot` degrees, Kähler differentials, matrices, span results, binder request shape, the `objectProduct` apex (which the kernel itself uses in `observeEquality`), and points inside compose/mediator. A leaf cannot answer correctly for any of these until the contract declares them, and the kernel must then decode them.
- **K3 required positives** and **K14 formed positives**: both need registered execution with protected negatives; K3 additionally needs owner admission after they hold.

### 3. Blocked inputs (not kernel work)

- **Four `series.coefficient_*` IDs** — `lean-categories` has no registered object for `Series.powerSeriesTAdic R`, and no acceptance-table row names it. Someone must commission the upstream row; the kernel cannot present the object.
- **K12 (`cc-cohere`)** — upstream needs a constructor-induced action on comparison cells; until then `CoerceProbes`' lift positive stays ambiguous. The related `CasAcceptance/LiftProbes.lean:29` ambiguity follows from it.
- **K2 question preservation** — every ID is flagged "question changed"; the ledger uses an older hash format, question identities embed the `lean-categories` revision, and tonight's new trace node kinds (`objectField`, `powerObjectMap`) altered some questions. 137 readable records differ from the stored ones. This blocks K2 and needs the construction-directive-B assessment.
- **K3 admission** — owner operation, only after the positives hold.
- **`KernelPurity` gate decision** — whether `LeanCategories.Catalogue.Realization` belongs in `allowedModules`; seven probe modules are also missing from the gate's imports, and the gate fails at the branch base.

### 4. After K1–K14 (directives B and D, not this session's work)

Freeze the candidate, then the ten exit trials in both directions (new structured object, new generic operation, group-valued construction, classifier/refinement, competing routes, parameter transport, nonidentity presentation change, structured result lifting, generic application/binder, leaf replacement), the compositional arguments, the question-preservation assessment, and independent acceptance.

### 5. Housekeeping

- The owner's uncommitted `CasCatalogue/Language.lean` edit (zero-family prefilter in `toElement`) is still in the main checkout, untouched; it needs a decision to keep as a parked patch or drop it.
- `b0/kernel` is pushed at `4bcd912` but not merged to `main`; the work lives only there.
- Reports and handoff are current only as of 17:59; `HANDOFF.md` says `Latest CI report … adaec09`, which is now behind the head.

Short version: **five known request-formation gaps (four blocked upstream, one a performance item), one unmeasured head, an incomplete leaf dispatch and contract encoding set, and four owner/upstream assessments** separate the branch from "ready for leaf work" — after which the trials and acceptance still follow.
