# Journal

Process narration lives here, not in chat: what was done, what was found, what is pending and on
whom. Chat carries only what needs the owner's action or decision. Newest entry first; one entry
per working session; terse. Not an authority: rules live in their owning documents (AGENTS.md).

## 2026-10-09 (B0 authority and real-backend execution)

- Corrected `StructuredResult.complete` failure stratification: a kernel exception
  while checking the fixed formal construction no longer becomes an `.error`
  subsequently reported as a malformed backend answer. Explicit computational
  validation errors remain malformed; interpreter exceptions propagate as internal
  failures. This addresses the existing `cc-failure-strata` obligation without
  weakening the required created-cone execution.

- Added a pre-dispatch check that the diagram obtained by transporting individual
  input wires is definitionally the image of the full original diagram under
  the selected registered creation functor. Previously the full comparison was
  deferred until reconstruction, after backend execution. This is only a source
  guard; compilation and registered acceptance remain unestablished.

- The requested creation-lift pre-dispatch guard now also refuses colimit
  requests and checks the complete diagram's source category against the selected
  structural functor's registered source. Target and shape agreement alone were
  insufficient to distinguish functors with the same lower-category target.
  Source-category checking compares both complete source categorical parameters
  of the typed diagram and typed functor. A bounded owner-local Lean invocation
  produced no result before interruption; no compile claim is made. This remains
  source validation, not a completed registered computation.

- Creation-lift dispatch now checks the selected lift's kind and shape, registered
  structural functor, and target category against the lower limit row before
  sending a backend request. Previously only the lift ID's existence was checked
  at that boundary; the full checks were deferred to subsequent reconstruction.
  This is a source guard, not evidence of completed lifted execution or B0 acceptance.

- Creation-lift realization: an explicitly selected but absent lift previously
  passed through `lift?.bind` into the unlifted branch, allowing lower-category
  data to be treated as an unlifted result. `Realize.realizeFresh` now refuses
  an unknown requested lift before constructing or sending the diagram, with
  `NoImplementation`. This protects the named-lift dependency rather than
  substituting ordinary limit computation. The generic lifted execution and
  registered acceptance remain to be established.

- Launcher source boundary: `validate_source` and `submit_source` now reject
  Git symlink/submodule entries masquerading as role-permitted regular files;
  the previous path-only checks admitted these candidate trees. Added a
  committed-symlink regression for both operations and made the isolated
  test-repository commits independent of ambient Git hooks. Focused launcher
  tests: 10 passed. This is source hardening, not established `b0-authority`.

- Correction to the `b0/lifted-execution` disposition: it is based on the old
  `b0/lifted-limits` decoder and is **not** the designated consolidation source.
  The candidate `b0/reconcile-typed-question` at `cbe4f17` already routes
  a created result through `StructuredResult.complete` with an independently
  reconstructed formal upper cone, apex, and defining maps; its separate
  `StructuredResult.lift` path reconstructs checked creation evidence. Therefore
  the earlier assertion that *the consolidated mechanism* lacks an upper cone
  was false. The missing task is to validate and integrate the entire generic
  structured-result/registered-dispatch mechanism at one compatible tuple,
  especially the demanded real execution, not to transplant a partial cone from
  the obsolete branch. `37c4836` and `9c4c422` remain historical checkpoints,
  not an accepted fix or a successor to #65. No accepted mathematical records
  or proofs were changed.

- On `b0/lifted-execution`, committed `37c4836` to require the lifted upper
  apex to map to the computed lower apex under the declared functor, and
  `9c4c422` to stop presenting the lower cone as an upper universal structure.
  The lower cone's legs live in the lower category; an upper cone with defining
  maps has not been reconstructed. This is a partial source correction, not
  satisfaction of `cc-realize`, independent approval or a registered assertion.

- Current leaf-specimen coverage, measured from the separate `lean-cas-dsl-leaves`
  checkout `48a99b5`: its 22 distinct `(operation, input)` registrations contain
  **no** `finite_sets` input registration and **no** formed-lattice discriminant
  or bilinear cokernel operation. Hence the frozen `finite_sets.limit.pullback.card`
  must use the upstream creation lift plus an existing `cat.sets` registration;
  on this kernel's `Realize.realize`, `lift?` immediately returns `noImplementation`
  before sending any diagram. The three frozen `lattices.discriminant.a1–a3`
  also have no available registered computation in this specimen. These are
  concrete execution gaps under `cc-realize` / `cc-backends`, not reasons to
  change the assertions, import leaf definitions, or mark the rows complete.
  The existing `origin/b0/lifted-limits` reference contains an `alongLift`
  realization, but its lifted cone and defining-map requirements must be
  reconciled with the consolidated structured-result interface before use.

- Continued `cc-realize` at the pinned tuple (`lean_categories` `5b96a8a`,
  `cas_leaf_contracts` `5133fb8`). Two bounded, owner-local attempts to compile
  `CasCatalogue.TestSuite` advanced the dependency graph through the catalogue
  semantic registrations, including its full `LeanCategories.Catalogue` module.
  However, `CasCatalogue.Language`, `Realize`, and `TestSuite` have no compiled
  `.olean` yet. The first command exited at its 180-second bound; the second
  stopped after an extended silent compilation. Neither executed a registered
  acceptance assertion. The next executable computational boundary is the
  compiled `CasCatalogue.TestSuite` plus `CasTools.Harness`; no output of the
  independent acceptance operation exists at this tuple.
- The separately installed real Sage 10.8.12 leaf port additionally returned
  `some false` for finiteness of integers and `some true` for the realized
  `Fin 6` presentation of `Fin 2 × Z/3`. The latter is a backend-level
  representative only; it does not itself verify the semantic product or its
  structural route. These two observations remain distinct from the frozen
  suite's integrated executions.

- `b0-authority` is not enforced. The current Core2 shell has an authenticated GitHub
  credential with repository administration capability. Read-only API inspection found
  `main` governed by ruleset `24252144` (`deletion`, `non_fast_forward` only, empty
  bypass list); GitHub's branch-protection endpoint reports no branch protection.
  This session can author the evaluator and has access to a credential capable of
  changing its hosting protection. No local gate, workflow, source signature or role
  label can establish requirement 4 in this configuration. The launcher must remove
  administration and accepted-reference write capabilities from the construction
  role and supply the evaluator/accepted references from a separately controlled
  revision before independent acceptance can be claimed. No protection setting
  or credential was changed here.
- Cloned the separate `lean-cas-dsl-leaves` specimen at `48a99b5` without editing
  it; installed PassageMath's modules, combinat and GAP packages in an ignored
  local virtual environment. Over its port protocol, real GAP 4.16.1 answered
  cardinalities 64 for `(Z/4)^3`, 7 for `Z/7` and 1 for `(Z/5)^0`;
  Sage 10.8.12 answered `aleph0` for the integers and 6 for `Fin 6`.
  The Sage set-limits port answered apex sizes 6 for `Fin 2 × Z/3`, 5 for
  `Fin 2 ⊔ Fin 3`, and 3 for the specified finite-set pullback.
  These are **backend-port observations only**: they do not close any required
  assertion without admitted registered execution and kernel-side decoding
  against independently established questions.
- The first attempt to build the harness was stopped when uncached transitive
  dependencies expanded the focused target. Pinned package checkouts were
  prepared without updating the accepted mathematical revision, and Mathlib's
  precompiled cache was subsequently obtained. A focused `lake build cas-harness`
  advanced through the pinned `lean_categories` source but expanded to 7,260
  transitive native targets and was stopped rather than running an over-broad
  build. The integrated harness did not run; the required 15 assertions therefore
  have no new accepted execution results from this session.

## 2026-10-09 (B0 acceptance-inventory gate)

- Directive B's central defect is still in `CasCatalogue/Language.lean`:
  `Claim.settled` stores only an outcome and flattened `about : Array Expr`;
  `judgedTerms` reconstructs membership/containment tokens after evaluation, and
  `Realize.claimQuestion` hashes that array. Consequently this is not the preserved
  typed logical question required by directive B. The consolidated reference
  `origin/b0/construction` (`cbe4f17`) instead defines `TypedQuestion`, a structural
  `QuestionIdentity` encoder, and an `interpret` stage whose request is consumed
  by evaluation. Recover and reconcile that *generic mechanism* with the current
  main changes and its complete probes, not further fingerprint/checker patches.
  `main` and the reference diverge at `bcd08de`; a merge-tree inspection reports
  multiple overlapping changes. No candidate source was merged or accepted by
  this finding; the protected question records must not be regenerated.

- Corrected the acceptance regression reader to reject duplicate `(file, id)` results.
  Previously dictionary construction silently took the last reported outcome, permitting
  an earlier failure to disappear from the comparison. This does not establish the
  complete B0 acceptance boundary or substitute for the independent evaluator.

- Hardened the `--record` operation: it no longer treats an absent record as an empty
  authoritative baseline or reports success while existing interpretations disagree
  with the current question. It rejects orphaned recorded IDs as well. It still cannot
  establish independent admission authority: `AGENT_ROLE` remains caller supplied.

- Corrected five realization-stage catalogue inconsistency branches in `Realize.realize`
  to throw interpreter errors rather than assert mathematical invalidity. These are
  missing registered forms/categories/functors/standard cones after the semantic reader
  has already admitted a typed claim; `runAsking` classifies these errors as `internal`.
  No semantic registration or acceptance assertion was changed.

- The question permanence comparison now fails when a candidate has readable admitted
  assertions absent from the independently established question record. Previously it
  printed the missing interpretations but returned success, allowing an unrecorded
  semantic reinterpretation to pass. No candidate questions or authoritative records
  were regenerated; the acceptance author must establish these interpretations.

- The question-permanence comparison and initial recording now refuse an admitted
  assertion whose semantic question was not read. Merely including the assertion ID in
  the harness report is insufficient: an unread assertion cannot acquire an accepted
  interpretation, and the required denominator remains the full admission inventory.
  This exposes existing unread interpretations rather than promoting an incomplete
  question record to a passing comparison. Independent initial interpretation and
  structural authority isolation remain open.

- Corrected two realization-stage comparison-form mismatches in `Realize.realizeClaim`:
  they now report `noImplementation`, not semantic `invalid`. The statement was already
  read; a realization using an incompatible form does not make its mathematical
  question ill-typed. This is a focused `cc-failure-strata` source correction,
  not completion of directive B or the full required computational execution.

- Extended the question-permanence candidate check to require the admitted assertion inventory,
  reject absent or extraneous report identities, reject duplicate identities, and refuse an absent
  accepted or candidate question record. This closes silent success when the runner prunes rows or
  a missing comparison reference is treated as an empty record. The incomplete initial question
  inventory and role-variable admission authority remain unresolved under directives B and A;
  this source patch does not establish either independent authority or B0 acceptance.
- Focused checks: Python compilation, acceptance-permanence check, and diff whitespace check pass.
- Corrected `just acceptance` to supply the mandatory `--base` question record instead of
  invoking the comparator without its required arguments. This local comparison checks the
  checked-in record against the run; CI separately compares to the base checkout's record.

- Corrected the construction-source gate to reject an absent admitted assertion inventory instead of initializing an empty one. `--correct` now refuses missing assertions instead of silently deleting them. The existing role-variable authorization remains an unresolved authority defect; this patch does not confer independent admission authority.
- Focused check: `python scripts/check_acceptance_permanent.py` and `git diff --check` pass. No mathematical assertions, accepted revisions or evaluator authority changed.

## 2026-10-04 (contract reconciliation)

- Resolved contradictory construction/acceptance instructions in AGENTS, CONTRIBUTING,
  architecture and the B0 plan. Construction authors may implement judges, never accept or
  activate their own authoritative replacement; role variables and hashes confer no authority.
- #65 is the single consolidation candidate. #63/#64 are divergent reference work whose binder
  and complete lifted-result obligations remain to be reconciled. This supersedes the older
  #64 decoder-repair queue below: #65 uses a different structured-result interface; the old
  `universal := none` option is a gap, not completion.
- Permanent mathematical questions are distinct from replaceable proof/serialization artifacts.
  Independent assessment governs migrations and corrections of faulty readings; every admitted
  identity remains required. Directives A/B/C allow independent source work; D consumes their
  actual accepted inputs and the full compatible tuple.
- Scope: documentation and branch disposition only. No code, pins, acceptance records, remote
  branches or hosting settings changed; implementation and deployed protection are not established.
  Focused diff/invariant checks only, no Lean build. The no-memory section and fixed B0
  mathematical acceptance table, computational IDs and exit-trial requirements are unchanged.

## 2026-10-02 (orchestrator)

- 14:50. HANDOFF (session stopped: usage limit). Durable state for the next kernel worker:
  - `b0/lifted-limits`, lean-cas-dsl#64, head `5fd3f92`. The realized reading executes the creation
    lift: `alongLift` sends each datum of `D` along the lift's functor `U` (objects by `transport`
    along the lift's edge, morphisms as their graph in the lower graph-literal form, each checked
    to be `U` applied to the datum), decodes and checks the cone in the row's category, and takes
    the object refining the apex along exactly the lift's edge. `decodeValue` no longer searches
    refinements; no runtime `invalid`. Probe (`RegistrationProbes`): `|pullback(f', g')|` of finite
    sets holds at 3, wrong at 2. NOT YET RUN at `5fd3f92`: full build, `cas-harness --report`,
    `check_acceptance_regression.py` against a main report, `check_question_permanence.py --base`
    main's `CasAcceptance/Permanent/questions.json` (both clean at `fa80460`). Run these first.
    Expected: `finite_sets.limit.pullback.card` holds over the real leaves. Read the newest
    custodian comment on #64 before changing anything.
    Custodian on `5fd3f92` (14:47), to repair next: (1) the lifted return pairs the apex above
    with the downstairs cone in `universal`; lift the legs along `U` (checked to map to the decoded
    cone) or return `universal := none`, and check `U.obj value ≡ apex`; (2) remaining runtime
    `.invalid` throws in `realize`/`realizeClaim` (catalogue inconsistency → internal error,
    realized form mismatch → noImplementation); (3) establish that `Decide.decideProp` returns
    `none` only on genuine non-decision, not on heartbeat exhaustion; (4) supply the run results.
  - `b0/binders`, lean-cas-dsl#63 (draft), head `f805933`, worktree `.tmp/wt-binders` (its
    `.lake/build` symlinks to `/dev/shm/wt-binders-build`; rebuild if gone). Kernel findings all
    repaired (row-local refusal, reducible row matching, per-token separator, evidence goals at the
    domain with `id` hints stripped); the custodian's last review found no kernel defect. Validated
    at `f805933`: no regression over the real leaves (153; only `calculus.limit_sinc` fails).
    Blocked on (a) an independently assessed upstream binder release (pin is unassessed
    lean-categories main, which carries `kernelSincStatement`/`collapseUnits`), (b) accepted
    interpretations for the six re-read assertions. Do not move the pin, regenerate the question
    record, or restore `--transition`.
  - Recorded defect (directive B, needs the acceptance authority before landing): question
    fingerprints (`Realize.claimQuestion`) hash evidence proofs; cleaning evidence goals changed
    `calculus.limit_infinity` and `series.coefficient_{zero,two,three,four}` with no change of
    meaning.
  - Owner decisions outstanding: role isolation (private repos with one environment per role, or
    public with unenforceable blindness); finish or archive the sessions dispatched under the old
    procedure; scheduling the upstream repair of kernel-shaped evidence (accepted pin stays
    `5b96a8a`); matrix `rank` (column-module rank or McCoy rank).
- 13:05. #62 merged (initial question record, 142). Kernel fixes from its review: settled
  questions carry relation, category and the typed element, element before set (`150a124`,
  `fbd5dfd`, `998df95`); the custodian review reads the current PR description (`003103c`).
  leaves#4 merged (product, coproduct, pullback of sets over Sage). passagemath (combinat, modules,
  gap) installed in the leaves checkout's `.venv`: stage D now executes on this host. Over the real
  leaves at main: `sets.card.fin2_times_z3`, `sets.finite.fin2_times_z3`,
  `sets.card.fin2_sqcup_fin3`, `sets.limit.pullback.card` hold through registrations.
  Open required: `finite_sets.limit.pullback.card` (kernel: the realized reading sends no
  diagram along a creation lift; next kernel unit after b0-binders, which is in progress on
  `b0/binders`); `lattices.discriminant.a1–a3` (the cokernel's diagram arrow has no form;
  lean-categories#81 under review). #77/#79 reviewer replaced (it held its reviews for approval).
- 13:15. With passagemath-gap: `sets.card.z4_cubed`, `z7`, `z5_empty_power` hold over GAP. Kernel
  defect exposed by a correct leaf answer: `sets.card.square` (|A × A|, A = Fin 2 × ℤ/3) is
  malformed because the realized reading sends the realized apex of the first product (`Fin 6`)
  but decodes the second cone at the semantic diagram (`Fin 2 × ZMod 3`). Next kernel unit
  (after b0-binders, same `.limit` case as the creation-lift gap): decode a cone at the realized
  diagram and identify realized and registered presentations by the limit's uniqueness iso, never
  by assuming them equal. `finite_sets.card_product` / `card_power_set`: the leaf takes no finite
  subset literal (`unavailable`; leaf coverage, not a kernel matter).
- 11:30. lean-cas-dsl main at `72fc3ba`: settled ∈/⊆ judgements fingerprint their terms (`cd355d8`);
  the question gate compares against the base's record and treats it as append-only (custodian
  finding on #62). The #62 shared fingerprints are identical propositions (one fact asserted
  twice), not operand loss. Acceptance recorder woken to re-read and post evidence on #62.
- lean-categories: #78 and #80 have independent reviews requesting changes; their authors were
  woken. The #77/#79 reviewer had posted nothing; woken to post. leaves#3 merged
  (power-set cardinality). Contract `41c08c6`, `e292368` state the wire encoding the leaf had to
  infer, diagrams and cones included: a limit row is registered on the diagrams of its category
  (`cat.sets`) and answers its cone, which the kernel rebuilds and checks (Realize, `.limit`;
  probes `registration_limits.json`). The leaf's "limits are not registrable" was the missing
  contract text. Leaf author messaged to register product, pullback, coproduct; formalization
  session_01RMwnyaFqMTvbk9S1jkbaut assesses the reported form defect independently (the
  cokernel's diagram arrow `L → L♯` has no form, by the kernel's gap text).
- Dispatches corrected against architecture.md "Authors" (a dispatch carries role, boundary and a
  pointer to or quotation of the owner's requirement; no content). Earlier briefs that carried
  assertions/expected values, kernel goal terms, row designs, or a kernel-repo read for the leaf
  author were stopped and replaced. Live: acceptance session_01Q9YWsNTV1zVddKmp7MRsbw,
  formalization session_01DPvLuRKBcdBVf1shacNovT, leaf session_014DrMxP5s6WX9xcYZRUrjyW.
  Correction: cloud sessions are messaged by a Routine bound to the session, fired
  (AGENTS.md, dispatch rule); SendMessage reaches only listed live peers. Used 10:46 to wake the
  #78 and #80 authors on their reviews and the #77/#79 reviewer, who had posted nothing.
- gov-meaning-permanence: `c5aa80e` on `b0/meaning-permanence` (claimQuestion fingerprint per
  statement in the report; check_question_permanence.py; gate wired). Stable across two
  runs: 137 of 149 assertions carry a question (the 11 without are the invalid ones, unread);
  suite vs main: no regression. `4f01a88` adds the readable proposition (--show);
  `7512bd3` fingerprints the terms a settled judgement is about (stable, no regression). Integrated
  into main. Recording dispatched: acceptance session_01HaXGBsWn4kWiAHP3TFzayQ. Formalization
  session_01L7hVsUoY69WmjyYJydyQxN (group-valued constructions) dispatched.
- Controller defect found on acceptance PR #61: in construction the reviewer was given the
  seal-relative file list but main-relative diffs (33 files, none shown) and answered "evidence
  needed". `811d72c`: construction reviews the PR's delta against main, ledger included
  (test_review 52/52). `fa442c4`: semgrep POLICY.RUNTIME_DEFAULT findings in review.py and the
  acceptance scripts repaired. PR #61 branch updated to main for re-review; subscribed.
- lean-categories#76 independently approved and merged (`7aef31a`). Pinning the kernel there was
  refused: upstream main also carries #72–#74 (the binder work the plan keeps out until its
  independent assessment), and at that pin ∫ is a binder row (integral_square/sine gap → invalid).
  Kernel stays at `5b96a8a`. Binder assessment dispatched: session_012x1AfmzWVvy15BYK1rMsTU.
  At the trial pin the polynomial/composed failures were gone (`let C` holds).
- PR #61 (acceptance: lattices rank/cardinality, 5 assertions) re-reviewed: custodian review PASS
  after the delta fix, all CI green; merged (`9bce2c4`). Its author reports E₈ rank, S₃ kernels,
  abelianness and the 𝔽₉ transport inexpressible until upstream has the objects (dispatched).
- Formalization PR lean-categories#76 open (units, nonzero/monic evidence); leaf session unblocked
  (owner approved add_repo). Independent formalization review of #76 dispatched:
  session_01J5TvBCNLNiuNXLHf2DyhdQ; the kernel stays pinned until it is accepted.

## 2026-10-01, later (orchestrator, stage B: b0-typed-application)

Branch `b0/typed-application`, integrated into main. Delivered, each with a probe and a suite run
compared per assertion with main (no regression):
- `1ae53ea` b0-typed-application: applications admitted only at the declared signature
  (applyFamily, invariantOf); composed.charpoly/det/trace internal → invalid.
- `fa0a426` b0-selected-structure: recognition by declaration identity; (ℤ/n)^k and Vec(ℤ/n, k)
  distinct (registry audit: the only reducibly equal pair); SelectedStructureProbes.
- `ea432e4` b0-domain-preservation: ring-hom coercions kept, kernel homs only unfolded; the
  Poly∖0/Monic evidence goals no longer contain `RingHom.toFun`.
Dispatched formalization session session_01CRqVaA7aRUSwk1Q7LKgACe (lean-categories): numeral
coverage of the Poly∖0, Monicₙ, units evidence; a convergence domain for lim.
Remaining stage B: core-admission-realized holds by its existing probes; b0-binders waits on the
upstream assessment. The 6 Poly∖0/Monic failures and lim ×2 are upstream (below). Suite at main `3c8eaec`: 148 assertions; 52 hold, 85 gaps,
8 invalid, 3 internal. Classified:
- `composed.charpoly/det/trace` internal: `C.det()` applied `det` to the set `C` (continuous maps)
  where `n : ℕ` stands; `isDefEq` assigns without checking types, elaboration then crashes. Kernel
  (b0-typed-application). Repaired in `1ae53ea`: applyFamily and invariantOf admit an application
  only at its declared dependent signature; probe in RegistrationProbes. (These three still fail:
  `let C` is invalid, below.)
- 6 invalid "not an element of Poly∖0 / Monic": upstream. The kernel forms the numeral `k` of `R`
  by the numeral row as stated (`Int.castRingHom (asRing R) k`, NamedRings.lean:84); the evidence
  of `obj.sets.nonzero_polynomials` and of `Monicₙ` does not establish its property for polynomials
  with those coefficients (EvidenceTests.lean covers only literal coefficients). Same pattern as the
  recorded ℤ/5 `Units` evidence finding. Owner: lean-categories, independent assessment (Policy 2);
  the kernel does not reshape the numeral or write evidence.
- `calculus.limit_sinc`, `calculus.limit_infinity` invalid: no registered domain of maps convergent
  at a point. Upstream; b0-binders (independent assessment of the binder work).

## 2026-10-01 (orchestrator, session_01SKJ21csPEAnJmemqQztSVD)

State: integration branch `b0/construction` (head after this commit) carries #59 (stage A
kernel), #60 (B0 documents), the gate correction (`partial def` ratchet, kernel-totality gate
withdrawn) and the construction mandate. #59 and #60 are superseded vehicles; their branches are
kept.

Done:
- Stage A source: registry reader in the kernel; one outcome model; suite out of compilation;
  `scripts/check_acceptance_regression.py` (new failing assertion fails; missing report fails);
  export checked as a faithful projection of the registry state and against upstream's catalogue
  root (`LeanCategories.Catalogue`). No Lean change since `da209f5`; CI full build and
  acceptance-vs-base passed at `7dc2d7c`.
- Controller: construction-aware `prompt.md`; `review.py` phase from base `custodian/phase.json`,
  typed outcomes, outage ≠ rejection, mandate + context + explanation inputs, batches,
  reconsideration; `verify.py --construction`; workflows; authorship gate maps `custodian/` to the
  orchestrator in construction. `test_review.py`: 49/49 on a scratch copy.
- Documents: construction mandate (architecture.md), AGENTS.md "Current task: construct B0",
  CONTRIBUTING "Documentation and construction work", plan stage A. "You have no memory" deleted
  on a retracted instruction, then restored (`ce0ad81`).

Pending:
- Ruleset `ecustodian-main` (id 24252144): drop `pull_request`, `required_status_checks`; keep
  `deletion`, `non_fast_forward` (custodian/SETUP.md). Needs repository administration; refused to
  this session ("Write access to this GitHub API path is not permitted through this proxy").
  Then fast-forward `b0/construction` onto `main`.
- #59 "Build and audit": semgrep's exception lookup for the known `pull_request_target` finding hit
  GitHub's rate limit (403); one re-run queued (run 36893318437).
- Next construction work: stage B (`b0-typed-application`) once stage A is on `main`.
