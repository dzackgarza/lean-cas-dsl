# Journal

Process narration lives here, not in chat: what was done, what was found, what is pending and on
whom. Chat carries only what needs the owner's action or decision. Newest entry first; one entry
per working session; terse. Not an authority: rules live in their owning documents (AGENTS.md).

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
