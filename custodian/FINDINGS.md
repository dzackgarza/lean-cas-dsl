# Custodian findings, 2026-09-30

## 2026-10-20 — Independent review of latest-main correction

Assessed construction revision
`230ed8d8502df5f5729047c2b7204cfd83d33698` in its clean external worktree.
Read the actual materialization, role-server startup, authority-review and signed
replay consumers, resolver, public-artifact readers and updated fixtures. The
resolver now fetches source dependency main from the configured trusted remote;
requirements, acceptance evaluator and signing identities are not resolved from
candidate-controlled inputs. `apply_assessment.assemble` reconstructs dependency
base identities from the signed envelope, then `Controller.advance` rebuilds the
complete snapshot and verifies its configured independent signature. No new
authority bypass was found in that replay path. This disposition is source
review, not protected deployment or B0 acceptance.

Remaining construction findings:

1. **Stale public metadata blocks roles that do not consume it.**
   `custodian/dependencies.py:31-39` validates public metadata whenever it exists
   in configuration. `custodian/launcher.py:205` calls this before selecting
   `ROLE_INPUTS[role]`. Thus a formalization author, whose only assigned input is
   mathematics, cannot start if unrelated public metadata has old contract
   provenance. Reproduced with two temporary local main repositories and a
   configuration assigned to formalization: after advancing only contract main,
   `resolve_dependencies(config)` raised `fixed public metadata provenance
   differs from current main`. This is an execution dependency imposed on a
   nonconsumer, contrary to the requirement to block only consumers of missing
   input. Resolve/check dependencies and artifacts for the actual consuming
   operation, retaining complete tuple checks where the independent assessment
   really consumes that tuple.

2. **Committed public artifacts can omit contract provenance.**
   `custodian/dependencies.py:38-39` accepts a `public_metadata` entry without
   `provenance` if its commit equals current mathematical main. The supported
   `configured_input` path wrapper then verifies only its content digest.
   Reproduced with a committed `public.json`, `path` and correct digest but no
   provenance: advancing contract main updated the resolved contract while the
   old artifact remained readable. Exact observed output was
   `contract_updated: True, old_public_artifact_still_readable: '{}'`.
   Require the actual mathematics and contract provenance for each supported
   artifact representation at its consumer; an unchanged mathematical commit
   cannot establish compatibility with a changed contract. Do not relabel or
   regenerate a protected artifact to satisfy that comparison.

3. **SETUP still instructs separate admitted source dependency releases.**
   `custodian/SETUP.md:9-19` retains the mathematics/contract accepted-reference
   bootstrap and immutable-input prerequisites from the earlier finding. The
   new resolver makes those configured source commits reproducibility snapshots,
   so replace these conflicting instructions in SETUP while preserving the
   independently protected controller, evaluator, requirements and signing
   operations. Updating CONTROLLER alone leaves the operative setup contradictory.

All seven lightweight fixture programs passed with
`GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1`: controller (1), launcher
(11), author launcher (1), materialize (1), assessment (1), dependencies (2) and
review context (2), 19 fixtures total. The two local-main reproductions above
exercise production resolver/artifact readers independently of fixture assertions.
No Docker runtime fixture or real external reviewer call ran in this assessment;
their previously bounded evidence gaps remain. No implementation, credential,
protected reference or authoritative record was changed by this review.

## 2026-10-20 — Independent controller source review

Assessed committed controller source at
`a6311e1ab86b8aa31741a91c5040a236677edb72`. The concurrent uncommitted
`CasCatalogue/Language.lean` edit was outside this review. Inspected controller,
role launcher, author launcher, materialization, candidate execution, assessment,
publication, authority workflow, review prompt/context transport and setup against
INTENT and the architecture's role, transition and reviewer-context requirements.
This is technical source assessment, not protected deployment or B0 acceptance.

1. **Dependency selection contradicts latest-main consumption.**
   `custodian/SETUP.md:9-19` still requires separately admitted mathematical and
   contract release references and immutable configured dependency revisions.
   `custodian/materialize.py:37-39` only checks those old commits exist;
   `custodian/controller.py:configured_input` consumes them unchanged. Neither
   refreshes those own-organisation dependencies to latest main as required by
   the owner ruling in `specs/architecture.md:13`. Reproduced with a temporary
   Git repository containing two main commits: passing the first commit to
   `configured_input` returned its old file contents after main advanced to the
   second. Resolve dependency main before construction builds/harness execution
   and retain its exact resolved identity for reproducibility. This correction
   must not let a candidate select its judge, requirements or signing authority;
   independently protected judging inputs remain separate from construction.

**Boundary observation, not a blocking finding:** configured candidate
   validation exposes the whole source repository.
   `custodian/launcher.py:97-113` checks only the candidate's changed paths and
   then passes the entire revision to `execution.execute`.
   `custodian/execution.py:25-39` archives and mounts every tracked file, all
   readable by the candidate process, and returns its stdout to the author.
   Consequently, configuring validation of an acceptance author's candidate
   program in the DSL checkout exposes unchanged `CasCatalogue/` implementation
   source, despite `read_source` correctly denying that read. To reproduce on a
   Docker-capable host, configure Python validation of an acceptance-owned
   `tests/acceptance/inspect.py`, have that program print
   `Path('/candidate/CasCatalogue/Language.lean').read_text()`, checkpoint it
   through the acceptance server and call `validate_source`. The changed-path
   check admits the program and the full-tree mount supplies its input.
   This runtime reproduction was not executed here: `docker info --format
   '{{.ServerVersion}}'` returned permission denied on `/var/run/docker.sock`.
   Under the 2026-10-10 owner ruling, technical ability alone is neither a
   conduct breach nor a B0 acceptance blocker. No inspected instruction
   authorizes the acceptance author to perform this forbidden read, and no
   actual forbidden read was observed. Thus this is a limit on the technical
   containment claimed by source inspection, not an additional repair or
   capability-removal prerequisite.

Existing source fixtures passed: controller (1), launcher (11), author launcher
(1), materialize (1), assessment (1), review context (2). Controller,
materialize and assessment needed `GIT_CONFIG_GLOBAL=/dev/null
GIT_CONFIG_NOSYSTEM=1` to keep ambient Git hooks out of their temporary fixture
commits; without it those fixture commits failed before the tested behavior.
These 17 fixtures establish their specific wiring/rejection behavior only.
The already recorded missing real external-reviewer context-read observation
remains open: the context fixtures do not execute that reviewer.

No protected reference, environment, signing identity or authoritative record
was changed. The remaining authority operation is bootstrap of an independently
reviewed controller revision at `accepted/controller`, with the real independent
public signing identity and protected environment/check configuration described
in SETUP; this source review neither supplies that identity nor performs the
bootstrap. The dependency-selection defect remains construction work, not a new
owner choice.

## 2026-10-20 — Integrated candidate and remaining B0 dependencies

Candidate `32c3897163a6f6595b44277b097efad0da9ccfdc` passes the complete local
7,554-job integration and hosted build/audit, purity and boundary checks in run
`39406008396`. Its completed computation-only report contains all 153 admitted
IDs exactly once, plus the failed inverse binding: 15 holds, 130 gaps, three
unavailable outcomes and five invalid readings. These are construction observations,
not independent B0 acceptance. Artifacts and exact clean inputs are in
`/tmp/b0-poc-32c3897/`; `analysis.json` summarizes the complete report.

The required registered-execution target remains **11/15**: reversal equality
holds with no dispatch and the three discriminants have no admitted cokernel
registration. Latest-main leaves `48a99b5` supply neither `mor.sets.fin_rev` nor
`colim.bil_w_form.cokernel`. They also supply no `meth.rank`, so the admitted
`rank(A₂) = 2` positive remains a gap. A kernel proof discharge or a historical
leaf revision cannot replace these required current registered computations.

The five inverse readings remain invalid through the same upstream evidence
failure tracked in lean-categories#92 (still open). No kernel evidence rewrite or
alternate mathematical admission was added. The other three unavailable outcomes
remain backend errors on returned finite-set/construction data; their strata are
preserved.

Of 148 readable questions, 147 are byte-identical to the previous complete run.
Only `calculus.limit_infinity` differs: its claim portion is byte-identical, while
its operation provenance now retains the structured domain parameter. This is
not self-issued interpretation acceptance. The unchanged permanence checker
fails on the five unread questions. There are still 11 unrecorded identities and
137 readable differences from the stored historical records, requiring independent
assessment. No assertion or authoritative interpretation record was edited.

Independent extension trials, their arguments and final acceptance remain
unestablished. Fresh-context formalization, acceptance and leaf authors are now
performing their respective remaining work under the owner's authorization to
delegate. Role separation governs their inputs and edits; it does not preclude
those assignments. The protected `accepted/controller` path still returns 404;
source integration does not bootstrap or approve it. The deployment operations remain
in `custodian/SETUP.md`. The completed inventory supplies no new required-execution
failure that can be repaired by authoring a leaf or upstream mathematics in the
kernel role. Unsupported broader computations remain visible gaps; they do not
reduce the fixed B0 obligations above.

## 2026-10-20 — Priority correction

The encoder repair removed the recorded repeated contextual encoding obstruction.
Continuing to optimize smaller reader costs before complete POC execution was a
work-selection defect. The owner corrected that priority: follow
`specs/computational-core-plan.md`, "Execution priority: finish the POC".
The latency observations below remain diagnostic history. Proposed usability
targets are deferred; complete preservation, functional execution and independent
B0 acceptance remain required. Performance work resumes before POC completion
only for a measured obstruction to a required run.

## 2026-10-13 — Current B0 construction defects

- Resolved in kernel construction source on 2026-10-18: neither the anonymous
  `Nat.Primes` parameter of `primeFactors` nor the anonymous `Fin n → K`
  parameter of `ker` requires new upstream mathematics. A parameter-free
  registered admission can form a point at an anonymous endpoint without
  assigning that endpoint a named alias; all applicable admission points must
  agree. A registered result constructor can be recovered from the direct
  declared parameters of the actual operand, but only when a registered point
  family names that constructor as its codomain. This recovers `Vec(K,n)` from
  the matrix's retained `K,n`, and the vector-zero family is then applied with
  those exact parameters. The unchanged prime-factor and matrix-kernel claims
  both read successfully against `lean-categories` `fd2cd45f` and contracts
  `3c2159b`; no carrier-only alias selection or assertion change was used.
- Performance defect observed on 2026-10-18: the matrix-kernel claim reads
  with trace recording in 12--40 seconds and produces 99 roots, but production
  `interpret` spent more than three minutes canonicalizing that trace. The
  identity encoder takes about 63 seconds before its 2--4 ms final JSON
  compression. An instrumented unchanged pass made 2,097,785 recursive proof
  checks and interner calls to produce only 640 canonical nodes; proof checks
  accounted for 10.9 seconds and interning 28.2 seconds. An exact contextual
  cache had zero hits because fresh local IDs distinguish the raw terms; making
  a fully abstracted key at every node repeated the expensive traversal. A
  function-spine proof-check optimization preserved the focused proof-identity
  probes but left exact encoding at 64.2 seconds and was reverted. The repair
  now encodes one source DAG and remaps its canonical nodes to reproduce the
  legacy standalone sort keys and final insertion order byte-for-byte. This
  removes the independent per-root expression pass: exact production
  interpretation completes in 149.890 seconds, with 65.178 seconds in source
  encoding, 0.988 seconds in remapped keys and 65.222 seconds in operation
  fields. Pre-encoding all operation fields made the exact run exceed three
  minutes because fields and roots do not share raw cache identities, and was
  reverted. A 2026-10-19 kernel candidate caches unopened syntax with binder
  context, so fresh local IDs no longer force those two repeated traversals.
  On the admitted 2×2 matrix-kernel assertion at latest-main mathematical
  revision `a2123729`, source and operation-field encoding each take 34--60 ms
  and the complete 28,383-byte question identity matches the previous encoder
  byte for byte. Semantic reading still takes about 10 seconds. A further
  generic morphism repair retained the first argument after it failed the
  declared leading-parameter check, instead of rereading it as the first
  operand. A further set-literal repair reuses initially read bound elements
  with an explicit non-category `in X`, whose value ignores the literal's
  ambient; all other elements retain contextual reading. The unchanged 3×3
  `subspaces.kernel` assertion now completes at the ordinary budget with 126
  roots and a full 39,816-byte identity byte-identical to its prechange
  diagnostic result. Its seven binding reads still total about 77 seconds,
  and assertion semantic reading takes another 38 seconds; further latency
  tuning is deferred until the POC is complete. The separate first-integral binder timeout was
  removed by reading a sole registered binder row once; focused
  `BinderReaderProbes` passes. Full protected acceptance has not run. Issue
  lean-cas-dsl#66 remains open for those integrated obligations; no timeout
  increase or weaker identity is acceptable.
  A 2026-10-20 reader profile located the remaining repeated work in tuple
  element coercion: 79.7 seconds cumulatively across the 3×3 file, compared
  with 11 seconds applying `cons`. Reusing closed numeral conversions within
  one fixed tuple element set, and across rows only for one explicitly typed
  matrix coefficient set, lowered cumulative coercion to 55.1 seconds.
  The full `subspaces.kernel` benchmark now takes 102.34 seconds with 25.91
  seconds in assertion semantic reading; its 126-root, 39,816-byte identity
  is byte-identical to the saved prechange diagnostic baseline. The 2×2
  identity is likewise unchanged. Independent interpretation preservation and
  full protected acceptance remain open; the proposed latency target is deferred.
  A subsequent profiler split found 12.0 seconds in speculative vector-zero
  family trials and 4.75 seconds in `0` operation trials on the same admitted
  3×3 file. The vector-zero declaration has a terminal `Fin 1` source, so
  source-type rejection cannot remove the family trial. Reusing its speculative
  result and a closed-source prefilter were tried and removed after the
  reader profile showed no family-trial reduction. Conditional profiling spans
  remain in the reader to locate the failing parameter/application check;
  this is an engineering defect observation, not acceptance evidence.
- Diagnosed formal-side dependency on 2026-10-18: the registered
  `Units.invertibleEvidence` proves invertibility for the same matrix over
  literal `ℚ`, but refuses it over the selected rational-ring object used by
  the catalogue. Running the registered numeral normalization first changes
  the displayed entries to `1,2,3,4` and still fails. A definitionally valid
  `change` from that selected carrier to
  `Matrix (Fin 2) (Fin 2) ℚ` makes the unchanged evidence tactic succeed.
  Thus the determinant and unit evidence already suffice; the formal evidence
  tactic fails to normalize the selected-object construction before selecting
  its field/unit route. This is an upstream evidence implementation defect,
  not missing mathematics and not a kernel admission to reformulate. The six
  inverse readings remain blocked on lean-categories#92 until the formal owner
  repairs it.
- Repaired in controller construction source: a signed decision without
  `findings`, or with `findings: null`, could advance accepted inputs. Red
  regressions reproduce both failures; decisions now require an explicit list.
  Required request artifacts, signed discussion reconsiderations and MCP call
  arguments likewise cannot be replaced by empty runtime defaults.
- Repaired the mocked context test by exercising the production context's real
  file materialization and cleanup. It establishes transport of the complete
  payload, not the independent reviewer's mathematical or technical judgment.
- Open (2026-10-14): that test exercises `materialized_context` only, and
  `custodian/review/test_review.py` substitutes `call_reviewer`. No check
  observes the actual external reviewer reading the complete
  `requirements.txt`, `change.txt` and `explanation.txt` through its scoped
  read interface, or the retrieval directory removed after that real call.
- Resolved at the owning QC boundary: the lexical `lean-shim-suffix-decl`
  rule was specified as a reviewer tripwire, but its ERROR severity rejected
  nine engineering declarations. Independently reviewed PR ai-review-ci#469
  integrated as `9b43a56c23518412dd4aa145441f0d4bc6425cb7`; the ordinary
  installed `just test-push` now passes. No declaration was renamed or excluded.
  Every native suffix finding remains visible for review. Independent source
  assessment classified the equation-reader fixtures, computational envelopes,
  and packet planning/validation/projection as engineering, not catalogue
  mathematics. Three retained native partial-parsing diagnostics affect the
  workflow's curl-to-shell rule; independent inspection of each affected clone,
  Python invocation and commit command found no such pipeline. These individual
  dispositions establish neither surrounding workflow correctness nor B0 acceptance.


The dated findings below retain their historical revisions.

This file is inside the sealed boundary. Revisions cited: lean-cas-dsl `0ba53dab`, lean-categories
`c06aeedc` (the pin), lean-cas-dsl-leaf-contracts `6588a86c` (the pin), lean-cas-dsl-leaves
`c4cff164` (the pin). Some line numbers come from the sibling branch heads (lean-categories
`6b2750c9`, contracts `9fd3c176`) and are marked (head).

The owner's `specs/owner/convergence-process.md` matches the stated sha256 `fb3fe73c…`.
`Lean-Cas-DSL-Intent.md` is not in any branch or commit of `dzackgarza/research`.

## A. Holes in the orchestrator's gates

The seal (`CONTAINMENT.md`) makes each of these moot as a route to acceptance, because the gate
files, the kernel and the pins can no longer change without a new seal. The holes are still there,
and they are the orchestrator's record.

1. `scripts/check_authorship.py` (retired 2026-10-02; the findings below are why)
   - Identity is self-declared.
   - A commit with neither `Agent-Id` nor `Claude-Session` is "a person's" and is not checked
     (`commits()`, `if agent is None: continue`). Omitting the trailer bypasses the gate.
   - `CUTOFF` exempts all earlier history.
   - `chain()` silently skips any sibling repository that is absent.
   - The gate assigns the orchestrator `LeanCategories/Catalogue/Registry/*`, the admission
     validator for the mathematics it consumes.
2. `scripts/check_acceptance_permanent.py`
   - `--correct` rewrites or deletes any admitted assertion as soon as the `lean_categories` pin
     differs from the recorded one. Any re-pin satisfies that, including one to an arbitrary
     upstream commit the orchestrator can push.
   - Its authority is `AGENT_ROLE=acceptance`, an environment variable anyone sets.
   - A missing `admitted.json` is recreated empty.
   - The ledger is plain JSON, editable by hand.
3. `scripts/check_kernel_totality.py` exempted any `catch` next to the comment
   `-- not a reading fallback:`, so the author certified its own exemption, and it saw only the token
   `catch`. It is withdrawn (B0 policy 2). The obligation it named, that no failure is reread into
   another meaning, is carried by the one outcome model (`cc-failure-strata`: every failure is
   reported as its stratum, an untagged one as an internal error) and by the acceptance comparison.
4. `CasGates/KernelPurity.lean`
   - `evidenceRunner.isPrefixOf d` exempts every declaration named `CasCatalogue.Language.establish.*`.
   - `CasContract.Probes` is skipped.
   - If `.lake/packages/cas_leaf_contracts/CasContract` is absent, `moduleFiles` returns `#[]`,
     so contract coverage passes vacuously.
   - `kernelRoots` excludes `CasDsl` and `CasTools`.
   - `allowedModules` admits `LeanCategories.Catalogue.Registry`, which the orchestrator writes.
5. `scripts/check_reuse_records.py` is keyed on the "Delivered"/"Next" markers the orchestrator
   writes in its own plan, and is not run in CI.
6. `.github/workflows/gates.yml` is taken from the pushed commit, and no branch is protected, so
   CI judges a change with rules that the change can edit.

## B. Mathematics admission (lean-categories, at the pin)

7. `Registry/Semantic.lean:2310`: the totality closure ends in `| _ => #[]`, so categories,
   functors, methods, properties, lifts, cells, limits and the other kinds are never
   totality-checked (introduced in `d4d6f1a`).
   - The ban list (head) is `Option, Part, PFun, Ring.inverse, Matrix.nonsing_inv, Matrix.inv`.
     It omits `Except`, `sorryAx`, `default`/`Inhabited` and `WithTop`/`WithBot`.
   - The `⁻¹`/`/` check skips types with loose bound variables (head `Totality.lean:71`), so
     `fun {K} [Field K] (x : K) => x⁻¹` passes.
   - The gate's own docstring says it "does not certify that a row is well defined". This is the
     owner's "ill-defined spec" hole, still open.
8. `Registry/Semantic.lean:2290,2375`: the author of a semantic row is decided by the module's
   root name (`LeanCategories`). Any package, a leaf included, can name a module
   `LeanCategories.X` and write semantic rows. The seal closes this for lean-cas-dsl and for leaves
   at the pin (path checks); upstream it is still open.

## C. The leaf contract (at the pin)

9. A leaf self-declares `trust := .trustedAssertion` on an unproved implementation (head
   `Extension.lean:464`), and it is accepted with a label.
10. `isLeafModule` is a denylist: any root not in `nonLeafRoots` is a leaf.
11. `RealizerEntry.category` is a leaf-declared parent category. The owner's step 2 names exactly
    this as the wrong design.
12. The contract repository has no gate and no CI.

## D. The kernel (sealed at the baseline, recorded as debt)

13. The former construct ratchet counted `unreachable!` occurrences as mathematical defects,
    including ordinary computational failure branches. Withdrawn 2026-10-03: `unsafe`,
    `extern`, `implemented_by`, `panic!`, `unreachable!`, and implementation recursion are
    assessed against their live role, not their count. Proof escapes remain prohibited.
    A computational failure does not redefine the mathematical request; returned computational
    data does not supply mathematical authority. Neither syntax absence nor source review
    establishes observed answer correctness.
14. `CasAcceptance/Standard.lean:380` proves an acceptance probe with `native_decide`, which trusts
    the compiler rather than the kernel.
15. `lakefile.lean` requires `nbdsl-worker` at `main`, a floating ref. The seal fixes the manifest
    revision.

## E. Leaves (at the pin)

16. The leaves put algebraic structure on handle types: `instance Group`/`CommRing` on tables
    (head `Algebra/Actions.lean:44–72`, `RingTables.lean:55`, `RingActions.lean:63`), and
    `ValueRing.castHom : … → Option` (`Modules/Bilinear/Valued/WForms.lean`).
17. `Algebra/RelabeledRings.lean` and `HostileSubgroup` (`Subgroups.lean`) are test-shaped
    fixtures, and `b818e4c` ("probe") has no role trailer.
18. The leaf scan against the seal's rules at the pin is clean (`leaf_baseline` in the seal).

## F. Judgment of `specs/proposals/extension-language.md`

**Not adopted as written.** Row by row:

- **Leaf: delete the forbidden constructors of `LeafContribution`.** Accepted in direction. It is
  what step 2 requires: unrepresentable, not rejected. It changes the sealed contract pin, so it
  enters only through a new seal. The negative probes must become a statement about the type's
  constructors, as proposed.
- **Leaf: remove `ImplementationEntry.trust`.** Accepted in direction, for the same reason (finding 9).
- **Leaf: keep `RealizerEntry.category`.** Rejected. The owner's text: "A leaf-facing 'declare
  parent category' field is already the wrong design if the category should follow from the
  construction." The proposal concedes that "the field could also be derived" and keeps it anyway.
  The category must be derived from the denotation's type.
- **Leaf: keep `backendOperation` and the dependent `presentation`.** No objection. The dependent
  check is still "build pending", so it is not delivered.
- **Leaf: realization ambiguity.** The step 3 argument is owed and not supplied. It remains an open
  obligation, not a kept interface.
- **Formalization: the validator is trusted core.** Agreed. The seal implements it: the
  `lean_categories` pin cannot move without a new seal. The proposal omits findings 7 and 8, the
  concrete admission holes.
- **Formalization: the orchestrator relays only a requirement's location.** A goal with no
  mechanism. The orchestrator spawns the formalization agent and writes its prompt, and nothing
  the orchestrator cannot forge separates the two. Recorded as unsolved.
- **Kernel: split `RegistryState` so the semantic reading cannot receive realization rows.**
  Sound, and structural as step 3 asks. It is a kernel proposal under the seal.
- **Kernel: `establish` and `KernelPurity` are trusted core.** Agreed. The proposal does not
  mention the gate's own exemptions (finding 4).
- **Acceptance: meaning permanence and prompts.** Meaning is now protected by sealing the kernel
  and the `#accept` elaborator. Prompt authorship is the same unsolved identity problem as above.
- **Omitted by the proposal:** every hole in section A. Those are the orchestrator's own
  exemptions. The proposal inventories the subagents' interfaces and not the orchestrator's.

## G. What remains unsolved (owner decision needed)

- **Independent authorship.** Every subagent is spawned by the orchestrator. Only keys the
  orchestrator never holds can separate roles: a formalization session and an acceptance session
  that the owner starts directly, each signing its deliverable. Until then, "independent" can mean
  only "sealed by the owner after review".
- **Successor signer.** The custodian's key dies with this session. Either the owner signs future
  seals with a key of their own, or the owner names a new custodian session and receives its
  fingerprint.
