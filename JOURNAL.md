# Journal

## 2026-10-20 — Integrated element-transport candidate 8fb0eb3

The first integration attempt at `64a4c69` failed on the new record's layout;
it remains a failed candidate. Correction `8fb0eb374878f5544a2f26935819ae6191ce0a7f`
passes the complete clean `B0_INTEGRATION=1 just build` gate (7,554 Lake jobs).
The gate's log and exit 0 are
`/tmp/b0-poc-7e44f61/integration-8fb0eb3.{log,exit}`. The original checkout was
fast-forwarded to this source without changing its pre-existing `Language.lean`
edit; the external candidate checkout remains clean and frozen at `8fb0eb3`.

The persistent element regression changes from the exact named-object refusal
to a passing target in 34.81 seconds. Its malformed-envelope checks also pass.
The focused realizer build passes in 106.66 seconds, and its automatic profile
completes in 82.85 seconds. The same-candidate question, proof-identity,
selected-structure, parameter, structured-result, registration, boundary and
purity probes pass in the integration gate. This validates their respective
contracts, not B0 acceptance.

Both required question diagnostics pass: `matrices.kernel` in 73.32 seconds and
`subspaces.kernel` in 129.04 seconds. Their complete identities are byte-identical
to the independently saved output of the earlier `7e44f61` run (28,383 and
39,816 bytes). This is preservation across the port-form repair, not independent
acceptance of either reading or migration of the 137 differing stored artifacts.

The complete unchanged computation-only inventory is running once at `8fb0eb3`,
session `9060`, runner PID `1607866`, using the existing repository virtual
environment for both Sage and GAP. Its source, inputs, process identity and log
are `/tmp/b0-poc-8fb0eb3/{inputs.json,harness-process.json,harness.log}`.
The wrapper saves `harness.exit` and `harness.json` when it finishes. Poll that
existing process before launching any successor. The completed `7e44f61` report
remains separate. Latest-main input revisions are unchanged from that report.

Construction source `8fb0eb3` is published on `b0/poc-completion-20261020`.
Hosted Gates run `39394721114` has exactly that full `headSha`; it is still
running. Its boundary-integrity and permanent-assertion job has passed. Older
run `39391136444` judges `929850d`, not this functional repair.
Current manifest registration metadata has no `mor.sets.fin_rev`,
`colim.bil_w_form.cokernel` or `meth.rank` registration. The required execution
gaps, selected-carrier admission dependency, independent interpretation
assessment, independent extensions and authoritative acceptance remain open.

## 2026-10-20 — Retain full selected forms in element transport

The complete inventory's `the selected element structure has no exact object descriptor`
gap is reproduced by reading `assert 2 + 3 = 5` and encoding its numeral points.
The persistent regression in `ElementDataProbes` fails at that refusal before
the correction (`selected-element-persistent-red.log`, exit 1, 35.32 seconds).
It checks complete selected descriptors, computational form identity and category,
and fixed point endpoints; it does not establish an arithmetic answer.

The construction candidate makes `Form.element` retain the full supplied form
rather than require an `ObjectEntry`. Encoding preserves the selected object's
descriptor and payload ownership. Presentation results likewise retain their
fixed target form. Admission of comparisons at named endpoints retains its
existing checks; no carrier-based endpoint recognition is added. The wire
grammar, registration IDs and formal operations are unchanged.

`just focus CasCatalogue.Admission` passes in 18.90 seconds. The required
dependent `Language` build passes in 201.06 seconds using the existing completed
target profile `/tmp/lean-cas-profile.QTqf3h.log` and diagnosed mode with a
360-second wall-clock budget. This is not a heartbeat increase or a performance
repair. The next check is the clean committed candidate's integration gate,
including the regression and protected negatives. The new runtime path and full
candidate acceptance are not yet verified. Evidence remains under
`/tmp/b0-poc-7e44f61/selected-element-*`; original-candidate harness evidence
remains separate and unchanged.

## 2026-10-20 — Complete computation-only inventory at 7e44f61

The original harness invocation completed with exit 1; its runner PID `815702`
is terminal. `/tmp/b0-poc-7e44f61/harness.json` contains all 153 admitted IDs
exactly once, plus one failed binding: 15 holds, 130 gaps, three unavailable
executions and five invalid assertions. No admitted assertion is omitted, and
there are no internal, malformed, wrong or ambiguous outcomes. Inputs and source
remain those recorded below for `7e44f61`; no later source result is combined
with this report.

Eleven of the fifteen required IDs hold with actual registered dispatches.
`sets.eq.rev_rev` holds with no dispatch and does not meet its registered-execution
obligation. The three `lattices.discriminant.*` IDs are gaps for the missing
`colim.bil_w_form.cokernel` registration on `cat.bil_wform`. These are missing
computational inputs, not authorization for the kernel author to implement leaves.
The five inverse assertions and their initial binding remain invalid because the
registered matrix-unit admission evidence fails over the selected rational carrier,
as isolated in the existing October 18 finding. No upstream evidence was changed.

The three unavailable executions are backend `ValueError` answers: finite-subset
product and power-set cardinality report `not a named object: [1, 2, 3]`, and
`sets.card.square` reports `no finite Sage parent for constructionApex`.
The report also exposes a kernel transport obstruction: element encoding requires
a named-object form even when its selected structure retains a complete structural
image form. That generic mechanism is the next source repair under investigation.

The read-only question comparison exits 1 for the five unread inverse assertions.
Of 142 stored records, 137 have readable candidate questions with differing
artifacts; eleven other admitted IDs have no stored interpretation. These counts
are comparison findings, not proof of changed mathematics or an accepted migration.
The comparison log is `/tmp/b0-poc-7e44f61/question-comparison.log`. Independent
interpretation assessment remains required; records were not regenerated.

The ordinary retry successfully published construction source `929850d18669fc336f31aec4438697c503ecd6a4`
to `b0/poc-completion-20261020`. Its six shell errors are gone; nine existing
naming warnings still request independent review but do not refuse publication.
The hosted Gates workflow was dispatched as run `39391136444` and its `headSha`
matches that source exactly. Boundary integrity and permanent-assertion checks
passed; remaining hosted jobs were still running at this observation. Neither
that source publication nor those checks establish B0 acceptance.

## 2026-10-20 — Checkpoint publication and focused-recipe boundary checks

Publishing `1b25499` to construction branch `b0/poc-completion-20261020`
was refused by the ordinary pre-push Semgrep gate. The report is
`/tmp/ai-review-ci-semgrep.VjC65o/head.json`: nine existing
`POLICY.NO_UNGROUNDED_MATH_NAME` warnings require independent review, and six
`POLICY.RUNTIME_DEFAULT` errors point to shell disjunctions and masked failures
in the focused recipes. The separately excepted workflow checkout finding is
not part of that remaining report. No hook or checker was bypassed.

The focused recipes now check their required profile inputs separately, let a
failed target-tag read fail directly, and retain the explicit build-success or
timeout states that trigger profiling. Successful-build log filtering no longer
ignores failures. Probe path validation reports its two invalid conditions
separately. Diagnostic budgets and accepted mathematical assertions are unchanged.
The ordinary `just focus CasCatalogue.TermGraphProbes` command succeeds in
6.76 seconds. Missing prior profile, extended budget without diagnosis, and
missing probe source each refuse with exit 2. Logs are in
`/tmp/b0-poc-7e44f61/`; the full original-candidate harness continues independently.

## 2026-10-20 — Execute the committed POC candidate and restore purity coverage

The complete integration recipe ran at clean `7e44f61fc0a4afcbed9b62e8103970d58ddc347b`
in the external checkout `/home/dzack/gitclones/lean-cas-dsl-poc-7e44f61`.
It exited 1 solely because `CasGates.KernelPurity` omitted
`CasCatalogue.TermGraphProbes` from its imports. All other requested targets
completed, including question, proof-identity, binder, registration and boundary
probes. The correction adds that import to the existing audit. The corrected
source was checked against the candidate's built modules with
`B0_FOCUS_BUDGET_SECONDS=240 just focus /tmp/b0-poc-7e44f61/KernelPurity.lean profile`:
exit 0, 140.33 seconds, peak RSS 2,181,168 KiB. This executes the corrected audit;
it does not establish a successful full integration build of the successor.

The complete unchanged computation-only harness is running once at the original
candidate, with session handle `47855` and runner PID `815702`. Its executable,
suite and checkout remain at `7e44f61`; the gate correction is in the original
checkout and does not alter that run. Invocation is `just harness
.lake/packages/cas_leaves/leaves.json --computation-only`, with both
`CAS_SAGE_PYTHON` and `CAS_GAP_PYTHON` set to
`/home/dzack/gitclones/lean-cas-dsl/.venv/bin/python`. Evidence is in
`/tmp/b0-poc-7e44f61/`: `build.log`, `build.exit`, `inputs.json`,
`build-process.json`, `harness-process.json`, `harness.log`, and `purity-fix.log`.
The wrapper saves `harness.exit` and `harness.json` when execution finishes.
Re-poll the existing handle or PID before considering another invocation.

Resolved latest-main inputs are mathematics
`a2123729df092e58b6fb0cd39c78db5e1714faf2`, contract
`3c2159b510db2ca63455530ed0f4c28ba27da2f8`, leaves
`48a99b5bcb2b090e1c778db29f006b612bed02ed`, and notebook worker
`4c6c2a77abcc717513a65ca35723ed428647e1bd`; all had clean worktrees.
The documented `accepted/controller` GitHub ref lookup returned HTTP 404.
Independent controller admission remains an external authority operation;
no accepted reference was created. B0 completion is unproved. Preserve all
153 admitted identities and all 15 required registered computations when
assessing the pending report. The pre-existing `Language.lean` edit is untouched.

## 2026-10-20 — Put complete POC execution before long-tail optimization

The owner corrected the work order after the encoder repair had turned into
repeated reader optimization before the POC was complete. The architecture and
execution plan now lead with the complete inventory, functional repairs,
question preservation, independent trials and integrated acceptance. The
handoff no longer sends the next session back to the old encoder bottleneck.
AGENTS and CONTRIBUTING retain focused checks and profile reuse, but no longer
require optimization of every slow successful check or attainment of proposed
latency targets before functional completion. Mathematical acceptance and
independent role boundaries are unchanged. Validation is the documentation diff
and consistency check; no Lean build is needed for this priority correction.

## 2026-10-20 — Enforce a diagnosed budget and import-only probe

The focused recipe now refuses a build budget above 120 seconds unless the
caller supplies a completed, target-tagged profile and uses diagnosed mode.
This prevents an ordinary source edit from silently becoming a longer compile
without the profile that justified it. `just probe /tmp/NAME.lean` runs a
bounded import-only reproducer with elapsed time, peak RSS and a `/tmp` log;
its default bound is 60 seconds. The contributor instructions route uncertain
declaration, registry, and branch questions there before another slow source
edit. A probe is diagnostic and cannot replace the target build or protected
assertions.

The refusal path was exercised with
`B0_FOCUS_BUDGET_SECONDS=121 just focus CasCatalogue.Language`: it stopped
with exit 2 before compilation. The
vector-zero source probe first exceeded a 30-second bound without a result;
under 60 seconds it completed in 22.59 seconds at 4,055,836 KiB peak RSS and
reported the `Fin 1` source. That observation set the default bound.
`just --list` parsed the revised recipe surface. No full build or acceptance suite
was run for this workflow change.

## 2026-10-20 — Isolate the zero-numeral reader cost

The `subspaces.kernel` reader-only profile on the unchanged acceptance file
assigned 4.75 seconds cumulatively to speculative `0` operation trials and
12.0 seconds to speculative vector-zero family trials. Forwarded numerals
accounted for 22.5 ms and registered numeral search for 102 ms. Tuple coercion
still accounted for 37.2 seconds, with 10.7 seconds in tuple construction.
These timings came from conditional Lean profiler spans; ordinary reading does
not run the profiler. The targeted `Language` compile passed in 199 seconds,
and the reader-only profile completed in 98.85 seconds with 126 trace roots.

Reusing a successful speculative family result did not improve this assertion:
its family trial yields no element result. A second candidate tried a closed
source-type prefilter, but an import-only probe showed the registered vector
zero has terminal source `Fin 1`, and the next profile still assigned 12.0
seconds to that trial. Both candidate optimizations were removed. The final
source retains only profiling spans around numeral forwarding, the two zero
trials, and registered numeral search. Neither experiment edited the
permanent assertion or its expected answer; a complete identity comparison
was not run on those discarded candidates. The next reader
optimization must identify which declared parameter or result check makes the
vector-zero `applyFamily` trial fail before repeating the full application.
An import-only reproducer then showed the mismatch more directly: the tuple's
fixed element set is `ℚ`, while the registered zero family targets `Vec`.
`familyLandsIn` rejects `ℚ` in about 1 ms, but it also rejects `ℚ³` before
explicit parameters are bound even though `applyFamily` returns an element
there. Moving that check ahead of the trial would therefore discard a valid
reading. The safe preflight still needs the family's actual parameter binding.
Focused compilation and reader timing here are engineering diagnostics, not
protected acceptance or completion of the latency milestone.

## 2026-10-20 — Locate and reuse repeated tuple numerals

The unchanged `subspaces.kernel` reader profile assigned about 70 seconds
cumulatively to tuple readings. A second profile isolated 79.7 seconds in
tuple element coercion across the admitted file, versus 11 seconds applying
`cons`; tuple empty-object and map construction were below 0.1 seconds each.
Kernel `perf` sampling was unavailable, so the instrumentation uses Lean's
in-process profiler and is inactive for ordinary interpretation.

The reader now caches a successful, closed numeral conversion for the fixed
element set of one tuple. Explicitly typed matrix rows may share that cache
only when their coefficient set and reading context are the same. Bound or
staged contexts and values with unresolved metavariables or free variables
bypass the cache. In the profiled 3×3 run, cumulative coercion fell from 79.7
to 55.1 seconds; assertion semantic reading fell from 34.27 to 24.75 seconds.
The full production-question benchmark fell from 116.50 to 102.34 seconds in
separate runs, with 25.91 seconds in semantic reading and 2,431,416 KiB peak
RSS. Its 126-root, 39,816-byte identity and the 2×2 66-root, 28,383-byte
identity are byte-identical to saved prechange diagnostic baselines. These
comparisons establish representation preservation for these specimens, not
independent acceptance or the proposed latency target.

Targeted `Language`, `TestSuite`, `QuestionProbes`, `ContextualSubsetProbes`,
`ParameterStructureProbes`, and `ProofIdentityProbes` builds passed with
latest-main dependencies. The same-target diagnosed build mode now requires a
completed profile tagged for its module and skips rerunning that profile; its
bounded `Language` build passed in 189.91 seconds. No full build or acceptance
suite was run for this iteration. Reader construction, full preservation,
composition, extension trials, and integrated B0 acceptance remain open.

## 2026-10-20 — Per-question closed-term reuse and reader-only feedback

The semantic reader now reuses fully instantiated object and element values only within one
question's immutable scope and trace. A bound variable, staged reading, selected category or
ambient result type bypasses the cache. The matrix reader also forms a shared row ambient once
for a matrix instead of reconstructing it for every row. The suite's paragraph splitter moved
unchanged to `CasCatalogue.FileItems`, allowing `benchmarks/semantic_reading.lean` to import the
reader without the realization/encoder layer. `just bench-reading ASSERTION` exposes that faster
diagnostic; focused build output now retains warnings in `/tmp` while printing a short result.

At the same latest-main mathematical and contract revisions, the unchanged `matrices.kernel`
assertion read in 7,898 ms versus 9,458 ms in the previous recorded run; `subspaces.kernel`
read in 31,469 ms versus 38,166 ms before these edits (40,514 ms after row-ambient sharing
alone). The complete 28,383-byte and 39,816-byte question identities were byte-identical to
their saved pre-cache baselines, with 66 and 126 trace roots. The full 3×3 benchmark took
116.50 seconds at 2,386,408 KiB peak RSS; these numbers are run-sensitive and remain far from
the proposed low-single-digit kernel budget. They are engineering observations, not independent
mathematical acceptance. The semantic-only diagnostic passed at 35,332 ms for its 3×3 claim;
it omits question construction and encoding by design.

Targeted `CasCatalogue.Language`, `CasCatalogue.TestSuite`, `CasCatalogue.QuestionProbes`,
`CasCatalogue.ProofIdentityProbes` and the new `CasCatalogue.FileItems` builds passed. The
reader's target build still required 233 seconds at about 2.6 GiB peak RSS. Its profile assigned
roughly 40 seconds to LCNF base compilation, 35 seconds to `do` elaboration, 34 seconds to
typeclass inference, and 52 seconds to unaccounted blocking. Its 3,900-line mutual block remains
a compiler feedback bottleneck. Full B0 acceptance and complete question preservation remain open.

## 2026-10-19 — Bounded focused runs and production question timings

`just focus` now caps each targeted build or profile at 120 seconds by default,
reports a timeout as a failed check, and retains the log for diagnosis. It
profiles a successful or timed-out build that reaches 60 seconds, with a
separate cap on that profile; an ordinary compile error does not trigger a
second expensive run. `just bench-question ASSERTION` now drives the existing
production-path timing harness from an unchanged admitted assertion under a
180-second limit. Its log records the source and latest-main dependency
revisions, dirty source state, per-binding and phase times, elapsed time and
peak memory. The recipes and contributor instructions require profile/import
diagnosis and a specific invariant check before increasing a budget.

Targeted validation: `just focus CasCatalogue.QuestionIdentity` passed in
17.36 seconds at 793,176 KiB peak RSS. The normal `matrices.kernel` question
benchmark passed with 66 trace roots and 28,383 identity bytes; its complete
run took 76.79 seconds at 2,257,812 KiB peak RSS, including 9.458 seconds of
assertion semantic reading. One-second diagnostic limits on both recipes
returned exit 124 and preserved their logs. The existing `justfile` has unrelated formatter drift,
so recipe parsing was checked with `just --dry-run`; `git diff --check` passed.
No full build or acceptance suite was run for this workflow edit.

## 2026-10-19 — Targeted feedback workflow and identity import boundary

The local gate now starts with `just focus TARGET`: it refreshes
own-organisation checkouts to latest `main`, resolves Lake only if those
heads differ from the manifest, builds one target, and records wall time,
peak RSS and a `/tmp` log. A build taking at least 60 seconds automatically
profiles that source with Lean and keeps a separate profile log. Local
`just build` now refuses an uncommitted or non-integration candidate; GitHub
Actions and an explicit `B0_INTEGRATION=1` at a clean revision retain the
complete integration gate. `AGENTS.md` and `CONTRIBUTING.md` now direct source
iterations to this smaller path and require analysis of slow profiles before
another broad check. Neither focused checks nor this workflow change count
as mathematical acceptance.

The term-identity DAG/table machinery now lives in its existing lightweight
`QuestionIdentity` import rather than the full `Realize` module. Its names and
encoding are unchanged. `TermGraphProbes` imports that module directly. The
same probe's Lean profile changed from 49.2 seconds importing and 71.66
seconds total to 2.85 seconds importing and 8.44 seconds total; its targeted
build passed in 10.19 seconds. `CasCatalogue.QuestionIdentity` built in 16.39
seconds. The targeted `CasCatalogue.Realize` build passed in 122 seconds and
automatically captured an 82.90-second source profile; no whole-repository
build was used for this edit. The admitted 2×2 `matrices.kernel` assertion
retained 66 roots and the exact 28,383-byte identity, byte-identical to the
saved pre-move baseline. `CasCatalogue.ProofIdentityProbes` also passes at the
changed import boundary. The resolver's unchanged/changed-head test passes;
the local integration guard refuses an ordinary or dirty full build before
dependency work begins, while the GitHub Actions path remains available.

## 2026-10-19 — End-to-end reading cost of the admitted 3×3 question

The reproducible `benchmarks/question_identity.lean` now reports each binding's
semantic-reading time as well as the assertion stages. At the committed
`e2bd797` kernel and latest-main inputs `lean-categories` `a2123729` and
leaf contracts `3c2159b`, a normal-budget, one-run `subspaces.kernel`
benchmark completed with 126 roots and 39,816 identity bytes. Its bindings
read in 6,740 ms (`M`), 5,202 (`v`), 5,011 (`b`), 10,412 (`u₁`), 9,958
(`u₂`), 24,474 (`W`), and 15,089 (`N`); the assertion's semantic reading
took a further 38,166 ms. Thus the earlier 38-second figure was only the
assertion, not the whole admitted request. Question construction was 965 ms;
source encoding 89 ms; remapped-key sorting 1,412 ms; operation fields 72
ms. This diagnostic excludes registration, transport, decoding and external
computation. The remaining latency is chiefly in semantic reading and formal
evidence, and the proposed low-single-digit end-to-end budget is open.

## 2026-10-19 — Read sole registered binders once

The binder reader tried every candidate under an isolated compatibility
check, then read the unique selected candidate again. For a token with
exactly one registered row, candidate selection needs no trial; the selected
row's full dependent signature is checked by the remaining reading. Tokens
with multiple rows keep the isolated uniqueness trials. The upstream
catalogue currently has one `∫` row, and the first integral probe timed out
in the repeated path at 200,000 heartbeats.

After removing that repeat, `lake build CasCatalogue.BinderReaderProbes`
completes successfully (3,716 jobs, 146 seconds on its last target) at the
ordinary heartbeat limit. The target exercises both integral readings,
two limit readings, a limit at infinity, and root-sum/root-product binder
readings. This is a focused reader result, not a passing full build or a
calculus acceptance result.

## 2026-10-19 — Reuse explicitly typed set elements

The set-literal reader previously evaluated each element to infer its set,
then evaluated it again with that set as an ambient input to construct the
subset. A bound element whose stored syntax explicitly says `in X` takes its
ambient from that annotation, independently of the enclosing literal. The
reader now reuses its first value only for that case; other elements retain
the contextual second reading. The chosen subset form and fallback union of
singletons use the same rule.

At the current latest-main dependencies, `subspaces.kernel` from the unchanged
admitted suite now completes under the ordinary 200,000-heartbeat limit:
126 trace roots, 39,816 identity bytes, and 37,914 ms semantic reading. The
entire identity is byte-identical to the prechange diagnostic result. The
`CasCatalogue.Language` and `CasCatalogue.QuestionProbes` targets build. This
removes the 3×3 timeout, but the measured full interpretation still exceeds
the proposed low-single-digit performance budget.

The preceding full `just build` at `645a1f4` failed at the first integral
probe in `CasCatalogue/BinderReaderProbes.lean:11` with a deterministic
`isDefEq` timeout at 200,000 heartbeats. Its remaining long-running jobs
were stopped after this failure; it was not a passing full gate. The binder
failure is separate from the set-literal result and remains open.

## 2026-10-19 — Reuse a rejected morphism parameter as its operand

The generic `morphism` reader used to evaluate the first argument of
`span({u₁, u₂})` as a possible leading parameter. When that set value failed
the declaration's object-parameter check, the reader evaluated the same
syntax again as the first operand. The rejected value now feeds the operand
call in the same reader context, retaining its first trace and avoiding the
second evaluation. This is a generic parameter/operand boundary, not a
special case for `span`.

Before the change, diagnostic evaluation of `W := span({u₁, u₂})` took 90,673
ms with the heartbeat cap lifted; its set-literal argument alone took 48,074
ms. A separately read set value took 54,061 ms, while the registered span
family applied to that value in 1,531 ms. These observations and the
`morphism` call path identify the duplicate argument read. Each bound vector
cost about 12 seconds to evaluate; set-literal reading still evaluates typed
vectors more than once while inferring and forming its subset.

After the change, the ordinary-budget `subspaces.kernel` benchmark reads all
bindings through `W` and `N`, but its assertion reaches a separate `whnf`
timeout. With only the diagnostic probe's heartbeat cap lifted, the assertion
retains 126 trace roots and a 39,816-byte identity byte-identical to the
pre-change source. Its semantic-reading stage fell from 113,291 ms to 59,165
ms. The full `CasCatalogue.QuestionProbes` target now builds successfully;
the previous line-258 span probe failure is gone. These checks do not make the
3×3 assertion usable under the ordinary budget or establish full B0 acceptance.

## 2026-10-19 — Contextual question encoding candidate

The encoder now caches unopened expression syntax with its ordered binder
types and let values, while using opened terms only for Lean's proof/type
inspection. This avoids giving repeated occurrences fresh local IDs before
the cache can identify them. It retains the existing canonical node format and
root insertion order. The `matrices.kernel` question identity matches the
pre-change 28,383-byte serialization exactly (`cmp` over the full strings).

At the same dependency revisions recorded below, a two-run production-path
benchmark reported these timings for `matrices.kernel`:

| Stage | First run (ms) | Second run (ms) |
| --- | ---: | ---: |
| Semantic reading | 10,854 | 9,955 |
| Question construction | 514 | 768 |
| Trace instantiation | 59 | 1 |
| Source encoding | 49 | 55 |
| Remapped keys and sort | 640 | 649 |
| Operation-field encoding | 60 | 34 |
| Final compression | 1 | 1 |

Both runs retained 66 roots and the same 28,383-byte identity. The timed
process peaked at 2,143,984 KiB resident memory; that whole-process number
does not establish an encoder memory improvement. `TermGraphProbes` and
`ProofIdentityProbes` pass. The first reader-mechanics block of
`QuestionProbes` passes separately, covering relations, logical forms,
parameters, selected structures, routes, binder spelling and a wrong-answer
outcome. The full `QuestionProbes` build still times out at line 258 while
reading `W := span({u₁, u₂})`. The complete build, protected negatives,
3×3 benchmark, integrated latency budget and independent acceptance remain
unproved.

## 2026-10-19 — Current question-identity performance baseline

At base source `0c139a8b1cd50abe73b70894fe887b20b962139c` plus this
change's timing hook, with
`lean-categories` `a2123729df092e58b6fb0cd39c78db5e1714faf2` and leaf contracts
`3c2159b510db2ca63455530ed0f4c28ba27da2f8`, the admitted
`matrices.kernel` assertion from `tests/acceptance/linear_algebra.cas` reads to
66 trace roots and a 28,383-byte complete question identity. The reproducible
diagnostic is `benchmarks/question_identity.lean`; run
`/usr/bin/time -v lake env lean benchmarks/question_identity.lean` after updating
own-organisation dependencies and building `CasCatalogue.Realize`. It calls the
production `interpret` path twice in one process and checks exact identity
equality. The timed run peaked at 1,931,060 KiB resident memory for the entire
Lean process; that figure does not isolate encoder memory.

| Stage | First run (ms) | Second run (ms) |
| --- | ---: | ---: |
| Semantic reading | 12,676 | 9,667 |
| Question construction | 2,955 | 2,442 |
| Trace instantiation | 2 | 1 |
| Source encoding | 28,645 | 28,450 |
| Remapped keys and sort | 567 | 688 |
| Operation-field encoding | 28,127 | 27,340 |
| Final compression | 1 | 2 |

The source and operation-field passes dominate both runs. This measures
interpretation only; it does not measure registration selection, transport,
decoding, leaf execution, or complete request latency. The earlier 149.890-second
profile in this journal used a different dependency revision and a 99-root
3×3 assertion, so the two measurements are not a before-and-after result.

At that checkpoint, the 3×3 `subspaces.kernel` benchmark stopped before interpretation while
reading its `W := span({u₁, u₂})` binding: `isDefEq` reached the 200,000-heartbeat
limit. A refreshed `just build` separately reported a timeout in the first
integral-binder probe at `CasCatalogue/BinderReaderProbes.lean:11`; the build
was interrupted after that failure while later probes were still consuming
substantial memory. Neither
run establishes a passing full build or a current 3×3 performance baseline.

## 2026-10-18 — Question identity performance boundary

The matrix-kernel claim records 99 trace roots. A separated exact profile took
62.879 seconds to encode those roots into 640 canonical nodes and 2 ms to
compress the resulting 13,857-byte JSON table. An instrumented copy of the
unchanged encoder made 2,097,785 recursive `isProof` and interner calls;
`isProof` accounted for 10.896 seconds and interning for 28.210 seconds. Thus
final serialization and trace-node metavariable instantiation are not the
cause. Raw context-sensitive expressions are traversed millions of times and
collapse only after their local binders and proof tokens reach canonical node
descriptions.

Two candidate repairs were falsified and removed. Propagating known-nonproof
status down application function spines left exact encoding at 64.201 seconds;
its committed experiment was reverted. A cache keyed by exact expression and
ordered binder context received zero hits because separate traversals use fresh
local IDs. Constructing a fully abstracted cache key at every node crossed two
minutes before completion and was stopped because it repeated the same whole
term traversal. The remaining source repair must prevent generation or repeat
visitation of the expanded contextual expressions while preserving the exact
question-identity format.

A canonical DAG remapper now removes one full expression pass without changing
the established serialization. Focused regressions compare both standalone
identity bytes and reordered shared-table bytes; the proof-identity probes also
pass. Exact production interpretation completes in 149.890 seconds: 13.175
seconds reading, 4.196 seconds building the assertion question, 65.178 seconds
encoding the source DAG, 0.988 seconds deriving all sorted keys by remapping,
and 65.222 seconds assembling operation fields. Pre-encoding every operation
field before the roots exceeded three minutes because the two sets do not
share raw expression cache identities; that experiment was reverted. The
remaining performance work is the distinct source-root/operation-field pair,
not sorting, final compression or metavariable instantiation.

## 2026-10-18 — Selected rational carrier blocks matrix-unit evidence

The six invalid inverse readings reduce to the registered formal evidence for
the matrix-unit constructor. `Units.invertibleEvidence` succeeds on the matrix
`!![1,2;3,4]` over literal `ℚ`, and it fails on the same matrix over the
catalogue's selected rational-ring carrier. `Units.evaluateNumerals` alone
normalizes the displayed coefficients but does not remove the failure. After a
definitionally valid `change` from the selected carrier to
`Matrix (Fin 2) (Fin 2) ℚ`, the unchanged evidence tactic succeeds.

This isolates the cause to formal evidence normalization across the selected
object construction. No alternative evidence, coefficient rewrite, or local
mathematical admission was added. Repair belongs to the formal owner; all six
inverse assertions remain invalid at the current pin until that dependency is
delivered.

## 2026-10-18 — Anonymous endpoint points from formal construction data

The frozen prime-factor and matrix-kernel assertions both failed before
question construction with `a numeral is an element of a named set`. The
formal declarations already supplied the required routes. For
`finiteSubsets Nat.Primes`, the registered prime admission lands at the exact
anonymous endpoint; the reader now evaluates all applicable parameter-free
admissions and requires their points to agree without assigning a named alias
to the carrier. For `powerSet (Fin n → K)`, the matrix operand retains its
direct declared parameters `n,K`. Result recognition now considers only
registered constructors named as codomains of point families, reconstructs
`Vec(K,n)` from those parameters, and rejects distinct constructor rows.
Equivalent applications of one constructor are coalesced only after their
constructed objects agree. The registered vector-zero family is applied with
the retained constructor parameters rather than asking carrier unification to
infer a bundled additive monoid.

At `lean-categories` `fd2cd45f` and leaf contracts `3c2159b`, direct reader
probes establish that the unchanged prime-factor claim and matrix-kernel claim
are valid in 31.3 seconds and 38.7 seconds respectively. The matrix claim with
trace recording produces 99 nodes in 38.9 seconds. Production `interpret`
then spent more than three minutes in post-read trace canonicalization before
the probe was stopped; that performance defect remains open and these focused
reader results do not establish execution, full acceptance, or B0 completion.

## 2026-10-13 — Full inventory observations and temporary artifact residency

The shared-package migration remains intact: its package directory and
normalized Mathlib URL are preserved as separate working-tree changes.
Own-organisation source declarations and resolved input revisions remain on
`main`. The dependency-preparation helper now recognizes Lake's quoted
`«nbdsl-worker»` identifier and updates the actual worker checkout.
The production-shaped real-Git fixture first fails on the missing worker
checkout, then passes latest-main advancement for every dependency and
preservation of dirty worker source. Red/green evidence is
`quoted-worker-{red,green}.log` in the completion directory. The actual
installed worker matches remote main `4c6c2a77abcc717513a65ca35723ed428647e1bd`.

The single computation-only harness at `9370ee5` finished with exit 1.
Its 156 entries report 120 gaps, 15 holds, six internal errors, four
ambiguities, eight invalid readings and three unavailable executions.
The durable report, log and source/input identities are
`.tmp/b0-completion-20261013/harness-9370ee5.{json,log}` and
`harness-9370ee5-process.json`. No assertion or authoritative interpretation
was regenerated from these outputs.

Of the fifteen frozen required IDs, twelve report `holds`: eleven have
nonempty registered dispatch and `sets.eq.rev_rev` has none. The three
`lattices.discriminant.*` IDs are gaps because the latest-main installed leaf
release supplies no applicable cokernel registration. Historical fifteen-ID
execution observations therefore do not establish the current requirement.
The three unavailable outcomes are backend `ValueError` responses about
unnamed objects or a construction apex, not absent Sage/GAP executables.

Reader-only measurements place the differential request at 225,208
heartbeats and the span request at 421,731; identity serialization takes
1,987 and 906 respectively. A single registered named signature was executed
both speculatively and again after selection. Construction source now executes
that unique typed action once; competing signatures retain their independent
applicability checks. Ordinary-budget request probes cover both full readings.

A separate selected-carrier regression reproduced ambiguity for two
presentations of the same complete form. Construction source compares the
complete selected structures and checks every retained source action before
coalescing their provenance. Different structures sharing a carrier remain
subject to the unchanged protected negatives. Validation is running; these
observations do not close a B0 acceptance row.

The first performance correction makes the differential ordinary-budget
probe pass and reduces its reader cost to 125,980 heartbeats. Span remains
421,737 and its new probe fails. Its name denotes both a three-parameter
object constructor and a morphism. The constructor's one-argument partial
application cannot have its registered object type, yet the old trial evaluates
the expensive argument first. Construction source now checks that declared
partial-application type before constructing the trial; compatible signatures
still execute their full typed actions. The speculative closed-source binding
guard was removed before validation. All three companion-matrix requests read
successfully at their own ordinary per-request budget.

The complete `SelectedCarrierProbes`, `ParameterStructureProbes` and
`QuestionProbes` build now finishes with exit 0 (3,729 jobs), including the
unchanged carrier negatives, admitted-point negatives and ordinary-budget
binder, differential and span requests. The durable log is
`closed-source-validation.log`; `closed-source-process.json` records the
construction source hashes and process identity. This establishes the request
mechanism checks, not mathematical acceptance or the full B0 requirement.
Unconsumed temporary `B0_*` evaluator progress prints were removed; evaluation
and its outcomes are unchanged.

The existing owner ruling of 2026-10-10 governs author role separation as
conduct even when broader credentials exist. Conflicting author-capability
wording in AGENTS, architecture and the plan now states that ruling.
Independent protected acceptance and authoritative transition controls retain
their separate obligations.

Eighteen inactive ELF harness executables occupied 6,516,485,888 bytes under
`.tmp`. After checking live process executable paths, all eighteen were compressed
with Zstandard checksums, retaining recoverable copies and original source/log
records. Temporary residency fell from 7.0 GiB to 2.3 GiB; no source checkout,
acceptance report or live compiler artifact was deleted. The per-file inventory
is `obsolete-binaries.json` in the completion directory.
All eighteen compressed copies pass Zstandard checksum validation;
`obsolete-binaries-integrity.log` records each result.

Hosted controller source validation at `4e14c11` passed (run `38417669602`),
as did boundary integrity, build/audit and kernel purity. Hosted acceptance
regression remains failed; its unchanged mathematical assertions require the
source repairs and independent question-preservation assessment.

## 2026-10-13 — Complete build, source publication and controller snapshots

At clean source `9370ee5be07bd0d45fe593688008e353e5c9367c`, the complete
`just build` finished with exit 0 and 7,551 jobs. Kernel purity and its protected
negatives passed with the admitted-point observation isolated. The ordinary
installed push gate passed and normal `git push` published that source to main.
The shared scanner work unit ai-review-ci#468 is closed after that downstream
publication. The final typed-term identity sample still matches its saved
pre-cache bytes exactly.

The full computation-only harness runs once at that recorded source and
executable hash; `harness-9370ee5-process.json` owns its process, log and exact
latest-main inputs. Controller source work does not alter those kernel inputs.

Hosted controller check `38414011963` failed while copying a live Git object
database: object paths vanished during fixture `copytree`, and a production
local-filesystem clone also failed. Repository snapshots now use Git's regular
transport (`--no-local`); fixture copies clone committed repositories and their
dependencies rather than copying `.git` directories. Git's
[clone documentation](https://git-scm.com/docs/git-clone) distinguishes this
transport from local object-directory copies. The real full transition fixture
passes 79/79; an actual garbage collection of its source repository completed
while it ran. The durable outputs are `controller-ci-9370ee5.log`,
`controller-transport-fixture.log` and `controller-transport-gc.log` under
`.tmp/b0-completion-20261013/`. This is snapshot transport evidence, not an
independent B0 acceptance grant.

## 2026-10-13 — Isolate registered-evidence observation artifacts

The complete build at `62d3a69405ef89dfb2fef283328b8e44176e14ee` finished
with one failed target, `CasGates.KernelPurity`; all other requested targets
completed. The ordinary-budget binder probe and the admitted-point protected
negatives passed, as did acceptance registration and notebook boundaries.
The purity failure named seven factorial equation/splitter lemmas generated
by registered evidence execution in the probe module. Isolating only the last
binder observation did not remove them; build `79fa7b1` repeated that failure.
An environment checkpoint before each of the nine observations showed no
factorial equation lemma before observation eight, and its presence before
observation nine. The admitted-point observation, not the last binder, creates
these artifacts.

Both complete request observations now use Lean's `withoutModifyingEnv`, which
restores the incoming environment after their positive and protected negative
checks. The purity gate, import coverage and allowed-module list remain unchanged.
The failed runs and the diagnostic remain in
`.tmp/b0-completion-20261013/build-62d3a69.*`, `build-79fa7b1.*` and
`question-environment-detail.log`.

## 2026-10-13 — Preserve actual structured result parameters

The matrix coefficient reader regression failed because result recognition
searched outer operands without their retained constructor parameters. Expanding
those actual parameters exposed a second defect: a complete structure and its
checked forward view were counted as unrelated selections. Recognition now
uses the existing full-source/carrier-route check, plus the operation's complete
declared parameter slots, including implicit arguments. It coalesces views only
at a fixed complete typed parameter and retains their checked source alternatives.

At upstream main `fd2cd45f6d81645f0b46632cc2fddb604299eb74`, matrix literal
construction and determinant reading pass. `ParameterStructureProbes.lean`
passes in full; `SelectedCarrierProbes.lean` passes with the unchanged map/vector
and distinct-form shared-carrier negatives. Added fixed-parameter checks retain
the exact chosen form in either candidate order, and reject two distinct full
parameters. Repeating the same full parameter in two slots reproduced an
ambiguity before the correction and passes afterward. Durable red/green outputs
are `repeated-parameter-red.log`, `repeated-parameter-green.log` and
`full-parameter-green.log` under `.tmp/b0-completion-20261013/`.

The final source also refuses conflicting selected categories before choosing a
parameter category. The complete build checks that source checkpoint, including
the large-question serializer and its ordinary-budget binder probe. No permanent
mathematical assertion or admitted interpretation was rewritten.

## 2026-10-13 — Shared scanner correction integrated

Independent reviewer and native downstream scanner regressions verified
ai-review-ci PR #469 at `088892b1690024a22317d7afe50dcac4b3b59254`.
Hosted QC passed at that exact head (run `38398299480`); fresh feedback
collection closed all five review threads with evidenced dispositions.
Source integrated as `9b43a56c23518412dd4aa145441f0d4bc6425cb7`, then the
ordinary installed `just test-push` returned 0. Its durable output is
`.tmp/b0-completion-20261013/integrated-qc-9b43a56.log`. The caller remains
dirty, so its retained scanner report is not a committed-revision report.
Nine suffix findings and three native parsing diagnostics remain reviewer
input; their individual source-level dispositions are recorded in
`custodian/FINDINGS.md`. No source name, exclusion or blocking exception was
changed downstream. This integration establishes the publication gate, not
kernel computation correctness or B0 acceptance.

Closed-subterm question serialization passed `ProofIdentityProbes.lean` and
preserved the five independently saved binder/proof/selected-dictionary
identities byte for byte. The complete binder request also exposed competing
retained parameter views. Its correction is being checked against the
operation's full declared parameters and same-carrier protected negatives;
no permanent assertion or interpretation record was changed.

## 2026-10-13 — Full latest-main computation-only harness result

The original background run finished with exit 1; it was not stopped or relaunched.
The immutable report is `.tmp/b0-completion-20261013/harness.json`, with exact inputs
in `harness-inputs.json`. It records 155 entries: 15 holds, 104 NoImplementation
gaps, 3 unavailable executions, 16 invalid interpretations and 17 internal failures.
The admitted inventory contains 153 identities; anonymous statement entries account
for the extra report rows and are not extra admitted assertions.

Eleven frozen required identities hold with registered dispatches. `sets.eq.rev_rev`
holds with no dispatch; current leaves main has no `mor.sets.fin_rev` registration.
The three frozen discriminant identities report missing
`colim.bil_w_form.cokernel` registrations. The previous October 10 focused results
therefore do not establish the required latest-main tuple. No leaf was modified.

Internal failures include category-family inference through `mkAppM Category`,
admitted-point category retention, and deterministic elaboration heartbeat exhaustion.
Invalid interpretations and internal errors remain kernel obligations; they are not
accepted NoImplementation outcomes. The permanent assertions remain unchanged.

## 2026-10-13 — Recover full B0 integration validation

- Current construction source began at `70e0364`; the existing uncommitted
  `AGENTS.md` correction is preserved. No earlier compiler or harness was live.
- The full `just build` runs once under PID 3817498, with log
  `.tmp/b0-completion-20261013/build.log` and recorded source/process metadata.
  Dependency refresh resolved `lean_categories` to `1a538db0796851e31de946bb4b01844ede14f0d3`.
  The build has not yet discharged integration acceptance.
- Corrected `scripts/ci_chain.py`, `track-main` and CI preparation to consume latest
  `main`, including the non-Lean leaves checkout. The previous CI script also used
  an unsupported `git checkout --end-of-options` invocation. A real local Git
  regression verifies latest-main selection, repeat execution and dirty-work
  preservation. Permanent acceptance and no-leaves static checks pass.
- Recorded the existing owner rulings on latest-main dependencies and durable
  background validation in the owning architecture document. This introduces no
  mathematical requirement or authority transition.
- Controller, launcher, author-launch, materialization, assessment and context
  fixtures pass with global Git hooks disabled only in their disposable test
  repositories. The repository's ordinary commit hooks remain active.
- Latest-main leaves are `48a99b5bcb2b090e1c778db29f006b612bed02ed`.
  The repository `.venv/bin/python` successfully runs the modular Sage and GAP
  entry points: `sage.all__sagemath_modules` and `sage.all__sagemath_gap`
  (integer arithmetic returns 4 and a cyclic group's order returns 7).
  `sage.all` is absent from this modular installation and is not its entry point.
  Earlier selected-assertion reports do not establish execution at these newly
  consumed inputs.
- All 11 script fixtures pass, including a further remote-main advance; they now
  run in `build`. Preparation finishes with `lake update` so Lake records the
  revisions it will compile. Full computation-only acceptance is queued once
  behind the successful integration build, under PID 3930594, with log
  `.tmp/b0-completion-20261013/harness.log`; its execution records all consumed
  dependency revisions in `harness-inputs.json` beside the report.
- The isolated review transition fixture completes with **79/79 checks holding**,
  including construction replacement, outage handling, reconsideration and large
  snapshot retrieval. Fixture keys and model responses establish controller
  wiring only; they confer no independent approval or B0 acceptance.
- The full build has compiled `CasGates.KernelPurity`, its protected negative
  probes and the harness executable. Registration and notebook boundary probes
  remain live; no full-build success is asserted from these partial results.
- The static push gate found existing controller defaults, a mocked context test
  and Lean name-suffix findings; it remains unsatisfied. Two red regressions
  reproduced acceptance of a signed decision omitting `findings` and a tool call
  omitting `arguments`. Required controller/request/discussion fields now fail
  when absent. The controller, all 11 launcher cases and complete assessment
  fixture pass after the correction. This changes construction source only.
- The subsequent controller regression also reproduces and repairs acceptance
  of `findings: null`; findings now require an explicit list. Both real context
  file tests pass after extracting the existing materialization lifecycle and
  removing their reviewer/budget monkeypatches. The remaining nine static
  name-suffix findings are recorded in `custodian/FINDINGS.md` with their actual
  engineering scope; the gate remains failing and has not been weakened.
- The full integration build completed successfully: **7,551 jobs**, exit 0 in
  `.tmp/b0-completion-20261013/build.exit`. All Lean kernel, gate, probe, tool
  and notebook-boundary sources are unchanged between its starting source
  `70e0364` and the current construction commits. This includes compilation of
  the protected kernel-purity negatives and axiom audit; it does not establish
  the permanent assertions or independently accept B0.
- The single queued full harness run is now preparing latest-main inputs under
  PID 3930594. Its log and final report are
  `.tmp/b0-completion-20261013/harness.log` and `harness.json`; its actual input
  revisions are recorded before execution in `harness-inputs.json`.
- `git push origin main` was refused by the ordinary pre-push hook's remaining
  nine Lean name-suffix findings. Exact output is
  `.tmp/b0-completion-20261013/push.log`. No hooks were bypassed. Publication
  and final independent acceptance remain outstanding; the live harness is not
  relaunched or stopped for elapsed time.

## 2026-10-11 — b0-typed-application: preserve explicit subset result contexts

After the scalar-parameter repair, the next unresolved reading was the unchanged binding
`let Fs := {h ∈ ∫ f dx | h(0) = 0} in 𝒫(ℚ[x])` from `differentials.cas`.
It failed with `only a map X → Y is applied`. The subset-comprehension domain and unary
primitive application both discarded the explicitly supplied power-object result context.
The primitive map therefore returned a power object over an anonymous polynomial carrier,
which correctly supplied no callable declaration for the predicate's generic element.
The diagnostic `.tmp/b0-primitive-callable.log` records that absent origin and callable.

Forward the existing expected result through these two calls. `applyFamily` still checks
the original dependent signature before retaining the complete supplied target. The
polynomial evaluator comes from the explicit `𝒫(ℚ[x])` annotation, not from identifying
an anonymous carrier with a convenient named object. No mathematical map, admission
evidence, expected answer, or upstream registration is added or changed.

At Language blob `26da62af57486c1b26eca2ee851b23fd801f9bf9`, ContextualSubsetProbes blob
`d7b6d7fecbf1a18cd257577a31b2468ebe99e893`, lean_categories `76ca85d7`, and contract
`e292368d`, the completed observations are:

- `.tmp/b0-subset-context-language.log`, BUILD_EXIT=0: direct reader compilation.
- `.tmp/b0-subset-context-probes.log`, CHECK_EXIT=0: the explicit complete power-object
  target and its callable base are retained; erasing the declaration cannot recover a
  callable from the bare carrier; an incompatible polynomial-coefficient target is invalid.
- `.tmp/b0-subset-context-primitives.log`, CHECK_EXIT=0: the original polynomial binding
  retains 27 closed, type-correct trace terms and the unchanged `Fs` binding retains 70.
  The selected input texts were checked against the permanent source without editing it.
- `.tmp/b0-context-normalized-count.log` and `.tmp/b0-context-normalized-equality.log`,
  both CHECK_EXIT=0: the same original bindings and the unchanged
  `integration.normalized_count` and `integration.normalized` assertions read successfully,
  retaining 72 and 104 closed, type-correct trace terms respectively.
- `.tmp/b0-subset-context-selection.log`, CHECK_EXIT=0: SelectedCarrierProbes still passes,
  including the Maps/Vec and distinct-form positive and negative observations.
- Acceptance-permanence, reuse-record and whitespace checks pass.

The positive and negative observations of this context-propagation repair hold together.
This is validity of the original reading, not evaluation of a primitive or its cardinality.
The full `b0-typed-application` row still requires every admitted assertion to read at its
declared types; no new entire B0 row is closed by this unit. The existing selected-structure
observations remain verified at this source. The remaining differential-workflow readings
after these observations are the explicit `F` binding and its differential, derivative and
evaluation assertions; the other admitted files still require the same row-wide check.

The focused companion check at the preceding committed reader also completed successfully:
`.tmp/b0-next-companion.log` validates the original `r` and `C` bindings and
`composed.charpoly`, with 29, 38 and 42 closed trace terms respectively. These are not
backend outcomes. The contract-dependent execution and owner-reserved coherence failures
remain separate; there was no contract polling, publication, or repeated full build.

## 2026-10-11 — b0-typed-application: complete parameters from structured operands

The `differentials.at_two` refusal was in generic parameter inference, not a missing
mathematical scalar-algebra construction. `registeredStructuredParameter` demanded a closed
constructor before its actual structured image could determine the target ring and map.
It now constrains the declared constructor by that image, completes remaining arrow parameters
from registered maps or the categorical identity at fixed endpoints, and checks the full
closed application through the ordinary route classifier. Named endomorphisms compete with
identity rather than being silently replaced by it. Anonymous carriers provide no structure.

Only a witness whose actual outgoing action reaches the operand is eligible; coefficient
objects elsewhere in its provenance do not select a different target. Repeated complete
images are coalesced within a target category. The chosen constructor and inferred maps are
recorded by their actual declarations, without a second name-recovery pass. `applyFamily`
retains one isolated inference result and its private trace, merging it only after its
operand endpoints and full application type check. It no longer reruns the entire search
just to reproduce its trace. The ordinary reader heartbeat budget is unchanged.

The extension control also exposed two registered presentations of the same complete scalar
algebra: the generic constructor and the named rational-to-complex algebra. All full candidate
structures are checked before choosing a serialization representative. The existing
`parameterEquivalence` record retains both declaration identities, all ordered parameters,
and kernel-checked equality witnesses for the complete structures. Different full structures
remain ambiguous; equality of carriers alone is insufficient.

Final checked source: Language blob `2030754fc04f05c8422eb2ea5967857915972d21`,
StructuredParameterProbes blob `43da68a257ace1818ed5d2ca7472a2cba614443b`,
lean_categories `76ca85d7bc35bf55b6268c81f8807ef46b6ab063`, and contract
`e292368d5ebbebc90833e0c0f78261d1436231d9`. Completed checks:

- Direct Language compilation: `.tmp/b0-scalar-equivalence-language.log`, BUILD_EXIT=0.
- The unchanged `.tmp/b0-reader-poly-eval.json` input passes actual `Language.claim`
  reading in `.tmp/b0-scalar-final-at-two.log`, CHECK_EXIT=0: the original binding retains
  27 closed, type-correct trace terms and `differentials.at_two` retains 40. This establishes
  validity of the reading, not evaluation or proof of its numerical answer.
- `.tmp/b0-scalar-parameter-controls.log`, CHECK_EXIT=0: exact self and nonidentity scalar
  maps; complete equivalence provenance; anonymous-carrier acquisition refused; named
  endomap versus identity ambiguous; missing coefficient map refused; incompatible operand
  rejected as `invalid` at a fixed complete dependent application.
- `.tmp/b0-scalar-selected-carrier-regression.log` and
  `.tmp/b0-scalar-parameter-structure-regression.log`, both CHECK_EXIT=0. Existing Maps/Vec,
  distinct-form, forward-view, missing-witness and coefficient-coercion controls still pass.

The first standalone probe exposed a spurious ambiguity from reinterpreting the already
selected constructor; the next exposed irrelevant coefficient witnesses. An earlier full
reading reached its heartbeat limit. Those failures were repaired in this unit, not accepted
as results. Two subsequent test sessions were invalidated by the connector before returning;
their incomplete logs are not results. The final completed runs above replace those attempts.
The positive and negative observations of this parameter-inference unit all hold together;
the existing selected-structure row observations remain verified at this source.

The full `b0-typed-application` row is not closed by one repaired reading: all admitted
assertions must still satisfy its positive observation. Shared-contract execution checks
and the owner-reserved CohereProbes failure remain separate dependencies. No permanent
acceptance statement, upstream mathematical source, leaf, or shared contract was changed.

## 2026-10-11 — b0-selected-structure: declared identity and full table observations

Completed the inherited selected-structure unit before further evaluator work. Recognition
now uses the actual registered declaration and its complete parameters or retained selected
values, never a search for a reducible alias of a bare carrier. Dependent binder domains and
result parameters retain the objects prescribed by their supplied arguments and public
inclusions. Forward carrier views retain their provenance; they do not recover a named
structure on an anonymous source.

All positive and negative observations of the `b0-selected-structure` table row hold at
Language blob `7e8a7cc4bcc67a21fe0d6ef91b35625f95fa1b2a`, SelectedCarrierProbes blob
`a76b7bc71a5cdcc5b97a6cc0fba38a1303e5c39d`, lean_categories `76ca85d7`, and
cas_leaf_contracts `e292368d`. The completed full build in `.tmp/b0-stage-a-full.log`
reports SelectedCarrierProbes built successfully: Maps and Vec retain distinct declared
identities in either candidate order; zero and multiplication forms on the same module
retain their complete choices; a common carrier without a witness selects neither, and
opposite carrier-only coercions between the forms are refused. The dependent-result probe
also retains the ambient supplied by the domain's actual inclusion. These assertions test
the generic recognition rule: name recovery is restricted to declaration identity, while
candidate order cannot remove multiple retained choices.

That same completed build passes Language, ParameterStructureProbes and BinderReaderProbes.
The unchanged factorization reading also completes with 118 closed, type-correct trace terms
(`.tmp/b0-selection-complete-factorization.log`, CHECK_EXIT=0). The full build finishes with
B0_BUILD_EXIT=1, reporting only the owner-reserved CohereProbes and contract-dependent Realize
failures; neither was suppressed. Thus the selected-structure row observations hold, not the
entire B0 table or independent final acceptance. The next unblocked selected unit is
`b0-typed-application`: the scalar-algebra parameter of `differentials.at_two`.

## 2026-10-11 — b0-domain-preservation: expose supplied carrier projections

The next `factorization.over_complexes` refusal was also in the kernel: the complete
admission obligation was definitionally the published constant-polynomial unit obligation,
but its carrier remained a projection of the registered algebra-forget action. Reducible
weak-head normalization left that projection stuck. The published units evidence already
handles canonical complex constant polynomials, including the initial-ring-map numeral;
no upstream evidence case is missing for this input.

The final presentation step now expands the existing plumbing owners only inside closed
type expressions that still reduce to a projection, after dictionary presentation. It
preserves predicate and arithmetic heads, the selected multiplication, the original
admission map, and the original complete obligation. Both the presented target and the
returned evidence are checked against that original obligation. An initial broader
carrier-expansion attempt failed the new positive probe by exposing function dictionaries;
it was replaced, not accepted as a result.

At `lean_categories` 76ca85d / contract e292368, the final Language build completed with
exit 0 (`.tmp/b0-carrier-final-language-build.log`). EvidencePresentationProbes completed
with exit 0 (`.tmp/b0-carrier-final-probes.log`): the published procedure establishes the
retained constant unit at its original obligation, while zero remains `invalid`.
ParameterStructureProbes also completed with exit 0 on this combined source
(`.tmp/b0-carrier-final-parameter-probes.log`), including the preceding coefficient fix's
forward, reverse-rejection, missing-witness and wrong-parameter cases.

The unchanged `factorization.over_complexes` now reads successfully: all 118 retained trace
terms are closed and type-correct (`.tmp/b0-carrier-final-factorization.log`, exit 0). The
four required calculus readings—limit_sinc, limit_infinity, integral_square and integral_sine—
also complete with closed, type-correct traces (`.tmp/b0-carrier-final-calculus.log`, exit 0).
These are actual reader observations, not backend evaluation or proofs of the numerical
factorization and calculus assertions.

The repaired coefficient and evidence-presentation units' positive and negative observations
hold together. This does not close all observations of either B0 table row or establish the
contract-dependent execution path. `b0-typed-application` still has the distinct
`differentials.at_two` application failure; it requires an exact chosen scalar-algebra
parameter for the published polynomial evaluator. The domain-preservation row's full
acceptance is not declared complete by these focused probes. No permanent assertion,
upstream mathematical source, leaf, or public contract was changed.

## 2026-10-11 — b0-typed-application: constants at witnessed coefficient views

The coefficient-inclusion refusal is a kernel coercion defect. The selected polynomial
target already retains its registered constants declaration and complete coefficient
parameter, but the source point may have that parameter's weaker ring interface. The
reader formerly demanded a reverse structural coercion before it could apply the constant
map. `identityCarrierView` now factors the existing exact forward-view check. The constants
branch uses that check against the independently supplied target parameter, then applies
the unchanged registered constant map at its original parameters and fixed endpoints.
It does not recover a stronger structure on the source or invert a nonidentity map.

At `lean_categories` 76ca85d / contract e292368, the focused Language build completed with
exit 0 (`.tmp/b0-coefficient-language-build.log`). The full ParameterStructureProbes file
completed with exit 0 (`.tmp/b0-coefficient-parameter-probes.log`). Its new positive checks
the actual constant arrow at the selected polynomial target. Its negatives refuse reverse
structure recovery, a coefficient with its action witness erased, and a different coefficient
parameter; an attempted application at that wrong parameter reports `invalid`. The existing
chosen-structure and forward-view observations still pass.

The unchanged `factorization.over_complexes` reading now gets past coefficient inclusion
but fails later at admission of the constant polynomial `C 2` into units
(`.tmp/b0-coefficient-factorization.log`, completed exit 1). The published upstream evidence
succeeds on canonical complex and rational constant polynomials, including the image of 2
under the initial ring map (`.tmp/b0-polynomial-unit-evidence.log`); therefore this failure
does not yet establish a missing upstream units case. The exact retained admission target
and evidence presentation need to be compared, without changing the assertion or its domain.
The separate `differentials.at_two` reading also completed and remains invalid at the
published polynomial-evaluation application (`.tmp/b0-coefficient-polynomial-evaluation.log`).

The tested coefficient-coercion unit's positive and negative observations hold. The entire
`b0-typed-application` row remains open; neither of these two permanent readings is claimed
to hold. No contract branch polling, leaf changes, upstream edits or publication occurred.

## 2026-10-11 — b0-binders: share the context-free argument reading

This unit contains only the generic binder argument-sharing change, its root-sum/root-product
reader probes, and its reuse record. When exactly one supplied argument has the same unscoped
reading in every candidate signature, evaluate it once and retain its complete value and
trace. Each candidate still checks its own dependent signature; contextual or multiple
arguments retain their previous path. The unique chosen binder's domain evidence is still
established only after selection. No operation-specific reading or increased heartbeat
budget is introduced.

Existing reader observations at `lean_categories` 76ca85d / contract e292368 record successful
reading of the four required calculus statements (`.tmp/b0-reader-calculus.log`), all four
series statements (`.tmp/b0-reader-series.log`), `composed.root_sum`
(`.tmp/b0-reader-root-sum-fixed.log`), and `composed.root_product`
(`.tmp/b0-reader-root-product-current.log`). These logs concern validity and retained typed
terms, not numerical truth. The root-probe addition checks the selected binder row, closed
well-typed parameters, actual body, admission and original generalized-point domain.

Fresh checks at the combined committed Lean source (`Language.lean` blob `abb78b4a08499a4059066aee4178422af876f8c7`),
after the required dependency refresh retained 76ca85d / e292368:

- `.tmp/b0-binders-8825b08-calculus.log` exits 0: all four table-named calculus readings
  succeed and every retained trace term is closed and type-correct.
- `.tmp/b0-binders-8825b08-root-sum.log` and
  `.tmp/b0-binders-8825b08-root-product.log` each exit 0. Both use the unchanged permanent
  assertion and its original polynomial binding. The unused `roots` binding is omitted
  from these focused runs; neither assertion refers to it.
- Source inspection of `evalAnalysis`, `binderReading`, and `binder` establishes the stated
  negative observation: binding syntax supplies a token, arguments and body to the same
  generic function; candidates come from `state.binders`; declaration, domain and parameters
  come from the selected row, not an operation-specific case. Shared evaluation is restricted
  by all candidates' dependent signatures, not by a binder id or mathematical function.
- The combined binder-probe command and series batch each reached their 150-second bound
  (CHECK_EXIT=124); neither is a completed successful check. The series log reaches a successful
  reading of `series.coefficient_two` but not the three remaining coefficients. The narrower
  root runs above completed; no time limit or acceptance assertion was relaxed.

The full `b0-binders` row therefore remains open: its remaining series observations have not
all been re-established in completed runs at this source. No full row is marked complete
from these component observations. These results are recorded in the same binder-unit commit,
not in an extra status-only commit. B0 integration remains a separate failure; reader work
is not waiting on the contract owner.

## 2026-10-11 — b0-selected-structure: retained forward carrier views

The forward-view unit is committed separately from binder argument sharing. `coercionMap`
accepts a structure-forgetting carrier view only from its retained complete source, the
actual prefix of that source's registered carrier route, and replayed applications giving
its exact selected target. Equal carriers alone remain insufficient; reverse structure
recovery remains refused. Inclusion failures now retain the selected endpoints in their
diagnostic. `SelectedStructureProbes` imports the reader directly instead of the
contract-dependent test runner; its existing assertions are unchanged.

Unit positive and negative observations hold in the completed focused build
`.tmp/b0-forward-view-probes.log`: the forward ring-to-monoid carrier view succeeds,
reverse recovery is refused, deleting the action witness prevents the same-carrier view,
and the existing full-structure distinction checks pass. The log ends `Build completed
successfully (3716 jobs)`. Dependencies are `lean_categories` 76ca85d and contract e292368.
This does not establish all observations of the table row: the table additionally names
two forms on one module and Maps/Vec; a complete row-wide result is not recorded here.

The detached full build has now genuinely finished, rather than timing out:
`.tmp/b0-stage-a-full.log` ends `build failed`, with only `CasAcceptance.CohereProbes`
and `CasCatalogue.Realize` in its failed-target list. The former remains reserved to its
requirement owner; the latter reports the absent shared-contract packet interfaces.
Those failures do not stop the independent reader units. No contract remote polling or
publication is part of this unit.

## 2026-10-11 (B0 reader ambiguity and unit admission observations)

- Removed the reader's dependency on the contract's absent `semanticAmbiguity` constructor.
  Interpretation now owns its ambiguity tag, reusing Lean Core's `MessageData.tagged`,
  `throwError`, `Exception.toMessageData`, and `MessageData.hasTag`. All reader producers
  retain their previous conditions and messages. The public reader outcome is still
  `ambiguous`; a semantic exception during execution remains `internal`. No backend
  stratum, mathematical row, admission procedure, or public packet grammar was added.
- The helper and Semantic compile against contract main `e292368`, with `lean_categories`
  `76ca85d`. Direct compilation of `CasCatalogue/Language.lean` to its OLean succeeded;
  `lake env lean CasCatalogue/ParameterStructureProbes.lean` then exited 0. The probes check
  the retained complete quotient ring and multiplication route, preserve distinct full
  structures, and classify the unrefined residue carrier as ambiguous. Logs:
  `.tmp/b0-reader-language-lean.log`, `.tmp/b0-reader-parameter-probes.log`.
- Checked the six unchanged unit assertion texts through the actual `Language.claim` reader
  and the existing kernel-checked Codec. The rational inverse and division and the `ZMod 5`
  inverse all report `holds` in `.tmp/b0-unit-reader-codec.log`. That first diagnostic exited 1
  on its later false case because it omitted production's per-attempt exception handler.
  After matching `Realize.evaluatedDecides`' bounded unsuccessful-attempt handling, the
  remaining negatives report `wrong`, `invalid`, `invalid`, respectively; the focused run
  `.tmp/b0-unit-reader-codec-negative.log` exited 0. The false rational equation is refuted
  by a kernel-checked proof of its original negation. No leaf or missing upstream units row
  was established by these checks.
- Reran the requested full background `just build`, including its latest-main update and
  repository checks, with a 180-second bound. It rebuilt the helper and Semantic native
  objects and reported the untouched requirement-owner-pending `CohereProbes:42` failure.
  It exited 124 while compiling Language, before Realize or RegistrationProbes completed;
  `.tmp/b0-unit-reader-full-build.log` is not a successful integration result. No build
  process was left running. The focused direct Language compilation above remains the
  available reader compilation result; the full build was not broadened or repeated.
- These are reader/Codec component observations, not execution of the ordinary Realize
  consumer. The current contract main still lacks `Backend.ComputationalValue` and
  `Backend.PointInvocation`, used by Realize. Although its transport carries arbitrary JSON,
  the complete packet grammar belongs in the separately published contract
  (`specs/leaf-registration.md`, wire grammar; architecture, contract ownership). The compatible
  published `b0/construction` source `d7b087b` must be integrated into contract main; a private
  kernel grammar or dependency branch override would not satisfy the current contract.
  Neither the admission row nor the broader units row is marked established by this check.

## 2026-10-11 (B0 unit-inverse refutation)

- Completed the isolated released-unit construction with the same evidence-presentation
  transformation used by `Language.establish`. Admission succeeds for the retained rational
  monoid. On `080779e`, Codec proves its true inverse equation but cannot refute the false
  equation. The earlier isolated admission refusal omitted this presentation step and does
  not establish a missing upstream unit-evidence case.
- Fixed the remaining generic Codec defect: negative equations did not traverse function
  wrappers that lack their own equality-decision instance. The new branch projects an actual
  one-field structure at the original complete equality type, recursively refutes the field
  equation, and applies that refutation to `congrArg` of an assumed record equality. It uses
  Lean's existing structure metadata and projection builder, supplies no instance or domain
  theorem, and cannot project quotient representatives. Final original-proposition kernel
  checking is unchanged. Independent source review found no blocking defect.
- `lake build CasCatalogue.CodecConditionProbes` passed, including the added true/false
  function-wrapper observations (`.tmp/b0-unit-refutation-codec-build.log`). The focused
  released-construction checks preserve the full rational and `ZMod 5` monoid parameters,
  invoke the published admission evidence, and check the group-inverse identification. Both
  true inverse equations and both false variants are proved/refuted with kernel-checked
  proofs; logs `.tmp/b0-unit-rational-refutation-check.log` and
  `.tmp/b0-unit-zmod-refutation-check.log`, both exit 0. These are component observations,
  not executions of the `RegistrationProbes` statements through the current reader.
- Reran the requested full background `just build`, bounded at 120 seconds. It reported
  `Semantic.lean:141,351` missing `Stratum.semanticAmbiguity` and the untouched
  requirement-owner-pending `CohereProbes:42`, then exited 124 at the bound. Log:
  `.tmp/b0-unit-refutation-full-build.log`. Contract remote main is still `e292368`; the
  required compatible source exists on its published descendant `b0/construction`,
  `d7b087b`. Integration of that public contract source into main remains necessary to
  execute the unchanged RegistrationProbes blocks at the current tuple. No B0 row is
  marked established by these component checks or by the incomplete full build.

## 2026-10-10 (B0 unit-inverse candidate; current contract integration blocks verification)

- Investigated the unchanged `RegistrationProbes` unit observations at kernel `95382b8`.
  The consumed `lean_categories` `76ca85d` already supplies the units admission/evidence,
  units functor and group inverse. No missing `lc-units-structure` row or leaf implementation
  was established. The rational gap discarded a retained parameter-equivalence presentation;
  the quotient reader selected the unrefined residue set instead of its declared ring, leaving
  distinct additive and multiplicative monoids as candidates.
- Candidate kernel changes retain `obj.rings.integers_mod` as the quotient's selected complete
  structure and use existing `realizedParameters` for admitted points, including the returned
  payload dependencies. Closed ordinary discharge reuses `Codec.conditionProof`; the original
  proposition is still kernel-checked and computation-only mode still skips discharge. Codec
  now tries the original type's published decision instance before carrier normalization and
  keeps negated equations visible to the existing equation-data proof transport. No inverse
  theorem, equality instance, mathematical row, leaf or acceptance expectation was authored.
- `lake build CasCatalogue.CodecConditionProbes` completed successfully after importing the
  existing `LeanCategories.Foundation.Mathlib` instance into that engineering probe. The probe
  establishes the true finite bundled-function equation, rejects its negation, rejects the
  false equation and establishes its negation. Log: `.tmp/b0-units-codec-probes.log`. The first
  two probe attempts failed on the negative case before the original-type decision was tried;
  their failures were not accepted as evidence. These are codec observations, not verification
  of either unit-inverse assertion.
- The required latest-main update changed `cas_leaf_contracts` from the previously consumed
  `bcd4721` to current `main`/`origin/main` `e292368`. That current main lacks
  `Stratum.semanticAmbiguity`, `Backend.ComputationalValue`, `Backend.PointInvocation` and the
  later published invocation/admitted-point wire interface. The focused owner build stops at
  `Semantic.lean:141,351` with unknown `Stratum.semanticAmbiguity`. The compatible public
  contract must be integrated by its kernel/contract owner; replacing ambiguity with invalidity
  or copying the missing public port into the consumer would not satisfy the contract.
- Reran the full requested background `just build`, bounded at 240 seconds. It reproduced
  those two Semantic errors and the existing requirement-owner-pending `CohereProbes:42`
  failure, then the bound terminated the remaining build (exit 124). Log:
  `.tmp/b0-units-full-build.log`. Re-read the assigned B0 construction boundary and narrowed
  the next action to the incompatible contract, without another broad build. The refreshed unit
  observations could not execute; neither their rows nor stage-A integration is established.
  The candidate is preserved for verification after the steward reconciles contract main.

## 2026-10-10 (B0 three additional frozen registered-backend witnesses)

- Ran the frozen assertions `sets.card.integers`, `sets.finite.integers`, and `sets.implemented.card_fin` in independent focused files, without changing their expressions, using the current corrected native `.tmp/b0-refinement-routed-harness` and installed specimen. All three individual assertion records report `kind=holds` with exactly one actual registered backend dispatch each. Report `.tmp/b0-integers-report.json`. A preliminary concatenation of separate two-line assertions into a single file caused a reader parser error; it was corrected by separating the unmodified assertions into separate files, with no evaluator or acceptance changes. The isolated suite still exits nonzero for the other required inventory entries omitted from the focused run.
- This increases the explicitly checked required-assertion witnesses at `b044ad9` to at least six (`sets.card.z4_cubed`, `sets.card.z7`, `sets.card.z5_empty_power`, and these three). Required created products, coproducts and pullbacks still lack admitted method registrations for their constructed image forms; no unverified result-form coercion is authorized.

## 2026-10-10 (B0 frozen cyclic-cardinality regressions)

- Re-ran the individual frozen required assertions `sets.card.z7` and `sets.card.z5_empty_power` against the corrected native `.tmp/b0-refinement-routed-harness` and installed specimen registrations, in separate tightly scoped suites. Both returned **holds** with exactly one real backend dispatch each: `.tmp/b0-z7-only-report.json` and `.tmp/b0-z5-only-report.json`. The process exit status is nonzero because the deliberately isolated suites omit other required inventory entries; the two individual assertion records are `kind=holds`, with no associated failure. Neither the accepted assertions nor the backends were modified.
- This validation establishes two additional requirement-3 witnesses at current commit `b044ad9`. The independently confirmed constructed-product and created-pullback result-form cardinality/finiteness admission gaps remain unresolved; no kernel-only registration substitution is justified.

## 2026-10-10 (B0 registered retained-route refinement now reaches Sage product)

- Repaired `Realize.lean`'s `.retainedRoute` dispatch: this branch always selected `transportImage`, bypassing already published object refinement rows even when its stored full functor applications were definitionally identical to the registered route. It now checks each **actual retained application** against its registered edge with Lean's definitional equality, selects `transport` (which checks the full registered refinement isomorphism) only if every application agrees, and otherwise retains `transportImage` with all original descriptors. No name-only coercion or backend-dependent erasure.
- Focused `lake build CasCatalogue.Realize:olean` succeeded. The fresh `-O0` native harness `.tmp/b0-refinement-routed-harness` executed frozen `sets.card.fin2_times_z3` through the registered Sage `lim.sets.product` backend: the independently published `obj.rings.integers_mod` → `obj.sets.integers_mod` refinement is now honored, the input pair is exactly `obj.sets.fin(2)` and `obj.sets.integers_mod(3)`, and Sage returns a complete `cone` with a six-element apex and two legs. It advances from `unavailable: no finite Sage parent for functorAction` to `gap: no admitted registration computes meth.cardinality on the form lim.sets.product`. Report `.tmp/b0-refinement-routed-report.json`. This is **not** a completed assertion.
- Native regression run `.tmp/b0-refinement-routed-recovery-report.json`: `sets.card.z4_cubed` still holds through GAP, and `finite_sets.limit.pullback.card` still completes its registered Sage pullback before the previously identified cardinality form gap. No frozen assertion, mathematical source, backend or registration changed. Requirement 3 remains open at the separate constructed-result cardinality admission boundary.

## 2026-10-10 (B0 focused required product through registered Sage backend)

- Executed the frozen `sets.card.fin2_times_z3` assertion through the corrected native harness `b0-cone-diagram-harness` and the installed specimen, independently of the known finite-set pullback. The registered `lim.sets.product` backend **was called**. Its input was the pair `obj.sets.fin(2)` and the full, four-step computational transport of `obj.rings.integers_mod(3)` (ring → multiplicative monoid → semigroup → magma → sets); the backend responded `ValueError: no finite Sage parent for functorAction`. Exact report: `.tmp/b0-product-20261010-report.json`. This is `unavailable`, not `holds`, and is a separate B0 requirement-3 failure.
- The corresponding kernel ownership boundary is `Realize.transportImage`: it retains the actual functor `obj` action as `functorAction(edgeDescriptor, priorDescriptor)` and the appropriate image form. The current specimen's Sage finite-parent decoder admits named `obj.sets.fin`/`obj.sets.integers_mod` but no `functorAction`. Erasing the four-step path solely to satisfy that decoder would assert an unvalidated identification of the underlying point representation. No changed leaf, assertion, mapping, or kernel code is justified by this observation alone. A corrective source change must carry a checked computational presentation equivalence for the **exact selected composite functor** before replacing any descriptor; the result must then be retested through the frozen assertion.

## 2026-10-10 (B0 finite-set pullback: typed graph and creation lift reach backend)

- Repaired the generic created-limit mapped graph realization in `CasCatalogue/Realize.lean`. The source graph is decoded under the *target* category's registered graph literal at the exact type of `U.map f`; Lean must identify that independently reconstructed map with the actual selected functor action (definitional equality or kernel-accepted equality proof). The raw graph is usable only if the target callable codec accepts it or, for its specific missing public point-codec case, the actual selected endpoint presentations pass `endpointKeys`/`validateGraphEndpoints`. All other actions retain their full `map` envelope; no backend output or leaf claim supplies the identification. `CasCatalogue.Realize:olean` compiled.
- Corrected the universal-cone creation datum: `formalLowerPresentation` was transported from the standard mapped cospan to `sourceDiagram ⋙ U` by checked `cospanCompIso`, but `Decoded.diagram` incorrectly remained the standard cospan. It now names the actual formal composite diagram, as required by `StructuredResult.lift`, without treating the two diagrams as definitionally equal.
- The focused native diagnostic harness compiled the current generated C with `-O0` and linked it against the unchanged existing harness dependencies (leaving the normal executable unchanged). Against the installed `.tmp/b0-leaves-specimen/leaves.json` and the unmodified frozen assertions, `.tmp/b0-cone-diagram-report.json` establishes `sets.card.z4_cubed` **holds** via one GAP `meth.cardinality` dispatch. `finite_sets.limit.pullback.card` now reaches one actual Sage `lim.sets.pullback` dispatch with a complete cone and passes the previously failing mapped-graph input and registered creation lift; its next result is `kind=gap`, `fails=false`, `NoImplementation: no admitted registration computes meth.cardinality on the form image:["cat.sets",{"classifierForget":"clf.sets.finite"}]`. This is an independent missing result-form realization, not a cone failure or acceptance. No assertions, upstream rows, or leaves were edited. B0 requirement 3 remains open.

## 2026-10-10 (B0 exact concrete-callable elaboration diagnostic)

- A targeted native diagnostic distinguished failure of the concrete-callable elaborator from failure of its equality check. On the frozen finite-set pullback, `ConcreteCategory.hom` **cannot elaborate the original arrow**; the mapped-arrow check is therefore not reached. The diagnostic harness reports `NoImplementation: diagnostic: original concrete callable cannot be elaborated`, with `sets.card.z4_cubed` still holding. Report `.tmp/b0-presence-report.json`.
- Tested a generic `DFunLike.coe` fallback for that original arrow, while retaining both the selected `U.map f` and the kernel-checked equality requirement. The resulting source compiled and its native diagnostic harness ran the same frozen assertions: GAP cardinality holds; Sage pullback still receives the complete `map(classifierForget(...), graph)` envelope and remains unavailable (`.tmp/b0-coe-fallback-report.json`). The fallback did not establish an accepted concrete-map equality; it was reverted, along with diagnostic-only exceptions. Production semantics, leaf registrations, accepted assertions, and the existing failed realization stratum are unchanged. B0 requirement 3 remains open.

## 2026-10-10 (B0 generic kernel-checked callable comparison)

- Extended the mapped-arrow data-presentation guard in `CasCatalogue/Realize.lean` to permit non-definitional concrete callable equality only if their inferred types are definitionally equal and `Codec.conditionProof` constructs a proof accepted by `Decide.kernelAccepts`. No backend-produced proof or claim is consulted; absent proof the complete selected `map` action is retained. Focused `lake build CasCatalogue.Realize:olean` succeeded. A fresh native diagnostic harness (the updated generated C built at `-O0` with the unchanged remaining link inputs) executed the two original frozen assertions against installed `.tmp/b0-leaves-specimen/leaves.json`: `sets.card.z4_cubed` holds (one GAP dispatch); `finite_sets.limit.pullback.card` remains unavailable after one Sage dispatch because it still receives the complete `map(classifierForget(...), graph)` descriptor. Report `.tmp/b0-checked-callable-report.json`. Thus the generic proof gate is present and compilation-checked but has not resolved the concrete finite-set comparison; B0 requirement 3 remains open. No upstream/leaf/acceptance changes.

## 2026-10-10 (B0 mapped-graph guard isolated by native execution)

- Isolated the failed condition in `e04c172` with a diagnostic-only kernel source change and actual native harness execution, using a focused `-O0` replacement native object and unchanged installed specimen. `sets.card.z4_cubed` still holds; the unchanged `finite_sets.limit.pullback.card` returns `NoImplementation: diagnostic: mapped and original concrete callables do not agree` **before** checking endpoint graph representation or calling Sage. Report: `.tmp/b0-map-diagnostic-report.json`. Thus the first `withTransparency .all / isDefEq` comparison of `ConcreteCategory.hom (U.map f)` and `ConcreteCategory.hom f` fails for the actual reconstructed terms even though an abstract theorem `rfl` holds for the finite classifier's map action. No unchecked graph erasure is justified. The temporary exception-based instrumentation and the subsequent endpoint-codec experiment were reverted from source; the result of this diagnostic is recorded without accepting or altering the frozen assertion. Next source owner must inspect the actual elaborated concrete morphisms and their selected endpoint comparison before attempting a typed computational graph transport. B0 requirement 3 remains open.

## 2026-10-10 (B0 corrected executable, finite-set mapped-arrow regression)

- A native *diagnostic* harness executable was successfully linked using a focused `-O0` compilation of the current `CasCatalogue/Realize.c`, substituted for precisely its native object in a copy of the pre-existing `cas-harness.rsp` (the standard `-O3` native compilation remained too slow). The original executable and build cache were not replaced. Diagnostic executable `.tmp/b0-graph-debug-harness`, report `.tmp/b0-graph-debug-report.json`.
- Running the two unchanged frozen assertions against `.tmp/b0-leaves-specimen/leaves.json` gave `sets.card.z4_cubed`: **holds**, one GAP dispatch, and `finite_sets.limit.pullback.card`: **unavailable**, one Sage dispatch, still reporting `a morphism is a list of pairs` for `map(classifierForget(clf.sets.finite), graph)`. Thus `e04c172` is **not an effective repair of this regression** at the current runtime path, notwithstanding its source compilation and the separate `rfl` identity for the abstract forgetful functor. The retained callable check did not authorize primitive graph projection in this actual execution. A new source correction must establish the exact instantiated concrete arrow/action equality and target graph codec; no backend-adaptive stripping or semantic rewrite is licensed. B0 requirement 3 remains open.

## 2026-10-10 (B0 mapped-graph native harness rebuild after e04c172)

- The focused kernel correction at `e04c172` has an updated `CasCatalogue/Realize.olean` and generated C. A fresh bounded `lake build cas-harness` of 240 seconds advanced through `CasCatalogue.TestSuite`, `CasTools.Harness`, and `CasTools.HarnessMain` but expired before producing a new executable; the prior executable still predates the correction. Exact build log: `.tmp/b0-e04-build.log`. The new source therefore has not been exercised by the frozen harness assertions. This is not evidence that either `finite_sets.limit.pullback.card` or B0 requirement 3 holds. No repeat of the already established stale-binary computation is counted as validation.

## 2026-10-10 (B0 checked graph presentation for concrete transport)

- Corrected `CasCatalogue/Realize.lean` at the general created-limit diagram transport: a selected `U.map f` may use the original finite graph as its computational input only when Lean checks definitional equality of the source and target *concrete callables* and the mapped arrow accepts those graph bytes at its actual target type. Otherwise its complete selected `map` descriptor remains on the wire. The source arrow, mapped arrow, chosen functor, cospan comparison and creation evidence remain the original typed constructions; this is a guarded computational representation, not an identification supplied by a leaf.
- Independently checked the particular pinned finite-classifier case by a Lean `rfl` proof of `ConcreteCategory.hom (finite.forget.toFunctor.map f) = ConcreteCategory.hom f` for arbitrary `f : X ⟶ Y` in `FintypeCat`, using the accepted upstream `LeanCategories.Foundation.Mathlib.finite`. Focused `lake env lean CasCatalogue/Realize.lean` succeeded. The native `cas-harness` rebuilds exceeded their bounded 170s and 140s commands during executable compilation/linking; the `lean --run` alternative reports an external native symbol required by `CasCatalogue.Tools.Harness.main`. Thus the changed runtime path has **not** yet been verified end-to-end, and the frozen `finite_sets.limit.pullback.card` cannot be counted as holding. Its later cardinality realization is separately absent in the installed specimen. No assertion, upstream mathematical row, or leaf changed.

## 2026-10-10 (B0 required lattice discriminants, real harness diagnostic)

- Executed the unchanged `tests/acceptance/lattices.cas` through `lake env cas-harness --computation-only` with `.tmp/b0-leaves-specimen/leaves.json`; report `.tmp/b0-lattice-focus-result.json`. Each frozen required `lattices.discriminant.a1`, `.a2`, `.a3` is `kind=gap` with zero dispatches: `NoImplementation: no admitted registration computes colim.bil_w_form.cokernel on the form cat.bil_wform`. The kernel does not presently reach a registered backend for these three computations. This is not acceptance and is not a mathematical-invalidity finding; neither an upstream semantic row nor an acceptance assertion was changed.
- Earlier current-tuple diagnostics identify the other unresolved required execution paths: finite-set pullback dispatch sends complete mapped-arrow envelopes that `sage-set-limits` cannot decode; ordinary set pullback and coproduct dispatch successfully but lack subsequent result-form cardinality registrations; `rev_rev` lacks its `mor.sets.fin_rev` registration. These are distinct failures, not permission to substitute computations or alter the permanent suite. B0 requirement 3 remains open.

## 2026-10-10 (B0 finite-set pullback creation transport to registered dispatch)

- Repaired the created pullback's formal diagram transport in `CasCatalogue/Realize.lean`: the target's standard cospan and the actual selected functor composite are checked using Mathlib `cospanCompIso`, not equated definitionally. The accepted lower universal cone/evidence is transported along this checked isomorphism; its independent standard-schema presentation still governs computational data fields. For the mapped arrow input roles, the exact original endpoint wires are realized and transported through the same registered edge, rather than attempting to interpret `U.obj X` as a fresh named object. `CasCatalogue.Realize:olean` and `cas-harness` compiled successfully.
- A fresh computation-only harness run of the unchanged `finite_sets.limit.pullback.card` assertion (`.tmp/b0-iso-endpoints-result.json`) reached a real `sage-set-limits` dispatch of `lim.sets.pullback` on `cat.sets`. Outcome `unavailable`, not `holds`: the retained complete cospan sent mapped arrow envelopes `map(classifierForget(clf.sets.finite), graph)`; this installed specimen expects only a raw pair-list graph and raised `ValueError: a morphism is a list of pairs`. This is now an explicit downstream realization/encoding incompatibility. The kernel must not erase the selected functor action to make the specimen pass. No assertions, upstream mathematical records or leaf implementations were altered. B0 requirement 3 remains open.
- Focused non-lift regression after the source correction: `.tmp/b0-z4-after-transport.json` reports `sets.card.z4_cubed` `holds`, `fails=false`, and a real GAP `meth.cardinality` dispatch with response `finite(64)`. The isolated test still omits the other admitted inventory assertions.

## 2026-10-10 (B0 ordinary set pullback registered execution)

- Ran the unchanged `sets.limit.pullback.card` assertion, with its original `let f` and `let g` bindings, through `cas-harness --computation-only` and `.tmp/b0-leaves-specimen/leaves.json`. Report `.tmp/b0-direct-pullback.json`: a real `lim.sets.pullback` dispatch to `sage-set-limits` returned a full `cone` with apex `Fin 3` and both projections (`[[0,0],[1,1],[2,2]]`, `[[0,1],[1,0],[2,0]]`), and the kernel continued to `kind=gap`, `fails=false`, `NoImplementation: no admitted registration computes meth.cardinality on the form lim.sets.pullback`. The set pullback cone decoder is not failing; the retained constructed-result cardinality route is missing. This frozen required assertion is not yet satisfied. The earlier finite-set variant also requires a separate created-cone comparison before this stage. The partial-suite command's nonzero exit reflects missing other admitted inventory entries.

## 2026-10-10 (B0 coproduct decoder end-to-end revalidation)

- The corrected kernel (`f279c99`) built its complete `cas-harness` executable successfully (`7440/7440`). A computation-only harness run of the original `sets.card.fin2_sqcup_fin3` assertion isolated without editing the proposition, against `.tmp/b0-leaves-specimen/leaves.json`, records a real `colim.sets.coproduct` dispatch to `sage-set-limits`: input `pair(Fin 2, Fin 3)` and returned complete `cocone(Fin 5, [[0,0],[1,1]], [[0,2],[1,3],[2,4]])`. The former `malformed` rejection is gone. Report `.tmp/b0-coproduct-validated.json` gives `kind=gap`, `fails=false`, `NoImplementation: no admitted registration computes meth.cardinality on the form colim.sets.coproduct`. Thus this specific kernel decoding defect is repaired and revalidated through registered execution, but the required assertion still does not hold computationally; the remaining result-form realization is a separate unfilled contract obligation. The narrowed run's overall nonzero exit reflects the required full inventory being absent from the diagnostic, not a wrong coproduct answer.

## 2026-10-10 (B0 coproduct actual endpoint graph validation)

- Following the registered `sets.card.fin2_sqcup_fin3` run, whose Sage cocone had complete `Fin 5` apex and legs but failed with `the callable's point types require their released data representation`, corrected the kernel's `ComputationalData.validatePlannedPort`: only that specific formal point-codec gap may be resolved using the already required actual input/output endpoint descriptors and `validateGraphEndpoints`. All other `validatePort` errors are retained, non-callable fields retain ordinary validation, and the graph must have the exact actual domain keys and admissible codomain points. No backend response becomes formal semantics and no expected assertion changes. Owner-local `lake build CasCatalogue.ComputationalData:olean` passed. Two bounded native harness rebuilds expired before linking, so this source correction has **not** been validated end-to-end and does not close the coproduct assertion or B0 requirement 3.

## 2026-10-10 (B0 finite-reversal required assertion)

- The unchanged `sets.eq.rev_rev` assertion was isolated verbatim from `tests/acceptance/sets.cas` and executed through `cas-harness --computation-only` with the installed `.tmp/b0-leaves-specimen/leaves.json` manifest. Its report `.tmp/b0-rev-only-correct.json` records `kind=gap`, `fails=false`, `dispatches=[]`, and `NoImplementation: no admitted registration computes mor.sets.fin_rev on the form obj.sets.fin`. This frozen B0-required assertion is not yet met by a registered computation. Do not count the `gap` as success, invent a fallback, or change the assertion. The narrow run reports missing inventory entries because the remaining admitted assertions are absent from the diagnostic file. A preceding multi-row diagnostic omitted a necessary `let` and timed out without a result; it is not evidence about the assertion.

## 2026-10-10 (B0 focused product and finiteness execution)

- Ran unchanged `tests/acceptance/sets.cas` assertions in a narrowed computation-only `cas-harness` invocation against `.tmp/b0-leaves-specimen/leaves.json`; the report is `.tmp/b0-next-finite.json`. `sets.finite.integers` holds with Sage `prop.is_finite` returning `some false` for `obj.sets.integers`. `sets.implemented.card_fin` holds with Sage `meth.cardinality` returning `finite(3)` for `obj.sets.fin` `[3]`. These establish two additional registered successful assertions (six total including the four prior required cardinalities).
- The same invocation exposed distinct failures: `sets.card.fin2_times_z3`, `sets.finite.fin2_times_z3`, and `sets.card.square` are `unavailable` after `lim.sets.product` receives a nested `functorAction` descriptor for its input, which the specimen rejects with `ValueError: no finite Sage parent for functorAction`. `sets.card.fin2_sqcup_fin3` is `malformed`: Sage returned a full `cocone` with apex `Fin 5` and two legs, but the kernel reports `the callable's point types require their released data representation`. Neither failure is semantic invalidity. Their correct kernel treatment, retained presentations and decoding must be investigated against the accepted contract without editing assertions or leaf code to force a pass.
- The diagnostic contains only a subset of the admitted inventory, so its overall nonzero exit does not negate the individually recorded passing rows. `finite_sets.limit.pullback.card` and the remaining required computations remain open.

## 2026-10-10 (B0 next registered computations)

- At `fc30b45`, the unchanged frozen `sets.card.z7`, `sets.card.z5_empty_power`, and `sets.card.integers` assertions were executed in `--computation-only` mode through the actual `cas-harness` and `.tmp/b0-leaves-specimen/leaves.json`. All three individually returned `kind=holds`, `fails=false` and recorded real backend dispatches: GAP `meth.cardinality` on `obj.sets.integers_mod_power` at `[7,1]` produced `finite(7)` and at `[5,0]` produced `finite(1)`; Sage `meth.cardinality` on `obj.sets.integers` produced `aleph0`. Report `.tmp/b0-card-next.json`; the isolated diagnostic's overall nonzero exit represents inventory entries omitted from the excerpt, not these three failures. The existing prior run established `sets.card.z4_cubed`; four frozen required assertions have now passed individually with registered dispatch. Full suite and finite-set pullback creation lift remain open. No acceptance assertion, leaf, or mathematical definition was edited.

## 2026-10-10 (B0 actual registered execution; finite-set lift failure)

- The pinned `cas-harness` built successfully (`7440/7440`). A focused `--computation-only` harness run of the **unchanged** `sets.card.z4_cubed` assertion against `.tmp/b0-leaves-specimen/leaves.json` returned `kind=holds`, `fails=false`, with a recorded dispatch to backend `gap`, operation `meth.cardinality`, input `obj.sets.integers_mod_power` parameters `[4,3]`, and answer `finite(64)`. The diagnostic used a byte-for-byte extracted assertion in `.tmp/b0-single-card.cas`; all other admitted assertions remained required by the inventory and were reported missing, so the diagnostic command as a whole exited nonzero. The isolated assertion's real registered kernel execution is established; full-suite completion is not.
- The equally unchanged `finite_sets.limit.pullback.card` extracted with its two original `let` bindings in `.tmp/b0-single-pullback.cas` returned `kind=gap`, `dispatches=[]`, `NoImplementation: the selected diagram transport is not the registered creation functor's action`. This is the first actually observed kernel barrier before Sage dispatch, not a leaf absence. Mathlib's `cospanCompIso` is the required canonical isomorphism between `cospan f g ⋙ U` and `cospan (U.map f) (U.map g)`; these diagrams are not definitionally equal. The structured data plan additionally requires a cone over the exact standard diagram. A source experiment constructing the actual composite removed the first failure but exposed `the computational fields have a different exact diagram type`. A further attempt to check the canonical isomorphism and separate the computational data schema from the formal composite compiled, but its focused harness run produced no result before the 100-second bound. It was **not validated and was reverted**, with no change to the pinned ontology, protected assertions, or acceptance gates. Next kernel correction must carry the accepted diagram isomorphism through the independent universal-cone presentation and its computational schema, retaining the exact selected functor rather than treating the standard diagram as definitionally identical.

## 2026-10-10 (B0 harness compilation frontier)

- `lake build @lean_categories/+LeanCategories.Lattices.Valued.Standard:olean` completed successfully (exit 0) after earlier bounded failures; the previously missing upstream `.olean` now exists. This was the exact owner-local dependency blocking the harness build.
- The first subsequent `lake build cas-harness` advanced to `7427/7440` and built `LeanCategories.Catalogue` and its registry semantic artifact before its 240-second bound. Later incremental builds completed the executable; see the newer execution entry above.

## 2026-10-10 (B0 specimen backend protocol checks; harness still outstanding)

- At `933c663`, directly exercised the installed specimen's framed backend port using its published `leaves.json` operation/input pairs, without importing leaf code into the kernel or changing an acceptance assertion. GAP 4.16.1 (`meth.cardinality`, `obj.sets.integers_mod_power`, parameters `[4,3]`) answered `{"ctor":"finite","args":[64]}` with `status=ok`. Sage 10.8.12 (`lim.sets.pullback`, `cat.sets`, the suite's graphs `[[0,0],[1,1],[2,1]]` and `[[0,1],[1,0]]`) answered a `cone` with apex `Fin 3` and complete legs `[[0,0],[1,1],[2,2]]` and `[[0,1],[1,0],[2,0]]`, `status=ok`. Both backend processes exited 0. These are computational port observations only, **not** B0 registered kernel/harness acceptance, formal cone reconstruction, or correctness evidence independent of the permanent suite.
- The kernel harness was still unbuilt (`CasCatalogue.TestSuite.olean` and `cas-harness` absent). Recent bounded builds repeatedly stalled in the pinned upstream `LeanCategories/Lattices/Valued/Standard.lean`; no backend failure through the kernel has been observed. Next owner-local requirement: run the two unchanged assertions through the actual harness once compiled, preserving their registered dispatch traces; inspect and correct only real kernel failures.

Process narration lives here, not in chat: what was done, what was found, what is pending and on
whom. Chat carries only what needs the owner's action or decision. Newest entry first; one entry
per working session; terse. Not an authority: rules live in their owning documents (AGENTS.md).

## 2026-10-09 (B0 authority and real-backend execution)

- Defining-map projection now requires the full opaque cone/cocone envelope to have
  exactly the number of data ports in the independently interpreted constructor
  schema. Previously `projectData` accepted extra fields and returned a single
  selected field without checking the full envelope cardinality. This is a
  generic `cc-realize`/malformed-output source correction, not proof of a
  registered execution or of B0 acceptance. Focused `lake env lean
  CasCatalogue/StructuredResult.lean` succeeded (one pre-existing deprecation
  warning); no broad suite was run.

- `StructuredResult.complete` now propagates a formal construction/diagram type
  disagreement as an internal interpreter error. Previously its `.error` return
  was classified by the caller as malformed backend output, although the backend
  cannot alter the independently fixed formal presentation or diagram.

- `StructuredResult.projectData` rejects a missing or mismatched cone/cocone
  constructor tag before extracting a defining-map field from opaque backend data.
  Previously the projection read `args` without verifying its envelope. This is
  a kernel-source correction; registered computational acceptance remains open.

- `StructuredResult.dataPortIndex` now propagates unexpected interpreter exceptions
  instead of converting them to an ordinary missing-data-port/schema result.
  Explicitly identified composite projections and absent schemas still return their
  distinct errors. No registered computation was executed for this source change.

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

## 2026-10-10 — B0 discriminant integration

- Updated `lean_categories` pin to GitHub main `76ca85d7bc35bf55b6268c81f8807ef46b6ab063` via `lake update lean_categories`; leaf manifest `lean-cas-dsl-leaves` `037f1e7` contains the discriminant cokernel/cardinality registrations.
- Removed obsolete `LiftEntry.computation` from the kernel registry manifest projection, matching the new upstream `LiftEntry` interface.
- Focused `lake build cas-harness` found an additional incompatible kernel consumer: `CasCatalogue/LiftedSubobjectData.lean` still requires removed `LiftEntry.computation` and `MonoLiftComputation` declarations. This is a real kernel adaptation, not a leaf or acceptance change. The discriminant suite has not been executed and 12/15 remains the last demonstrated count.
- Adapted lifted-subobject packet handling to the published lift evidence alone: computational callback signatures removed upstream are no longer treated as semantic fields. The packet still fixes the exact prescribed route, selected formal lift, source/base envelopes, and applies separate data validators. `lake build CasCatalogue.LiftedSubobjectDataProbes` succeeds; discriminant execution still requires the harness binary rebuild.
- Committed the kernel's construction-apex category correction as `0630d04`; its receiver now decodes a computed colimit apex in the registered colimit's category rather than the transported result's category. Committed harness recipe defaults for the repository Sage/GAP Python as `21a8e34`.
- Against `lean-cas-dsl-leaves` `037f1e7` and `lean-categories` `76ca85d7`, the focused `--computation-only` permanent discriminant suite reports `holds` for `lattices.discriminant.a1`, `.a2`, `.a3`. Each dispatches both registered `sage-discriminant` operations (`colim.bil_w_form.cokernel` and `meth.cardinality`), with outputs respectively 2, 3, 4. Together with the preceding 12 demonstrated required assertions (`c304a25`, `a9be96a`), all **15/15 frozen required computational assertions** have demonstrated registered execution. The complete acceptance inventory has not passed: a full-suite invocation ran almost five minutes without producing its report and was stopped under the command-duration rule; the focused suite's report marks absent inventory identities as internal failures. Accordingly this records completion of the 15-assertion computational B0 target, not independently accepted B0 or satisfaction of every other B0 obligation.

## 2026-10-10 — Consolidated frozen-assertion execution audit

- A single `--computation-only` harness invocation over unmodified permanent assertion bodies selected from `sets.cas` and `lattices.cas` reports `holds` for **all 15 frozen IDs** at the same kernel and installed leaf manifest (`.tmp/b0-frozen-computation.json`). The focused suite retained the original `f`, `g`, `f'`, `g'` declarations needed by pullback assertions. Its nonzero process exit is caused by the other 138 identities of the full inventory being absent from this focused run, not by the 15 selected results.
- The dispatch audit reveals an outstanding distinction: **14/15 selected IDs have nonempty registered-backend dispatch traces**, whereas `sets.eq.rev_rev` reports `holds` but `dispatches: []`, even under `--computation-only`. Consequently the preceding claim that *all 15* have demonstrated registered execution is too strong: all 15 propositions hold, but only 14 have witnessed backend dispatch. The plan expressly forbids counting proof discharge in place of a registered execution requirement. Do not mark that requirement completed until the equality assertion is shown to execute through a registered implementation, or the controlling authority resolves the requirement's interpretation independently.

## 2026-10-10 — Registered Fin reversal and first B0-table integration checks

- `a64fbb2`: direct harness backend startup now defaults `CAS_SAGE_PYTHON` and `CAS_GAP_PYTHON` to the workspace `.venv/bin/python` when no explicit override exists. The Sage reversal leaf at `d522046` then dispatched correctly, returning `[[0,2],[1,1],[2,0]]` for `Fin 3`; this exposed a **kernel** gap in observing composite finite maps, not a missing leaf.
- `bf5455a`: finite graph compositions are normalized as computation data and independently decoded at the full fixed formal arrow type before equality comparison. The unchanged `sets.eq.rev_rev` assertion now reports `holds` with one `sage-fin-rev` dispatch (`.tmp/b0-rev-graph-observation.json`). The focused `CasCatalogue.Realize` and `cas-harness` builds passed.
- A single computation-only run at this candidate tuple reports **all 15 frozen required assertions `holds`, each with nonempty registered dispatch** (`.tmp/b0-frozen-registered-current.json`). This establishes the specified positive computational observations, not completion of B0's realization row or the other acceptance rows.
- Stage-A `b0-integration` acceptance remains unestablished: a complete targeted multi-module build passed some targets but exceeded the five-minute action boundary; no row is closed by that partial compile. Focused gate compilation identified `QuestionProbes` assuming exactly two equivalent parameter origins, despite the current upstream API retaining three distinct sources (`obj.commutative_rings.complexes`, `obj.fields.complexes`, `obj.rings.complexes`). The assertion now checks at least two **distinct** origins and retains the full validation loop over every source. `lake env lean CasCatalogue/QuestionProbes.lean` passes. Remaining integration obligations require their own positive and negative checks at this tuple.
- Further stage-A focused gate compilation exposed two probes still referencing the retired `Wire` construction fields or bypassing the formal construction context: `StructuredResultProbes` and `StructuredReconstructionProbes`. The former now checks a decoded complete cone's apex/legs and the exact source computational packet surviving the registered representation change; the latter reconstructs and checks the noncanonical cone, projects the actual graph using the registered construction schema, decodes at the returned noncanonical leg endpoints, and rejects contextless `constructionLeg` envelopes. Both files pass focused `lake env lean` checks. These are integration-probe repairs, not separate B0 row completions.
