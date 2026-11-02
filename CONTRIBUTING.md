# Contributing

[`specs/architecture.md`](specs/architecture.md) is the contract every contribution conforms to.
This file states the behavioural policies for contributions and where each kind of contribution goes.

## Behavioural contribution policies

**Agents may change the means of solving a task, but may not change the obligation
they are solving.** These policies govern how contributors choose work, conduct
research, divide responsibilities, interpret evidence, and decide to stop. They
apply before a substitute task becomes the work order.

They operate within the repository's separation of authors and acceptance
authority. Repair the implementation and interfaces owned by the assigned role;
record missing upstream mathematics against the existing obligation without
authoring or commissioning it downstream. Counterevidence reopens agent-selected
implementation assumptions, never authorizes candidate output to revise admitted
mathematics or acceptance assertions.

### Preserve the requested obligation

Researching, decomposing, delegating, implementing, testing, or reporting a task
must preserve its required outcome, relevant domain, semantic distinctions,
constraints, and standard of evidence.

An agent may revise its implementation, hypotheses, and order of work. It may not
replace the requested outcome with an easier example, a local proxy, a different
context, a supporting artifact, or a weaker acceptance condition.

Difficulty, uncertainty, an inconvenient implementation, and successful
intermediate checks do not authorize changing the obligation. They determine what
work remains necessary.

The agent must also avoid adding completion prerequisites that are neither
requested nor necessary to satisfy the actual task. Necessary consequences of the
requirements and demonstrated environmental constraints count; preferred
infrastructure and self-authored plans do not acquire that status merely by being
written down.

An accurate description of incomplete work does not discharge the remaining
obligation.

**An agent can report every limitation honestly and still substitute the task
through its subsequent choices.** Repeatedly saying "this is only an intermediate
result" does not help if the agent continues producing intermediate results
without completing their required integration.

"Preserve the obligation" must not mean "maximize it." The authoritative target is
the actual requested capability and its necessary consequences, not every stronger
property an agent can imagine.

### 1. Decompose the work without losing the parent obligation

A subtask may be narrower than the requested outcome. Its success claim must
remain equally narrow.

Choose subordinate work because its result contributes to a necessary subsequent
step. After it succeeds, perform that step while the work remains authorized and
feasible.

The agent responsible for the parent task retains responsibility for composition
and integration. Completion of all delegated components does not establish
completion of the parent task unless their combined operation satisfies the
original requirement.

Checkpoints, partial implementations, and handoffs preserve progress; they do not
transfer away unresolved responsibility or create a requirement for another user
instruction to continue.

A small implementation slice can be the correct next action. The failure occurs
when its convenient success condition becomes the effective definition of the
whole task. For example, "make this reader probe pass" can be a necessary step
toward correct composition. It cannot become the standing replacement for "make
selected constructions compose correctly."

The same applies to delegation within the permitted roles. Separately completed
components can leave the required connection between them absent. The parent
agent must resolve that connection without crossing authorship or input
boundaries.

**Required response to a violation:** restore the missing requirement to the
active work, connect the partial result to its actual consumer, and complete the
omitted integration. Adding a truthful "remaining work" paragraph is insufficient.

### 2. Research the required responsibility before choosing the implementation boundary

Frame the research question in terms of the capability required by the user's
workflow. Do not treat the incumbent's modules, helper functions, intermediate
representations, or accumulated responsibilities as requirements.

Compare existing capabilities, reference implementations, and the incumbent
against that contract. A reusable component need only own the responsibility
under consideration; it need not implement the entire application.

Establish the concrete gap requiring bespoke code before assigning that
responsibility to bespoke code.

Survey the complete required workflow before choosing a local work unit. Resolve
uncertainties that could invalidate the architecture before investing heavily in
components that depend on those assumptions.

For lean-cas-dsl, searching for a library that implements the current reader's
entire combination of registry lookup, provenance recovery, endpoint recognition,
and runtime ownership already accepts that combination as the correct
responsibility. The more useful questions concern the constituent obligations:
dependent term formation, binding and substitution, typed composition,
preservation of selected constructions, and reuse of actual results.

Long-horizon planning means examining what happens to a construction **through
its required downstream uses**, before committing to a representation that only
handles its initial formation.

The relevant cost includes the consumers, repeated reconstruction, future repairs
within the required feature set, and verification burden. The smallest immediate
diff does not necessarily minimize that cost.

**Required response to a violation:** reformulate the question around the
required capability, inspect the relevant existing implementations, and perform
the smallest meaningful experiment that resolves the consequential uncertainty.

This does not require an exhaustive literature survey or a predetermined rewrite.
Research should support an engineering decision and then lead into implementation.

### 3. Preserve established information and repair the boundary that loses it

Before introducing inference, retries, metadata searches, duplicated state, or
repair logic, determine whether the required information was already established
earlier in the workflow.

If a project-owned boundary discarded information needed by a required consumer,
repair that boundary and its consumers so they preserve the established value,
choice, relationship, or dependency.

Do not treat successful reconstruction as equivalent to preservation of the
original selection or result.

When a defect exposes a shared invariant, investigate all affected paths within
the required scope. The currently failing example does not define the scope of
the invariant.

**A representation can have every field populated and still discard the selected
identity or relationship that downstream computation needs.** Investigate where
the information was lost before deciding that the missing information needs an
inference mechanism.

Ask where the selected construction's endpoints, dependencies, owners, and
actual results cease to determine subsequent computation. Adding another
recognizer at the point of failure can make the example work while preserving
the cause of the next failure.

Once several branches are known to implement the same broken
producer-preservation rule, "only one currently has a reproduction" identifies
unfinished investigative work. It does not establish that the other branches
are outside the obligation.

**Required response to a violation:** correct the responsible producer or
interface within the assigned layer, cover the actual affected consumers, and
verify the original chain of use.

The scope remains bounded by the real requirement. This does not demand
retaining irrelevant information, protecting hypothetical future consumers, or
changing unrelated code. An abstraction can omit information when the required
downstream uses do not need it, or when it remains available through an explicit
reference.

### 4. Contrary evidence must reopen the responsible implementation decision

Treat agent-selected architectures, plans, estimates, and explanations as
revisable hypotheses.

A decision record does not establish the truth of its premises. When evidence
contradicts a premise required by the chosen design, investigate and revise that
premise before extending mechanisms that depend on it.

Validation must be allowed to establish that the chosen implementation is
unsuitable. Do not restrict it to confirming the choice while excluding the
requirement that justified choosing it.

Preserve the user's requirements while reconsidering the means chosen to satisfy
them.

Do not turn "test whether this representation is sufficient" into "this
representation is settled; every subsequent failure must be repaired within it."

Distinguish a local implementation defect from evidence against an architectural
assumption. A typo does not require reopening the architecture. A required
consumer repeatedly needing information that the completed representation was
supposed to preserve bears directly on that representation's adequacy.

Recognizing that machinery should be eliminated must not regress into improving
or centralizing that machinery while retaining the cause of its existence.

**Required response to a violation:** identify the smallest responsible
assumption, inspect or exercise the boundary that can settle it, and revise the
implementation accordingly. Update the plan to reflect the result.

This does not introduce periodic architecture ceremonies or automatic rewrite
thresholds. The trigger is relevant contradictory evidence.

### 5. Evidence must establish the property being claimed

Evaluate evidence against the original obligation before accepting a success
claim.

A test must not manually supply the state, relationship, execution, or lifecycle
whose establishment it claims to verify.

Helper correctness, copied identifiers, successful typechecking, an API call,
and a green status establish only the properties they actually exercise.

When the task requires transferring a responsibility, verify that the receiving
component performs that responsibility and that the superseded implementation
no longer performs it for the transferred use.

Ask: **Could this evidence remain unchanged if the required capability were
absent?**

If fabricated owner tags are copied successfully even when no real supplier
session exists, that evidence does not establish preservation of actual
supplier-owned data.

If the reader still performs ordinary argument construction and instance
synthesis, calling Lean's elaborator afterward does not by itself establish that
the responsibility has moved to Lean.

If a proposition is proved without invoking the required computational
implementation, that proof does not establish the requested execution.

These are different failures because the original obligations differ. Preserve
that specificity; do not impose one universal testing ritual on every task.

**Required response to a violation:** exercise or inspect the missing capability
at the relevant boundary and obtain evidence for the actual claim. A test can
legitimately establish unrelated setup state; it cannot supply the very property
whose establishment is under examination.

Where the requested change concerns architecture, source inspection and
responsibility tracing may be necessary alongside behavioural tests. A few
successful outputs cannot establish that a prohibited reconstruction path has
been removed.

Engineering checks establish their stated engineering properties. Mathematical
correctness and acceptance remain governed by the permanent, independently
authored acceptance suite and its authority; this policy does not turn source
inspection, a kernel probe, or a leaf's claim into mathematical acceptance.

### 6. Verify decision-critical inherited claims against primary evidence

A statement in an agent report, issue, review, handoff, or generated document is
a claim, not independent verification.

Before using such a claim to determine scope, architecture, ownership, or
acceptance, inspect the primary evidence supporting that decision at the relevant
source state, using the inputs permitted to the assigned role.

Reuse previously verified evidence when its assumptions and source state remain
applicable. Cross-references provide access to evidence; they do not create
corroboration.

When a decision-critical claim is falsified, reconsider the decisions that
depended on it, not merely the sentence containing the error.

This applies to claims about behaviour, architecture, requirements, and completed
verification, as well as dependency names, namespaces, API shapes, and
conventions. Check the implementation before using an assertion about it to
decide what to build, omit, or accept.

**Required response to a violation:** remove the unsupported premise from the
active decision, inspect the relevant implementation or evidence, and reconsider
the choices whose justification depended on it.

This does not require reproducing every inherited experiment. It targets claims
that materially determine what the agent builds, omits, or accepts. The objective
is reliable decisions, not repeated verification for its own sake.

### 7. Supporting work must return to the substantive task

Supporting work is justified by an actual dependency of the requested outcome.

Once that dependency is sufficiently satisfied, use the resulting capability and
resume the substantive task.

Do not promote desirable properties of tooling, infrastructure, research,
documentation, or verification into new completion requirements.

When an engineering choice has been delegated, resolve the uncertainty through
investigation and engineering. Do not convert it into a request for approval
merely because the choice is consequential or unfamiliar.

Before declaring work blocked, establish the specific unavailable input, denied
operation, or user-owned decision that prevents it. Continue work that does not
depend on that obstacle.

Obtaining sufficiently useful local compilation and runtime feedback should
cause the agent to resume implementation. Persistence across replacement of the
environment is a separate property. It cannot become a prerequisite without an
actual requirement or demonstrated blocking failure.

During an implementation assignment, discovering and describing the remaining
engineering work does not release the agent from doing it. A completed research
report can satisfy a research assignment; it cannot satisfy the implementation
assignment that the research was meant to support.

**Required response to a violation:** remove the invented prerequisite, use the
adequate available mechanism, and perform the next necessary substantive step.
Actual permissions, role boundaries, and independent acceptance operations
remain binding.

### Establish which choices are user requirements

Preserve actual user requirements and source-backed product contracts. Do not
infer that an internal mechanism is user-mandated merely because it is unusual,
specific, documented, or already implemented. Distinguish required behaviour
from the agent-selected means of producing it. Investigate uncertain provenance
without removing required behaviour.

**The shape of an implementation does not establish who required it.** Protect
the user's features and constraints while scrutinizing the architecture agents
invented around them.

### Apply approval requirements to the active assignment

A review-only assignment does not authorize implementation. An implementation
assignment retains the authorization already granted. Loading a review skill,
finding an architectural defect, or revising an agent-authored plan does not
create a new approval requirement for work within that authorization. Interpret
"continue" in the context of the active assignment.

Do not turn an analysis safeguard into a transfer of delegated engineering work
back to the user.

### Apply the policies through the next substantive action

| Situation | Required next action |
| --- | --- |
| One branch passes, but adjacent branches share the broken invariant | Investigate and complete the affected invariant. |
| No dependency matches the entire incumbent design | Compare the constituent responsibilities against existing capabilities. |
| A required consumer contradicts the chosen architecture's premise | Reconsider the responsible implementation assumption. |
| A test supplies the ownership or state it claims the system establishes | Exercise the real establishment and subsequent use of that state. |
| A report labels a consequential technical claim "verified" | Inspect its primary evidence before relying on it. |
| Tooling now supports the required experiment | Run the experiment and resume substantive implementation. |
| A partial result is accurately described | Use it to complete the remaining authorized work. |

**The enforcement consequence is continuation of the original work:** when
substitution is detected, correct the active task, repair the missing capability
or evidence, and proceed. A new checklist, diagnosis, disclaimer, or compliance
statement does not satisfy these policies.

## Which repository?

| You need | It goes to |
| --- | --- |
| A category, functor, classifier, operation (method), predicate, coherence, constructor or family that is not yet formal | `lean-categories`, through its independently assigned mathematical requirement and sources. A kernel worker records the missing accepted input, never authors or commissions the upstream repair. Consume the upstream mathematics under the current dependency rule; never coin it downstream. |
| A computation of a registered operation on one of its declared input forms | A leaf, in `lean-cas-dsl-leaves` or another package written against the leaf contract |
| A proposition the language should always make true | `tests/acceptance/*.cas`, as a permanent test |
| Resolution, calls, the language or surface syntax | The kernel (`CasCatalogue/`) or the notebook (`CasDsl/`), under a plan node in `specs/computational-core-plan.md` |
| The realization registry, the leaf API or the port | The leaf contract (`lean-cas-dsl-leaf-contracts`, `CasContract/`), with the kernel change that needs it |

The semantic registry is `lean-categories`' (`LeanCategories.Catalogue`, rows under
`LeanCategories/Catalogue/Semantics/`). `normalized_registry` refuses every module outside
`lean-categories`. Own-organization dependencies follow the architecture's latest-`main`
rule; record the exact revisions actually loaded for a build or execution. This source-selection
rule does not transfer mathematical authority to the kernel or a leaf.

## Mathematics is never inverted into implementation

`lean-categories`' policies [LC-13, LC-14 and LC-15](https://github.com/dzackgarza/lean-categories/blob/main/CONTRIBUTING.md#lc-13--structure-belongs-to-the-category-never-to-a-typeclass-on-a-carrier)
bind the kernel, the language and every leaf. Their consequences here:

- The language and the kernel never supply structure that the catalogue did not give an
  object: no element, unit, `0` or operation is attached to a set because a Lean instance
  happens to exist on its carrier (LC-13).
- Every operation is total on its domain object, and there are no partial maps: an argument not
  known to lie in the domain makes the statement invalid when it is read, never a gap, value or
  failure found when it is computed. No fallback reinterprets a term to make it land in a domain
  (a divisor retried in another set, a numeral read where no numeral exists) (LC-14).
- LC-14 is about mathematics: an operation, a domain, a value. It is not about the kernel's own
  program structure. A `partial def` in the elaborator, a parser or an encoder says that a piece
  of code is not proved to terminate; it gives no term a meaning off a domain, so it is not a
  partial map. What LC-14 forbids in the kernel is semantic: reading a term outside its
  operation's domain, a fallback reading, a default for something that does not exist. The
  seal's ratchet on new `partial def` anywhere in this repository, and `custodian/FINDINGS.md`
  item 13, conflate the two; the ratchet is corrected as an ordinary independently reviewed change (the plan, B0, "Gates"; architecture.md, policies 2 and 6).
- A numeral is the image of the map out of the initial object of its object's category; where
  there is none, it is not a numeral of that object (LC-15).
- A leaf computes on an input form that `lean-categories` and the kernel define for the
  catalogue's object; it never shapes the object or says what its values mean. A contract rule
  that would need the catalogue to change to suit a leaf's representation is itself a defect.
- An operation exists only where its structure exists: `⁻¹` on units and automorphisms, never on
  endomorphisms or a bare monoid (LC-16). The language never attempts an operation on a value
  not established to lie in its domain.
- The kernel carries no mathematics, and no proof automation about mathematics: it is purely
  categorical and completely general. That a value lies in a domain (a unit, a monic polynomial,
  a smooth map), and how that is established, is the domain's: formalized with the domain in
  `lean-categories`, and registered as the `evidence` of its admission (LC-18). The kernel runs
  that evidence and nothing else. It cannot do otherwise: the default build target
  `CasGates.KernelPurity` fails on any reference to mathematics, any tactic syntax, and any proof
  procedure run outside `establish`. If a statement fails because evidence is missing or too
  weak, record the missing accepted input against the existing obligation. The independent
  upstream author owns the mathematical repair; the kernel neither supplies it nor sends an
  implementation-shaped formalization request.
- How a value comes to lie in a domain `D ↪ B` (derived from LC-14 and LC-15; the kernel's
  reading rule):
  - a numeral needed in `D` is formed there: the numeral of `B`, with the proposition that it lies
    in `D` (`2 ∈ ℚˣ`) decided when the statement is read. A false one (`2 ∈ ℤˣ`) makes the
    statement invalid;
  - any other value is in `D` only when the statement forms it there, `x in D`, with its evidence
    established when the statement is read. The kernel never admits a value into `D` implicitly
    because an operation needs it there, and never tries another reading when one fails;
  - a variable (a generic element at a stage) is never in `D` by admission: `t ↦ 1/t` is a map
    only on a domain of units.

## Authors are separated by layer

[architecture.md](specs/architecture.md), "Authors: one role per agent":
- The orchestrator owns policies, gates, compliance, the kernel and the leaf contract.
- Formalization (`lean-categories`), acceptance assertions and leaves each have a separate
  subagent author.
- No agent writes in two layers.
- The implementation never informs the formalization or the tests.
- Downstream findings stay in their owning review channel. Upstream assignments come from the
  approved mathematical requirements, never a downstream finding rewritten as a request.

The leaves are not part of this repository; the dependency that remains is a defect
(`gov-no-leaves-here`).

## Documentation and construction work

An already-issued decision is recorded in the existing document that owns it.
Recording the decision is ordinary maintenance, not a new approval transaction.

A documentation-only correction is an ordinary commit. It needs no dedicated PR,
custodian verdict, owner signature, plan node, full Lean build, or unrelated code
change to carry it. Documentation accompanying an implementation change belongs
with that change.

A proposed change to mathematical requirements, acceptance standards, or reserved
authority needs the appropriate decision. A faithful record of a decision already
made does not. File extensions do not determine this distinction.

In a controller session during B0 construction, the controller, reviewer prompt, gates, and publication
workflow are themselves implementation work. Correct them under the construction
mandate. Do not submit their replacement to an obsolete policy in order to obtain
permission to write or test it. Source integration does not accept or install a new
authoritative judge: the author cannot approve its own replacement. The evaluator,
accepted mathematics and acceptance inputs used to judge a candidate remain
independently accepted revisions outside that candidate's control.

The [owner's issue-language instruction](https://github.com/dzackgarza/lean-cas-dsl/issues/82#issuecomment-6476540209)
also applies to the operative work order and acceptance, not just its introduction.
State the selected mathematical constructions, morphisms, relations, universal data and
required coherent compositions that will be interpreted and computed. Keep necessary
build, execution, failure, launch and source-inventory checks as supporting engineering
obligations. A software-state ladder, renamed runtime object or mathematical preamble
does not replace the construction-specific work and acceptance.

Run the checks relevant to the actual change. A changed reviewer decision path
needs reviewer tests. A changed kernel mechanism needs its relevant kernel tests.
A descriptive text correction does not acquire a full mathematical build merely
because the repository contains Lean code.

In a controller session, a publication dependency does not suspend implementation or invalidate the
instruction being recorded. Preserve the commit and continue the selected work
while the already-specified publication correction is executed.

## Writing a leaf

**Development-phase prerequisite.** Substantial production leaf work begins only
after the [kernel-MVP readiness gate](specs/computational-core-plan.md#kernel-mvp-proved-readiness-for-substantial-leaf-development)
has passed, including independently selected extension trials on the frozen
kernel/contract. Before then, an independent leaf author may supply a small
diagnostic specimen to check a fixed public request/reply form or generic
execution path; it is not a license to invent representations or build out
method coverage. A form missing from the released contract is an unfinished
kernel/contract obligation, **not** leaf work. The full B0 acceptance suite
and its required actual backend computations remain mandatory after the
readiness gate.

A leaf holds zero semantic authority, and nothing from it is trusted in any form
(`INTENT.md`; `specs/architecture.md`, "The evidence model: nothing from a leaf is trusted"). It
ships no mathematics and no Lean. It is a registration:
- the operation id, of a semantic operation or composite of operations registered in
  `lean-categories`;
- the input form it accepts, one of the typed request forms that `lean-categories` and the kernel
  define for that operation;
- an opaque implementation, in any language, returning a value of the operation's declared
  result form.

The system runs that implementation and believes nothing about it. A leaf states nothing else:
no denotation of its values, no proof, certificate or checker about its own code, no
identification of two values, no evidence for a property or an equality, and no status or trust
level. Anything of that kind it writes is ignored. A leaf may be arbitrarily bad; the worst leaf
imaginable can make its own answers fail the suite and nothing else. It may keep whatever
internal tests it wants; they are evidence of nothing. Whether its answers are right is decided
only by the permanent acceptance assertions below, run by `lean-cas-dsl`'s harness
(`cas-harness`, `just harness`) over the installed leaves; a leaf package never imports or runs
the suite.

A leaf never adds a category, method, property, placement, forgetful route, coercion or natural
transformation. If it seems to need one, or needs to forward an inherited method, the defect is
upstream: record that dependency, without commissioning or prescribing its repair. Anything that
can be discharged in Lean is never a leaf's: either
`lean-categories` proves it, or the kernel discharges it generically.

Never write a leaf against, or extend, a contract form that carries a functor, a proof, an
isomorphism, evidence or a status.

**A leaf is glue over existing backends** ([`lean-cas-dsl-leaves` AGENTS.md](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md), "A leaf is
glue over existing backends", following `sage-categories`' `specs/leaves.md`, "Computation-engine
boundary"):
- it wires a registered operation to a mature engine (GAP, Sage, Singular, Macaulay2, Julia, SymPy,
  research code): declared input form, then engine input, then the engine's routine, then the
  engine result, then the declared result form;
- it hand-rolls no algorithm, and names the engine and routine it calls;
- it carries no kernel machinery (dispatch, placement, propagation, composition, refinement,
  caching); a leaf that needs any has found a kernel or contract gap, reported upstream;
- engine values stay private: only a value of the declared result form crosses the port.

This is writing guidance, checked by a separate engineering review. Following it earns no trust:
correctness is judged only by the suite, and the firewall holds even for a leaf that ignores it.

**Backends.** A backend is a child process speaking the port protocol (`CasContract/Port.lean`;
reference implementation `python/cas_port.py` of the contract, put on the adapter's
`PYTHONPATH`). Its announced capabilities must be registered operation ids, or `connect` refuses
it. Its answers are untrusted JSON, read by the kernel into the operation's declared result form
or rejected as malformed. A backend's restrictions restrict its computation, never the
operation's domain.

## Acceptance assertions

A permanent assertion is a proposition in the mathematical language, in `tests/acceptance/*.cas`,
with the source of its expected value:

```
let A := {1, 2, 3} in 𝒫(ℤ)

test finite_sets.card_power_set "SPEC.md: |𝒫(A)| = 2^|A| = 2^3 (Mathlib Fintype.card_set)":
  assert |𝒫(A)| = 8
```
(`tests/acceptance/finite_sets.cas`)

It never mentions a leaf, a handle, a backend or a representation, and its truth is never
established from an implementation's definitions. The acceptance suite is the whole body of
correctness evidence: an installed computation's answer is compared against it.

The independent acceptance author submits the assertion and its mathematical interpretation
through the acceptance channel. `python3 scripts/check_acceptance_permanent.py --admit` records
text hashes; running it, or setting `AGENT_ROLE=acceptance`, does not confer admission authority.
Admission depends on the independent acceptance operation specified by `b0-authority`.
An assertion that no installed computation answers yet is a gap (`#acceptance_gaps`); it cannot
satisfy an obligation requiring execution.

- State the proposition in the mathematical language, through the public surfaces.
- Write its expected value from a proof, a cited source or an independent oracle before you run
  anything, and record that provenance.
- Never read a leaf, a handle's internals or a backend to decide what to assert.
- An admitted assertion is permanent. If an implementation disagrees, the implementation is wrong.
  Only an independently accepted upstream correction changes its mathematics, with the release
  that corrects it.
- The permanent object is the full mathematical question, expected answer and execution
  requirement, not a particular syntax, serialization or proof term. A meaning-preserving
  artifact change uses an independently assessed comparison or migration preserving every
  admitted identity. A changed hash alone neither proves changed mathematics nor authorizes
  rewriting its accepted record. Equal truth values do not prove identical questions. An erroneous
  old reading or record may be corrected independently against the unchanged assertion and its
  mathematical sources; the candidate's behavior cannot determine the intended question.
- Every admitted assertion remains in the report, including unreadable and unrecorded ones.
  Neither an interpreter failure nor a missing fingerprint removes it from the denominator.

## Gate

A kernel construction session chooses its checks by the
[kernel construction procedure](specs/computational-core-plan.md#kernel-construction-procedure-owner-instruction-2026-10-21),
"Running checks". The commands below are how to run them; none of them selects work.

Run what the change touches:
- **Kernel, language, probes, tools during development:**
  `just focus CasCatalogue.Language` builds one target and its dependencies, measuring elapsed time
  and peak memory. Substitute the changed target. A run reaching 60 seconds automatically profiles
  that source; `just focus CasCatalogue/Language.lean profile` requests a profile directly. The
  direct profile is diagnostic, while the targeted build establishes current imported dependencies.
  When a downstream probe needs a fresh import, focus that exact probe next. Each
  invocation fetches own-organisation latest `main`; it runs `lake update` only if a resolved
  revision changed. Logs stay in `/tmp`. If a focused run reaches 60 seconds, use its profile to
  choose a smaller check of the required invariant before another broad check. Caching,
  compiler-boundary and elaboration changes are made only inside the procedure's rule-4
  performance work. Verify the specific invariant
  with the unchanged admitted assertion or a targeted probe. A faster check reports only that
  invariant, not acceptance. Each focused command has a 120-second limit; timeout is failure, not
  proof that the target compiled. Increase `B0_FOCUS_BUDGET_SECONDS` only for a diagnosed target
  when the build or profile log explains why more time is needed; making every finite required
  build fit the default limit is not a prerequisite to B0. A build budget above 120 seconds
  requires a completed profile tagged for that target and diagnosed mode. If the next change rests
  on an uncertain declaration type, registry row, or branch result, first run a minimal import-only
  reproducer from `/tmp` with `just probe /tmp/NAME.lean`; its 60-second default limit forces a
  smaller question before another slow compile. A probe cannot establish a current source build.
  For another edit to the same diagnosed hotspot, set `B0_PRIOR_PROFILE_LOG` to its completed
  profile and run `just focus TARGET diagnosed`; the focused build still runs under its time
  limit, while the redundant automatic profile is skipped. Profile again when the cost moves.
- **Reader or encoder performance work (procedure, rule 4, only):** `just bench-question matrices.kernel` and
  `just bench-question subspaces.kernel` measure the unchanged admitted questions through the
  production reader, recording dependency revisions, per-binding and phase timings, and peak
  memory. The 180-second default
  limit can be changed with `B0_BENCH_BUDGET_SECONDS` after inspecting the log. Compare full
  identities with an independent baseline and run the relevant protected negatives before
  claiming behavior preservation; benchmark timings are engineering data, not correctness evidence.
  For reader iterations, `just bench-reading subspaces.kernel` imports only the reader and
  reports the semantic claim's time, trace size, and closed-term count. Use it before rebuilding
  the realization layer; it cannot establish complete identity or execution behavior.
- **Clean integration candidate:** `B0_INTEGRATION=1 just build` runs the repository checks (no
  leaves, reuse records, permanent acceptance) and compiles the kernel, gates, acceptance probes,
  tools and notebook package. Plain local `just build` refuses to start; CI runs it directly.
  Compilation does not execute the suite. `just test` adds `cas-axiom-audit` (only `propext`,
  `Classical.choice`, `Quot.sound`) and the no-sorry check; `just test-ci` re-executes the demo
  notebook. Do not spend a full build on each small edit.
- **Acceptance:** `just harness` runs the suite and reports every assertion's outcome;
  `just acceptance BASE` compares that report with a base report, assertion by assertion
  (`scripts/check_acceptance_regression.py`). That is development regression, not B0
  completion, which is judged against the fixed B0 requirements at one revision tuple.
- **Reviewer controller:** `python3 custodian/review/test_review.py` on a scratch copy (its usage
  line).
- **Workflow provenance:** the [plan's Running checks section](specs/computational-core-plan.md#running-checks)
  distinguishes Gates on `main`/`b0/**` from the committed-tuple V1 candidate workflow.
  Main's inspected Gates file has no Sage/GAP setup; the candidate branch adds it to its
  Gates definition, while the V1 candidate workflow installs its declared engines. Inspect
  the actual workflow revision and stage/report; failed compilation can prevent execution/export,
  and a diagnostic tuple does not establish latest-main compatibility.
- **Documentation only:** inspect the focused diff and its stated invariants; no Lean build.
  CI skips the Lean jobs for documentation-only changes.
