# Custodian findings, 2026-09-30

## 2026-10-20 — Independent compositional assessment at 8cef0b2

Assessed committed candidate `8cef0b299ebd9d37f910fcf3244b6945d8d8f6d5`
against the fixed B0 acceptance-table arguments, after reading the owning reuse
records. Its `CasCatalogue/` bytes are identical to `5410e70`. Read generic
kernel source and protected probe source, not leaf source, leaf claims, or the
concurrent harness outcomes. Public formal-interface inspection used the local
`lean_categories` checkout at manifest revision
`eea5c7f3bce7a1d2fdfbd58840c4d4bd75c9a8bc`; this was verified before inspecting
the registry, family-reindex validator and lift computation interfaces.
This assessment supplies conditional engineering arguments and concrete gaps;
it supplies no new mathematical theorem, protected approval or B0 acceptance.

**Dependent application and admission.** `Language.applyFamily` (3045 onward)
opens the registered declaration's complete dependent telescope, binds explicit
parameters and actual source endpoints jointly, applies only admitted
coercions, synthesizes instances and closed obligations, then checks the whole
instantiated application. Unresolved parameters fail; supplied applications
must have the registered head, exact argument count and correct full type.
The completed operation is retained in the trace rather than reconstructed from
its answer. `typedParameter`, `registeredStructuredParameter`,
`selectedOperationApplication` and `applyOperation` retain complete selected
structure witnesses instead of selecting an arbitrary carrier alias. The
compositional argument is conditional on each input already having its declared
semantic endpoint: applying the same telescope rule to the next registered
arrow preserves those endpoints and obligations, without a per-operation case.
`Language.admit` (4756 onward) separately retains original map/category/endpoints,
applies the row's admission at its actual target, and obtains hypotheses only
through the row's evidence operation. Operation demand never supplies admission
evidence. These are inspected mechanisms, not a proof that all readable inputs
or independently supplied extensions succeed. Selected-structure, parameter,
evidence-presentation and binder probes are relevant bounded checks; none was
rebuilt during this assessment.

**Structural closure and coherence.** `Resolve.resolveMethod` enumerates
registered structural routes; `closure` derives receiver operations from that
resolution, not a receiver-specific method inventory. `Semantic.method`
composes the registered functors and applies the method at its owner.
Consequently a new row enters the same closure computation provided its source,
target and retained parameters match the registered route. `comparisonsFrom`
and `classify` identify routes only through registered invertible cells, with
common-prefix/suffix rewriting; multiple comparison cells, several classes or
no unique directed source remain resolution errors. The explicit `CellSyntax`
surface elaborates composition, whiskering and actual `NatTrans.app` components
using Mathlib. There is a remaining argument gap for the ordinary method path:
resolution carries `comparisons`, but `Semantic.method` records only method id,
route and receiver in `Node.method`; `Realize` executes that source route and
does not consume those comparison ids. The separate explicit-cell surface and
resolver probes therefore do not establish automatic execution/provenance of
the comparison required by `cc-cohere-exec`. No claim that all such comparisons
are actually applied follows from route identification alone.

**Prescribed reindexing.** `Semantic.reindex` (314) admits only registered
`.familyReindex` functors, binds the actual base morphism and selected receiver
type, rejects open terms, and refuses multiple applicable reindexings. Public
upstream `validateSemanticEntryDeclaration` checks that such a row uses its
family's `CategoryFamilyRealization.reindexRealization`, rather than merely
having matching endpoint names. `Trace.functor` retains the chosen declaration
arguments and receiver; `Realize`'s corresponding branch reconstructs that exact
action and verifies its semantic image before dispatch. This gives a conditional
prescribed-transport argument from the checked upstream family structure; it
does not establish all fibrations or new source presentations. The family
registry probe rejects constant counterfeit inclusion/reindexing realizations;
its source was inspected, not rerun.

**Complete structured results and route lifts: concrete defects remain.**
`StructuredResult.dataPlan` saves constructor-binder and diagram-input roles
before formal unification, so equal formal objects need not collapse distinct
computational ports. `validatePlannedData` requires the complete ordered packet;
`complete` keeps its independently fixed formal presentation separately from
opaque backend fields, and `projectData` selects defining maps from that complete
schema. Validators return `Unit`, not backend-derived categorical laws.
For subobjects, `Resolve.resolveMethod` requires a lift for every route step,
and `Semantic.method` reverse-folds `liftSubobject` over the saved intermediate
receivers. This is a formal compositional argument: each accepted lift is
applied at the actual next base and source, preserving the defining arrow and
its formal monicity. It is not yet the required computational argument:

- `Realize.realizeFresh`, `.methodWithLifts` (2733 onward), establishes that
  `sourceCategory.expression` uses the Arrow constructor and builds a separate
  result `category` using Subobjects, but passes `sourceCategory` to
  `LiftedSubobjectData.decode` (2764). The decoder (84 onward) requires its
  category argument to use Subobjects and rejects an Arrow constructor. Thus
  this production call cannot complete a lifted packet even though the direct
  packet probe passes the correct `cat.subobjects_bilin_module` argument.
  Its exact failure position can occur earlier: `Language.method` (2051)
  records `.arrow sourceCategory.id` using the base category, and `Realize`'s
  `.arrow` branch turns that directly into `Form.arrow`; `Form.category` returns
  that id although transport expects the Arrow category's expression. The
  actual production path needs one consistent base/Arrow/Subobjects context.
- Public `LiftEntry.computation` publishes the prescribed
  `MonoLiftComputation.obj`, `.hom`, `.forward` and `.backward` callable data.
  The production kernel never reads that field. `LiftedSubobjectData.decode`
  constructs `packet.components` as pending plans, but only its direct probes
  read the components; `Realize` returns `packet.data` without executing them.
  Later `.functor` and transport branches forward the opaque packet under
  their own operations; they contain no lift-component dispatch loop.
  `decodeLiftedAt` explicitly refuses law-bearing reconstruction and supplies
  no deferred computation path. Therefore neither creation of a closed formal
  lift nor storage of a plan establishes required component execution or
  composition of actual intermediate outputs. Missing component computation
  must remain a named execution gap. Do not substitute the formal lift or copy
  the downstairs data into every step.

**Proof refinement and group constructions.** Property interpretation is
classifier-based (`Semantic.property`), while `Realize.realizeDecision` returns
an untrusted `Option Bool` through its ordinary computation port. It cannot
re-type an object; `.property` is not a value-producing realization branch.
Formal proof discharge uses `Decide`/`Codec`, independently of that answer.
However, the reuse record describes a generic `CasCatalogue.refine` and
`refine%` surface that are absent from the tracked Lean source inspected here.
The current `Language.object` selects already registered refinements and
`Realize.transport` follows their accepted identifications; this does not
establish the table's generic proof-driven retyping of `Fin 2 × ℤ/3`.
That row's positive interface/production path must be established, rather than
counting the property-resolution probe as its retyping argument.

Group inverse itself has a generic dispatch path: notation calls
`applyOperation "⁻¹"`, whose selected-structure binding and dependent
application are shared with other operations. A construction already supplied
as an object of the group category can obtain that interface without a bespoke
inverse-method inventory. This argument is conditional on complete upstream
construction/category/structural rows and their typed result recognition. It
does not establish the required second construction, subgroup inclusion or
registered computation observations; those independent inputs and trials remain
separate obligations.

**Stage-specific outcomes: concrete ambiguity collapse.** The outer pipeline
has the right separation: `interpret` prepares a typed question before execution;
`ExecutionOutcome` cannot express semantic invalidity/ambiguity;
`executionFailure` maps unexpected semantic/runtime exceptions to `internal`;
`TestSuite.runFile` catches an escaped execution exception as `internal` and
preserves the assertion id. `send` distinguishes absent/ambiguous registrations,
unavailable sessions and port failures; packet rejection is `malformed`.
But `Semantic.method` (475) and `Semantic.property` (519) map *every*
`ResolutionError` to `throwStratum .invalid`, including unresolved route/property
ambiguity, competing comparison cells and no unique source route. Production
`Language.method` uses those functions. `Outcome.ofException` (5327) sees the
invalid stratum and cannot recover the distinct ambiguity tag. This violates
the required stage meaning; a correctly typed outcome enumeration alone does
not prove a total correctly stratified pipeline. Correct the resolution-error
translation, preserving invalidity, ambiguity, missing computation and internal
failure according to their actual stage.

**Preserved question consumed by execution.** `Realize.TypedQuestion` contains
claim, immutable interpreted trace, identity and mathematical revision.
`interpret` constructs it before discharge/dispatch; `evaluate` consumes that
claim and trace rather than re-reading source or deriving a question from the
answer. `QuestionIdentity.encodeInContext` rejects open/metavariable terms and
retains declaration identities, levels, application arguments, binder types,
let values, projections and propositions of proof arguments; metadata and
binder spelling are ignored. Operation-tree serialization includes selected
parameters, explicit maps and routes. This supports the architecture of one
typed request crossing evaluation, with the coherence-provenance limitation
above. It is not an independent mathematical preservation comparison for all
admitted identities or dependency changes. No authoritative interpretation
record was edited or regenerated.

No Lean builds, live backend executions or extension trials were launched in
this review; root held the Lean slot and the full harness was still running.
Inspected probes establish their stated boundaries only when actually run at
the candidate. Source arguments above neither replace those observations nor
close the fixed B0 rows. Only this findings document was changed.

## 2026-10-20 — Independent disposition of exact-blob snapshot repair

Assessed focused repair `f1061e045d8779fbd15119db765592bfe3dc6986`.
The snapshot imports `retrieve_candidate.py` by the trusted review module's own
location, not from the candidate. Root and dependency snapshots both reuse that
blob materializer with their independently read exact revision; fetching HEAD
must reproduce that revision or retrieval fails. Source/dependency status reads
retain the sanitized Git environment. No checkout remains in these snapshot
materialization paths, and the helper validates complete regular-file trees
before writing raw blobs. No authority or mathematical input selection changed.

Independently reran the CRLF and ambient clean/smudge reproductions together
through production snapshot, using separate temporary source and dependency Git
repositories. Both contained `candidate.txt text eol=crlf filter=reviewfixture`
attributes; the ambient clean/smudge commands would create a marker. Observed:
filter marker absent; exact source revision preserved; exact dependency revision
preserved; source and dependency bytes both remained `b'committed\n'`.
The existing real Git retrieval/snapshot fixture also passed, including its
source/dependency raw-byte assertions and prior link/moved-ref rejection paths.

The previously reproduced ambient-filter and checkout-EOL findings are resolved
in this construction source. No additional blocking finding was found in this
focused repair. This disposition does not establish protected runtime deployment,
real reviewer completion, independent signing approval or B0 acceptance. No
implementation or protected authority was changed by the assessment.

## 2026-10-20 — Exact-byte snapshot construction repair

The reviewer identified candidate `.gitattributes` with `text eol=crlf` changing
committed LF bytes during the remaining snapshot checkout, despite ambient filter
isolation. Reproduced as a failing byte comparison through production `snapshot`.
Snapshot source and dependency materialization now both call the existing trusted
Git-blob retrieval helper, preserving complete-tree path/link validation and exact
revision checks without checkout attribute conversion. Metadata/status reads retain
the isolated Git environment. Requirements, signing and admission paths are unchanged.

The real temporary Git regression now exercises source and dependency snapshots
with candidate CRLF attributes and independently configured clean/smudge commands:
committed LF bytes remain exact and no filter marker appears. Twenty controller
fixtures and two review-context fixtures passed; the expanded dependency-byte check
also passed. These are bounded construction checks, not independent approval or a
hosted workflow/acceptance result.

## 2026-10-20 — Independent snapshot ambient-Git reassessment

Assessed `8399a64055cacafdd3e09cf2ac5ece7f2967c378` on the focused
snapshot path. Root and dependency revision/status checks, clone and checkout
operations now use the explicit sanitized environment and disabled hooks.
The remaining `V.tracked` calls list files; they do not perform clean/smudge
materialization. Independently reran the original temporary global filter
reproduction with both clean and smudge marker commands: neither retrieval nor
snapshot created the marker, and the ordinary candidate bytes and exact revision
were preserved. The real retrieval/snapshot fixture also passed. The previous
ambient-filter finding is resolved in this construction source.

**Remaining exact-byte finding in this same snapshot path:** sanitized
`git checkout` still applies candidate-controlled built-in attributes. A separate
real Git reproduction committed `candidate.txt` as `b'committed\n'` with
`.gitattributes` containing `candidate.txt text eol=crlf`, retrieved it with the
production helper, then invoked production `snapshot`. Retrieval retained
`b'committed\n'`; snapshot produced `b'committed\r\n'`. The revision stayed
the same but snapshot bytes differed. This does not execute candidate programs,
and it is not a remaining ambient command-filter path. It prevents claiming
that snapshot materialization always presents the committed bytes to byte-based
seal/assertion checks. Materialize snapshot files from their Git blobs, or
otherwise prevent attribute transformations while preserving the exact source
revision and regular-file checks. Do not change authoritative hashes or
acceptance assertions to match checkout-transformed bytes.

No implementation, protected authority, evaluator or mathematical input was
changed by this assessment. It is technical source review, not independent
authority activation or B0 acceptance.

## 2026-10-20 — Independent review of candidate data retrieval

Assessed repair `3764b13204dd059775addcb79e38147d338fb338` against
`5410e70`, including the trusted review workflow, new retrieval helper, chain
preparation and the existing snapshot consumer. The helper validates full SHA,
checks fetched PR ref against the event SHA, and uses object reads instead of
checkout. It rejects links, gitlinks, absolute/traversal/Git-metadata paths and
backslashes before writing candidate files. Its fresh destination and sanitized
Git environment prevent candidate source and ambient checkout filters from
running during retrieval. Workflow inputs are shell-quoted environment values;
the executable helper remains the trusted base's. No changed mathematical,
requirements, evaluator or signing-identity selection was found.

The real Git retrieval-to-snapshot fixture passed, preserving exact candidate
bytes and revision, leaving its executable marker absent, rejecting a symlink
tree before materialization and refusing a moved PR ref. Source inspection found
no new arbitrary candidate-execution or protected-authority path in this repair.

**Bounded remaining filter-path finding:** the downstream existing
`custodian/review/review.py:snapshot` still invokes ordinary `git clone` and
`git checkout` with ambient Git configuration. Independently reproduced with a
temporary candidate containing `.gitattributes` naming `reviewfixture` and a
temporary global Git config defining its smudge command as `touch MARKER; cat`.
`retrieve_candidate.retrieve` preserved exact bytes and left MARKER absent;
the subsequent production `snapshot(verify, head, target)` created MARKER.
Thus initial retrieval is filter-free, but its current snapshot consumer is not
filter-free by construction. This is an existing consumer condition, not proof
that the hosted runner has that filter or that a candidate can install an
arbitrary filter command. Complete the end-to-end guarantee by suppressing
ambient filters in snapshot materialization, or establish the exact protected
runtime configuration excludes them; do not infer that guarantee from replacing
the workflow's first checkout alone.

No privileged hosted run, real reviewer invocation, protected publication or
activation was performed. This is independent technical source assessment;
passing the retrieval fixture is not protected approval or B0 acceptance.

Construction repair note (2026-10-20): the actual snapshot consumer now uses a
fresh Git environment for metadata/status reads and every repository/dependency
clone and checkout. Ambient global/system configuration and inherited Git
configuration variables are absent, and hooks remain disabled. A real subprocess
regression supplies both clean and smudge commands through a temporary global
Git config and candidate `.gitattributes`: the marker appeared before the repair;
afterwards neither filter executes and snapshot bytes still match committed
candidate bytes. Twenty controller fixtures and two review-context fixtures pass.
This repairs the reproduced ambient configuration path; it does not claim an
arbitrary preexisting local Git configuration is trusted or independently accepted.

## 2026-10-20 — Privileged candidate checkout source repair

The push-time Semgrep rule
`yaml.github-actions.security.pull-request-target-code-checkout.pull-request-target-code-checkout`
reported `.github/workflows/custodian-review.yml` checking out a PR head under
`pull_request_target`. Candidate commands were not intentionally run, but candidate
filesystem links reached privileged dependency preparation before review snapshot link
checks. Candidate retrieval now runs trusted-base code that fetches Git objects, verifies
the event SHA, rejects links/gitlinks and escaping paths across the entire tree, and writes
only regular blob bytes without checkout filters, hooks or candidate execution. Protected
base review code, judging requirements, signer and signature/publication checks remain the
independent authorities. The fetched PR ref comes from the base GitHub repository and
must still equal the event's full SHA; a moving ref fails rather than selecting a new one.

A temporary real Git repository test exercises retrieval through the actual reviewer
snapshot consumer, checks candidate bytes and exact revision, verifies a candidate script
never executes, and rejects a later symlink and a moved ref before exposing candidate
files. Twenty controller fixtures and two review-context fixtures passed. Semgrep's
`p/github-actions` scan ran 11 YAML rules with zero findings on the changed workflow;
no suppression or QC change was made. No real GitHub workflow, Docker runtime check,
independent acceptance or deployment ran as part of this construction repair.

## 2026-10-20 — Independent disposition of consumer/provenance correction

Assessed clean construction revision
`1ca184cb7a600e18d806c04a06a21e7b6aa19784`, including its actual launcher,
resolver, committed/external artifact readers, controller snapshot reconstruction,
assessment assembly, publication verifier and owning SETUP instructions.
The three remaining findings recorded for `230ed8d` are resolved in this source:

- Launcher selects the assigned role before resolving its `ROLE_INPUTS`.
  Public metadata adds mathematics/contract only for an operation consuming that
  artifact. Independently rerunning the prior two-repository production-resolver
  reproduction after advancing contract main now lets the mathematics-only
  formalization consumer proceed and leaves the unrelated contract snapshot
  untouched. Real launcher subprocess fixtures additionally establish that
  formalization, acceptance and kernel nonconsumers start despite stale metadata,
  while an unavailable contract blocks its actual acceptance consumer.
- Both committed and external public metadata now require explicit mathematics
  and contract provenance. Independently rerunning production resolution for
  both representations rejected stale contract provenance and missing
  provenance. `AcceptedArtifact`, `ExternalArtifact`, leaf assignment and
  full review request assembly retain/check the corresponding provenance;
  signed request reconstruction includes it. A metadata descriptor without a
  fixed artifact wrapper is rejected at the consuming resolver rather than
  exposing an upstream repository as public metadata.
- SETUP now states latest-main source consumption without separate dependency
  admission or re-pin transactions, distinguishes reproducibility snapshots
  from fixed judging inputs, and limits stale-artifact blocking to consumers.
  Protected controller bootstrap, evaluator/requirements protection and the
  real independent signing identity remain separate authority operations.

Inspected signed replay separately from latest-main selection:
`apply_assessment.assemble` reuses captured source base commits without fetching,
keeps configuration-owned requirements, acceptance/judging and reviewer identity,
and calls `Controller.advance` to reconstruct the exact source/artifact snapshot
before verifying the independently configured signature. Publication verification
requires that reconstruction to match the proposed configuration. The real Git
and ephemeral-fixture-key assessment/publication fixture passed its signed
snapshot, absent-evidence, changed-authority-field and forged-source cases.
Its substituted model response establishes transport only, not independent
reviewer competence or protected admission. No additional blocking finding was
found in these changed consumer/provenance and replay paths.

Independently ran all seven lightweight fixture programs with
`GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1`: controller (1), launcher
(11), author launcher (1), materialize (1), assessment (1), dependencies (4)
and review context (2), 21 passing fixtures. The separate production-resolver
reproduction confirmed protected requirements, acceptance and reviewer identity
were unchanged. No Docker runtime fixture or real external reviewer invocation
ran; prior evidence gaps remain bounded to those operations. Broader technical
capability alone is not a conduct defect or additional acceptance prerequisite
under the 2026-10-10 owner ruling. This source review neither activates a
controller nor declares B0 accepted.

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

Construction repair note (2026-10-20; independent disposition remains separate):
The launcher now supplies its role's permitted input names to dependency resolution.
Only consumed inputs and public-artifact provenance dependencies are resolved or checked;
full assessment/materialization still checks its complete consumed tuple. Both committed
and external artifacts require exact mathematics and contract provenance. Committed
artifact provenance is retained in the signed request and checked during reconstruction.
SETUP now states current-main source consumption and reproducibility snapshots, retaining
separate controller/evaluator/requirements/signing protection. Temporary Git repository
regressions exercise a contract main advancing while unrelated authors continue, unavailable
nonconsumed source repositories, mathematical main advancing for a formalization author,
and missing provenance in both artifact representations. Nineteen controller fixtures and
two review-context fixtures passed with isolated Git configuration. These are construction
checks, not independent acceptance, deployment, a real reviewer result or a Docker runtime
result; the previously recorded Docker evidence gap remains.

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

Runtime candidate `5410e70e012963501d4583e0660b14d4079bbd02` passed the local
7,554-job integration. Its completed computation-only run reports all 153 admitted
IDs exactly once and one additional failed inverse binding. It imported mathematics
`eea5c7f3`, contract `3c2159b5`, leaves `c5bf283c` and notebook worker `4c6c2a77`.
Artifacts, complete reports and input observations are in `/tmp/b0-poc-5410e70/`.
No hosted result is attributed to this candidate: ordinary publication failed its
source QC gate and is being corrected through normal source operations.

| Admitted assertion outcome | Count |
| --- | ---: |
| Holds | 18 |
| NoImplementation | 127 |
| Unavailable | 3 |
| Invalid | 5 |

All **15/15 required computations hold with nonempty registered dispatches**,
including reversal and all three discriminants. This establishes that runtime
observation, not the additional positives, question preservation or B0 acceptance.
The report has a provenance limitation: a concurrent diagnostic refreshed the
running worktree's manifest while its imported environment stayed fixed. Readable
question labels split between 82 `eea5c7f3` and 66 `293fccff` records. They are
retained unchanged. The final integrated candidate must run with stable inputs;
this mixed-label report cannot establish one coherent authoritative tuple.

Five inverse questions remain unreadable through matrix-unit admission, despite
the independently published upstream repair and closure of lean-categories#92.
That source milestone did not discharge the actual unchanged assertions. Establish
the current reader/admission boundary on latest mathematics before assigning the
remaining defect; the kernel does not reshape upstream evidence or commission
mathematics from its failing term. Three broader unavailable outcomes are backend
errors on finite-set/construction data; their failure stratum remains visible.

All 148 readable complete question bodies and propositions match `32c3897` after
removing only the revision-label prefix for diagnostic comparison. Independent
acceptance assessment covers those identities against its prior source-grounded
specifications and retains the five absent questions. This does not admit new
interpretation records. The unchanged permanence checker stops at those five
unread questions; it has not passed the later record comparison. A separate exact
audit finds 11 unrecorded identities and 137 readable differences from the stored
historical records. The record itself is unchanged from the saved base.

The additional positive proposals expose generic runtime work, including Arrow
request categories and canonical source-form dispatch for already admitted
composites. Independent source assessment also identifies unexecuted prescribed
lift components. The ambiguity-stratification defect is corrected in `69e96e2`
with real reader-boundary red/green checks; its wider integrated behavior remains
to be established. No admitted mathematical assertion or expected value changed.

Upstream mathematical source instances and their bounded independent assessment
are published through `80520813`; they are not kernel extension-trial outcomes.
Independent trials, their complete compositional arguments and final acceptance
remain outstanding. The last verified protected `accepted/controller` lookup was
404; source integration does not bootstrap or approve it. Actual deployment
operations remain in `custodian/SETUP.md`. These dependencies do not stop available
generic kernel construction or permit downstream authorship of mathematics/leaves.

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


## 2026-10-20 — Unfinished route-completeness argument at owner stop

Read-only review of construction `4bc36b6` found all seven kernel consumers of public
`SemanticState.routes` omit its fuel argument (default 32). Thus a complete finite
composition argument has not been established by the consumed enumeration. This
is not evidence that any particular admitted assertion fails; the native inventory
was interrupted by the owner before producing its report.

A proposed kernel-consumer correction would discover a finite reachable enclosure,
check closure under actual public `edgesFrom`, and pass its vertex count to the existing
simple-route enumerator. Current Arrow/Core lifting and non-growing explicit endpoint
spines permit such an enclosure in the inspected tuple; future releases require actual
closure checking. No correction or extension trial was implemented. See `HANDOFF.md`
for remaining validation and the distinct missing constructor-cell action.

**Correction to the proposed resolution (2026-10-29).** The two registration
invariants proposed in [#79](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6475626921)
do not settle this finding. CC-COHERE preserves distinct structures and permits ambiguity;
it does not force every structural cycle to compare to identity. Non-increase of a
well-founded measure does not imply finite reachability: on vertices n in Nat with edges
n→n+1, the constant measure zero is non-increasing while the reachable set is infinite.
The [later audit](https://github.com/dzackgarza/lean-cas-dsl/issues/79#issuecomment-6476123893)
already records this missing hypothesis.

For the actual implicit-resolution rules, establish a finite reachable enclosure closed
under `edgesFrom`, then enumerate its simple routes using the enclosure size. This alone
does not establish completeness for arbitrary walks or make explicit cyclic composites
redundant. Any normalization must state its hypotheses and preserve the selected comparison
witnesses and directions. Exhausting a resource limit reports failure to establish closure
within that limit, not mathematical nonexistence of a finite enclosure.

K11 retains that precise search-completeness obligation. It is not blocked on the two
proposed universal admission conditions. Deletion of fuel, the enclosure limit or an
incomplete-search outcome requires an adequate replacement argument and implementation.
