# Native notebook / CAS session contract v2 — consolidated design

**Feature:** `001-categorical-research-language` · **Updated:** 2026-11-07. **Specification:** [scope, clarifications and workflows](../spec.md) · [requirements and acceptance](../spec.md).

This is the current planning contract, not evidence that a candidate implements or has passed it. Read with the [consolidated computational runtime](computational-runtime.md), [mathematical-input contract](mathematical-input.md), and [data model](../data-model.md). It incorporates the existing staged/committed completion, non-settling duplicate-ID, inert observation and exact-demand liveness corrections. Their earlier findings remain historical evidence, not contradictory alternative instructions.

The native Lean 4.33 worker and Python Jupyter adapter retain the original mathematical notebook, questions and lifecycle. This internal artifact includes protected validation context; release only neutral API material to public-only contributors. A notebook/front-end must not add a route preference, supply a missing categorical choice, request leaf-authored mathematics, or turn a source-prescribed selection error into a different query.

## 1. Authoritative state and explicit execution

Immutable Environment snapshots own prepared programs, actual committed values, CommittedReceipts and data-only observation descriptors. An active transaction may use its whole-reply-validated StagedCompletions, but a query sees only committed state. The external live supervisor owns real connection generations, monotone occurrence/reservation and transport-ID metadata, permits and active coordination—not a completed-value/closure heap, result cache or recovery journal. The adapter owns display bookkeeping and snapshot references; saved cell text/output are document data, not live computational state.

One mutating cell transaction is active per worker; explicit executions queue with their selected parents. Internal consumers of the same actual pending CAS occurrence join it within that transaction. Equal source text, a hash or a repeated notebook transport ID is not that occurrence. A later Python research facade uses the same mutation boundary and is not added as a V1 prerequisite.

Only explicit execution or explicit session start may start a worker. Inspection, completion, documentation, syntax completeness, display refresh, reconnection and snapshot selection do not start/recover one. Fresh startup creates a fresh actual nonce. Worker loss never authorizes session-cache restoration, prefix replay or rebinding old tokens into a new process. Previously rendered output may remain visible as saved output only.

Actual chosen mathematical data remain part of the question/result context. The adapter forwards the kernel's prescribed missing-data/ambiguity/ill-typed-evidence outcomes; it does not resolve them by choosing a route, trying another provider or silently changing an ordinary request to a choice-producing one. An independently specified choice operation may legitimately produce different later selected contexts; those actual choices persist.

## 2. Handshake before source transmission

Retain dedicated inherited request/reply file descriptors and ASCII byte-length/newline/UTF-8 JSON framing. stdout/stderr are diagnostic streams, not protocol channels. The historical worker at `f3e73ed400df38f23821a038ec078cfa1d1bfed5` used protocol 1 and executable inspection; extra fields cannot safely opt it into this contract. That is a pinned historical comparison, not a statement about an uninspected current build.

On explicit startup, before accepting source:

```json
{"op":"ready","protocol":2,"release":"<build release>","lean":"4.33.0",
 "pid":1234,"worker_nonce":"<fresh actual process nonce>","snapshot":"0",
 "realization_profile":{"id":"<selected profile>","sha256":"<frozen profile hash>"},
 "features":["cas-session/2","explicit-parent/2","atomic-cell/2",
 "inspect-environment/2","complete-environment/2","cancel-by-request/2",
 "no-replay/2","no-session-cache/2"]}
```

Require protocol 2 and all eight notebook features before serializing/transmitting any candidate `code`. Require the immutable startup realization-profile hash to match the recorded configuration; it selects computational availability, not mathematics or a per-cell preference. Release/PID are diagnostic; the actual connected process and nonce identify the session. Send:

```json
{"op":"hello","protocol":2,"worker_nonce":"...","session_policy":"cas_no_replay"}
```

Require the matching nonce/policy with `op:"hello", protocol:2, status:"ok"`. Before acknowledgement only handshake/version/shutdown controls are accepted. Unknown majors, policies, modes and control fields fail; no executable fallback or downgrade. The separate provider protocol requires its own four features; do not confuse the two handshakes.

An existing incompatible or unacknowledged worker yields local `unavailable/incompatible_protocol` without transmitting candidate source. No live worker yields `unavailable/worker_absent` without startup. These guards apply to inspect/complete as well as execute. Features grant no semantic registrations or interpretation preference.

## 3. Exact transport identity and requests

Post-handshake requests include `protocol:2`, a fresh string `request_id`, actual `worker_nonce` and `op`. Snapshot serials are decimal strings scoped to that nonce. A different nonce is rejected without evaluating anything or consuming an ID in the current session. Cancellation mode is exactly `cooperative` or `force`; omission/unknown values are protocol errors. UI cell IDs, transport IDs and CAS occurrence IDs are distinct.

### 3.0 One transport ID is admitted once

After validating the session header and ID shape, atomically claim the unused `(actual nonce,request_id)` **before** operation-specific validation/evaluation, enqueue, transaction creation or waiter registration. A newly claimed ID stays consumed even if later payload validation fails. The namespace covers all post-handshake operations, and its used-ID set is nonrollbackable resource metadata with no source text, result payload or completed promise.

Every repeat is rejected whether its payload is identical, changed or a different operation. It is not joined, reexecuted or answered from a cached result. Emit exactly the source-free diagnostic:

```json
{"op":"protocol_error","worker_nonce":"<actual nonce>",
 "offending_request_id":"<repeated ID>","reason":"duplicate_request_id"}
```

It contains no snapshot, commit or outputs, and is not a success/error/cancellation response for the original execution. It must not settle that original pending promise or claim it rolled back. The adapter handles it separately, without resend/fresh-ID retry. Deliberate rerun uses a fresh ID. Internal consumers of one actual pending CAS occurrence still share that occurrence under the runtime rule; this does not send duplicate notebook requests.

The atomic insert has one winner and only that winner enqueues; completion, cancellation, lost reply or snapshot selection never removes the ID. This establishes at-most-once admission for that nonce, not durable exactly-once external effects.

### 3.1 Execute

```json
{"protocol":2,"request_id":"<fresh transport ID>","worker_nonce":"...",
 "op":"execute","cell_id":"<UI cell>","parent_snapshot":"12",
 "session_policy":"cas_no_replay","code":"<explicitly submitted cell>"}
```

The parent must be an available committed snapshot in this worker. Choosing an older snapshot is legal but does not roll back resource metadata. Missing parent gives `unavailable/snapshot_unavailable`, never prefix execution. Edited predecessors are not automatically run. Use explicit-parent `execute_at` with cache/ledger replay disabled, not `restart_and_replay` or `_ensure_prefix`. Each deliberate rerun has a fresh transport ID and fresh internal occurrences.

Preparation uses the complete source context and selected comparison/choice rules in the mathematical-input contract. A mandatory missing semantic datum errors before its dependent invocation. An absent implementation of a valid choice computation is a different outcome. A reply omitting required computational choice data is malformed; no partial dependent result is staged/published as success.

Successful response:

```json
{"request_id":"...","worker_nonce":"...","status":"ok",
 "parent_snapshot":"12","snapshot":"13",
 "commit":{"transaction_id":"...","output_batch_id":"...","profile_sha256":"...",
           "result_refs":["<opaque live reference>"]},
 "outputs":[],"diagnostics":[]}
```

Outputs form the complete committed batch. Each entry has unique `result_id`, a `mime` mapping with usable `text/plain` and mathematical `text/latex` where applicable, actual selected-result qualifications and required primary mathematical/routine references. Emit once per result event; useful fallback text is not a second plaintext display event. Deduplicate delivery by batch/result ID, never by reexecution. Internal proof terms/slots/routing vocabulary are not required user steps. Do not stream usable results/references/LaTeX batches before commit or disguise an uncommitted structured result as diagnostic text.

Failed/cancelled execution retains `snapshot = parent_snapshot`, empty outputs and no commit. Errors have `status:"error"` with actual existing stratum when present and precise reason/diagnostic. Cancellation has `status:"cancelled"`, not a mathematical answer. After lost communication following send, report `unavailable/connection_lost_after_send` with indeterminate execution; no invented rollback/success assertion and no resend.

### 3.2 Inert inspection, completion and syntax completeness

```json
{"protocol":2,"request_id":"...","worker_nonce":"...","op":"inspect",
 "mode":"environment","snapshot":"13","code":"<candidate buffer>",
 "cursor":17,"detail_level":0}
```

Check completed negotiation before serializing/transmitting code. Candidate buffer text only locates tokens/spans. Read immutable committed environment names and prepared observation descriptors with non-extensible, data-only lookup/formatting. Do not pass candidate text to `Frontend.processCell`, command elaboration, user macro expansion, `#eval`, proof search, CAS dispatch, cache restoration or source replay.

Do not reuse an executable `Query.inspect` path merely because it begins from an Environment. In particular `Meta.ppExpr`/registered delaborators, documentation callbacks, lazy-field/provider calls and extensible formatting on **success or error** paths are not inert observation. Preserve the historical query's useful lookup concepts only after replacing its effect-capable work. Prepare needed type/context/selected-map/cell/choice/qualification/provenance descriptors at authorized compilation/publication, within original measured budgets; do not hide preparation in warmup. Committed mathematical metadata need not disappear merely because a computational owner died.

Source requiring an unexecuted local declaration may yield no result; do not establish it by execution. `complete` has the same fields except `detail_level`, requires environment mode and `complete-environment/2`, and returns names/retained-binding completions without arbitrary candidate elaboration. `is_complete` uses syntax mode and nonexecuting tokenization/syntax inspection; it must not invoke user extensions or evaluate code to obtain an answer. With no compatible worker, a local nonexecuting syntax answer or `unknown` is allowed, not startup/recovery or a local mathematical interpreter.

Query success returns inert operation-specific data (`found`, retained documentation/type text, completion matches or syntax state). Missing snapshots/worker loss/incompatible modes use `status:"unavailable"` with a resource reason. Malformed/unknown controls are protocol errors. A query consumes its transport ID under §3.0 but creates no CAS occurrence, dispatch, value publication, owner change or native resource. It cannot see an active transaction's staged prefix.

### 3.3 Cancellation and source-free commit status

```json
{"protocol":2,"request_id":"<fresh cancel ID>","worker_nonce":"...",
 "op":"cancel","target_request_id":"<execute ID>","mode":"cooperative"}
```

Handle source-free cancellation outside the queued evaluator. The commit/cancel gate has one linearization point. If cooperative cancellation wins, mark the transaction cancelled, stop new child/resume scheduling, retain exact frame drainers, and publish no new outputs/references. If commit wins, return `already_committed` with its actual commit/snapshot; it cannot be undone. A queued execute can be cancelled before its transaction starts. Unknown target returns `not_found`, without creating an occurrence. These are control acknowledgements, not mathematical strata.

A detached waiter is distinct from whole-cell cancellation; it does not kill another waiter's required work. Normal interrupt requests cooperative cancellation: drain the exact in-flight frames, discard late value/deferred programs and only their uncommitted leases. Keep the permit until that reply drains, so a later request cannot consume it. Never schedule late children/resume after cancellation. If the engine does not reply, report draining/busy state without silently closing a prior owner. An unacknowledged worker cancellation reports `unavailable/cancel_unacknowledged`; no asserted rollback or hidden forced kill.

Explicit force closes the actual still-active/draining connections associated with the target and returns `forced` plus exact `invalidated_owners`. Required transitive dependents become unusable. Shutdown/restart or actual framing/transport failure similarly reports generation loss, not successful cooperative cancellation. No implicit escalation, retry or replay. Unrelated portable data/owners survive as specified while their committed state remains available; local access to an independent stored field is distinct from a demand for a stale whole record.

A fresh source-free `commit_status` request names `target_request_id` and an available committed `snapshot`. Return `committed` only from a CommittedReceipt visible there, `pending` only for permitted current active work, otherwise `unavailable`. An active transaction with StagedCompletions is still pending. The ledger's consumed/used-ID tombstone supplies neither hidden payload nor receipt. This query does not resend code or recover results. Duplicate transport requests use §3.0, never the former “reject or join” alternative.

## 4. Joint publication, actual captures and demand-scoped owners

Extend the successful command/Environment snapshot boundary to the entire CAS program/value/CommittedReceipt/observation delta and complete display batch. Whole reply validation produces transaction-local StagedCompletion first; later expressions in that transaction may use it. Whole-cell commit promotes everything atomically after cancellation/required-owner checks. Failure/abort publishes none; consumed reservations stay consumed. The adapter publishes only committed batches. A partial joint reply or a successful prefix of a failing cell is not public success.

Lookup first establishes visibility of an actual retained node/receipt. A local stored-field projection or inert metadata read does not demand unrelated siblings or execute a lazy field. An actual computation checks **all** dependencies of its prepared demand, including every required export/suspension capture/context/argument, before reservation and actual send. Whole-record demands keep their full dependency closure. This preserves independent portable-field survival without weakening captured-owner checks.

Native callables execute on their original actual connection/generation under the runtime's exact fresh capture frames. Suspended generators resume only under their captured-reference/role correspondence and one-use token; no expired scope is revived. A stale preliminary check followed by hidden process restart cannot authorize send. Unexpected later process death is reported under lost-reply semantics, not a promise to predict it. Owner loss does not mutate mathematical meaning/immutable payload or manufacture another chosen object/cell. Snapshot restoration changes none of these live resource facts.

## 5. Outcome correspondence

| Established event | Outcome |
|---|---|
| Missing/ill-typed mandatory formal selection, or invalid source request | Existing `invalid` preparation/evidence outcome from the accepted rule; no dependent dispatch |
| Competing inherited bindings without their required accepted selection/agreement data | Existing `semanticAmbiguity`, not proof that no comparison could ever exist |
| Interrupted required checker/planner or interpreter defect | Actual `unavailable` reason or `internal`; not semantic absence or permission to pick a route |
| No eligible realization, or multiple realizations of a fixed operation | `noImplementation` / `ambiguousRealization`; no fallback |
| Required owner dead, consumed occurrence lacking visible completion, unavailable worker/snapshot, incompatible protocol, lost connection | `unavailable` with precise reason |
| Missing required computational choice datum, invalid leaf packet/reference/layout | `malformed`; no fabricated datum or partial dependent publication |
| Malformed client controls or repeated transport ID | Protocol error; duplicate-ID diagnostic does not settle the original execution |
| Cooperative cancellation | Control `cancelled`; parent snapshot and no new output |
| Cancellation after successful commit | Control `already_committed`, actual commit metadata, no reexecution |
| Explicit forced close | Control `forced` with exact invalidated generations; required subsequent uses are unavailable |
| Well-shaped but mathematically wrong candidate | Still an untrusted computational claim assessed against the unchanged independent expectation; no universal runtime correctness detector |

The adapter and worker use the same distinctions. Missing live observation state is not mathematical non-applicability. Legitimate different returned choices produce different later contexts, not an excuse to change one fixed question's meaning. A successful protocol exchange is not a passed mathematical question.

## 6. Complete lifecycle validation entrypoint

The selected API extends retained `scripts/ci_kernel_workflows.py` with `lifecycle-v2`, preserving default full-workflow behavior and original phase names. This document does not assert that a particular current candidate already implements it. After the applicable implementation and identified candidate build:

```bash
python3 scripts/ci_kernel_workflows.py \
  --phase lifecycle-v2 \
  --root "$CAS_ROOT" \
  --runtime "$CAS_RUNTIME" \
  --published-kernel-commit "$CAS_CANDIDATE_COMMIT" \
  --legacy-worker "$CAS_LEGACY_NB_WORKER" \
  --output "$CAS_RUN/lifecycle-v2"
```

Root/runtime/published-commit retain their original meanings. The output directory is new; do not overwrite old evidence. `--legacy-worker` is the executable built at `lean-jupyter-kernel@f3e73ed400df38f23821a038ec078cfa1d1bfed5` with its normal dependencies, not shell text or a requirement for an old adapter. Its deliberate validation setup does not alter the frozen candidate tuple. The candidate runtime has the compatible adapter/worker and original engine/leaf controls.

Exercise the **actual** Jupyter/client/worker and original #24/#68/RX10 controls. Explicitly start the old worker in validation setup and prove the new adapter rejects source-bearing inspect/execute before sending candidate source. Production inspection never starts it. No new mathematical specimen, oracle or independently chosen challenge is defined here.

Keep every source-mapped observation: one actual occurrence/shared dispatch; reserve/send/receive/commit interruption; old snapshot/receipt behavior; joint admission and missing mandatory data; export capture rebinding/nested frames and suspension transfer; all captures before send; known and racing owner loss; independent stored portable field survival versus genuine whole-record dependency; same-provider deferred/resume; failed/cancelled zero publication and prior commits; waiter detach; drain versus explicit force; no hidden prefix/cache recovery; absent/incompatible worker observation; printer/documentation/error-path and lazy callback refusal; identical/conflicting/cross-operation duplicate-ID rejection without settling the original; deliberate rerun; nonce/snapshot isolation; and commit/cancel races. Actual mathematical inputs/expected results remain the original controls.

Produce `lifecycle-v2.json` with exact candidate/runtime/source and legacy-worker identities, all original source anchors, per-observation `pass|fail|environment_error`, raw wire/dispatch/publication evidence paths and overall result. Retain executed notebook and raw diagnostics. Exit 0 only when all required observations execute and pass; 1 for observed violation or skipped/not-run/unreached required observations after otherwise prepared execution; 2 for environment/artifact initialization/identity/protocol failure, never acceptance. Preserve the entire denominator on every outcome.

This phase supplements, not replaces, four connected workflows/all 17 assertions, mathematical acceptance, complete RX continuations, performance and independent extension trials. Model tests of transitions are not native protocol/SDK/notebook execution.

## 7. Preserved delivery and source provenance

Keep all 153 complete permanent readings, 134 positive extensions and original negatives/environment controls; RX01–RX10 and full RX-LIFT, its 22-binding/shared-200,000-heartbeat scope; original 99-root 3×3 under-60-second computation with full preparation/execution/admission/publication/required-descriptor timing; four actual real-engine workflows/three areas/17 assertions; and both independently chosen frozen-extension directions/all mechanisms. Full B0/parity and later public interfaces retain separate owners. No budget, expected answer, higher scope, contributor isolation or task marker changes here.

Current authority: [specification](../spec.md), [constitution](https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md), current mathematical/runtime contracts linked above, [original lifecycle](https://github.com/dzackgarza/lean-cas-dsl/issues/68#issuecomment-6586827096), [unchanged acceptance](https://github.com/dzackgarza/lean-cas-dsl/issues/24).

Historical implementation sources for reuse/replacement: [Worker.lean](https://github.com/dzackgarza/lean-jupyter-kernel/blob/f3e73ed400df38f23821a038ec078cfa1d1bfed5/worker/Worker.lean), [client.py](https://github.com/dzackgarza/lean-jupyter-kernel/blob/f3e73ed400df38f23821a038ec078cfa1d1bfed5/nbdsl_kernel/nbdsl_kernel/worker/client.py), [Protocol.lean](https://github.com/dzackgarza/lean-jupyter-kernel/blob/f3e73ed400df38f23821a038ec078cfa1d1bfed5/worker/Worker/Protocol.lean), [Query.lean](https://github.com/dzackgarza/lean-jupyter-kernel/blob/f3e73ed400df38f23821a038ec078cfa1d1bfed5/worker/Worker/Query.lean), [retained runner](https://github.com/dzackgarza/lean-cas-dsl/blob/016d3d34e526297034c7e5907a3da14368176b36/scripts/ci_kernel_workflows.py). These are not current conformance claims.

The [staged/suspension correction](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6684996781), [capture/transport correction](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6706802517), and [inert-observation/liveness correction](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6707359041) explain the incorporated failure traces and transition arguments. The current body above, rather than the old conflicting base wording, is the operative contract.

## Continued mathematical use

Publication of a result must preserve its selected occurrence and complete formal interface for
later cells. A later use of its endpoint, defining leg, chosen structure or functor image consumes
that retained relationship. Equal expressions in separate cells cannot substitute occurrences.
Formal refinements extend the applicable interface with their evidence and selected data.
The session preserves the original mathematical context when providers change. See MM005–MM012
in the [specification](../spec.md#mathematical-model-acceptance).
