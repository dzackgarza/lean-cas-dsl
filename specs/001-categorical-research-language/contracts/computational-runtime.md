# Computational execution contract v2 — consolidated design

**Feature:** `001-categorical-research-language` · **Updated:** 2026-11-09. This is the required runtime design, not a claim of released implementation or acceptance.

Read with the [current mathematical-input contract][M], [data model][D], [notebook contract][N], [corrected plan][P] and [functional][T1]/[delivery][T2] task bodies. The [current constitution][C], including C6 and C21, governs. Actual selection/admission/owner checks are functional requirements. General proofs, independent assessment, frozen trials and performance follow required functionality; they do not gate implementing the concrete executor or public connection. Final budgets and all original observations remain due.

This remains an internal design artifact. The neutral released wire/SDK material excludes kernel handoffs, protected questions, expected answers and contributor choices. No mathematical definition, proof endpoint, choice criterion, denotation or oracle is created. Historical [staging/suspension](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6684996781), [export frames](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6706802517) and [observation/liveness](https://github.com/dzackgarza/lean-cas-dsl/issues/69#issuecomment-6707359041) findings explain the retained requirements; their old task ordering is not an additional work order.

## 1. Authority and actual execution

Independent mathematics fixes categories, operations, laws, actual comparison cells, allowed-choice families and abstract computational obligations. The leaf supplies prescribed computational candidates, never the criterion it implements or proofs of its laws. Keep selected-cell use, allowed-choice computation and inherited-operation agreement distinct.

Under C6, a declared preferred route is public registration data selecting an admitted surviving binding without asserting agreement. It is validated and retained with the reading. It is not a route chosen by execution success, provider priority, installed order or cost. Required source-defined cell/coherence data inside that chosen construction remain required. A missing selection or unresolved source ambiguity fails before dependent dispatch; omitted required computational choice data fail reply admission. No global all-route proof search or identity insertion repairs these omissions.

Use Lean 4.33.0, the accepted computation families, CSLib `PFunctor.FreeM` at `3951377e5a3f5772737f11cd62bc5bb6a72f95d1` and PolyFun stateful handlers at `a5895e454254a400774fa396b64d5b968f0933df`, under the compatible delivery-input policy. Their generic sequencing laws are not a CAS compiler/executor or a proof of arbitrary answers. `P.B request` contains computational candidates at prepared roles, not foreign law-bearing mathematical inhabitants.

The real source lowerer produces the operational program. The concrete **kernel-owned** executor selects the prepared realization, calls the actual live framed connection, admits/retains the reply and resumes the compiled continuation. The public command, services and derived operations use this same path. An interpreter that leaves primitive/application execution to an unspecified caller callback, or a test that manufactures the request/program/executor, does not establish this behavior.

The Lean worker owns immutable committed state and live resource supervision; Python provides SDK/notebook interfaces. Native objects and continuations remain in their actual provider processes. No second mathematical interpreter or mutable completed-value authority is introduced.

## 2. Retained state and identities

| Record/location | Required contents |
|---|---|
| PreparedProgram, immutable Environment | Source/program/span identities; complete rigid context/universes and binding correspondence; exact expression/type and computation-family refs; selected routes, preference declaration where applicable, actual cells/actions; fixed/choice roles, layouts and operational code. No unresolved metavariables. |
| ValueNode, active staging then committed graph | Actual occurrence/field-role/program identity, source association, immutable payload, exact value/capture references, selected continuations and genuine dependencies. Projection reads this same node. |
| StagedCompletion, active transaction | Whole-reply-admitted occurrence, realization/profile, program/role, inputs, all result roots, provenance and transaction. Usable only in that active cell; not external publication or correctness evidence. |
| CommittedReceipt, immutable Environment | Admitted association plus commit/snapshot/batch identity, published only by whole-cell commit. Reuse checks the actual demanded dependencies. |
| CellTransaction | Committed parent, staged programs/values/completions/observation/output, pending typed continuations and cancellation. Commit publishes its whole delta or none. |
| SuspensionRecord, active transaction | Actual supplying connection/generation/token, original request/parent chain, prepared callable/result role, ordered captures/proxy-index correspondence, child requests/results and one-use/disposal state. |
| ResourceLedger, outside rollback | Nonce, monotone counters, reservations and transport-ID tombstones, actual generations/permits and active coordination. No completed payload, completed closure environment or value-recovery cache; settled promise payloads are cleared. |
| Provider process | Actual native objects/callables/generators under local tokens, without semantic or committed-state authority. |

Portable values have independently fixed encodings; dependent records reference exact actual fields; compiled closures retain code and actual captures; owner-bound exports retain their native tokens. Lazy/indexed/symbolic values keep the full promised domain/interface, not a finite display. Expr/hash/FVarId/name/bytes/token equality is not occurrence identity. Explicit rerun creates fresh nonce/serial identities; an existing binding retains its occurrence.

Separate visibility of the original association, local traversal to an already stored field, and computational use of a demand's complete owner closure. A dead sibling does not hide unrelated portable data or inert mathematical metadata. Whole-record demands, lazy actions and all genuine export/suspension captures still require their owners. This does not allow partial initial admission/publication, reconstruction or resurrection.

## 3. Registration, framing and negotiation

Retain the exact registration identity `operation,input,backend`; exact-input and category-wide registrations have equal standing. Command/cwd/environment identify execution. The released registration schema additionally carries the C6 declared preferred-route selection, where supplied, as explicit data validated by the source-selection boundary. It names a surviving route and asserts no equality or new subject rule. This is separate from the realization profile and wire control frames. No cost/priority, semantic result type, proof/certificate, invented meaning or self-selected owner field gains authority. Conflicting or invalid preferences cannot be resolved by iteration order or trying backends.

Use ASCII decimal UTF-8 byte length, newline, then JSON on dedicated stdin/stdout; stderr is diagnostic and notebook transport is separate. Require:

```json
{"op":"ready","protocol":2,"contract":"cas-computation/2",
 "features":["scoped-values/2","deferred/2","suspend-resume/2","export-capture-frames/2"],
 "backend":"diagnostic name","backend_version":"diagnostic version"}
```

Validate exact major/contract and all four required features. Extra feature strings are ignored; unknown control fields are rejected. The SDK provides framing even for an immediate-only provider, but the **kernel must implement every advertised generic feature**. Negotiation alone proves none of that behavior. Incompatible/missing negotiation is `unavailable/incompatible_protocol` before computation; no automatic v1 downgrade. T024/T025 bridge work remains retired. Retained leaf migration is T104, by separate public-only authors after kernel readiness.

Send `{"op":"hello","protocol":2,"contract":"cas-computation/2"}` and require matching contract with `op:"hello",status:"ok"`. Before acknowledgement only negotiation/shutdown is allowed. Kernel owners come from the actual connection, not names/PIDs returned by a provider.

```json
{"protocol":2,"request_id":73,"op":"<published operation>",
 "input":"<admitted input address>","args":{},"scope_id":"<kernel-issued scope>"}
```

Request IDs are nonnegative monotone integers on that connection, never reused. `op/input/args` retain the complete operation-specific grammar and selected context. References are restricted to the actual connection, transaction and dispatch. A leaf supplies no authoritative semantic program, result type or owner.

## 4. Scoped values and actual application

The public SDK proxy refers to an actual retained value, without a producer-private class/decoder or reply-supplied code.

- `inputRef(path)` addresses the original request by string fields/nonnegative indices at its full prepared role.
- `resultRef(index)` addresses a prior completed result of that deferred group, never a self/forward/out-of-range result.
- `scopeRef(slot)` addresses a kernel-issued exact value/role in the current invocation/resume scope; no raw foreign token or expired-scope access.

Ordinary deferred calls have exactly `op,input,args`. Graph controls have `op,args`: `$cas.project` takes `value,field`; `$cas.apply` takes `value,arguments`. They act on prepared roles, not new mathematical types, coercions or proofs.

Projection reads a declared stored computational field locally; lazy fields execute their retained continuation with genuine owner checks. Application executes actual compiled code/captures or the retained native callable, checking complete source-defined roles. Tags, bytes or reverse inference cannot establish mathematical domains/equalities. Keep the supplied apex/maps/factors/comparisons; no reconstructed canonical object, identity replacement or sample table substitutes for a required function.

### 4.1 Native export invocation and capture frames

A native application allocates a fresh occurrence, checks the actual supplying/captured/context/argument owners and sends to the original live connection:

```json
{"protocol":2,"request_id":81,"op":"$cas.invoke_export",
 "scope_id":"<fresh scope>","token":"<actual local token>","captures":[],
 "context":{"kind":"published","operation":"<published operation>",
 "input":"<admitted address>","args":{"ctor":"apply","args":[
 "<published operation>",["<complete parameter data>"],
 {"ctor":"typedMap","args":[{"ctor":"scopeRef","args":[0]},
 {"ctor":"scopeRef","args":[1]},
 {"ctor":"opaqueData","args":["<actual local token>"]}]},
 {"ctor":"scopeRef","args":[2]},
 {"ctor":"scopeRef","args":[0]},
 {"ctor":"scopeRef","args":[1]},
 {"ctor":"scopeRef","args":[3]}]}}}
```

This example has zero captures. For `c` retained captures, the mandatory top-level list is exactly `scopeRef(0),…,scopeRef(c−1)` and those slots contain the original ordered reference/role pairs. Context/arguments follow, so the illustrative 0–3 are not universal offsets. Preserve all seven PointInvocation fields: operation, complete ordered parameters, actual whole arrow, original generalized domain, actual source, actual target and actual argument. Substitute the owner's native token only at its actual callable position; foreign inputs remain scoped. Never search registrations again for a selected callable.

The alternate dependent context has exactly:

```json
{"kind":"dependent","prepared_role":"<kernel role ID>",
 "parameters":[],"bindings":[{"slot":0,"value":{"ctor":"scopeRef","args":[0]}}],
 "arguments":[],"argument_layouts":[],"result_layout":{}}
```

It also has the mandatory top-level capture prefix. Parameters/bindings/arguments preserve complete ordered context and unique prescribed slots; layouts come from the independent interface, with exact dependency and arity correspondence. Formal hypotheses are not reply fields. Native classes/tokens cannot choose a role or add mathematical meaning.

Use an invocation-local SDK frame mapping original captured proxy occurrences to the fresh prefix. No global proxy mutation or reinterpretation of an old numeric slot. Nested/repeated calls have separate frames. Return/error/suspension expires the frame; escaped asynchronous gateway access remains unauthorized. Suspension explicitly transfers required current-frame captures into its new record, not an ambient old scope.

The same actual callable can return immediate/deferred/suspended data under its prepared role. A missing token on its live owner is execution failure; a dead/replaced owner is rejected before send. Neither permits another producer. A committed export lease supports multiple fresh calls; only suspension tokens are one-resume.

### 4.2 Complete reply and export admission

```json
{"request_id":73,"status":"ok","value":{},
 "exports":[{"token":"local-token","captures":[]}]}
```

Each newly introduced token occurs once in the export table. Resolve every capture before its source scope expires into exact immutable reference/role pairs and original occurrence/index correspondence. Duplicate identical capture occurrences are malformed; distinct roles do not merge because their values coincide. Owners are the actual supplying generation plus every genuine transitive capture owner. Input references retain original owners; self-contained bytes do not acquire a supplier owner.

Compiled closures retain actual environments. Native exports declare every public proxy they later use; hidden native memory grants no undeclared scope. This does not assert introspection of arbitrary memory or provider honesty. The token always depends on its actual process generation.

Validate the **entire** promised joint result before staging any field: mandatory chosen data, dependent roles/endpoints, scopes, exports and owners. Omitted fields are malformed, not inferred choices. Structural conformance does not prove naturality/coherence, inverse laws, universality or correctness. Independently assessed wrong answers remain distinct from malformed packets. Separately declared deferred fields retain separate demands; complete joint admission does not force execution of all unused lazy operations.

## 5. Mathematical preparation and computational selection

Use mathematical-input §4 for actual cells, allowed choices, source agreement, declared preferred routes and mandatory-data errors. No historical universal discovery/coverage gateway is required. Validate whole computation templates before specialization and preserve exact prerequisite refs/slots. Each reached parametric invocation uses its actual arguments.

Reject genuinely stale required inputs/captures before filtering computational candidates; do not remove a dead owner to select another implementation. A new operation can consume public proxies on its selected realization; it is not forced onto an input producer. An existing native callable remains on its actual owner.

Preserve primitive/generic/fused registration identities. A separately registered adequate fused implementation can create realization ambiguity and must receive the complete original composite/context/comparisons. An internal justified optimization of an already selected realization is not another registration. No unexecuted primitive receipts are fabricated.

### 5.1 Closed finite exact demands

For fixed actual child demands whose accepted closure is finite, use OR demand nodes, grounded primitive alternatives and AND derivations with ordered prerequisite occurrences. No depth cutoff or dropped cycle establishes closure. Saturate `{0,1,2}` counts, with 2 meaning multiple distinct finite grounded realizations:

`c(q) = min(2, primitive_count(q) + sum_d product_i c(prerequisite(d,i)))`.

Starting at zero, monotone iteration terminates because each finite count rises at most twice. Induction on finite realization-tree height gives the least fixed-point interpretation. Ungrounded cycles contribute none; productive wrapped/unwrapped alternatives remain multiple. A cycle does not invalidate a direct grounded alternative; equal types do not merge identities/slots.

Zero yields `noImplementation`, one retains the selected actual plan/bindings before dispatch and two yields `ambiguousRealization`; zero/two dispatch nothing. This argument concerns that exact finite computational graph, not route equality. Native construction/correspondence and proof remain T026/T039 responsibilities. Missing justified closure or exhausted computation is procedural/internal, not absence inferred from incomplete search.

### 5.2 Delayed demands

Result-dependent calls retain code/environment until actual arguments exist. Do not enumerate all inputs or execute unused fields. A finite graph at one stage is not the adaptive future tree. A later missing/ambiguous/failing demand fails as specified without replay under another realization.

Several already eligible root recipes are ambiguous before trying their children. A statically absent prerequisite can rule out grounding; an unknown delayed requirement cannot be treated as absent. Retaining a recipe does not establish provider coverage or successful required later uses.

### 5.3 Immutable realization profiles

`--realization-profile PATH` and notebook startup `CAS_REALIZATION_PROFILE` select computation availability only; absent a file, all are enabled:

```json
{"format":"cas-realization-profile/1","id":"<run profile>","default":"all",
 "rules":[{"target":{"kind":"method","id":"<published family ID>"},
 "primitive_registrations":{"mode":"all"},
 "derivations":{"mode":"only","ids":["<published derivation ID>"]}}]}
```

Targets retain the actual published family kind and ID and are unique. The existing operation/functor/method/construction/morphism kinds retain their `ComputationRef` identities and normalized encoding. The runtime availability target additionally admits `lift`, `presentation`, `property`, `application`, `component`, `cartesian` and `binder` with their existing registry IDs; these introduce no mathematical family or derivation.

A lift target covers only its published `<lift id>#<field>` ports. An application target uses the original object ID and covers its exact `<object id>#application` port. A component target uses the original cell ID and covers its direct component and accepted ordered constructor paths. A cartesian target uses the original reindexing functor ID and covers its `<functor id>#cartesian` port. A binder keeps its original published ID. An `edge` target instead uses the canonical complete `action:<compact identity>` family address, with no port suffix; its object and map registrations retain that same exact recursive edge. Unknown suffixes, noncanonical action identities and `#map` used as a family target are rejected.

Primitive selection is `all` or `only` exact `operation,input,backend` triples belonging to that target through the same published-address grammar used by manifest admission. Derivations use `all` or `only` exact checked IDs of the target; all additional primitive-only targets accept `all` or an empty `only` set and reject nonempty derivation selections. Empty `only` selects none; unlisted targets remain all. Reject duplicate/unknown/wrong-target entries before execution. No regex, priority, cost or first-success selection.

Load/freeze normalized sets and hash at startup with actual baseline/overlay identities. No leaf selects the profile, per-cell setter or post-failure change. Explicit generic-only/fused-only experiments are separate sessions, not fallback. A C6 preferred-route declaration is a separate selected-reading input, not a profile ranking rule.

Prescribed later independent trials freeze the profile while retaining authorized additive/replacement overlays. Use `all` for unknown future contribution classes rather than preselecting their IDs. Post-choice exclusions/decoder/rule changes fail that trial and require the existing repair/refreeze. Such trials do not precede implementing kernel functionality under C21.

## 6. Deferred and adaptive execution in the concrete executor

`deferredData` carries ordered ordinary/control calls and a final template. Read/validate the complete response, release the provider permit **before** child dispatch, run children through the same production executor with fresh scopes/occurrences, bind exact backward results and admit the template against the parent's fixed layout. The consumer receives the computed result, not an unexecuted recipe.

```json
{"request_id":73,"status":"suspended","continuation":"local-token",
 "captures":[{"ctor":"scopeRef","args":[0]}],
 "calls":[{"op":"<published operation>","input":"<address>","args":{}}],
 "exports":[]}
```

Captures are mandatory even empty, ordered, and resolved before old-scope retirement. Reject repeated identical addresses, future results, old scopes, foreign tokens and new semantic claims; preserve distinct roles. SDK proxies needed after resume retain capture-index correspondence. Validate the complete captures/exports/nonempty finite child group before scheduling children.

The active SuspensionRecord retains actual owner/generation/token, request/parent chain, full callable/result role, original scope, exact captures/roles/correspondence and transitive owners, children/results and `suspended → resume_reserved → resuming → retired`. Retired tokens cannot be reissued in that generation. Tombstones contain no hidden completed data. The original ambient scope expires; only explicit captures transfer to the resumed provider.

```json
{"protocol":2,"request_id":74,"op":"$cas.resume",
 "continuation":"local-token","scope_id":"<fresh scope>",
 "captures":[{"ctor":"scopeRef","args":[0]}],
 "results":[{"ctor":"scopeRef","args":[1]}]}
```

For `c` captures and `n` children, capture `i` is slot `i` and child `j` is slot `c+j`, with exact original order, arity and dependent roles. Kernel constructs the mapping. Check the continuation, every actual capture/result owner, cancellation and one-use status before reservation and again before send. Known loss prevents resume. SDK invokes the same retained generator with explicit correspondence, not old addresses, type/name recovery or historical ambient scopes.

A fresh resume request consumes its right even if the reply is lost. Further suspension makes a new token/capture table in the current scope. Empty groups, duplicate/late resume and scope mismatch are malformed. Child failure/loss retires the chain without substitute results/providers. Cancellation retires appropriate descendants and request-local leases after exact drain while preserving prior leases. New suspensions belong to their fresh request for cleanup; lost cleanup replies are recorded without resend.

No whole-cell success while required active work is suspended; an uninvoked legitimate lazy callable is different. Release/suspend/resume avoids retaining the only permit across child calls. Detect real pending-demand cycles; retries are not a solution. SDK-only generator support does not satisfy the required kernel implementation.

## 7. Reservation, liveness and publication

Use short atomic sections for reservation/liveness/commit arbitration and no blocking I/O under the coordinator mutex. Per-connection permits serialize exact frames; queued work retains its reserved generation.

| Transition | Required behavior |
|---|---|
| Prepare | Complete source selection/roles and all presently required data; semantic error dispatches none. |
| Reuse | Visible committed association, else same-transaction staged association, else the same active pending occurrence; check demanded owners. A tombstone alone has no result. |
| Reserve | Atomically check required owners and fresh occurrence; consume one dispatch right. |
| Send | Recheck cancellation/generation on the actual connection; no restart/replacement after owner-dependent selection. |
| Await/defer | Match request/occurrence/owner/transaction; completely read/validate control; release permit before children. |
| Stage | Validate the full promised reply/roles/exports/references and recheck owners, then retain all joint fields in the active transaction. |
| Commit | One final owner/cancel gate installs the complete value/completion/observation/output delta; clear settled promise payloads. |
| Abort/unknown | Publish none of the cell's new results; keep consumed rights, dispose applicable new leases and retain failure/cancel/indeterminate status. No resend or alternative provider. |

The kernel cannot predict death after a check. It must not knowingly dispatch using an invalid owner, rebind stale tokens or restart implicitly. Lost/EOF replies after send are failure/indeterminate execution, not safe-retry evidence. Snapshot rollback restores neither rights nor owner generations. A fresh worker nonce cannot revive old values by replay.

A waiter may detach without cancelling others. Cooperative cell cancellation stops new child/resume/publication, not prior valid owners. A resource-only drainer retains the permit until the exact frame arrives, discards late output and schedules no children. New calls cannot overtake it; deadline is `unavailable/busy_draining`. Unacknowledged drain persists until explicit force or actual loss, not hidden escalation.

```json
{"protocol":2,"request_id":75,"op":"$cas.discard","discard_request_id":73}
```

The reply is `{request_id:75,status:"ok",disposed:true}`. Revoke only the originating request's new leases/continuations, preserving earlier committed leases. Revocation is not a claim of native memory reclamation without an engine API. A lost cleanup reply is not resent. Explicit close/force or actual framing/transport failure invalidates the exact generation and its dependent uses; unrelated portable fields/owners survive. A malformed stream is not a drained reusable connection. No durable exactly-once external-effect promise is made.

Notebook transport-ID handling and source-free status follow its contract. Only visible committed receipts report committed success; staging is pending and tombstones supply no hidden payload. Inert inspection uses prepared immutable data and non-extensible formatting on every success/error path; it executes no delaborator, documentation/proof callback, lazy operation or provider request.

## 8. Outcomes and authority of checks

Preserve `invalid`, `semanticAmbiguity`, `noImplementation`, `ambiguousRealization`, `unavailable`, `malformed`; untagged implementation defects are `internal`. Cancellation is transactional, not a truth value. The mathematical-input contract distinguishes actual missing required selection, invalid supplied evidence, interrupted checking, absent realization and malformed missing candidate data. A preferred route is validated explicit input, never invented as fallback. No universal runtime wrong-answer detector is promised.

A leaf `status:"error"` with string kind/message maps to identifiable failed execution/unavailable. `unsupported` names exactly the dispatched operation and maps to that consumed noImplementation outcome without fallback. Unknown/mismatched request/status/control/role/scope/capture fields are malformed. A reply cannot declare semantic invalidity/ambiguity to change the question.

| Boundary | Establishes | Does not establish |
|---|---|---|
| Parser/SDK | Exact framing/fields/addresses/arity/scope | Subject types, laws or correctness |
| Source preparation | Accepted judgment, explicit selection/C6 data, required roles and source-prescribed errors | Availability or truth of returned candidates |
| Reply admission | Complete mandatory layout, dependent associations, captures and actual owners | Mathematical naturality/coherence/universality or arbitrary answer correctness |
| Supervisor | Reservations/generations/joins/no resend/atomic publication | Mathematical meaning |
| Independent assessment | Original complete answer/continuation/budget/trial observations | Candidate-defined expectations |

## 9. Functional work and final evidence

The corrected plan assigns concrete execution to T013/T019–T023/T026, source lowering to T032/T033 and the real public connection to T038. Implement these and all required generic capabilities without a proof/export/frozen-trial gate. Necessary validation and actual scoped/owner checks remain in the code path. Complete kernel readiness precedes substantial public-only T104 migration/glue. No handshake, model or helper-only test counts as readiness.

Retain full RX-LIFT maps/comparisons/factors and 22-binding scope, all RX01–RX10 outcomes, 153/134 readings/positives, negatives/environment controls, 17 connected assertions, original 99-root 3×3 question, unchanged-consumer trials and complete real SDK/worker lifecycle observations. C21 permits larger resources during functionality; the original under-60-second and shared 200,000-heartbeat conditions are still mandatory in the last performance/acceptance phase. Do not replace questions, alter expected relations or use higher-limit functional results as proof of final budgets.

Sources retained: [current constitution][C], [independent agreement rule](https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/operation-agreement.md), [checked computation families](https://github.com/dzackgarza/lean-categories/blob/fc6d3d6961223c75290c93da540c87f17a926cc7/LeanCategories/Catalogue/Registry/Computation.lean); historical contract mechanics [manifest](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/f0431bebeb01c93cc65bb3fdc5bd23d9613e4b31/api/manifest.md), [Port](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/f0431bebeb01c93cc65bb3fdc5bd23d9613e4b31/CasContract/Port.lean), [service](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/f0431bebeb01c93cc65bb3fdc5bd23d9613e4b31/api/kernel-service.md) and [failure strata](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/f0431bebeb01c93cc65bb3fdc5bd23d9613e4b31/CasContract/Failure.lean); [CSLib](https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean), [PolyFun](https://github.com/Verified-zkEVM/PolyFun/blob/a5895e454254a400774fa396b64d5b968f0933df/PolyFun/PFunctor/Handler/Stateful.lean), [Lean mutex](https://github.com/leanprover/lean4/blob/v4.33.0/src/Std/Sync/Mutex.lean). These are design/source references, not fresh builds or permission to revive retired bridge work.

[C]: https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md
[M]: mathematical-input.md
[D]: ../data-model.md
[N]: notebook-session.md
[P]: ../plan.md
[T1]: ../tasks.md
[T2]: ../tasks.md

## Required realization boundary

A category implementation consumes the generated public category view of accepted mathematical
declarations: admitted object/morphism constructors, operations at their actual domains,
immediate functor actions and complete dependent inputs/results. T028 extends the existing
exporter and reconciles public contract/leaf guidance; the kernel continues to read the
independent registry. An operation/input/backend port is an invocation registration, not the
complete category interface. No new wire schema or mathematical authority is introduced.

Different admitted constructor families must reach the same unchanged applicable consumer.
Required positive combinations execute their complete original continuations. C22 leaves
algorithm control, established-engine glue and permitted private code reuse with computational
implementations; public interoperability does not depend on private representation knowledge.
T104 supplies focused builds and public execution with the actual software dependencies, without
unrelated optional engines. Generated category filtering alone cannot establish that locality.

Provider substitution preserves the full fixed question and independently specified result
relation. Actual allowed choices and defining maps remain attached to their subsequent uses;
an independently prescribed exact selection or normalization stays binding. Structural admission
or agreement between providers does not establish the whole mathematical obligation.


The prepared mathematical request fixes the obligation before provider selection. Functor actions
construct actual target objects and arrows through public interfaces, with selected endpoints.
The runtime retains result occurrences, ownership and the dependent associations supplied by
preparation. It supplies earlier results by those associations, not by equality searches or
construction-specific field algorithms. A subsequent target method consumes the target interface
without reading a source leaf's private state.

Deferred and provider-requested computations resolve scoped operands, use the common mathematical
preparation boundary and execute its result. A result cannot redefine the request's denotation.
C22 governs missing implementations and prohibits unpublished computation by kernel reduction.
MM002 and MM007–MM012 specify the corresponding public behavior; wire conformance alone does not
establish their mathematical assertions.
