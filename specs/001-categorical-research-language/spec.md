# Feature Specification: Categorical Mathematical Research Language

**Feature Branch**: None; this installation has no branch-creation hook. Publication follows the repository's existing documentation policy.

**Feature Directory**: `specs/001-categorical-research-language`

**Created**: 2026-11-05 (Asia/Taipei)

**Status**: Requirements specification; implementation acceptance is not asserted.

**Input**: Apply the specification workflow to the active language requirements and permanent constitution. Incorporate the owner's November 7 clarification at the requirement source, rather than asking the owner to choose a new route-dispatch policy.

**Authority and source baseline**: the [current constitution][C] (v4.0.0 of 2026-11-25); the original [mathematical language specification][P]; governing issue texts retrieved on 2026-11-05; and the owner's clarifications recorded below. Constitutional identifiers refer to the current constitution. The first formulation of this specification used constitution v1.2.1 at `69613d4f4aec17d5c5f6dd2f28a30c912bc1e9a1`. The [independent whole-operation agreement contract][OA] was rechecked at `lean-categories@6c7f6a8f026500da30c00736580c5bd30c87331b`; its blob is unchanged from the planning input. This specification does not amend the constitution, replace protected acceptance questions, or choose an architecture. All existing code, representations, execution arrangements and plans remain replaceable subject to these requirements.

## Clarifications

### Session 2026-11-07

These answers were already supplied by the owner; no new question, route-preference election or permission request was needed.

- Q: What resolves competing functorial routes? → A: The independently specified categorical data and selection rules, including the actual required comparison cells, their boundaries, direction and coherence, or an explicitly permitted selected route. The kernel consumes those data; it does not invent a dispatch preference. A comparison is not a Boolean assertion that two paths are interchangeable.
- Q: What happens when required cell or choice data are missing, and must an allowed choice be unique? → A: The kernel reports the prescribed missing-data or ambiguity error before the dependent use. Where the accepted contract permits a choice, any permitted choice may be supplied, including computational candidate data from a leaf when that is the declared responsibility; the actual choice must be retained. Neither a canonical choice nor equality of every possible choice is required merely because several choices exist. An ordinary ambiguous request is not silently converted into a new choose-a-route operation.
- Q: Can the leaf author define or formalize the contract it implements? → A: No. The categorical definitions, laws, admissible choice family, comparisons and abstract computational obligations are independently formalized in lean-categories. Leaves supply only the computational data/operations prescribed by that prior contract, never mathematical definitions, proofs or their own correctness criterion. Moving a downstream-authored definition to an upstream repository does not establish independence.

### Session 2026-11-15

- Q: Who computes an operation, method or predicate, for example whether a polynomial is irreducible? → A: A leaf. Every such notion is formalized in lean-categories, and its computation is a leaf's job. The kernel resolves each requested computation to a leaf that implements it, or reports no implementation. It computes nothing itself. [C22][C22]
- Q: Where does control logic such as `f(p) := if is_irreducible(p) then A(p) else B(p)` live? → A: In the leaf that implements `f`. Its implementation may use any formalized operation, whether or not some leaf implements it: it computes it internally, uses another leaf's code directly without the kernel, or asks the kernel to resolve it. The kernel routes that request or returns no implementation. A missing implementation surfaces only when a computation demands it. [C22][C22]
- Q: May the kernel settle a closed question such as `2 + 2 = 4` without a leaf? → A: Yes, when a proof procedure registered in lean-categories settles the proposition: that evaluates a proposition, not a computation, and is usually much quicker. The kernel must not evaluate, in Lean, an operation that no leaf publishes, for example gcd on concrete numbers. [C22][C22]

### Session 2026-11-22

The owner requested constitutional treatment of the durable principles in both comparative
reports. Constitution v3.1.0 elaborates C0/C9/C21/C23/C24: source-derived category interfaces,
actual dependency locality, continuing feedback, truthful current-run evidence and complete
choice-sensitive assessment. It preserves every mathematical and independent-author boundary.

The roadmap update applies the existing C21/C23/C24 requirements to current delivery. No new
owner choice is required: the requested priority is fast development feedback, with the full
mathematical and independent-acceptance obligations retained.

- The maintained task list owns execution order. GitHub milestones state complete outcomes:
  current feedback, full functional kernel F, actual V1 category implementations and compatible
  delivery, independent V1 acceptance, full B0/Sage coverage, and retained research/client work.
- Category interfaces, their public computational realizations and physical build dependencies
  are distinct. Object constructors are not category-level `ConstructorEntry` rows; individual
  ports are not complete category implementations.
- Constructor-independent use covers the complete declared interface and every assigned positive
  constructor–operation use. Missing computation cannot pass a required positive workload.
- The current changed-source/public-consumer loop has immediate priority and remains in use.
  T016 retains its dated result; the current loop is established separately. The image port
  remains T105 unless the actual environment blocks an active task. General proofs, independent
  trials and final mathematical performance retain their existing later position.

### Session 2026-11-25

The owner supplied these answers; no new question was needed. Constitution v4.0.0 records them ([decision record](https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-7155201731)).

- Q: What happens when a kernel task needs a mathematical declaration that lean-categories does not have? → A: The task list holds a lean-categories task before the consumer, and the workstream does that task in lean-categories. There it is formalization work: from the mathematical requirement and its sources, at its own generality, not shaped to the kernel. A task does not stay open with no one assigned because its input belongs to another repository. The answer of 2026-11-07 about leaf authors is unchanged: a leaf author does not formalize the contract that its code implements. (Constitution v4.0.0, C21 and the authorship rule.)
- Q: Does kernel work need computed mathematical results for its acceptance? → A: No. A check of kernel work observes kernel behaviour: the selected reading, the prepared request, the dispatch, the admission, the retained value and its later use, with a protocol peer or an empty manifest. A mathematically correct computed value is leaf work. It needs an implementation of every category on the selected structural route. Example: `2 * 3 = 6 in ℤ` needs the implementations from sets up to rings, because the multiplication comes from a monoid structure of the ring. Each user story keeps its acceptance, which is assessed when those implementations exist. (Constitution v4.0.0, C22.)
- Q: How is computational work organized? → A: In version milestones of its own, separate from the kernel milestone. Their order is the order of the structural scaffolding of the categories: sets first, then independent directions. Each milestone is vertical: enough of each category on a route for one stated computed result. An early attainment is `2 * 3 = 6 in ℤ`. (Constitution v4.0.0, C23.)
- Q: How is a category implementation written? → A: It connects mature existing computation and reinvents nothing. An open-ended survey of engines and libraries comes first. Computation that the system performs outside a category implementation moves into one. (Constitution v4.0.0, C23 and the established-implementations policy.)
- Q: Can computational work start before kernel readiness? → A: No. The released contract is published at the end of the kernel work, so an earlier implementation would be written against an unfinished contract. Before kernel readiness, a protocol peer is the only counterpart of the kernel. (Constitution, production-leaf sequencing policy.)
- Q: When are the timing records, the test-run logs and the application logs of constitution C24 due? → A: Now. Each test and each computation has a timing record, each test run has a durable log in the repository, and the kernel session writes detailed application logs. This work comes before further kernel tasks. It is not evidence that follows functionality. (FR-043, SC-016.)
- Q: Who fixes the computed result of a computational milestone? → A: It is not an owner decision. The result is what later work needs from the categories of the milestone in order to rely on them. It comes from the original workloads: the statements whose selected route stays within those categories. One of them or all of them serve. (FR-042.)

## User Scenarios & Testing *(mandatory)*

### Product and delivery scope

The product is a mathematical research language in which a researcher introduces objects and hypotheses, constructs and composes maps, asks mathematical questions, computes answers, and uses the actual answers in subsequent mathematics. Its capability grows from independently formalized categorical mathematics: new constructions acquire existing applicable operations, and new generic operations apply to existing objects. Structured answers include their defining data and usable maps. Infinite objects, dependent families and higher comparisons retain the meaning and interface required by the selected mathematics. A collection of isolated calculations or a catalogue of types is insufficient. [C0–C8, C11–C12, C15][C]

The full mathematical scope includes exact arithmetic and explicit approximation; finite and infinite sets and comprehensions; functions and morphisms; polynomial and linear algebra; relative differentials; complete families of primitives; limits, integrals and series; and the structured, dependent and higher constructions required by accepted mathematics. Accepted hypotheses and specified scope govern applicability. This neither promises a decision procedure for arbitrary mathematics nor permits narrowing a promised construction to examples already implemented. [Original language][P] [C3, C6–C8, C15][C]

One product has the following existing delivery assignments. They are not alternative definitions of success:

| Assignment | Required result |
|---|---|
| **Current complete V1** | The unchanged [#24 A–F][A] obligations, with [#66][Q] and [#69][U]: all 153 permanent readings; all 134 positive extension questions across 14 files, comprising 105 original and 29 completion questions, with prescribed outcomes; protected negatives and environment controls; RX01–RX10 and RX-LIFT; complete composition and continuation; actual connected CAS/notebook workflows; prescribed independent extensions; and integrated delivery. Complete readings of all 153 questions do not make every otherwise later full-B0 algorithm a new V1 execution requirement. |
| **Required work informing V1** | The bounded consumer-construction review in [#23][H], source-coordinate/inventory work in [#20][I], and classification in [#21][K] retain their existing assignments. Backend coverage cannot substitute for mathematical specification. |
| **Required subsequent delivery** | [#19][B] retains full-B0 computational delivery, K1–K14 scope and all 26 K13 question IDs, K3/K14 obligations, and broad Sage parity. [#68][N] retains the later public Python/research-consumer interface; [#13][D] the subsequent genuine research-demand harvest; [#3][G] and [#34][V] their later production/portability scope. They remain required in their assigned scope without becoming additional V1 gates here. |

A subject may occur in both V1 and the later inventory. The **fixed question and prescribed outcome**, not its subject label, determine the current obligation. Stories below specify complete product behavior. Their V1 witnesses and execution requirements are those already assigned by #24; stronger subsequent computations remain assigned by #19. No illustrative scenario here adds an oracle, replaces an immutable question, or preselects a contributor's outstanding independent extension. [V1 boundary][A] [Full B0][B]

Priorities express user importance. Each story has an independently assessable outcome, but passing a subset does not satisfy the complete assigned delivery. All required stories, continuations, controls and existing acceptance conditions must hold together. The acceptance of a story needs the kernel and the category implementations that its questions use. The kernel checkpoints of the [plan](plan.md#m1-checkpoints) are earlier observations of kernel behaviour for the forms of a story; a checkpoint does not satisfy its story (FR-013, SC-014).

### User Story 1 — Develop a connected mathematical calculation (Priority: P1)

A researcher works in one coherent context: defining objects, stating hypotheses, composing maps, asking propositions, computing exact or explicitly approximate answers, and continuing with those answers. They use the mathematical language without translating each step into a backend's private vocabulary. [C0, C6, C15][C] [Original language][P]

**Why this priority**: Connected mathematical work is the product's purpose. Language recognition, dispatch or one correct scalar answer does not supply it.

**Independent Test**: Assess the original arithmetic, sets, function-composition, polynomial, differential and linear-algebra questions at their assigned delivery stage, retaining complete context and subsequent uses. For V1, use the permanent readings and prescribed connected workflows rather than a substitute notebook.

**Acceptance Scenarios**:

1. **Given** the original exact arithmetic questions and selected number systems, **when** a researcher defines values and evaluates prescribed assertions, **then** selected domains, inclusions and numeral meanings stay fixed and independently expected answers are obtained. A modular interpretation cannot replace a selected integer interpretation. [Original language][P] [C6][C]
2. **Given** the original typed functions and bound composites, **when** they are evaluated or composed later, **then** actual selected functions, domains, codomains and local hypotheses govern that expression. An unresolved earlier binding cannot be bypassed by executing a shortened replacement question. [Original language][P] [Dependent questions][Q]
3. **Given** the original polynomial/root/companion-matrix workflow, **when** the researcher changes coefficients, forms the prescribed root collection and matrix, and performs later observations, **then** selected polynomial, coefficient maps, root-set convention and matrix construction are retained and original expected relations hold. Root-set cardinality is not silently changed to a multiplicity count. [Original language][P] [Full B0][B]
4. **Given** a required positive calculation, **when** its implementation is absent, fails or returns a wrong answer, **then** its full mathematical question and required answer remain unchanged and it remains incomplete until corrected. Reporting a gap does not satisfy that positive requirement. [C3, C9–C11][C] [V1 acceptance][A]

### User Story 2 — Construct an object and use its complete interface (Priority: P1)

A researcher receives a usable construction, including defining maps, selected structures, parameter dependencies and operations promised by its meaning. They can impose further conditions, obtain required factorizations and apply the actual returned maps. [C5, C7–C8][C]

**Why this priority**: Mathematics proceeds through constructions and maps. A label, cardinality or unrelated isomorphic object cannot replace them.

**Independent Test**: Use the existing primitive-family continuation and universal-construction questions at their assigned stage. For V1, execute original RX08 and distinct RX-LIFT with full preceding bindings, original nonzero factor samples, maps and later applications. [Original language][P] [V1 acceptance][A]

**Acceptance Scenarios**:

1. **Given** the original indefinite-integration request, **when** the researcher obtains the family of primitives, imposes the initial-value condition, selects its unique member where established, and differentiates it, **then** each step uses the complete specified family and actual selected member. An arbitrary primitive at the first step is insufficient. [Original language][P] [Full B0][B]
2. **Given** a required universal construction in its declared ambient category and hypotheses, **when** its result is used in a prescribed factorization or map application, **then** its object, defining diagram, maps and required universal data satisfy independently specified relationships. An apex alone does not complete it. [C7–C8][C] [Constructed results][U]
3. **Given** original RX-LIFT, **when** successive prescribed lifts and nonzero factors are computed and applied, **then** the actual selected returned data and nonidentity comparisons act in every required continuation within the original budgets. A product example or shortened binding context cannot replace the trial. [V1 acceptance][A]
4. **Given** RX08's selected underlying-module kernel with restricted form, or RX-LIFT's formed-module data, **when** inclusion and factors are used, **then** specified module-level relations and formed maps are preserved. No categorical kernel among form-preserving maps is asserted without corresponding independently established hypotheses and universal property. Original RX08 ambiguity and its separately assessed positive clarification both remain. [V1 acceptance][A]

### User Story 3 — Compose selected structures, parameters and higher comparisons (Priority: P1)

A researcher can depend on the actual chosen structure, basis, lift, presentation or comparison throughout a calculation. Parameter changes, inherited operations and higher compositions preserve the complete context required for later use. [C4–C8][C]

**Why this priority**: Equal carriers or matching endpoints do not determine the same structured mathematics. An actual selected comparison and a proof permitting an identification are not interchangeable.

**Independent Test**: Run existing selected-structure, classifier/refinement, competing-route, reindexing, realization-transport and higher-coherence cases, including RX05–RX07 and fixed #24 composition controls. Include their prescribed missing/reversed/parallel comparison outcomes and subsequent actual-map uses. These scenarios sharpen those obligations; they do not replace the protected corpus or prescribe new independent contributor specimens. [V1 acceptance][A] [Dependent questions][Q] [Constructed results][U]

**Acceptance Scenarios**:

1. **Given** distinct accepted structures or structural routes on one carrier, **when** an inherited operation is requested, **then** it uses the selected structure and actual route/comparison, without merging routes by endpoint or choosing meaning by registration order or backend success. RX05 retains its complete original ring-carrier diagram and route inventory. [V1 acceptance][A]
2. **Given** a dependent family and admissible parameter map, **when** declared reindexing or transport is followed by another operation, **then** the new base, variance, selected comparison and full dependent result govern that use. Restriction of scalars, extension of scalars and a parameter projection are not substituted for one another. [C5–C7][C] [V1 acceptance][A]
3. **Given** the prescribed nonidentity presentation comparison, **when** data and maps move through it in each permitted direction and are subsequently used, **then** its actual action produces the independent expected observations. Naming a comparison or agreeing on an initial scalar is insufficient; a noninvertible comparison has no invented inverse. [V1 acceptance][A]
4. **Given** a promised higher diagram extension with selected boundary cells and matching conditions, **when** it is composed, substituted, reindexed or later applied, **then** all required coherence acts as specified. Unrelated pointwise fillers or truncation adequate only for an earlier scalar do not establish the continuation. [C7–C8][C] [V1 acceptance][A] [Higher coherence][X]
5. **Given** competing inherited bindings and no accepted agreement or required selection/comparison data resolving them, **when** the kernel prepares the dependent operation, **then** it reports the source-prescribed ambiguity or missing-data error without dispatching that operation. It does not choose a preferred route, demand a new policy decision from the owner, or wait for a proof that no comparison could exist in any mathematical extension. An interrupted required check remains a procedural failure, not evidence that data are absent. [C3, C6–C7][C] [Agreement contract][OA]
6. **Given** an independently specified choice-bearing construction that permits a route or comparison choice, **when** its designated supplier supplies any permitted candidate choice, **then** that actual choice determines the dependent continuation. No uniqueness, canonicality or equality of all possible choices is added. If the released computation contract assigns that datum to a leaf, omission fails that computational responsibility before dependent use; supplying it does not confer mathematical authority or prove its laws. [C2–C3, C5, C8][C]
7. **Given** different permitted comparison cells between the same routes, **when** one is selected or returned under that choice contract, **then** its components, direction and required coherent data remain available and are used. Endpoint equality, mere existence of a cell, graph connectivity or a global path-equivalence label cannot replace them. A fixed selected cell cannot be replaced by another permitted one. [C5, C7–C8][C]

### User Story 4 — Work with exact, infinite and explicitly approximated mathematics (Priority: P1)

A researcher describes admitted infinite objects and families without replacing them by a finite display, and requests approximation or truncation without losing the exact source or the meaning of its error. [C6–C8, C15][C] [Original language][P]

**Why this priority**: Finite examples, samples and representations must not silently narrow the object being studied.

**Independent Test**: Assess original infinite-set, ellipsis, series, approximation and truncation questions under their accepted conventions. Execute V1's exact RX09 admission/rejection, enumeration cases and other assigned continuations; retain remaining full-B0 execution requirements. [V1 acceptance][A] [Full B0][B]

**Acceptance Scenarios**:

1. **Given** an admitted infinite set or indexed construction, **when** a finite display is followed by a valid operation outside that display, **then** the complete domain, index object and rule remain in force. Finite rank, support of an element, presentation and diagram shape are not interchangeable hypotheses. [C8][C] [Original language][P]
2. **Given** an exact object and its original approximation request, **when** the answer is used or inspected, **then** its specified error relation and tolerance remain, the exact source is available, and the qualification accompanies the affected result. A failed tolerance cannot become a relaxed or exact answer. [Original language][P] [C6, C15][C]
3. **Given** the prescribed series operation, **when** RX09's admissible family and exact constant-one nonsummable control are submitted, **then** the positive result and rejection at the intended typed obligation match unchanged independent expectations. Another negative family is not a replacement. [V1 acceptance][A]
4. **Given** advertised integer/rational enumeration and its owner-adopted `Denumerable.ofNat` ordering, **when** existing enumeration questions execute, **then** that selected order is preserved. A different valid enumeration is not silently substituted. [V1 acceptance][A] [Dependent questions][Q]

### User Story 5 — Extend mathematics in both directions (Priority: P1)

Independent contributors add a construction or a generic operation. New objects receive existing applicable operations through genuine mathematical relationships; new generic operations reach old applicable objects without edits to their implementations. [C0, C4, C12][C]

**Why this priority**: Growing mathematics must not require implementing every inherited consequence repeatedly for each object.

**Independent Test**: Perform existing independently chosen new-object, new-operation, group-valued, classifier/refinement and competing-route trials against the prescribed frozen baseline. Keep the generic compositional argument distinct from finite trial results. [V1 acceptance][A] [Trial clarification][T]

**Acceptance Scenarios**:

1. **Given** frozen accepted interfaces and old operations, **when** an independent contributor introduces an authorized construction through its new mathematical data and immediate relationships, **then** all entailed interfaces become available and required instances execute without per-operation forwarding or accommodation edits to old leaves. [C4, C12][C] [V1 acceptance][A]
2. **Given** existing orthogonal-group, subgroup and stabilizer constructions, **when** a generic group/subgroup operation is independently admitted, **then** it applies to the relevant old constructions without editing their definitions or leaves, using actual supplied group data and selected maps. [C0, C4][C] [Owner intent][O] [V1 acceptance][A]
3. **Given** declared immediate structures, **when** their composite follows from the accepted calculus, **then** its interface is derived; a redundant primitive declaration of the same intended composite with no new mathematical content is rejected with the existing composite identified. Distinct routes stay distinct unless accepted comparisons resolve them. [C4][C]
4. **Given** a fully selected old question and newly admitted mathematics, **when** the language grows, **then** its selected meaning is preserved. Underspecified expressions may gain genuine readings, which cannot be discarded to preserve a convenient computation. [C3–C4][C]

### User Story 6 — Use independent computation without surrendering mathematical authority (Priority: P1)

Researchers and contributors rely on released computational obligations already fixed by independent mathematics. Leaves claim to implement accepted operations and return computational data. They cannot define the mathematics, supply mathematical proofs or certify their own answers. [C1–C2, C9–C12][C]

**Why this priority**: Agreement between a provider's implementation and its own invented correctness criterion does not establish the intended mathematics.

**Independent Test**: Audit the public contribution boundary and prescribed permitted inputs; execute existing independent-producer/unchanged-consumer and leaf-replacement trials, assessed against independent expectations including RX10's wrong-answer control. [V1 acceptance][A] [Trial clarification][T]

**Acceptance Scenarios**:

1. **Given** an independently formalized operation and its abstract computational obligations, **when** a leaf registers or returns a result, **then** these are claims against the fixed contract. Its contribution boundary grants no mathematical category creation, semantic membership/inheritance, domain changes, mathematical identities or acceptance authority. [C1–C2][C]
2. **Given** a leaf contribution, **when** its deliverables are assessed, **then** mathematical definitions and proofs, including optional proof/certificate replies, are neither leaf responsibilities nor accepted leaf deliverables. Formalization and proof stay upstream; generic kernel discharge concerns already formalized obligations, without leaf-specific mathematical invention. [C2][C]
3. **Given** an independently chosen producer extension and unchanged existing consumer, **when** the consumer uses the new output and defining maps, **then** required continuations work through the released categorical interface without private representation knowledge or accommodation edits to the frozen baseline. [C12][C] [V1 acceptance][A] [Trial clarification][T]
4. **Given** the same immutable RX10 question, **when** providers succeed, return wrong results, are missing/unavailable, return malformed data or cause prescribed internal failure, **then** its meaning and expected assertion stay fixed and outcomes are independently assessed. This does not assert a runtime procedure detecting every possible opaque wrong answer. [V1 acceptance][A] [C3, C10][C]
5. **Given** a needed route/cell/choice interface, **when** implementation responsibilities are assigned, **then** its categorical definition and laws already belong to the independently authorized mathematical role. The leaf role receives only the released computational obligation. A combined assignment to formalize a convenient comparison and implement it is prohibited even if its files are put in different repositories. A leaf-supplied selected datum remains allowed where the prior contract requests it. [C1–C2 and independent authorship][C]

### User Story 7 — Continue a real notebook calculation with valid live results (Priority: P1)

A researcher executes connected mathematics in the required actual notebook/CAS surface, retains usable intermediate objects and callable results, inspects without execution side effects, and receives prescribed behavior on cancellation or owner loss. [V1 acceptance][A] [C8, C13][C]

**Why this priority**: A result unusable later in the real research session does not complete a construction.

**Independent Test**: Execute the existing minimum four connected real-engine workflows across three mathematical areas and all original 17 connected assertions, including notebook inspection, cancellation and owner-generation controls. [V1 acceptance][A]

**Acceptance Scenarios**:

1. **Given** a required notebook workflow, **when** it runs and its structured outputs are used in later cells, **then** actual intermediate objects, maps, comparisons and dependent results are used and original assertions hold. Stored outputs or an external demonstration do not establish actual notebook behavior. [V1 acceptance][A]
2. **Given** a cell containing computation and resource-opening/using/closing actions, **when** inspection is requested, **then** committed-state inspection changes neither execution counts, occurrences, dispatch, results nor resource liveness. Without a live worker or with a stale/missing predecessor, inspection does not bootstrap, restore, replay or execute the prefix. An endpoint lacking a guarantee of nonexecuting committed-environment inspection is rejected before any executable cell text is transmitted; checking its response afterward cannot satisfy this boundary. [V1 acceptance][A]
3. **Given** cooperative cancellation, **when** it completes, **then** no new result references are published and valid prior owners survive as prescribed. **Given** forced owner replacement, **when** old references are used, **then** the old generation is invalid and cannot be revived or silently reconstructed. Closed-owner and invalid-generation references are rejected before external dispatch, including after snapshot restoration. [V1 acceptance][A] [Lifecycle][L]
4. **Given** failed or consumed execution, **when** no new execution action is taken, **then** it is not automatically retried, replayed or migrated. Explicit rerun is a fresh invocation; reading a committed binding or joining the same pending execution is not another dispatch. [Existing retry policy][C] [Lifecycle][L]
5. **Given** an earlier notebook snapshot or concurrent demand for one occurrence, **when** execution state is restored or requested concurrently, **then** an already consumed live-generation occurrence is not dispatched again. A failed/cancelled cell publishes none of its newly staged references; earlier successful results stay usable while their owners live. A possibly executed request without a usable reply is reported as unavailable/disconnected with an indeterminate-execution diagnostic, without retry or a claim of success or mathematical invalidity. [Lifecycle][L]

### User Story 8 — Discover and inspect the mathematics being used (Priority: P2)

A researcher discovers applicable operations, inspects hypotheses and selected mathematical data, and sees answers automatically in usable mathematical notation. Actual computational provenance can be inspected when needed. [C0, C15][C]

**Why this priority**: Research use must not depend on hidden conventions, backend vocabulary or knowledge of the implementation.

**Independent Test**: Inspect applicable operations and selected data in existing workflow questions before and after provider changes; assess mathematical display and provenance on those same results. [V1 acceptance][A] [Rendering][R]

**Acceptance Scenarios**:

1. **Given** an object and accepted context, **when** operations are discovered before and after provider removal/failure, **then** applicability and hypotheses are unchanged and computational availability is separately visible. [C3–C4, C15][C]
2. **Given** a result qualified by a basis, root convention, approximation or other relevant choice, **when** it is displayed, **then** the qualification accompanies it and selected data can be inspected. Mathematical display is automatic, uses LaTeX when available with usable text fallback, and emits once per event. [C15 and display policy][C] [Rendering][R]
3. **Given** a performed computation, **when** provenance is inspected, **then** the actual routine is identified with verified primary documentation or a relevant source fallback. Backend, routing and timing diagnostics are opt-in. [C15][C]

### User Story 9 — Change an implementation and obtain useful feedback (Priority: P0)

A contributor changes the implementation that owns a mathematical capability and gets a fresh
result from its original public question and continuation. The iteration uses the affected
dependencies and exposes the actual discrepancy without an unrelated full build or setup cycle.

**Why this priority:** C21 gives fast development feedback immediate priority. C24 and the
existing contribution rules require a short ordinary loop. This enables the mathematical work;
it does not replace any required computation.

**Independent Test:** make a substantive edit at the owner of a capability and run the ordinary
focused loop on its unchanged public consumer. Then read the timing records and the logs that
the run left in the repository (SC-013, SC-016).

**Acceptance scenarios:**

1. A substantive source edit rebuilds its affected executable dependencies and executes the
   unchanged public consumer through the normal short-loop command. Diagnostics stream and the
   current result, exit status and elapsed time are visible.
2. A relevant failure reaches that same public path. A missing, stale, skipped, timed-out or
   partial selected run cannot inherit a previous success. An expected negative is distinguished
   from a failure to run its assertion.
3. The ordinary iteration neither refreshes dependencies nor provisions packages. A category
   implementation uses its actual declared dependencies; a shared interface change may rebuild
   its real clients. File splitting alone does not establish useful physical modularity.
4. A required positive mathematical outcome remains due even when feedback correctly exposes
   its failure. Full aggregate evidence and final mathematical budgets remain later obligations.
5. Each run leaves a durable log and a timing record for each test and each computation in the
   repository. A session run leaves an application log from which a reader can follow each
   statement from its reading to its outcome (FR-043).

### User Story 10 — Implement a category and obtain computed mathematics (Priority: P1)

A contributor implements a category against its published category interface, as glue over
mature existing computation. A researcher then obtains computed answers for the statements whose
selected route uses that category and the categories below it. [C22, C23][C]

**Why this priority**: The kernel computes nothing. Every computed answer of the product comes
from the category implementations on the whole selected route.

**Independent Test**: For each computational milestone, run the statements of the original
workloads whose selected route stays within the categories implemented through that milestone.
The actual implementations are registered, and no kernel-side evaluation supplies a part.

**Acceptance Scenarios**:

1. **Given** the category implementations from sets up to rings, **when** `2 * 3 = 6 in ℤ` runs, **then** it holds as SC-015 states.
2. **Given** a statement whose route reaches a category with no implementation, **when** it runs, **then** its outcome is no implementation and names the missing operation. Kernel-side evaluation or an implementation outside the category structure does not supply the answer. [C22][C]
3. **Given** a new category implementation, **when** it is registered, **then** the kernel and the existing implementations are unchanged, and the new implementation builds and runs with its actual dependencies only (FR-041). [C12, C23–C24][C]
4. **Given** an implementation to write, **when** the contributor starts, **then** the survey record of engines and libraries exists, and the implementation hand-rolls no algorithm (FR-042). [C17][C]
5. **Given** a leaf that asks the kernel for an operation, **when** no leaf implements that operation, **then** the asking leaf receives the no-implementation outcome and continues under its own control logic (FR-013). [C22][C]

### Edge Cases

| Situation | Required behavior | Obligation |
|---|---|---|
| Equal carriers, endpoints or labels; distinct selected structures | Preserve structures, maps and comparisons; carrier equality does not select an identification. | C5–C8; Story 3 |
| Existence of a lift without a selected point | Do not expose existence as chosen data needed for later computation. | C5, C7; Stories 2–3 |
| Required route, comparison component or coherent choice data are absent | Reject the affected preparation/use with its prescribed missing-data or ambiguity outcome. Do not ask a backend or a new owner policy to select a substitute. | C2–C3, C6–C8; Story 3.5 |
| A supplied comparison is ill-typed or has the wrong boundary/direction | Reject the supplied evidence/data at that boundary; do not treat it as successful agreement or silently fall back. | C5–C7; Stories 3.3, 3.5 |
| Several valid choices are allowed by a prior mathematical contract | Accept the prescribed candidate data for an actual permitted choice and retain it; do not add uniqueness or canonicality. A well-shaped candidate is not a proof of its laws. | C2–C3, C5; Story 3.6 |
| Several cells have the same source/target routes | Retain the actual selected cell and action; same endpoints or existence of a cell do not identify the choices. | C5, C7–C8; Story 3.7 |
| A leaf is asked to formalize the choice family that its code will implement | Reject that combined assignment; preserve independent mathematical authorship and the data-only leaf obligation. | C1–C2, C9–C10; Story 6.5 |
| A generalized point has a nonterminal stage | Retain its stage and actual map. | C5; Story 3 |
| No declared family action on the proposed parameter map | Do not invent base change, variance, fibration or transport from a family name. | C5–C7; Story 3 |
| A comparison is directed and noninvertible | Use declared directions; do not invent an inverse. | C5, C7; Story 3 |
| An outer operation makes an ambiguous argument convenient | Preserve legitimate argument interpretation; backend feasibility cannot select it retroactively. | C3, C6; Stories 1, 3 |
| Multiple mathematical readings with zero, one or many implementations | Preserve mathematical ambiguity; distinguish it from implementation multiplicity. | C3; Story 6 |
| Zero, one or multiple eligible realizations of one selected operation/input form | Use the no-implementation, selected-call or implementation-ambiguity rule; no first/cheapest/priority/retry-until-success choice. | Existing realization policy; Stories 6–7 |
| A leaf asks the kernel for an operation that no leaf implements | Return the no-implementation outcome to the asking leaf. Do not end its computation for it and do not substitute a result. | C22; Story 10.5 |
| A well-formed but wrong reply | It remains a claim against unchanged mathematics; independent expectations assess required cases. | C2, C9–C11; Story 6 |
| A local hypothesis leaves scope | Do not promote a conditional result to an unconditional theorem or reuse it without context. | C1, C6; Stories 1, 3 |
| Finite display, finite support or finite rank | Retain full admitted extent; distinguish these from carrier, presentation and diagram finiteness. | C8; Story 4 |
| Repeated roots or selected coordinates | Preserve declared set/multiplicity or coordinate meaning, with result-local qualifications. | C15; Stories 1, 8 |
| Incomplete exploration of possible readings | Do not claim no reading exists; required resolution completeness in the promised calculus is still owed. This differs from the established absence of mandatory supplied selection data. | C3–C4; Stories 3, 5 |
| Failed prerequisite, malformed result or lost owner | Do not fabricate completion, revive references or substitute selected data. Required dependent observations stay unmeasured and required. | C8, C10–C13; Stories 2, 7 |
| A proposed independent specimen was already exposed | Do not relabel it as unseen. Preserve contributor choice and permitted inputs. | C9, C12; Stories 5–6 |

### References for this part

[C]: https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md
[C22]: https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md#c22-the-kernel-resolves-computation-leaves-perform-it
[P]: https://github.com/dzackgarza/lean-cas-dsl/blob/73bfb1110eb319ff6a6689ac5b01e3b2b1ee049d/SPEC.md
[O]: https://github.com/dzackgarza/lean-cas-dsl/blob/df43c82e939d3b5a54c9b1126abcaa2927c62e3f/specs/owner/intent-discussion.md
[OA]: https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/operation-agreement.md
[A]: https://github.com/dzackgarza/lean-cas-dsl/issues/24
[T]: https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6586827500
[Q]: https://github.com/dzackgarza/lean-cas-dsl/issues/66
[U]: https://github.com/dzackgarza/lean-cas-dsl/issues/69
[X]: https://github.com/dzackgarza/lean-cas-dsl/issues/82
[B]: https://github.com/dzackgarza/lean-cas-dsl/issues/19
[H]: https://github.com/dzackgarza/lean-cas-dsl/issues/23
[I]: https://github.com/dzackgarza/lean-cas-dsl/issues/20
[K]: https://github.com/dzackgarza/lean-cas-dsl/issues/21
[M]: https://github.com/dzackgarza/lean-categories/blob/63e9f620f4f5722bc6d5e73249597deba8f23dd5/INTENT.md
[F]: https://github.com/dzackgarza/lean-categories/blob/c7f1bbcad513219b54d8b698aa28152daf3ff1d4/FOUNDATIONS.md
[J]: https://github.com/dzackgarza/sage-categories/blob/f37647af4f59d8f3505e1b18b11dab30bf3edf84/specs/computational-generality.md
[N]: https://github.com/dzackgarza/lean-cas-dsl/issues/68
[D]: https://github.com/dzackgarza/lean-cas-dsl/issues/13
[G]: https://github.com/dzackgarza/lean-cas-dsl/issues/3
[V]: https://github.com/dzackgarza/lean-cas-dsl/issues/34
[L]: https://github.com/dzackgarza/lean-cas-dsl/issues/68#issuecomment-6586827096
[R]: https://github.com/dzackgarza/lean-cas-dsl/issues/16
[Y]: https://github.com/dzackgarza/lean-cas-dsl/issues/84
[Z]: https://github.com/dzackgarza/lean-cas-dsl/issues/10#issuecomment-6574949858

# Feature specification — Part 2: requirements, success criteria and traceability

**Feature:** `001-categorical-research-language`. Read with [Part 1: scope, workflows, scenarios and owner clarifications][S1]. **Consolidated:** 2026-11-09 (Asia/Taipei), against the [current constitution][C2], including the owner-adopted C6 selection rule and C21 order. This does not amend the constitution, change protected questions/expectations or mark implementation/independent review complete.

The consolidation of 2026-11-09 carried FR-001–FR-040 and SC-001–SC-012 forward. FR-041 and SC-013 were added on 2026-11-22; FR-042, FR-043 and SC-014–SC-016 on 2026-11-25. The consolidation incorporates the distinction between a mathematical comparison and a declared preferred-route selection, and removes obsolete proof/trial/performance-before-functionality timing. The required mathematics, correct composition, independent assessment, complete workload and original final budgets remain. The [plan][PLAN] and the [task list][T1] implement these requirements rather than overriding them.

## Functional requirements

“Accepted” means independently specified under the constitution, not declared true by a provider. “Required” and “promised” mean the complete already assigned scope, not an implementation-selected subset. Requirement identifiers do not replace permanent acceptance IDs. The V1/later-full-B0 boundary remains Part 1 and [#24][A]/[#19][B].

### Mathematical expression and connected work

- **FR-001 — Context and assertions.** Users MUST define/bind mathematical objects, functions and propositions, introduce parameters and explicit local hypotheses, request computations and establish the original assertions. Definitions, assertions, requests and outcomes remain distinguishable. Hypotheses retain scope; accepted rules may determine hypothetical objects without individual catalogue entries. Abstract declarations MUST be scoped assumptions, never global axioms; defined declarations retain their specified definition/scope behavior (#86). [C0–C1, C5–C6][C2] [Original language][P]
- **FR-002 — Exact arithmetic.** Retain the original integer, rational, real, complex and modular arithmetic, accepted inclusions/membership, gcd/factorization, real/imaginary parts, conjugation and norm. Numerals use accepted category-specific constructions and initial-object maps where defined. Host literals cannot create a missing numeral, inclusion or domain. [C6][C2] [P]
- **FR-003 — Sets and indexed expressions.** Retain original finite sets, predicate comprehensions, images, products, powersets, infinite sets, sequences/indexed families, and their specified operations, membership, inclusion, equality/cardinality. Binders keep domains/scope; ellipses and indexed variables retain the accepted reading. Finite display cannot replace an infinite definition. [C6, C8, C15][C2] [P]
- **FR-004 — Functions and maps.** Define, evaluate, compare and compose original typed functions/morphisms and form specified images. Preserve actual domains/codomains, selected maps and admitted equality. Coordinates/matrices cannot silently replace the morphisms they present. [C5, C7–C8][C2] [P]
- **FR-005 — Polynomial work.** Retain selected coefficient rings/indeterminates, formation/evaluation, degree/factorization, coefficient change through accepted maps, root collections and companion constructions. Set/multiplicity semantics and relevant selected conventions remain explicit. [C5, C15][C2] [P]
- **FR-006 — Relative differentials.** Retain relative base, source, differential-object target and selected coordinate identification. Users can inspect and compute the specified action; a coordinate derivative cannot erase its relative meaning or comparison. [C5, C7–C8][C2] [P]
- **FR-007 — Complete primitive families.** A family request returns the specified complete family and relationship to the differentiation kernel. Preserve original conditions, required cardinality/uniqueness, selection of the requested member and subsequent differentiation/use. A single arbitrary primitive is insufficient. [C8, C15][C2] [P]
- **FR-008 — Limits, integration and series.** Express/perform original limits, definite integrals, exact formal/Taylor series, coefficients and explicit truncations at their assigned delivery stage, retaining all admission hypotheses. Exact series and truncations remain distinct with their prescribed comparison; RX09 keeps its exact positive and negative inputs. [C6–C8][C2] [P] [A]
- **FR-009 — Linear and structured algebra.** Retain original vectors, matrices, spans, typed linear maps and specified actions, determinants, ranks, kernels/inverses on their actual domains, followed by prescribed relations. Subobjects retain ambient object/maps. Required group-valued constructions expose accepted group/subgroup interfaces and actual selected actions. [C0, C4–C8][C2] [P] [O]
- **FR-010 — Infinite generality.** Preserve promised infinite/nonenumerable domains, infinite-rank objects, admitted indexed/infinitary constructions and their full interfaces/existence hypotheses. Distinguish finite carrier, rank, support, presentation, arity and diagram shape. Full indices/rules and required component/mediating maps survive bounded observations. Completeness requires neither enumeration of a nonenumerable set nor eager function evaluation. [C8][C2] [J]
- **FR-011 — Qualified approximation.** Retain exact source, requested tolerance and independent error relation. No approximate answer to an exact request, silent tolerance relaxation, erased exact source or invented quotient from historical notation. Relevant qualifications accompany the result. [C6, C15][C2] [P]

### Independent mathematics and encapsulated responsibility

- **FR-012 — Upstream mathematical authority.** Categories, structures, methods, laws, domains, dependent signatures, admissibility, comparisons and abstract computational obligations MUST be independently formalized in lean-categories, including full result data/operations and compositional relationships. Presentations and computation belong to that same mathematics. Definitions/proofs are faithful to independent sources, not implementation-shaped definitions, unauthorized axioms or `sorry`; hypotheses stay explicit. Cell/choice families, boundaries, required coherence and the division between laws and computational data are fixed before leaf implementation. A C6 preferred-route declaration selects existing data and does not author mathematics. [C1–C2, C6][C2] [M]
- **FR-013 — Computational-only leaves.** Every operation, method and predicate is computed by a leaf. The kernel resolves each requested computation to a leaf implementation or reports no implementation, and computes nothing itself; it may discharge a closed proposition through a proof procedure registered upstream. A leaf owns all control logic of its implementation and may use any formalized operation internally, through another leaf directly, or by asking the kernel. The kernel routes that request like any other and returns the result, or the no-implementation outcome, to the asking leaf. A value with no published operation has the no-implementation outcome [C22][C2]. Kernel work is accepted on kernel behaviour, observed with a protocol peer or an empty manifest, and requires no computed mathematical result; a computed result is leaf work on the whole selected structural route (constitution v4.0.0, C22). Leaves claim to implement accepted operations and return prescribed computational data, never mathematical definitions/proofs, optional certificates or acceptance authority. Generic kernel discharge concerns already formalized obligations, not leaf-specific mathematical invention. The boundary cannot create categories, membership/inheritance, domains, result types, mathematical identity or correctness criteria. Required route/cell/choice data MUST be supplied where assigned; omission fails admission/use, not a kernel default. C6 permits declared preferred routes as registration selections of admitted bindings, asserting no agreement. It does not permit leaf-authored cells or laws. [C2, C6][C2]
- **FR-014 — Independent interpretation and assessment.** Fix mathematical operation, permitted representation interpretation, observations and correctness relation independently of the candidate. Leaf denotations, identities, proofs, certificates, checkers and self-tests supply neither meaning nor correctness authority. Registration/decoding is not correctness. Public leaf work uses permitted established implementations/glue, not newly authorized algorithm or proof development. Well-shaped choice/cell data do not establish their laws. [C2, C9–C10][C2]
- **FR-015 — Actual authorship/input separation.** Formalization receives mathematical requirements/sources; independent acceptance receives accepted mathematics/public language/independent sources; public-only leaves receive the released contract/catalogue and permitted computational material. Leaves do not receive kernel source, internal handoffs, protected expectations or prior outcomes; authorized public specimen/runtime material remains allowed. A missing mathematical dependency is a task of lean-categories: the task list names it before its consumer, and the workstream does it there as formalization work, from the mathematical requirement and its sources (constitution v4.0.0, C21). An implementation-generated goal or failure can show that such a task is due; it cannot fix the mathematical content of the definition. One leaf author cannot formalize its own comparison/choice criterion then implement it, even across repositories or renamed roles. [Constitution authorship rules][C2] [T]

### Selected meaning, composition and growth

- **FR-016 — Complete selected context.** Retain actual categories, objects, maps, parameters, hypotheses, structures, comparisons/coherence and observations. Equal carriers/endpoints/names do not identify structures. Generalized points keep their stages. A specified choice operation may return any allowed member; retain that actual member and its continuation without added equality/canonicality. A fixed selection cannot be replaced, and an ordinary unresolved question cannot be converted silently into a new choice-producing operation. A C6 declared route is explicit selection data recorded with the reading. [C3, C5–C8][C2]
- **FR-017 — Comparisons and identity.** Distinguish equality, isomorphism, presentation equivalence, selected occurrence and computational-reference identity. Translation preserves required observations/continuations through its accepted actual comparison. Nonidentity components act on data/maps; noninvertible cells acquire no inverse. Retain boundaries/components/laws and required higher coherence, not existence or connectivity flags. Required omission fails before dependent use. Inherited-operation agreement concerns complete rigid families with actual directed transports, via definitional equality or an independently accepted comparison. Alternatively a valid C6 preferred-route declaration selects a surviving binding without asserting agreement. If neither required agreement nor valid selection resolves the request, report ambiguity; no theorem of absolute comparison nonexistence is required. [C5–C8, C13][C2] [OA] [A]
- **FR-018 — Classifiers and families.** Retain actual selected points/lifts and comparisons, not classifier inhabitation. Simultaneous structures use the homotopy limit of their full compatibility diagram under accepted size/existence hypotheses. A classifier map alone grants no fibration/transport. Dependent declarations retain context, varying codomain, base, admitted parameter maps, variance and coherent reindexing. [C5][C2] [F]
- **FR-019 — Domains and structural roles.** Inherited use follows accepted structural functors at actual selected images and actual operation domains. Reachability/being a functor alone does not grant inheritance. Parameter projection, forgetting, base change and reindexing retain declared roles. Admission evidence holds when reading the request; an outer desired operation cannot implicitly restrict or reinterpret its argument. [C4–C6][C2]
- **FR-020 — Universal data and lifts.** Supply every promised apex/diagram/map/comparison/factorization/application interface in its independent relation. Lifts use actual selected data and accepted creation/lifting hypotheses; existence or an isomorphic reconstruction cannot replace them. RX08/RX-LIFT retain their declared module-level meaning, not an invented universal kernel among form-preserving maps. [C7–C8][C2] [A]
- **FR-021 — Higher mathematics.** Retain infinity categories, functors, general natural transformations, higher modifications and required mapping objects in the intended `(∞,2)` setting, with independent model/interface, size/existence hypotheses and structured morphism conventions. Diagram extensions retain complete boundaries, selected fillers and matching compatibility. Every reduction/truncation/strict interpretation needs independent adequacy for every promised observation/action/substitution/composition/continuation in which it is used. [C7–C8][C2] [F] [X]
- **FR-022 — Provider-independent meaning.** Fix accepted mathematics, public language, hypotheses and the complete selected question, including its declared route selection. Provider addition/removal/replacement/reordering/failure cannot change meaning, domain, applicability or expected assertion. Missing computation is an execution gap; success cannot resolve ambiguity. Accepted mathematical growth preserves selected old meanings and genuine new readings of underspecified expressions. Different legitimate choice outputs or explicitly different declared route selections establish different selected contexts; this does not let availability select a reading within one fixed context. [C3–C6, C9][C2]
- **FR-023 — Old operations on new constructions.** New accepted constructions acquire every applicable old operation/composite through actual immediate mathematical relationships, without per-construction forwarding, duplicate inherited declarations or old-leaf edits. Operations retain their generating owner. Reject genuinely redundant primitive declarations with the existing intended composite identified; common endpoints do not identify routes. [C4, C12][C2] Different admitted constructor families into one category MUST expose the same complete applicable public interface; all constructor–operation combinations assigned to positive workloads retain their original later uses. Object and morphism actions are both required where the formal functor supplies them. See the [category-interface conformance contract](../architecture.md#constructor-and-operation-conformance).
- **FR-024 — New operations on old constructions.** New generic operations reach all applicable old constructions without editing their definitions/leaves, including required orthogonal-group, subgroup and stabilizer uses. Applicability survives absent/broken computation; required executable instances still must work. [C0, C4, C12][C2] [O]
- **FR-025 — Faithful generic interpretation.** The published category implementation view MUST be generated from accepted declarations and the released contract: object/morphism constructors, operations at their actual domains, immediate functor actions and complete dependent input/result signatures. The existing supported SDK MUST expose directly consumable category signatures and constructor/call/result access helpers derived from that source and the released protocol grammar. Where host-language types cannot express a dependency, preserve its explicit descriptor and existing runtime checks; generated datatype metadata is not a new wire codec. Reuse the existing exporter, addresses and protocol; the kernel continues to read the independent registry, not generated documentation as semantic authority. No separately hand-maintained downstream mirror of the category API or private-origin interpretation cases are permitted. Consume accepted current/extended declarations faithfully, with no maintained semantic hierarchy, whitelist or per-declaration accommodation. C3/C6 lookup completeness concerns enumeration of first-binding routes over the accepted signature; it does not require deciding arbitrary inherited-operation agreement. Validate supplied source data and declared selections under the actual rule. Failed/incomplete checking is not proof of no reading. Composites retain actual inputs, images, maps and component actions. No stronger universal quotient, unrestricted theorem search, convenient smaller language or fabricated missing choice substitutes for this obligation. [C1, C3–C4, C6][C2] [OA]
- **FR-026 — Correct composition.** Assuming independently specified primitives are correct, interpretation/substitution/composition, functorial action, reindexing/lifting, comparisons and universal-map use MUST preserve the complete selected construction and every promised continuation. The argument covers the first supported mechanism and every additional one, including actual native implementation rather than a free `Correct` premise. Its completion follows functionality under C21; it is not an implementation prerequisite or a waiver of source laws/runtime checks. Permitted fused realization retains the same mathematical composite. Conditional composition does not prove arbitrary primitives correct. [C4, C7–C8, C10–C12, C21][C2] [A]
- **FR-027 — Complete returned values.** Results expose all prescribed data/callables and preserve actual maps, parameters, comparisons, dependencies, identity and lifetime through later use. A recipe, first scalar or same-labelled replacement is insufficient. Symbolic/lazy/indexed representations are permitted only with the full promised interface and independent interpretation. [C8, C13][C2] [U]

### Execution, independent extension and research interaction

- **FR-028 — Realization selection.** For one fixed mathematical operation/input form, zero eligible registrations gives the no-implementation outcome, one the selected call and multiple implementation ambiguity. No first/cheapest/priority/installed-order/retry-until-success policy. An occurrence retains its registration. Explicit comparison/replacement experiments and adequate fused realizations retain their rules. This is distinct from C6's declared mathematical route selection. [Current policies][C2]
- **FR-029 — Outcome separation.** Distinguish mathematical invalidity/ambiguity, missing/unavailable computation, failed execution, malformed data, internal failure and independently established wrong answers. Unknown is procedural, not a truth value or permission to change a domain/expectation. Distinguish absent mandatory semantic data, invalid supplied evidence/preference, interrupted checking, missing realization of a valid choice request and omitted mandatory reply data. No condition licenses default selection or dependent dispatch without required data. No universal opaque wrong-answer detector is asserted. [C2–C3, C6, C10, C13][C2]
- **FR-030 — Fixed independent acceptance.** Provider substitution is assessed against the full original relation, including required maps and actual chosen results through later use. Permitted noncanonical answers need not be byte-identical; prescribed exact values, ordering, normalization and selected input structures remain binding. Agreement with an existing CAS or a correct scalar projection cannot replace the complete obligation. Preserve complete questions, selected contexts/comparisons, expected relations and outcomes across implementation changes. Keep actual author/input separation and independent harness ownership; leaves do not run/import the permanent suite as their evidence. Distinguish validity, interpretation, admission, execution and answer correctness. Outputs/self-tests/exposed cases cannot replace independent expectations. [C9–C10][C2] [A]
- **FR-031 — Growth and interoperability.** Every prescribed mechanism works against the frozen baseline: new objects/old operations, new operations/old objects, group-valued constructions, classifiers/refinements, competing routes, reindexing, nonidentity presentations, binders/admission, complete results/lifts and replacement. Independently supplied data/maps support unchanged old consumers through the public categorical interface, without private representation knowledge. [C12][C2] [A] [T]
- **FR-032 — Genuine frozen trials.** Eligible independent contributors choose concrete extensions after the complete applicable baseline is fixed. That baseline identifies kernel, released contract/API, accepted mathematical inputs, registrations, old objects/leaves/consumer and unchanged questions/expectations. Zero accommodating changes; authorized additive/replacement contributions remain separate. A necessary patch fails that candidate and requires repair/refreeze/affected reruns with original fresh-choice/input rules. Known RX recovery, independent trials and general mechanism arguments remain separate evidence. Under C21 trials follow required functionality; they do not gate completing it or create an ever-growing oracle inventory. [C12, C21][C2] [A] [T]
- **FR-033 — Complete assigned execution.** The designated combination performs every assigned positive computation/continuation and all prescribed controls with full hypotheses/bindings/maps/comparisons. Missing infrastructure/algorithms, crashes, wrong answers and unreached dependents remain required. Rejection or a conditional theorem cannot replace positive execution. Full V1 and later-B0 assignments remain distinct and complete. Kernel readiness permits no stub in required generic behavior. Kernel readiness is observed on kernel behaviour (FR-013); the computational milestones (FR-042) deliver the positive computations of this requirement. [C10–C12, C21][C2] [A] [B]
- **FR-034 — Actual notebook use.** The public CAS/notebook executes original real-engine workflows and uses actual intermediate native/lazy/callable objects, maps, inherited operations and comparisons later. Preserve function/binder/composition, indexed-polynomial and owner-selected enumeration behavior. Stored outputs, a standalone binary or another frontend are not the required actual notebook. [A] [Q]
- **FR-035 — Inert inspection.** Committed-state inspection creates no occurrence, dispatch, result/liveness change, resource open/close, worker bootstrap, restore/replay or preceding-cell execution. This holds for live/missing/stale predecessors and no worker. Establish the nonexecuting committed-environment capability **before** transmitting executable text; unsupported endpoints receive none. Source-bearing requests followed by reply inspection are insufficient. All query success/error paths avoid executable printer/delaborator/documentation/proof/lazy/provider hooks while retaining useful mathematical metadata. [A]
- **FR-036 — Lifetime/cancellation/rerun.** Preserve required actual owners. Cooperative cancellation before commit publishes none of the active cell's new references while preserving valid previous owners; force/replacement invalidates its old generation. Reject closed/stale dependent references before external dispatch, including after old-snapshot restoration. No resurrection, automatic retry/replay/migration. Explicit rerun is fresh; reading a committed binding, same-cell staging or joining one pending occurrence is not new dispatch. Rollback and concurrent demand cannot restore consumed rights or duplicate invocation. Whole-cell failure publishes none of its staged values; previously committed results survive genuine owners. Possibly executed requests without usable replies remain unavailable/disconnected with indeterminate-execution diagnostics, not success/invalidity/safe-retry or exactly-once effects. Stored independent portable fields are not invalidated by unrelated sibling owners; whole-record/capture demands retain all actual dependencies. [C13/current retry policy][C2] [A] [L]
- **FR-037 — Discoverable mathematics.** Discover the full interface warranted by accepted constructions/hypotheses independently of provider availability. Documentation states actual generality/hypotheses, not only convenient examples. Inspect selected types, parameters, structures, presentations, defining maps/cells and relevant assumptions without private provider vocabulary. [C0, C3–C5, C15][C2]
- **FR-038 — Mathematical display/provenance.** Automatic mathematical output uses LaTeX where available and useful text fallback, once per event without duplicate plaintext. Required qualifications accompany results; backend/routing/timing diagnostics are opt-in. Inspection identifies the actual routine and verified primary documentation or relevant source fallback as inert information. The complete public language remains documented/usable. [C15][C2] [R]
- **FR-039 — Coherent reproducible delivery.** Publish one compatible source/runtime combination with current contract, usable actual examples/notebook, exact provenance, reproducible commands, complete reports, independent assessments and mechanism arguments. Own-organization delivery uses required latest-main inputs and records actual compatible revisions; diagnostic pins are not separate releases. All V1 A–F hold together; incompatible successes cannot be assembled into a pass. V1 closure is recorded at #97 only with #24/#66/#69 discharged. #10 stays open for the later scopes, and later owners retain their scope. [C10–C12, C19][C2] [A]
- **FR-040 — Final budgets and functional priority.** Final acceptance retains all original question-specific budgets, inputs, contexts and later uses: original 99-root 3×3 matrix-kernel computation strictly under 60 seconds on the measured host, with phases, and RX-LIFT's shared 200,000-heartbeat preparation/evaluation with all 22 prerequisites. No inflated final budget or trimmed question creates success. C21 gives the changed-source development loop immediate priority (FR-041), permits whatever limits functional development needs, and places final mathematical/runtime performance last, after all required public capabilities work. A timeout or red expensive aggregate does not select or block unrelated functional work. Outside the explicit development-feedback priority, only the narrow cannot-finish-at-all exception permits necessary optimization during functional development. [C21][C2] [A] [Q] [Y]

- **FR-041 — Fast local development feedback.** A contributor MUST be able to change the responsible implementation, rebuild its actual affected imports and executable dependencies, and execute the unchanged public question and required continuation through the existing focused workflow. The normal loop uses the existing 300-second limit, streamed diagnostics and truthful current-run status; a slow loop is a defect of that workflow, not permission to narrow the mathematical question. Ordinary iterations do not refresh dependencies, provision packages or run an unrelated full aggregate. Production and category implementation boundaries must exclude unrelated test/probe/backend aggregation while retaining necessary shared and executable dependencies. Existing logs retain the actual revision, environment, input, changed owner, affected targets, result and elapsed time. A missing or stale report is not a successful run. This engineering requirement is distinct from final mathematical budgets and independent correctness evidence. [C21, C24][C2] [Feedback workflow](../../CONTRIBUTING.md#feedback-loops)

- **FR-042 — Computational milestones.** Category implementations are delivered in version milestones of their own, separate from the kernel milestone and after kernel readiness. The order follows the structural scaffolding of the accepted categories: an implementation follows those of the categories that its structural functors and classifier forgets reach, starting with sets. Each milestone is vertical and has a stated mathematical result that MUST hold as a computed result through the selected structural route. The result comes from the original workloads: the statements whose selected route stays within the categories implemented through that milestone. It includes each operation of those categories that a later milestone consumes; the [plan](plan.md#computational-milestones) lists the statements. Each implementation is glue over mature existing computation and hand-rolls no algorithm (established-implementations policy); the control logic of an operation is glue and stays with its leaf (C22). An open-ended survey of engines and libraries comes first, with the record that C17 requires: the inspected source and revision, the responsibility that it supplies, the decision and its reasons. Computation that the system performs outside a category implementation MUST move into one. (Constitution v4.0.0, C17, C22 and C23.)

- **FR-043 — Logs, timing records and construction cost.** Every test and every computation MUST have a timing record that includes setup, fixtures, construction and nested work, with its run, revision, environment and input. Every test run MUST write a durable log. The records and the logs are kept in the repository. The application MUST write detailed logs: for each statement, the kernel session and the notebook worker record the reading, the selection, the prepared request, the dispatch, the admission, the retained value and the outcome. Diagnostics shown to the user stay opt-in (FR-038). Construction of a mathematical object MUST be close to instant: forming an object computes no field that no statement has demanded, unless an explicit flag requests eager computation (FR-027 permits lazy results). These obligations are current work and do not wait for functionality. Optimization that the timing records select still follows functionality (FR-040). [C24][C2]

## Key entities

These are mathematical/user concepts, not another storage or capability ontology.

| Entity | Required meaning |
|---|---|
| Mathematical context | Actual bindings, parameters, scoped hypotheses and selected structures determining the complete question with accepted mathematics/public language. |
| Accepted declaration | Independent category/construction/operation/law/domain/signature/comparison and its abstract computational obligations. |
| Complete question | Selected relation/construction/observation with context, required maps/cells/outcome and later uses; independently retained. |
| Structured object/morphism | Actual object/map with domains/codomains, structures, parameters, presentation relationships and full required interface. |
| Dependent family/choice fibre | Fixed base, admissible maps/variance/transport; a choice result supplies actual permitted data without added uniqueness. |
| Comparison/coherence | Actual selected cells, boundaries, direction, components, matching data and actions—not a path-equivalence flag. |
| Required selection | Source-prescribed datum with its fixed supplier/stage/dependent uses, required before those uses. |
| Declared preferred route | C6 registration data selecting an admitted surviving binding and retained with the reading; no agreement/law is asserted. |
| Constructed result | Candidate actual object/map/factor/callable/dependency data sufficient for all promised continuations. |
| Computational realization | Claim to compute an accepted operation/form; availability/selection separate from mathematical meaning. |
| Execution/live reference | Actual occurrence/result/registration/owner/lifetime/outcome, distinct from equality or fresh recomputation. |
| Independent expectation/assessment | Preserved question/relation and outcome assessed under the required separate author/input boundary. |
| Qualified observation | Exact or explicitly approximate/truncated result with source, conventions, comparison/error relation and tolerance. |
| No-implementation outcome | The prescribed outcome of a selected operation that has no eligible realization. It names the operation. The realization policy of the constitution calls it the declared gap; the session reports it with the kind `gap` and the contracts with `noImplementation`. |
| Kernel readiness (F) | Every required generic kernel capability works through the real public entrances. It is the closure condition of milestone M1 and is observed on kernel behaviour (FR-013). |
| Kernel checkpoint | One observation of kernel behaviour through the public session, with a protocol peer or an empty manifest (a manifest with no registration). It needs no computed mathematical result and satisfies no user story (SC-014). |
| Computational milestone | A version milestone of category implementations in structural order, with a stated computed result from the original workloads (FR-042). |

## Measurable success criteria

These are targets, not present implementation or review claims. Existing inventories supply exact inputs and independently expected relations; no new oracle or contributor specimen is selected here. Functionality precedes evidence-only work/performance as C21 directs; all outcomes remain due for full delivery.

- **SC-001 — Complete readings.** Export all 153 permanent questions exactly once and all 134 positive extension questions in 14 files (105 original + 29 completion), with complete selected judgments and prescribed outcomes. Keep unreadable IDs, protected negatives and environment controls separate. Independent comparison includes actual structures/parameters/maps/composites/cells and higher data, not tags/counts. [A]
- **SC-002 — Unchanged computations.** Assess every original fixed extension and RX01–RX10/full RX-LIFT outcome on the candidate. Preserve RX01–04 structures/arrows/classifiers; RX05 full route inventory; RX06–07 actual reindexing/bidirectional F9 and later computation; RX08 full module maps/restricted form and separate ambiguity/positive; RX09 exact series controls; RX10 same-question correct/wrong/missing/unavailable/malformed/internal outcomes with callable/owner use; full successive RX-LIFT/nonzero factors. Zero easier substitutes, shorter contexts or weaker relations. [A]
- **SC-003 — Actual selected data and continuation.** Every required construction/later use retains and applies actual maps, cell components, direction, higher compatibility and universal/factor data. Original permutation/direction/omission/multiple-route/unresolved-cell controls retain their prescribed outcomes. Missing mandatory data cause zero dependent dispatch; invalid evidence and interruption stay distinct. Valid nonunique choices retain actual data, not canonical replacements. An explicit C6 preference can select its admitted route but is not fabricated in an unresolved protected control. All required successive whole-arrow/factor observations are measured; unexecuted prerequisites remain incomplete. [A] [T]
- **SC-004 — Connected research execution.** Execute at least four real-engine workflows across at least three mathematical areas with all 17 original connected assertions, through the actual configured notebook/public surface. Retain binder/composition, indexed-polynomial and enumeration behavior, actual intermediate constructions/maps/inherited operations/nonidentity transport, and reproducible executed artifacts. [A]
- **SC-005 — Independent extension.** Every prescribed mechanism trial succeeds after its complete applicable baseline freeze and independent contributor choice. Record kernel/mathematics/contract/API/profile/registrations/old objects/leaves/consumer/questions/expectations. Zero accommodating changes; authorized additive/replacement contributions remain allowed. Actual produced data/maps reach the unchanged consumer. Keep regressions, unseen trials and general arguments separate; repaired candidates are refrozen and affected trials rerun. Trials are not prerequisites to implementing remaining functionality. [A] [T] [C21][C2]
- **SC-006 — Fixed-context invariance.** Original replacement/removal/reordering/failure controls make zero changes to their complete selected question/domain/applicability/expected assertion. Unresolved mathematical ambiguity persists with two/one/no implementations; realization ambiguity remains separate. Explicit selections and legitimate choice-result contexts are retained rather than equated. Finite controls accompany the general safety argument, not replace its quantifier. [C3–C6][C2] [A]
- **SC-007 — Generic preservation and completeness.** Establish source-grounded arguments for every actually supported promised mechanism and every required continuation, including substitution, composition, functorial action, reindexing/lift, comparisons and universal-map use. C3/C6 first-binding enumeration and source-prescribed selection/error behavior retain their exact scope, not universal semantic-equivalence discovery. Reductions have adequate independent preservation for actual uses; arbitrary primitive correctness is not inferred from decoding or handler laws. C21 schedules this evidence after functionality, without dropping the first mechanism or any later mechanism from its scope. [C3–C4, C6–C8, C10–C12, C21][C2] [A]
- **SC-008 — Encapsulated authority.** Actual contribution/assignment/input review finds zero leaf semantic/acceptance authorities, mathematical-proof deliverables, combined self-defined/formalized-and-implemented choice contracts, or implementation-shaped correctness criteria. Every abstract computational obligation traces to independent mathematics. Prescribed candidate choice data and C6 route declarations remain legitimate data, not laws/proofs. Leaf self-tests do not replace acceptance; exposed cases are not relabelled unseen and required isolation/disclosures remain. [C1–C2, C6, C9–C12][C2]
- **SC-009 — Full mathematical product.** Preserve all original language capability/readings/discovery/documentation. At their assigned later boundary, all K1–K14 computations, all 26 K13 IDs, K3/K14 obligations and broad Sage parity meet their separate independent expectations with full continuations. Full-B0 computation and broad parity retain distinct evidence and can be completed separately; #19 requires both. Current overlaps satisfy V1 now without importing every later algorithm as a new V1 gate. [P] [B] [A]
- **SC-010 — Useful interface.** All prescribed workflow cases discover every applicable operation and inspect actual selected context/data/provenance independent of provider absence. Every display event emits once with automatic mathematical rendering/fallback/qualifiers; actual routine references use verified primary documentation/source. Assess actual delivered workflows, not a mock interface. [C15][C2] [A]
- **SC-011 — Inert queries and exact lifetime.** All live/missing/stale/incompatible-worker query controls produce zero dispatch/occurrence/result/liveness changes; incompatible endpoints receive zero executable text before capability validation. Cooperative cancellation before commit publishes zero new references and preserves prior owners; forced invalid generations have zero usable dependent references and zero stale external dispatch, including old snapshots. No automatic retry/replay/migration, duplicate consumed invocation, partial cell publication or hidden payload recovery. Preserve all existing reserve/send/receive/commit/rollback/concurrency/close/restart/drain/duplicate controls and indeterminate-execution outcomes. Whole-record/capture liveness remains exact while independent stored fields/metadata survive unrelated owner loss. Required real execution and subsequent reuse still succeed. [A] [L] [C13][C2]
- **SC-012 — One complete delivery and final budgets.** All V1 A–F hold on one published compatible latest-main source/runtime combination with exact revisions, commands, current API, actual notebook/examples, complete reports, independent assessments and mechanism arguments. Meet original full-input budgets in the last phase: 99-root 3×3 kernel under 60 seconds on the measured host with phase timings; full RX-LIFT with shared 200,000 heartbeats and all 22 bindings. No 66-root/2×2, shortened prefix, changed expectation or higher-limit development run passes this criterion. Existing bounded #20/#21/#23 obligations and separate later scopes remain. V1 closure is recorded at #97 only with #24/#66/#69 discharged; #10 stays open for the later scopes. [C21][C2] [A] [B] [Q] [Y]

- **SC-013 — Fresh bounded edit-to-result loop.** On the current compatible implementation, a substantive representative change and its unchanged public consumer complete the ordinary focused loop within the existing 300-second bound, with current diagnostics and measured build/execution/total time. A relevant failure control reaches that consumer; failed, missing, stale or partial selected execution cannot produce a successful result. Inspect the real rebuild closure to establish locality. Retain the observations in the existing timing/log surfaces, and repair regressions during later functional work. This criterion establishes developer feedback only; it does not mark an unfinished mathematical capability, the published-image port or final independent acceptance complete. [C21, C24][C2] [#84](https://github.com/dzackgarza/lean-cas-dsl/issues/84)

- **SC-014 — Kernel checkpoints.** Each kernel checkpoint of the [plan](plan.md#m1-checkpoints) holds as one observation of kernel behaviour through the public session, with a protocol peer or an empty manifest. A checkpoint establishes kernel readiness for its observation only. It satisfies no user story and no positive computation.
- **SC-015 — Computed attainment of the ring milestone.** `2 * 3 = 6 in ℤ` holds as a computed result: ℤ is read as a ring, its multiplication is reached through a selected monoid structure of that ring, its numerals are images under the universal map, and its equality is a computed predicate, all through category implementations from sets up to rings. No kernel-side evaluation and no implementation outside those categories supplies a part of it. The milestones before it have their own stated results (FR-042).
- **SC-016 — Logs and timing records.** On the current implementation, each run of a test module and each computation of an acceptance statement has a timing record in the repository, with setup, fixtures, construction and nested work and with its run, revision, environment and input. Each test run has a log in the repository. A session run writes an application log from which a reader can follow the reading, the selection, the request, the dispatch, the admission, the retained value and the outcome of each statement. Forming an object with no later demand dispatches nothing. [C24][C2]

## Distinct quantifiers and scheduling

| Obligation | Quantifier / evidence |
|---|---|
| Semantic safety | Fix accepted mathematics, public language, full selected context/question; allow arbitrary provider behavior, including well-shaped wrong replies. Meaning/domain/selection/expectations are protected. Original controls supplement the general argument; no universal runtime detector is claimed. |
| Conditional correct composition | Assume primitives meet independently fixed relations; quantify over every promised supported composition/continuation, actual maps and selected choices. Establish preservation/adequacy. Registration/decoding does not establish the primitive premise. |
| Complete delivery | The actual compatible candidate performs every assigned computation, control, continuation, trial and final resource requirement. A catalogue, rejection, conditional theorem or isolated success is insufficient. |

All three are mandatory and none discharges another. C21 changes their implementation order, not their eventual scope: current fast development feedback first and preserved throughout, with its timing records and logs (FR-043); complete required kernel functionality next; substantial leaf work after F, in the computational milestones of FR-042; evidence-only proofs/assessments/frozen trials and final mathematical performance afterward. Actual mathematical/source/data/owner checks required to execute a function remain part of functionality. A missing mathematical input is a lean-categories task in the task list, which the workstream does there (FR-015). A document review does not authorize a code/CI change or mark any evidence complete.

## Requirement traceability

| Requirements | Required stories/observations | Success criteria and existing owners |
|---|---|---|
| FR-001–FR-005 | US1 connected context/arithmetic/sets/functions/polynomials and US3 selected context | SC-001–SC-004, SC-009; #24 assigned computations and #19 later work |
| FR-006–FR-009 | US1/US2 differentials, full primitives, structured/linear constructions | SC-001–SC-004, SC-009; original stage boundaries |
| FR-010–FR-011 | US4 full infinite domains, display-prefix, exact/approximate/truncation | SC-001–SC-003, SC-009–SC-010 |
| FR-012–FR-015 | US6 actual formalization/computation/evidence author/input separation; kernel work accepted on kernel behaviour | SC-006–SC-008, SC-014 (#92); independent authority and trials |
| FR-016–FR-019 | US3 actual cells, required selection, permitted nonunique output, C6 preference, domains/families | SC-001–SC-003, SC-006–SC-007 |
| FR-020–FR-021 | US2/US3 complete universal/higher data and every promised continuation | SC-002–SC-003, SC-007; #69/#82 |
| FR-022–FR-025 | US3/US5/US6 fixed meaning, both growth directions, actual source judgments | SC-005–SC-007; #24 C–E |
| FR-026–FR-027 | US1–US3/US7 full actual result and later use | SC-002–SC-005, SC-007; #66/#69 |
| FR-028–FR-030 | US6/US7 exact errors/realizations and independent expected relations | SC-002, SC-006, SC-008, SC-011 |
| FR-031–FR-032 | US5/US6 original independent additive/replacement contributions and unchanged consumer | SC-005, SC-007–SC-008 |
| FR-033–FR-036 | US1/US2/US7 complete public execution, inspection and lifetime | SC-001–SC-004, SC-009, SC-011–SC-012 |
| FR-037–FR-038 | US8 actual discovery, selected data, one-emission display/provenance | SC-010 |
| FR-039–FR-040 | Same complete delivery, preserved input/provenance and final original budgets | SC-012; #24 F and existing #19/#84 scope |
| FR-041 | US9 actual changed-owner build and unchanged public consumer; physical dependency locality | SC-013; #84/T114, continued during #92/#93 |
| FR-042 | US10 category implementations in structural order, each with its computed attainment | SC-015 (#93) |
| FR-043 | US9 timing records, test-run logs, application logs; construction that computes nothing undemanded | SC-016; T112, T127 |

Task IDs/functional dependencies are maintained only in the [task list][T1] (its Part 1 and Part 2), not a second state table here. Their earlier subsystem-first and proof/trial-before-functionality order is superseded by the current plan; stable IDs preserve history, not that order.

## Assumptions, boundaries and sources

The feature remains the complete categorical research language under its permanent constitution, not a new smaller project. Mathematical precision is user-facing domain content, not a chosen internal stack. #24 defines V1 questions/outcomes; #19 retains stronger full-B0/parity execution. Actual CAS/notebook is V1; the later Python facade, subsequent genuine researcher demand harvest and later production/portability scopes remain #68/#13/#3/#34, except their already assigned V1 overlaps.

Each mathematical dependency supplies its independently accepted model/interface, universes, hypotheses, structured morphisms, variance/transport, admissibility, cell/choice rules and adequate lifting/reduction at the promised use. Naming a gap is not permission for a downstream author to define it to fit code; the workstream supplies it in lean-categories from the mathematics (FR-015). Finite ordered-basis examples do not limit infinite indexed scope; the ambient category determines the actual universal property. No arbitrary limits/transports are asserted here.

No explanatory example selects a new independent oracle or contributor specimen. Preserve original questions, separate original ambiguities/clarifications and the no-accommodation rules. Original November 7 answers on cells/choices/authorship remain integrated, with the subsequent owner C6 preferred-route and C21 sequencing changes now explicit. Earlier quality checklists/review digests apply only to their recorded versions; this consolidation does not provide fresh independent approval.

Issue records own work records, diagnostics and evidence. The constitution, the mathematical execution model, the contribution rules and this feature directory (specification, plan, research, data model, contracts, validation guide, checklists and tasks) are maintained repository documents. No CLI invocation, native build or code conformance is claimed by this editorial consolidation.

Primary/source register: current constitution and its historical ledger; original public-language specification/owner intent; independent mathematical foundations/computational generality; #24 A–F and its trial clarification; #66/#69/#82; #19–#23 scope assignments; existing lifecycle, rendering and development-feedback obligations. Old source pins below identify requirement provenance, not current implementation readiness. C6's route-selection declaration is governed by the current constitution; the pinned agreement text fixes the mathematical comparison rule, not an extra universal decision procedure.

[C2]: https://github.com/dzackgarza/lean-cas-dsl/blob/main/.specify/memory/constitution.md
[S1]: spec.md
[P]: https://github.com/dzackgarza/lean-cas-dsl/blob/73bfb1110eb319ff6a6689ac5b01e3b2b1ee049d/SPEC.md
[O]: https://github.com/dzackgarza/lean-cas-dsl/blob/df43c82e939d3b5a54c9b1126abcaa2927c62e3f/specs/owner/intent-discussion.md
[OA]: https://github.com/dzackgarza/lean-categories/blob/6c7f6a8f026500da30c00736580c5bd30c87331b/LeanCategories/Catalogue/Registry/operation-agreement.md
[A]: https://github.com/dzackgarza/lean-cas-dsl/issues/24
[T]: https://github.com/dzackgarza/lean-cas-dsl/issues/24#issuecomment-6586827500
[Q]: https://github.com/dzackgarza/lean-cas-dsl/issues/66
[U]: https://github.com/dzackgarza/lean-cas-dsl/issues/69
[X]: https://github.com/dzackgarza/lean-cas-dsl/issues/82
[B]: https://github.com/dzackgarza/lean-cas-dsl/issues/19
[M]: https://github.com/dzackgarza/lean-categories/blob/63e9f620f4f5722bc6d5e73249597deba8f23dd5/INTENT.md
[F]: https://github.com/dzackgarza/lean-categories/blob/c7f1bbcad513219b54d8b698aa28152daf3ff1d4/FOUNDATIONS.md
[J]: https://github.com/dzackgarza/sage-categories/blob/f37647af4f59d8f3505e1b18b11dab30bf3edf84/specs/computational-generality.md
[L]: https://github.com/dzackgarza/lean-cas-dsl/issues/68#issuecomment-6586827096
[R]: https://github.com/dzackgarza/lean-cas-dsl/issues/16
[Y]: https://github.com/dzackgarza/lean-cas-dsl/issues/84
[PLAN]: plan.md
[T1]: tasks.md
[T2]: tasks.md

## Mathematical-model acceptance

These maintained scenarios apply C23 and the [execution model](../architecture.md). They extend
both linked specification parts without changing the original workloads or author separation.
They state required behavior; their presence is not a pass or an implementation-status claim.
A scenario that verifies computed values (MM002, MM007, MM008) is assessed when the category
implementations that it uses exist. Its kernel part is a kernel checkpoint (SC-014).

| Requirement | User scenario and observable acceptance |
| --- | --- |
| MM001 | Construct an object in a declared category and call an applicable inherited operation. The accepted formal composite supplies its meaning and complete result interface. Removing its provider leaves that meaning intact and yields the no-implementation outcome when demanded. |
| MM002 | Construct an image under a functor implemented independently of its target consumer. The unchanged target method consumes the image through its public interface. Apply the functor to identities and composable morphisms and verify the independently specified functor laws and exact endpoints. |
| MM003 | Request a method whose domain is an owner's core groupoid or a dependent, slice, arrow or higher construction. Interpretation uses that actual domain and does not invent an action on unsupported morphisms. |
| MM004 | Request an inherited operation along competing routes. Use definitional equality of the complete dependent families, an accepted comparison with its prescribed transport, or the explicit C6 binding preference. In its absence, report ambiguity. Route order, provider speed and equal endpoints do not resolve it; a natural isomorphism does not silently become judgmental equality. |
| MM005 | Use a formally finite integer subset in a finite-set operation. The declared refinement and available evidence make its finite-set interface applicable, retaining the specified underlying-set comparison and original ambient inclusion. A backend list alone cannot provide this evidence. Two applicable refinements can coexist. |
| MM006 | Perform a calculation requiring a chosen basis, orientation or enumeration. An existence proof alone does not supply that choice. Subsequent calculations consume the actual selected data and their relation to the original object. |
| MM007 | Construct a limit or colimit and use a defining leg and universal factor in a later public operation. The maps come from its selected cone or cocone and satisfy its naturality and universal factorization equations. Distinct selected constructions sharing an apex keep their own maps. |
| MM008 | Execute the original lift and factor workflow, then use the returned object, defining map and comparison in subsequent functor actions. Verify the original equations with the required computational implementations and inputs. Equal formal expressions from distinct occurrences cannot substitute for the selected returned values. |
| MM009 | Execute a dependent construction with later fields consuming earlier results. Supply the actual values prescribed by its formal dependent interface. Another admitted record requires no construction-specific runtime case. |
| MM010 | Make the same selected public computation directly and through a deferred or provider request. Both paths preserve the same operation, parameters, comparisons and dependent inputs through common mathematical preparation. |
| MM011 | Add an independently authored category with immediate functors, then apply an unchanged target consumer. Add a generic operation and apply it to existing eligible objects. These extensions require no accommodation edits to old categories or leaves, respectively, under the C12 frozen-baseline procedure. |
| MM012 | Replace a computational provider while keeping the mathematical context fixed. Formal denotation remains fixed; different coverage or an incorrect answer remains an execution or correctness issue. The kernel does not compute an unpublished value by Lean reduction. |

Each scenario includes subsequent mathematical use where specified. The complete original
acceptance workload and independent assertions remain required. These scenarios do not authorize
candidate authors to author independent expected answers or reduce acceptance to finite examples.
