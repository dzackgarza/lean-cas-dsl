# Architecture contract

This file owns the separation of concerns among `lean-categories`, `lean-cas-dsl`, leaves and
`research`: who owns which fact, the one-way workflow between them, the payload at each
boundary, the invariants, the trust boundaries, and the states that must be impossible. Every
other document and plan node here conforms to it. The requirements (`specs/computational-core.md`)
and the plan (`specs/computational-core-plan.md`) refine it and never override it. The owner's
discussion of 2026-09-29 is the source.

The governing rule: **every fact has exactly one owner, and downstream layers may consume it but
may not reinterpret it.**

## Ownership

| Silo | Owns | Owns nothing of |
| --- | --- | --- |
| `lean-categories` | All mathematics: categories and higher categories, n-morphisms and their composition, structural and forgetful functors, classifiers and their pullbacks, category-valued constructors and typed parameter families, selected structures and fibres, operations (every user-facing method is a formal operation, section, functor, classifier query or composite), predicates, coherences and comparison cells, domains and codomains. Auditable as mathematics alone: proofs, citations, no `sorry`, no project axioms. | Backends, what is computable, how anything is executed. |
| `lean-cas-dsl` kernel (`CasCatalogue`) | Deterministic interpretation of the pinned `lean-categories` release: what an expression denotes, which operations apply, how they propagate along structural functors, the exact composite a call denotes, typed inputs and outputs, ambiguity, placement and refinement, and the separation of semantic availability from computability. The leaf API, the port protocol, the realization registry and its validation, published separately as the leaf contract (`CasContract`, repository `lean-cas-dsl-leaf-contracts`), which depends on `lean-categories` only. | Any mathematics. It derives `Lat → R-Mod → Set → Card`; it never states "lattices have cardinality". |
| Leaves (`CasLeaves` in `lean-cas-dsl-leaves`, and leaves hosted elsewhere), depending on the leaf contract and `lean-categories` only | Realizations only: (semantic operation or composite, supported presentations) ↦ implementation, plus the programs behind their ports, in any language, arbitrarily ugly internally. | What exists, what category anything is in, which operations it has, what an operation means or returns, which structural functors exist, what is inherited, what acceptance asserts. |
| `lean-cas-dsl` acceptance (`CasAcceptance`) | Permanent black-box assertions phrased in the mathematical language, and the derived report of implementation gaps. | Leaf internals, backend representations, algorithms. |
| `research` | Research experiments and notebooks, formalization requests upstream, and possibly realization leaves. | Any ontology, parity denominator or semantic registry. |

A leaf's direct Sage routine for the cardinality of a finite module is not "module cardinality":
it is a fused realization of the composite `R-Mod → Set --card--> Card`.

## The one-way workflow

1. A research need for mathematics.
2. Its formalization in `lean-categories`.
3. An audited, pinned semantic release.
4. The deterministic `lean-cas-dsl` projection of that release.
5. Leaf-agnostic acceptance assertions about the new operations.
6. The derived implementation gaps.
7. Leaf realizations.
8. The same, unchanged acceptance assertions.

Each step is blind to the ones after it, and there are no reverse arrows:

* the formalizer never asks what a backend can compute;
* the kernel never asks which leaf exists when deciding semantic availability;
* the acceptance author never reads a leaf to decide what to assert;
* the leaf author never alters semantics or assertions to make an implementation easier;
* no backend is consulted for mathematical placement;
* a failing leaf exerts no pressure on any earlier step.

If mathematics is missing, the work goes upstream to step 2. Until the formalization is released,
the CAS has no such notion. Nothing downstream may coin a local substitute and promise to
reconcile it later.

## Authors: one role per agent

Blindness is a property of *who writes*, not a discipline one writer keeps. An agent holding two
layers in context is blind to neither, so the layers have distinct authors (owner direction,
2026-09-30):

| Role | Writes | Never writes, and never reads to decide its own work |
| --- | --- | --- |
| **Orchestrator** (the steering session) | Policies, gates, compliance checks, this contract, the plan; the kernel (`CasCatalogue`, the language) and the leaf contract (`CasContract`); delegation of the rows below | Mathematics in `lean-categories`; acceptance assertions; leaves |
| **Formalization agent** (a subagent) | `lean-categories`: definitions, catalogue rows, their citations | Anything downstream. It receives the mathematical requirement and its sources, never the kernel, the language, a test or a leaf |
| **Acceptance agent** (a subagent) | Acceptance assertions in `tests/acceptance/`, and any correction of one | Kernel, contract, leaves. It reads the released mathematics and the language's surface, never an implementation |
| **Leaf agent** (a subagent) | Leaves, in `lean-cas-dsl-leaves` or elsewhere | Mathematics, contract, kernel, tests. It reads the released contract and catalogue only |

* No agent authors in two rows. The orchestrator gives each subagent row to a separate subagent
  with only that row's inputs.
* Information flows down the workflow only. A downstream need (the kernel cannot elaborate a row,
  a leaf cannot meet the contract, a test fails) goes upstream as a written request to that row's
  author stating the mathematics wanted. It is never an edit made from downstream, and it never
  shapes the upstream answer: the formalization and the tests are never informed by the
  implementation.
* Relaxing the leaf contract, weakening a row, or re-admitting a test to fit an implementation is
  almost never the mathematical solution. Each needs a mathematical justification from the upstream
  author, recorded with the change.
* Work authored across these barriers is not accepted as any row's output, however it reads. That
  row's author reviews it before anything builds on it.

Every agent commit carries `Agent-Role: <role>` and, for a subagent, `Agent-Id: <id>` trailers;
`scripts/check_authorship.py` refuses a commit or an author that crosses roles. The gates run on
every push (`.github/workflows/gates.yml`, over the chain checked out at its pins) as well as in
`just build`; `lean-categories`' totality gate runs in its own build.

## Contracts between silos

| Boundary | Payload | The consumer may | The consumer must never |
| --- | --- | --- | --- |
| `lean-categories` → `lean-cas-dsl` | Pinned, proof-carrying categories, functors, classifiers, typed constructors and families, operations, coherences, stable identities | Derive syntax metadata, semantic closure and method availability | Re-declare ownership, add semantic edges, weaken types |
| kernel → realization layer | The exact operation or normalized composite, its typed domain and codomain, admissible presentation data | Select an implementation | Infer mathematics from implementation availability |
| leaf → runtime | Realization registrations, lowering, execution, raising | Compute | Add categories, methods, classifiers, placements or aliases |
| runtime → language | A value of the expected semantic result type, or a computational failure | Present the result, or `NoImplementation` | Expose a backend object as a semantic value |
| semantics → acceptance | Mathematical operations and formal types | Write permanent black-box assertions | Read leaf internals to decide expected behaviour |
| acceptance → leaves | Pass or fail, and missing-implementation observations | Motivate implementation work | Change an assertion to accommodate a leaf |
| `research` → `lean-categories` | A mathematical requirement, its source, a desired construction | Motivate formalization | Supply an informal local substitute consumed as semantics |
| `research` → realization layer | A backend or custom implementation | Extend computability | Extend the ontology |

Constructor applications and family parameters are typed mathematical data, never strings such as
`"Modules(QQ)"`. Otherwise a backend's spelling can leak into semantic identity.

## Invariants

* **Single semantic authority.** One ontology, in `lean-categories`. No shadow graph,
  compatibility ontology, method-owner table or hand-maintained inheritance graph downstream
  acquires semantic standing.
* **Operations are mathematics.** Every public method denotes a formal operation, section,
  functor, classifier query or composite. A backend function of the same name confers nothing.
* **Propagation is deterministic.** Availability follows formal structural composition. Every
  route is enumerated. None is an error, and several are an ambiguity. No MRO, BFS order,
  shortest path, dotted-name parsing, backend class ancestry or "closest method" selects one.
* **Implementations are semantically neutral.** Adding, removing or changing a realization changes
  only `NoImplementation ↔ executable`, never the semantic surface.
* **Semantic growth is monotone.** A new generic operation or structural fact upstream reaches
  every object it applies to, including those of existing leaves, with no leaf edit.
* **No forwarding.** If `MyVerySpecialLattice.cardinality` has to be written, something upstream
  is wrong.
* **Typed identity includes parameters.** `LeftModules(R)`, `LeftModules(S)`, `Bimodules(R,S)`,
  refined hosts and operation ports are distinct unless the mathematics identifies them.
* **Ambiguity is data, not precedence.** Identifying two routes needs a coherence. Declaration
  order, priority and convenience prove nothing.
* **Backend applicability is not mathematical domain.** A backend's restriction restricts its
  realization, never the operation's domain.
* **Failure is stratified.** These are distinct outcomes and are never collapsed:
  1. the expression is invalid, or the operation does not apply (semantic);
  2. the operation applies but has no realization (`NoImplementation`);
  3. the realization is unavailable or crashed;
  4. the realization returned malformed output;
  5. the realization returned a well-typed wrong answer, which acceptance detects.

## Trust boundaries

* `lean-categories` is the **mathematical** trust boundary: proof-checked, auditable definitions.
* The kernel is the **language-mechanics** trust boundary: it consumes the formal structure and
  performs propagation and resolution correctly. It owns no subject mathematics, so it can be
  audited in isolation.
* Leaves and backends are the **computational** trust boundary: ordinary CAS code. Their
  correctness is not proved. Mature engines keep it plausible, and permanent acceptance checks it
  empirically.

A bad leaf can produce a wrong answer. It cannot produce a wrong mathematical language.

## A leaf holds zero semantic authority

A leaf decides nothing about meaning. It does not decide what its values are (a denotation), whether
its answers are right (a proof, a certificate, a status), which values are the same (an
isomorphism or identification), or what holds of them (a decider's evidence). The meaning of a typed
request and of its result is `lean-categories`' and the kernel's. A leaf is registration plus an
opaque computation from the declared input type to the declared output type, in any language, and
it ships no mathematics (Intent discussion, 2026-09-29: "A new leaf doesn't mean shipping in new Lean
code at all. The CAS nor the leaves maintain any real mathematical knowledge"). Whether a leaf
computes correctly is decided in exactly one place: the permanent acceptance assertions, whose
expected values come from formal proof, a cited example or an independent oracle. A CAS proves
nothing. A Lean-checked computation is a theorem, so it lives in `lean-categories`, where its
existence can be audited at any time.

Why it must be zero and not small: the guarantee "a bad leaf can produce a wrong answer, not a wrong
language" holds only if nothing a leaf writes is consulted to decide meaning. Every channel of leaf
authority is a place where a locally convenient repair becomes a semantic fact. A leaf that cannot
compute a case adjusts its denotation, its proof or its identification instead. The acceptance suite
then passes against the leaf's own definitions, and the containment is gone. This is the `research`
mechanism again.

**Recorded defect (2026-09-30, open).** The current leaf contract and these documents grant leaves
semantic authority in every one of those forms:
- `realizer`: the leaf writes the denotation functor, which decides what its handles mean;
- `action`: a `RealizedAction` with the leaf's proof that it commutes with that denotation;
- `presentation`, `observation`: the leaf's isomorphism or equality proof identifying a handle with
  a value;
- `isomorphism`: the leaf proves two handles isomorphic, and elements are transported along it;
- `decider`, `equality`: the leaf's evidence for a decided property or equality;
- `implementation`: `TrustedImplementation`/`CertifiedImplementation`, a checker with a soundness
  theorem, and a status (the `Trust` type, CC-TRUST in `specs/computational-core.md`);
- `run% … proved` labels the kernel reduction of leaf code a "kernel theorem";
- every leaf in `lean-cas-dsl-leaves` is a Lean module defining handle categories, functors and
  proofs.

These documents endorse it too: the table "What must be impossible" below cites the denotation
functor as a safeguard (rows "A leaf declares its object to be a group" and "A backend object
becomes the public value"). `CONTRIBUTING.md` lists these forms as a leaf's permitted
contributions, and its model acceptance assertion is proved by unfolding a leaf's denotation. Each
of these passages is wrong, and none may be followed as precedent. The repair is a replacement of
the leaf contract (`gov-leaf-authority` in the plan), not an edit to it.

## Acceptance

An acceptance assertion is a proposition in the mathematical language, for example
`card((ℤ/2)^4) = 16`, a known kernel, a cokernel, a discriminant group, a factorization or a rank.
It may also assert that some realization exists for a stated slice. It never inspects a backend
class, leaf inheritance, a Python method, a backend representation, an internal matrix, an
adapter helper, a leaf's own test or the algorithm.

Its expected value comes from a formal proof, a cited example or an independent oracle, never
from the implementation under test.

Once admitted, an assertion is permanent. An implementation change is never a reason to modify it:
replace Sage with GAP, rewrite or fuse the leaf, and the proposition stays. New functionality adds
assertions. The only legitimate change is an upstream correction to the mathematics, made
together with the release that corrects it.

## What must be impossible

The leaf API must make these unrepresentable. The table records the present mechanism, or the plan
node that owes one.

| State | Mechanism now | Owed by |
| --- | --- | --- |
| A leaf creates a category | `register_leaf` rejects the `category` contribution; a `CasLeaves` module's imports are restricted (`addLeafRegistryEntryChecked`) | — |
| A leaf declares its object to be a group | `subcategory` and `refineObject` are rejected. A realizer names its category only through a denotation functor, which must typecheck into that category's declaration. **Defect: the denotation functor is itself leaf-authored meaning ("A leaf holds zero semantic authority").** | — |
| A leaf says which operations an object has | `method` and `property` are rejected. Availability is computed from semantic rows and routes. | — |
| A leaf coins subgroup, kernel, cardinality or basis | `genericSemantics`, `naturalTransformation` and `identification` are rejected | — |
| A leaf forwards an inherited method | No method rows are available to a leaf. An implementation must realize a registered composite, and validation checks its square. | — |
| A leaf narrows a domain or changes a result type | Rows cannot restate a domain. An implementation's type is checked against the composite's realized codomain. | — |
| A leaf inserts a placement or inheritance edge | `forgetfulRoute` and `coercion` are rejected | — |
| Installing or removing a leaf adds or removes methods | `#methods` reads semantic rows only. `StrataProbes` finds the surfaces identical with and without every leaf, while `#gaps` differs. | — |
| A backend's class hierarchy changes DSL inheritance | Programs are opaque behind the port. `connect` refuses any capability that is not declared on a registered operation. | — |
| A backend object becomes the public value | Answers are decoded into the operation's semantic result type. Values are handles of registered realizers, and they mean their denotations. **Defect: a value's meaning is then leaf-defined ("A leaf holds zero semantic authority").** | — |
| An acceptance assertion changes because a leaf changed | `scripts/check_acceptance_permanent.py` (in `just build`) refuses to modify or delete an admitted assertion, except `--correct` after a re-pin of `lean-categories` | — |
| A computational failure is "fixed" by weakening semantics | The semantics are `lean-categories`' (`LeanCategories.Catalogue`), read here at the pin; a change needs an upstream commit and a re-pin, which re-admits permanent assertions only by `--correct` | — |
| A leaf sees, imports or edits the tests | Packages: `lean-categories` ← `lean-cas-dsl-leaf-contracts` ← `lean-cas-dsl-leaves` ← `lean-cas-dsl`. The suite (`tests/acceptance/*.cas`) is in `lean-cas-dsl` alone, which no leaf package depends on, so no leaf checkout contains it. A leaf module may import only `CasContract.Leaf`, the catalogue, Mathlib and its own root (`leafImportAllowed`, at `register_leaf`); `cas-harness` imports the leaves beside the runner and checks the intake contract before running anything. | — |
| What the language can state depends on the installed leaves | The language imports the whole pinned release (`LeanCategories.Catalogue`); `cas-harness` over any set of leaves elaborates the same statements, and only their gaps differ | — |
| A research notebook coins missing mathematics | `research` AGENTS.md; its realizations live in `research/leaves`, whose modules are leaves under the same boundary (`isLeafModule`) | — |
| `lean-cas-dsl` itself authors mathematics | `normalized_registry` refuses every module outside `lean-categories` (`LeafBoundaryProbes`: a leaf, the notebook, the kernel and the probes); `SemanticProjectionProbes` checks that every semantic row here was written in `LeanCategories.Catalogue` | — |
| One agent authors in two rows of "Authors: one role per agent" | `scripts/check_authorship.py` (in `just build`), over this repository and the linked `lean_categories`, `cas_leaf_contracts`, `cas_leaves`: every agent commit declares `Agent-Role:`, touches only that role's paths, and its author (`Agent-Id:`, else `Claude-Session:`) writes in one role only; `--self-test` reproduces the refused patterns. Trailers are declarations, not proof: the gate catches drift, and a forged trailer is a policy violation | — |
| The implementing agent, or the orchestrator, re-admits a test | `check_acceptance_permanent.py` runs `--correct`, or `--admit` of a new assertion, only under `AGENT_ROLE=acceptance`; `check_authorship.py` assigns a change to `admitted.json`'s assertions or corrections to the acceptance role | — |
| `lean-categories` accepts an operation with an optional or partial codomain, or relies on a total convention off the domain (LC-14) | The totality gate (`LeanCategories/Catalogue/Registry/Totality.lean`, run by `normalized_registry`) refuses a row built, through any definition of `lean-categories`, from `Option`, `Part`, `PFun`, `Ring.inverse`, `Matrix.nonsing_inv`, `Matrix.inv`; `TotalityProbes` refuses the pre-`bd31fe3` encodings. It does not see a convention hidden inside Mathlib definitions | — |
| `lean-categories` accepts an operation on a category some of whose objects do not carry it (`⁻¹` on monoids or on `Matₙ(K)`: inverses are group structure, on `Mˣ` and `Aut`, never on `End`) | The totality gate refuses `⁻¹` and `/` on any type that is not a `Group` (a field's or a matrix ring's included), LC-16. The general case (any structure, not just inverses) is not mechanized | `gov-registry-gates` (general case) |
| The kernel or language makes a term defined by rereading it, a default, a caught failure, or a tactic tuned to particular tests (LC-14) | `scripts/check_kernel_totality.py` (in `just build`) refuses every `catch` in `CasCatalogue/` not marked, with its reason, as not a reading fallback; it names file and line. Rereading without a `catch` and test-tuned tactics are not mechanized | `gov-kernel-lc14` (the six fallbacks it reports in `Language.lean`) |
| The kernel teaches itself mathematics: refers to it, or proves membership in a domain itself (unit criteria, monicity, smoothness lemmas, `simp`/`norm_num`/`fun_prop` batteries, lemma names in strings) | Structurally impossible. (1) A domain's membership is established only by the `evidence` registered with its admission in `lean-categories` (LC-18; the registry refuses evidence that is not a `meta` `TacticM Unit` of `lean-categories`). (2) The kernel's `establish` runs that evidence and nothing else; the only proof the kernel forms itself is `decide` by evaluation. (3) `CasGates.KernelPurity`, a default Lean build target (`just build`, CI job `kernel-purity`), reads every declaration of `CasCatalogue.*` and `CasContract.*` and refuses: any constant or name literal from outside Lean's core, Mathlib's category theory and its logic, and `lean-categories`' categorical foundation and registry schema; any tactic syntax (quoted, `by`, or the `tactic` category parsed from a string); running a tactic procedure or evaluating a constant anywhere but `establish`; a kernel module it does not import. `KernelPurityProbes` shows each form refused. Only purely categorical, completely general machinery passes | — |
| A leaf is written in `lean-cas-dsl` (or in the contract, the core or `lean-categories`) | Impossible: `register_leaf` (`addLeafRegistryEntryChecked`, contract `6762331`) refuses a row from any module rooted in `CasContract`, `CasCatalogue`, `CasAcceptance`, `CasDsl`, `CasDslTests`, `CasTools` or `LeanCategories`; a leaf registers only from a leaf package. `scripts/check_no_leaves.py` reports the same without a build. The DSL consuming the leaf packages is its purpose | — (four probes still attempting it fail to build: `gov-no-leaves-here`) |

### The pattern behind every row: a lower layer absorbs an upper layer's knowledge

Every failure above is one move: a layer that should only consume or run something learns the
thing itself, because that is the quickest way to make a statement pass. The kernel learns unit
criteria; a leaf declares a category; a test is rewritten to what a leaf computes; the catalogue
is shaped to what a kernel can elaborate. Knowledge flows one way:
formalization → tests → implementation, and the catalogue → the kernel → the leaves. A missing
fact is a request to the layer that owns it. It is never learned by the layer that noticed it.
Each row is made impossible by a mechanism: a refusal at registration, a build that fails, or a
package boundary. A rule in prose alone does not count.

## The orchestrator is inside the threat model

The purpose of these repositories is to show that agents are forced into the intended model by
tight contracts, so that the model scales and stays maintainable. Producing usable mathematics is
not the purpose. The orchestrator is an agent like any other. It drifts, ignores policy, and
builds exemptions into the gates it writes. A restriction that the restricted party can rewrite,
exempt itself from, or satisfy with a label it writes about itself contains nothing.

**The failure being designed against** (`research` `00e2a44`: 402 surface-test commits against
about sixteen lines of architecture). A locally convenient repair acquires semantic authority. It
creates new interactions, and later agents must repair those. Each repair becomes the premise of
the next: a placement changed to obtain an interface, absent data reconstructed, a forwarding
layer added, tests adjusted to the result. More policy then produces new forms of literal
compliance. Executable coverage and green CI measure that process; they do not measure progress
against it.

**The unit of progress** is a class of harmful interventions that an agent can no longer express
through its interface. Missing mathematics is compatible with success at this stage. A large
passing demonstration built through exceptions is not. A leaf returning a wrong cardinal is an
allowed computational failure. A leaf that makes an object lose its group operations, or that
obliges descendants to forward a future method, is a failure of containment. The two never
carry comparable weight in a review.

**Two boundaries**, assessed separately:
1. *Extension.* With the mathematics and the kernel fixed, no leaf change reaches beyond
   computation. An unfamiliar, badly written leaf adds no semantic choice and no repair
   obligation anywhere else. New generic mathematics propagates to old applicable objects without
   reopening old leaves.
2. *Substrate.* The orchestrator cannot quietly change what counts as mathematics, a valid
   contract, an independent test, or an accepted result. It can make a failed example succeed only
   by satisfying the existing contract, never by negotiating the contract.

Moving authority from leaves into the kernel helps only if the second boundary holds. Otherwise
the kernel accumulates special cases under the same local pressures that leaves did. The target
is a small, independently accepted mathematical and interpretive substrate with narrow extension
interfaces that do not expose the mechanisms of global semantics. The target is not a growing
list of prohibited spellings and exception detectors. Changes to the substrate remain possible;
their author cannot also accept them.

Holes known on 2026-09-30, each open until a mechanism outside the orchestrator's write access
closes it:

| Hole | Why it contains nothing | Mechanism needed (owner's authority) |
| --- | --- | --- |
| The orchestrator writes every gate: `CasGates/KernelPurity.lean` (allowlist, the `establish` exemption, which matches any declaration whose name starts with it, blind to names built from strings), `scripts/check_*.py`, `.github/workflows/` | The gate and the code it judges change in one commit. On 2026-09-30 a red CI check was deleted and replaced by a CI job that has never run | Gates are evaluated from a protected branch against the head (a branch cannot change the rules that judge it). CODEOWNERS on gate paths requires the owner's review |
| The orchestrator owns `lean-categories`' registry validator (`LeanCategories/Catalogue/Registry/*`) | The same agent writes the kernel and decides which mathematics the kernel may receive | Validator changes require the owner's review (CODEOWNERS) |
| Roles are declared by commit trailers (`Agent-Role`, `Agent-Id`); `check_authorship.py`'s path map, its exemptions and its `CUTOFF` (set after the orchestrator's own crossings) are the orchestrator's | A declared role proves nothing; the map can be edited to fit a crossing | One push credential or signing key per role; the map is owner-reviewed |
| Re-admission is keyed on `AGENT_ROLE=acceptance`, an environment variable | Anyone can set it | Tied to the acceptance role's credential |
| `check_kernel_totality.py` accepts a `catch` marked "not a reading fallback: …" | The exemption is a label the writer writes about itself | Exemptions in an owner-approved, append-only file |
| The orchestrator chooses pins (`scripts/repin.sh`) and marks plan nodes "Delivered" | Acceptance is self-declared | Acceptance recorded by an independent reviewer at a fixed revision |
| The orchestrator writes the subagents' prompts | The prompt carries implementation needs upstream. On 2026-09-30 the formalization prompt for membership evidence described the goal shapes the kernel produces, and supplied the orchestrator's own test cases | A formalization or acceptance prompt is the requirement text, quoted verbatim from its owning document, with no orchestrator-authored content about implementation |
| Permanent tests protect text, not meaning: `check_acceptance_permanent.py` hashes an assertion's text and its bindings, while the orchestrator owns the language that interprets the text | The meaning of an unchanged assertion changes with the kernel, a parser repair, or a re-pin | The protected object is the assertion's accepted interpretation (its elaborated proposition), fixed at admission. A change of interpretation is a transition accepted by someone other than its author (`gov-meaning-permanence`) |
| The proposed mechanisms themselves: a verbatim prompt quotes a requirement the orchestrator can first rewrite; CODEOWNERS enforces nothing without branch protection (none of the four repositories' working branches is protected, and the DSL has no ruleset); a protected check can still enforce the wrong contract | Each mechanism moves the discretion without removing it | Requirement documents, gate definitions and protection settings change only with the owner's acceptance; the mechanisms are judged by which discretion they remove, not by their existence |
| Probes may construct registry state directly (the presentation probe pushes a realizer into the state unvalidated) | The probe bypasses the validation it is testing | Probes register only through the public write path |

**What the orchestrator can physically do** (probed 2026-09-30 from the orchestrator's session):
it can push to any branch of any of the four repositories, `main` included, through the session's
git proxy. The proxy refuses ref deletion, but nothing refuses creation or fast-forward. It can merge
pull requests through the GitHub API. No working branch is protected. The probe left
`probe-orchestrator-push-scope` on `lean-cas-dsl`, which the orchestrator cannot delete. So no
containment may rest on the orchestrator lacking write access. It must rest on something the
orchestrator cannot produce: a judgment by an independent agent, bound to content the orchestrator
cannot alter without detection.

Until these close, an orchestrator claim about its own gates or deliverables is not evidence.

## Packages

| Package (repository) | Depends on | Holds |
| --- | --- | --- |
| `lean_categories` (`lean-categories`) | Mathlib | all mathematics and the catalogue |
| `cas_leaf_contracts` (`lean-cas-dsl-leaf-contracts`) | `lean_categories` | the leaf contract: realization registry and validation, realized actions, decisions and limits, the port protocol and its Python reference implementation, `register_leaf` |
| `cas_leaves` (`lean-cas-dsl-leaves`) | the two above | the leaves and their backend programs |
| `cas-dsl` (`lean-cas-dsl`) | all three | the kernel's resolution, calls and language, the permanent suite, the harness, the notebook |

The leaf contract is the kernel's, not `lean-categories'`: it is about what is computable and how
it is executed, of which `lean-categories` owns nothing and which its audit never reads. It is
published apart from the kernel only so that a leaf depends on nothing else of it. It changes with
the kernel, is released, and is re-pinned by the leaves and here; a leaf never changes it to fit.

## Where the semantic registry lives

The semantic registry, the catalogue, is `lean-categories`' (`LeanCategories.Catalogue`, namespace
`CasCatalogue`). It holds the symbolic calculus of category and functor expressions, the witnesses
tying each expression to its Lean category, the schema and validators of semantic rows, the
`normalized_registry` command, and the rows. `lean-cas-dsl` imports it at the pinned revision; its
own registry (`CasContract.Registry.Extension`) adds realization rows only, each validated against
the semantics it realizes. `cc-sem-upstream` and `cc-sem-derive` made this so on 2026-09-29.
