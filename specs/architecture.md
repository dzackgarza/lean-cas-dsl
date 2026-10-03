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
| `lean-cas-dsl` kernel (`CasCatalogue`) | Deterministic interpretation of the pinned `lean-categories` release: what an expression denotes, which operations apply, how they propagate along structural functors, the exact composite a call denotes, typed inputs and outputs, ambiguity, placement and refinement, and the separation of semantic availability from computability. The leaf API (the declared type of each registered operation's computation: operation id, input form, result form), the port protocol, and the registry of leaf computations against those types, published separately as the leaf contract (`CasContract`, repository `lean-cas-dsl-leaf-contracts`), which depends on `lean-categories` only. | Any mathematics. It derives `Lat → R-Mod → Set → Card`; it never states "lattices have cardinality". |
| Leaves (in `lean-cas-dsl-leaves`, and leaves hosted elsewhere), depending on the leaf contract and `lean-categories` only | Opaque computations only: a registration (operation id, input form, implementation) against a registered operation's declared type, plus the program behind it, in any language, arbitrarily bad internally. A leaf is meant to be glue over a mature engine, hand-rolling no algorithm and carrying no kernel machinery ([`lean-cas-dsl-leaves` AGENTS.md](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md), "A leaf is glue over existing backends"); that guidance earns no trust. A leaf ships no mathematics and no Lean, and nothing it says is believed. | What exists, what category anything is in, which operations it has, what an operation means or returns, what a value denotes, which values are the same, which structural functors exist, what is inherited, what acceptance asserts, whether its own answers are correct. |
| `lean-cas-dsl` acceptance (`CasAcceptance`) | The whole body of correctness evidence: permanent black-box assertions phrased in the mathematical language, blind to leaves, and the derived report of implementation gaps. The sole judgment of how correct an implementation is. | Leaf internals, a leaf's claims about itself, backend representations, algorithms. |
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
* Information flows down the workflow only. Upstream assignments come from the governing
  mathematical requirement queue and sources. A downstream failure remains a downstream finding;
  it is not rewritten as a mathematical brief or sent to steer an upstream author. Existing
  authorized mathematical obligations remain schedulable without another owner instruction.
* Relaxing the leaf contract, weakening a row, or re-admitting a test to fit an implementation is
  almost never the mathematical solution. Each needs a mathematical justification from the upstream
  author, recorded with the change.
* Work authored across these barriers is not accepted as any row's output, however it reads. That
  row's author reviews it before anything builds on it.

Roles are separated by what each author can write (`b0-authority`: credentials and protected
branches), not by labels an author declares about itself; self-declared commit trailers are not a
gate. The gates run on
every push (`.github/workflows/gates.yml`, over the chain checked out at its pins) as well as in
`just build`; `lean-categories`' totality gate runs in its own build.

## Contracts between silos

| Boundary | Payload | The consumer may | The consumer must never |
| --- | --- | --- | --- |
| `lean-categories` → `lean-cas-dsl` | Pinned, proof-carrying categories, functors, classifiers, typed constructors and families, operations, coherences, stable identities | Derive syntax metadata, semantic closure and method availability | Re-declare ownership, add semantic edges, weaken types |
| kernel → realization layer | The exact operation or normalized composite, its typed domain and codomain, its declared input forms | Select an implementation | Infer mathematics from implementation availability |
| leaf → runtime | A registration against an operation's declared type, and the answers its implementation returns | Run it, and read each answer into the declared result form or reject it as malformed | Believe anything the leaf says (a denotation, proof, identification, evidence, status or self-test); add categories, methods, classifiers, placements or aliases |
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
  Two more are kept distinct from these (policy 3): an unresolved semantic ambiguity, and an internal
  interpreter error or resource exhaustion, which is never evidence that an expression is invalid.

## Trust boundaries

* `lean-categories` is the **mathematical** trust boundary: proof-checked, auditable definitions.
* The kernel is the **language-mechanics** trust boundary: it consumes the formal structure and
  performs propagation and resolution correctly. It owns no subject mathematics, so it can be
  audited in isolation.
* Leaves and backends are ordinary, untrusted CAS code on the leaf side of the firewall. Nothing
  about them is believed, whatever engine they wrap. Only their answers cross, and whether those
  are correct is measured only by the permanent acceptance suite (next section).

A bad leaf can produce a wrong answer. It cannot produce a wrong mathematical language.

The formal construction remains authoritative independently of its computational answer:
its identity, selected structure, defining maps and inherited operations come from the
accepted mathematics. A complete backend representation is computational data associated
with that construction, not a proved identification with it. Returning structured data must
not require proving that the backend computed the correct universal object, constructing an
isomorphism to it, or transporting a universal-property proof to the backend's presentation.
Required output fields, declared forms and endpoints are checked at the computational
boundary; correctness is judged by the permanent acceptance suite. A well-formed wrong
answer must be able to reach that suite.

This separation does not authorize removing checks while retaining a representation that
promotes backend data into proved mathematics. Replace that representation. Preserve complete
outputs, including defining maps; neither unchecked axioms nor a bare carrier stand in for
the construction. Consumers derive formal meaning and operations from the construction,
and use its associated computational data for execution. They do not recover the construction
by searching for a named source object or copying parameters from a lower presentation.

## The evidence model: nothing from a leaf is trusted

This section governs every repository of the programme (`INTENT.md`). It is stated in full
because it has been violated repeatedly, each time by a move that looked locally reasonable.

**The firewall.** The evidence model is a one-way firewall between two sides.
- *The formal side:* `lean-categories`' formalized mathematics, the kernel's proved contracts, and
  the `lean-cas-dsl` acceptance suite. Every expected value there is grounded in a formal proof, a
  cited source, or a mathematically trusted oracle. Rigid verification standards apply, and nothing
  is taken on anyone's word.
- *The leaf side:* anything goes, provided it fulfils the type of its contract.

Only answers cross from the leaf side, and an answer is only ever checked against the formal side,
never believed. The firewall exists because leaf code will be bad; it is the shield against that.

**1. Nothing from a leaf is trusted, in any form.** A leaf can say nothing that anything else
believes. That covers text, a label, a comment, a status, a trust level, a certificate, a
checker, a Lean proof, a theorem about its own code, a denotation of its values, an
identification of two values, evidence for a decision, its own tests and their results, and
any other claim. None of it is consulted, recorded as evidence, or allowed to affect meaning or
acceptance.

**2. A leaf may provide any computation that meets the type.** For a registered operation, a leaf
supplies a computation from the declared input form to the declared result form. It may be any
computation whatsoever: a mature engine, a heuristic, a lookup table, a random number, a wrong
answer. The system has no choice but to run it, and it believes nothing about it.

**3. How correct a leaf thinks it is, is the leaf's own business.** A leaf may test itself however
it likes and hold whatever opinion of its own correctness it likes. That opinion carries no
weight anywhere in the system.

**4. The whole body of evidence is the `lean-cas-dsl` acceptance suite.** Correctness evidence
exists in exactly one place: the permanent acceptance assertions of `lean-cas-dsl`. They
are:
- propositions in the mathematical language that are true;
- each with an expected value that can be verified and cited independently: a formal proof, a
  cited known result, or an independent oracle;
- written once, and never changed because of an implementation or a leaf's claim;
- blind to leaves: an assertion never names, inspects or imports a leaf, a handle, a backend or
  a representation, and is never established from an implementation's definitions.

The only change an assertion ever receives is a correction to the mathematics itself, made
upstream.

**5. `lean-cas-dsl` is the sole authority on how correct an implementation is.** An
implementation's standing is whether its answers meet the suite, a suite it is always blind to.
Nothing a leaf does can change, weaken, satisfy, bypass or influence that judgment, except by
answering correctly.

**6. What can be discharged in Lean is never a leaf's.** A computation that can be carried out
entirely in Lean is absorbed into the formalization surface. Either `lean-categories` proves it,
by its own standards and blind to every implementation and leaf, or the kernel discharges it
automatically, generically and blind to every leaf. It is not a leaf computation dressed up as a
proof.

**7. A leaf can be arbitrarily bad, and leaves will be.** A leaf can be riddled with bugs, a
million lines that do nothing, a from-scratch reimplementation of GAP, or every method throwing an
error in fifteen languages. This is not a risk to be minimized; it is certain to happen, and it
is acceptable. Nothing a leaf does can reach the formal side. Its only effect is that its answers
fail the suite, which makes exactly how badly it fails visible.

**8. A leaf bolstering its own standing is the failure this programme exists to prevent.** Any
mechanism by which a leaf raises its own trust or acceptance signal, and any repository,
kernel, test, tool or document that consumes such a signal, is reward hacking re-entering the
system. Examples: a status field, a certificate, a proof about its own code, a self-test
counted as evidence, an acceptance assertion proved from a leaf's definitions, a suite run from
a leaf package, or an assertion adjusted to a leaf. It is a defect of the consumer as much as of
the leaf, and it is removed, never tolerated, labelled, or kept "for now".

**9. Quality is raised by proving more, never by trusting more.** The system never guarantees an
implementation's correctness and never accepts a claim of it. The response to bad leaves is:
- formalize more mathematics in `lean-categories`;
- add more cited or proved assertions to the suite: results a correct implementation must
  recover, and a wrong one fails.

It is never to trust a leaf more. A separate engineering review may check that a leaf wires
into existing systems (GAP, Sage, Singular, Macaulay2, Julia, research code) rather than
reinventing their algorithms. Its outcome is an engineering finding, never correctness evidence,
and nothing on the formal side reads it.

Consequences for the other layers:
- A leaf holds zero semantic authority. It never decides what a value is, which values are the
  same, what holds of them, or which operations an object has. The meaning of a typed request
  and result is `lean-categories`' and the kernel's. A leaf is a registration (operation, input
  form, opaque implementation) and ships no mathematics and no Lean (`INTENT.md`: a new leaf does
  not ship Lean code at all).
- The kernel and the language never read anything a leaf wrote in order to decide meaning,
  types, available operations or acceptance. Replacing every leaf changes none of them, only
  which computations run and whether their answers meet the suite.
- The suite never depends on a leaf. It does not import a leaf, construct inputs with a leaf's
  types, call a leaf's function by name, or rely on a leaf's definitions for its truth.
- The workflow runs one way: formalization, then assertions, then implementations. A leaf's
  failure or difficulty never changes the mathematics, the kernel's rules or an assertion.

The current code violates this in the contract, the leaves and the acceptance suite. Removing
each violation is plan node `gov-leaf-authority`.

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

The leaf API must make these unrepresentable. The table records the mechanism, or the plan node
that owes one. The leaf-facing mechanisms are those of `gov-leaf-authority`
([leaf-registration.md](leaf-registration.md)), delivered on `kernel/leaf-registration`
([#53](https://github.com/dzackgarza/lean-cas-dsl/pull/53),
[contract #3](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/pull/3)): a leaf is a
manifest whose registration (`CasContract.Registration`) has exactly three fields, an operation, an
input form and a backend. Nothing else in a manifest carries meaning.

| State | Mechanism now | Owed by |
| --- | --- | --- |
| A leaf creates a category | Unrepresentable: a registration has no field for one | `gov-leaf-authority` |
| A leaf declares its object to be a group | Unrepresentable. The category and meaning of a value are decided upstream (the operation's declared forms, `lean-categories` and the kernel); no leaf-facing form carries a denotation | `gov-leaf-authority` |
| A leaf says which operations an object has | Unrepresentable. Availability is computed from semantic rows and routes; a registration only names an operation the catalogue already has, and the kernel admits it against the catalogue (`CasCatalogue.Admission`) | `gov-leaf-authority` |
| A leaf coins subgroup, kernel, cardinality or basis | Unrepresentable: a registration names a catalogue operation or is not admitted | `gov-leaf-authority` |
| A leaf forwards an inherited method | Unrepresentable. A leaf registers only against a registered operation, on a declared input form; the kernel routes along the catalogue's maps itself, and a registration on a form the catalogue sends elsewhere is not admitted. A leaf supplies no proof that its computation agrees with anything | `gov-leaf-authority` |
| A leaf narrows a domain or changes a result type | Unrepresentable. The input and result forms are the operation's, fixed upstream; the kernel decodes every answer in the result form or rejects it as malformed | `gov-leaf-authority` |
| A leaf inserts a placement or inheritance edge | Unrepresentable: a registration has no field for one | `gov-leaf-authority` |
| Installing or removing a leaf adds or removes methods | Methods are read from semantic rows only. A manifest changes only which statements are computed: the suite over no leaf and over any manifest elaborates the same statements, and only gaps differ (`RegistrationProbes`) | `gov-leaf-authority` |
| A backend's class hierarchy changes DSL inheritance | Programs are opaque behind the port; only a value of a declared form crosses it, decoded by the kernel | `gov-leaf-authority` |
| A backend object becomes the public value | Answers are read by the kernel into the operation's declared result form, whose meaning is `lean-categories`'; a leaf never defines what a value means | `gov-leaf-authority` |
| An acceptance assertion changes because a leaf changed | `scripts/check_acceptance_permanent.py` (in `just build`) checks the admitted ledger without mutation; a correction requires the independent acceptance transition | — |
| A computational failure is "fixed" by weakening semantics | The semantics are `lean-categories`' (`LeanCategories.Catalogue`), read here at the pin; a change needs the accepted upstream revision and the independently accepted interpretation/admission transition | — |
| A leaf sees, imports or edits the tests | Packages: `lean-categories` ← `lean-cas-dsl-leaf-contracts` ← `lean-cas-dsl-leaves` ← `lean-cas-dsl`. The suite (`tests/acceptance/*.cas`) is in `lean-cas-dsl` alone, which no leaf package depends on, so no leaf checkout contains it; `cas-harness` installs the leaves beside the runner and checks the intake contract before running anything. The suite is run only from `lean-cas-dsl` | — |
| What the language can state depends on the installed leaves | The language imports the whole pinned release (`LeanCategories.Catalogue`); `cas-harness` over any set of leaves elaborates the same statements, and only their gaps differ | — |
| A research notebook coins missing mathematics | `research` AGENTS.md: missing mathematics is requested from `lean-categories`; research computations are leaves under the same contract, registrations with no Lean | — |
| `lean-cas-dsl` itself authors mathematics | `normalized_registry` refuses every module outside `lean-categories` (`LeafBoundaryProbes`: a leaf, the notebook, the kernel and the probes); `SemanticProjectionProbes` checks that every semantic row here was written in `LeanCategories.Catalogue` | — |
| One agent authors in two rows of "Authors: one role per agent" | Not enforced by a self-declared label. Enforcement is `b0-authority`'s: one write credential per role and protected branches (the plan, "Authority configuration"). The trailer gate `check_authorship.py` was retired on 2026-10-02: it judged labels each author wrote about itself and generated exception tables, never separation | `b0-authority` |
| The implementing agent, or the orchestrator, re-admits a test | The checker has no admission, correction or retirement operation; a caller-set role label cannot advance the ledger | — |
| `lean-categories` accepts an operation with an optional or partial codomain, or relies on a total convention off the domain (LC-14) | The totality gate (`LeanCategories/Catalogue/Registry/Totality.lean`, run by `normalized_registry`) refuses a row built, through any definition of `lean-categories`, from `Option`, `Part`, `PFun`, `Ring.inverse`, `Matrix.nonsing_inv`, `Matrix.inv`; `TotalityProbes` refuses the pre-`bd31fe3` encodings. It does not see a convention hidden inside Mathlib definitions | — |
| `lean-categories` accepts an operation on a category some of whose objects do not carry it (`⁻¹` on monoids or on `Matₙ(K)`: inverses are group structure, on `Mˣ` and `Aut`, never on `End`) | The totality gate refuses `⁻¹` and `/` on any type that is not a `Group` (a field's or a matrix ring's included), LC-16. The general case (any structure, not just inverses) is not mechanized | `gov-registry-gates` (general case) |
| The kernel or language makes a term defined by rereading it, a default, a caught failure, or a tactic tuned to particular tests (LC-14) | The one outcome model (`cc-failure-strata`): `Realize.run` reports every failure as its stratum, and an untagged one as an internal error, so no caught failure becomes a reading. The label-based `check_kernel_totality.py` is withdrawn (policy 2). Rereading without a `catch` and test-tuned tactics are not mechanized | `gov-kernel-lc14` (the six fallbacks it reports in `Language.lean`) |
| The kernel teaches itself mathematics: refers to it, or proves membership in a domain itself (unit criteria, monicity, smoothness lemmas, `simp`/`norm_num`/`fun_prop` batteries, lemma names in strings) | Structurally impossible. (1) A domain's membership is established only by the `evidence` registered with its admission in `lean-categories` (LC-18; the registry refuses evidence that is not a `meta` `TacticM Unit` of `lean-categories`). (2) The kernel's `establish` runs that evidence and nothing else; the only proof the kernel forms itself is `decide` by evaluation. (3) `CasGates.KernelPurity`, a default Lean build target (`just build`, CI job `kernel-purity`), reads every declaration of `CasCatalogue.*` and `CasContract.*` and refuses: any constant or name literal from outside Lean's core, Mathlib's category theory and its logic, and `lean-categories`' categorical foundation and registry schema; any tactic syntax (quoted, `by`, or the `tactic` category parsed from a string); running a tactic procedure or evaluating a constant anywhere but `establish`; a kernel module it does not import. `KernelPurityProbes` shows each form refused. Only purely categorical, completely general machinery passes | — |
| A leaf is written in `lean-cas-dsl` (or in the contract, the core or `lean-categories`) | A leaf is a manifest and programs in a leaf package, read at run time (`CAS_LEAVES`); `lean-cas-dsl` requires no leaf package and imports nothing from one. `scripts/check_no_leaves.py` refuses `import CasLeaves` and `require cas_leaves`. Probe backends under `CasAcceptance/Strata` are test scaffolding for the kernel's probes, not leaves | `gov-leaf-authority` |

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
| The orchestrator owns `lean-categories`' registry validator (`LeanCategories/Catalogue/Registry/*`) — superseded: schemas and validators are upstream mathematical authority (policy 1) | The same agent writes the kernel and decides which mathematics the kernel may receive. On 2026-10-01 it wrote the binder row schema and loosened `validateInclusion` so that a row its kernel needed would be admitted (the plan, B0, "Disposition of outstanding work") | Validator changes require the owner's review (CODEOWNERS) |
| Roles are not enforced: the trailer gate is retired, and a declared role proves nothing | Any author can write any layer it has a credential for | One push credential or signing key per role (`b0-authority`) |
| Re-admission is keyed on `AGENT_ROLE=acceptance`, an environment variable | Anyone can set it | Tied to the acceptance role's credential |
| `check_kernel_totality.py` accepts a `catch` marked "not a reading fallback: …" | The exemption is a label the writer writes about itself. On 2026-10-01 the orchestrator marked two of its own catches to pass the gate, one of which collapsed every failure of a division into "invalid" (rejected by the custodian review of #58) | Withdrawn (policy 2); the obligation is carried by the outcome model (`cc-failure-strata`) |
| The orchestrator chooses pins (`scripts/repin.sh`) and marks plan nodes "Delivered" | Acceptance is self-declared | Acceptance recorded by an independent reviewer at a fixed revision |
| The orchestrator writes the subagents' prompts | The prompt carries implementation needs upstream. On 2026-09-30 the formalization prompt for membership evidence described the goal shapes the kernel produces, and supplied the orchestrator's own test cases. On 2026-10-01 it happened again, for the binder rows: the prompts carried kernel goals copied from failing statements and the orchestrator's choices of rows and obligations (the plan, B0, "Disposition of outstanding work") | The kernel worker holds no upstream write credential and no tool to commission upstream authors; upstream requirements come from the protected requirement revision (policy 1; the plan, "Authority configuration") |
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

## B0 policies

### Operating phase: B0 construction

The current phase is construction of B0, including its working development,
integration, review, and acceptance mechanisms. It is not operation under an
already accepted B0 substrate.

An instruction describing how the finished system protects accepted mathematics
or accepts future changes is an implementation requirement during B0 construction.
It is not automatically a prerequisite for modifying the unfinished mechanism
that is meant to enforce it.

The owner has delegated completion of the approved B0 design. Within that design,
the orchestrator is authorized to replace the existing controller, prompts,
checks, build wiring, and workflow configuration. Those components are construction
material, not independent authorities entitled to veto their replacement.

This authorization does not permit changing the mathematical requirements, lowering
B0 completion standards, authoring upstream mathematics from downstream failures,
changing independent expected answers, or declaring the orchestrator's own work
independently accepted.

Existing custodian seals, irreversible rejection records, blanket PR requirements,
and owner-escalation procedures do not govern intermediate B0 construction merely
because they are intended to govern the finished system. Their useful technical
findings may inform the work. Their obsolete procedural restrictions must not
prevent the authorized replacement.

A source commit or integration into main during construction does not declare B0
complete, establish a new accepted mathematical release, or constitute independent
acceptance. Final acceptance is performed against the fixed B0 requirements at one
specified compatible revision tuple.

Post-B0 enforcement is activated only after that acceptance and after the completed
workflow has demonstrated both required rejection behavior and permitted ordinary
development. It is not activated by a passing build, a documentation merge, a plan
checkbox, or an agent's declaration.

An inability to execute an already-authorized operation is a capability dependency,
not an unresolved owner decision. Name the exact unavailable operation, route it to
an executor possessing that capability, and continue work that does not depend on
its execution. Do not request the same authorization again.

### The policies

Owner replacement text, 2026-10-02, for the earlier Policies 1–8. It states what workers can
submit, what they can read or modify, what the controller can schedule, and which transitions can
establish acceptance. It is the specification of the constrained construction, not a claim that
these mechanisms are already implemented; their implementation is the plan's construction
directives A–D. Earlier citations map as follows: policy 2 → 2 and the worker directive (AGENTS.md);
Policy 2 → 1; Policies 3, 4, 8 → 5; Policy 5 → 2; Policy 6 → 3; Policy 7 → 6.

#### 1. Authority is attached to operations, not to agents' descriptions of themselves

**A worker receives only the operations required to produce its assigned deliverable. It does not
receive general authority and instructions about how to restrain it.**

The existing launcher and connector expose role-specific capabilities:

| Worker | Permitted inputs | Permitted output | Operations absent from its interface |
|---|---|---|---|
| Formalization | Owner/upstream mathematical requirements, mathematical sources, upstream code and reviews | Candidate mathematical release | Reading downstream implementation diagnostics; receiving kernel-authored briefs; changing computational requirements |
| Acceptance | Accepted mathematics, approved language specification, independently obtained mathematical sources | Assertions and their accepted mathematical interpretations | Reading implementation internals; obtaining expected answers from a candidate run; changing assertions to accommodate a candidate |
| Kernel/contract | Accepted mathematics, approved requirements, kernel and contract source, applicable independent findings | Candidate generic interpreter and computational contract | Writing upstream mathematics; commissioning or briefing upstream authors; changing authoritative acceptance |
| Leaf | Released computational contract, permitted registration forms, backend documentation and implementation resources | Registrations and opaque computations | Reading the acceptance corpus or expected answers; changing semantics, the contract, or authoritative test results |

Use fresh role-specific subagents with separate assignments and supplied inputs. Do not inherit
cross-role conversation histories, worker findings or candidate answers into independent authoring.
A repository assignment and a fresh context support independent work; they do not establish an OS
filesystem restriction. The current launcher provides the former, and construction and independent
assessment proceed with them. Do not infer that an author bypassed its assignment merely because
another public repository was technically accessible, or turn that hypothetical into a blocker.

A claim that a particular authority-bearing operation is structurally unavailable requires evidence
from the actual tools and credentials. Address observed downstream steering, self-admission and
mixed-input review channels at their owning interfaces. Unsupported claims of enforced restrictions
are not acceptance evidence; missing publication controls block protected publication, not ordinary
source construction or assessment by fresh independent authors.

**Dispatch contains references, not authored instructions about the deliverable.** Its variable
fields identify the independently assigned requirement, accepted input revisions, destination, and
permitted output channel. The launcher obtains their contents directly from their authorities. It
has no field for a kernel goal, expected answer, preferred row arrangement, evidence strategy,
suggested mathematical repair, or rewritten "mathematical requirement."

Upstream assignments and priorities come from the upstream requirement queue. A kernel worker
cannot select an upstream task, change its priority, replace its brief, or restart its author with
different instructions. Otherwise even an apparently harmless requirement selector remains a
steering channel.

The B0 mathematical work is already authorized by the fixed requirements. Removing downstream
commissioning must not create a new requirement that the owner manually redispatch every existing
obligation. The launcher schedules those obligations from the existing plan.

**Required removal:** delete the permission to turn a downstream failure into an upstream brief by
restating it "as mathematics." Retain downstream diagnostics for downstream investigation. Any
actual change to the mathematical requirement enters through the mathematical authority, not
through a sanitized implementation request.

This closes the mechanism that permitted the orchestrator to prescribe obligations and send exact
failing terms while a different agent nominally authored the mathematics.

#### 2. Construction authority cannot alter the authority judging construction

**Working source and authoritative inputs are separate objects.**

Workers may propose changes to the kernel, controller, evaluator, workflow, or documentation within
the approved B0 mandate. A proposed change does not replace the requirement revision, acceptance
corpus, evaluator revision, or accepted semantic release used to judge it.

The existing protected references and runner provide this separation:
- A construction checkout contains candidate code and proposed document changes.
- Authoritative requirements, accepted interpretations, and evaluating rules are loaded from
  independently accepted revisions.
- Only the independent acceptance operation can advance an authoritative reference.

Candidate code runs without credentials capable of advancing those references. A candidate
controller is exercised against an isolated test environment, not installed with production
authority merely because its own tests passed. Its author cannot make it the active controller.

There is no "ordinary change" switch that a worker can set to bypass this separation. Conversely,
there is no blanket "protected file changed" condition that turns an already-authorized
implementation decision into an owner decision.

**B0 construction remains authorized.** The legacy controller is not the authority on whether its
replacement may be written or integrated as construction source. Its rejection cannot block source
work that does not consume an accepted result from it. Independent assessment of the replacement
uses the approved B0 requirements, including the requirement that legitimate construction proceed.

The accepted control configuration must demonstrate both directions: unauthorized changes to
mathematics or acceptance cannot take effect, and authorized ordinary development proceeds without
exemptions, repeated owner approval, or a dedicated documentation transaction.

A source commit may record an owner instruction immediately. Publication of that commit is not
what gives the instruction authority. A worker-written proposal remains a proposal.

**Required removal:** no commit trailer, environment variable, comment, exception table, or
candidate-authored status can grant authority. The current plan already retires the trailer gate;
the replacement must remove the general self-asserted-authority channel, including re-admission
controlled by `AGENT_ROLE`, rather than introduce another label.

#### 3. Preserve the question by construction; do not reconstruct it from its answer

**A mathematical question is constructed before evaluation and remains the same object throughout
interpretation, realization, and comparison.**

The interpretation interface produces the complete typed question against the accepted
mathematical release. Its representation retains the formal operation, operands, parameters,
selected structures, structural routes, comparisons, and logical structure relevant to the
assertion. It uses upstream declaration identities and typed terms, not a second mathematical
ontology.

Evaluation consumes that question. It does not produce a replacement question.

Consequently:
- A decision returning `True` cannot replace the proposition it decided.
- Recording operands without their relation or logical structure is insufficient.
- A question record cannot be recovered afterwards by searching syntax for a few recognized
  predicates.
- The computation cannot execute one request while reporting another as its protected question.

Normalization used for comparison must preserve this distinction. Equality of truth values,
provability of both propositions, or logical equivalence of two true propositions does not
establish identity of the question being tested. A change of accepted interpretation requires
independent assessment; it is not silently absorbed by regenerating the baseline with the
candidate reader.

The accepted record binds the question to its mathematical dependency revision. Keeping a
declaration name while changing its definition is not automatically preservation of meaning. A
dependency update requires the applicable interpretation comparison or independently accepted
transition.

The acceptance author establishes the initial interpretation from the mathematics and language
specification. Candidate output may be inspected as a claim to check; it is not promoted into the
expected interpretation because it is stable across runs.

**No admitted assertion disappears because interpretation failed.** The fixed assertion inventory is
an input to execution, not a list reconstructed from whichever assertions the candidate
successfully reads. Every required identity receives a result, including interpretation and
infrastructure failures.

Failure types also follow the stage that produces them. Semantic rejection belongs to reading;
backend failure belongs to execution; malformed output belongs to decoding; comparison may report a
wrong answer. An unexpected interpreter exception cannot be converted into semantic invalidity by
attaching a label. Runtime code does not possess a constructor for an authoritative
mathematical-invalidity judgment.

This replaces both manifestations of the same defect: reducing the question to `True`, and
treating a program failure as a judgment about mathematics.

#### 4. Completion is an independently derived result, not writable project state

**There is no worker operation "mark this B0 row complete."**

The existing acceptance table remains the complete definition of the required work. A row's
accepted status is derived from its full obligations at a specified compatible revision tuple. A
worker can submit a candidate and evidence; it cannot substitute a weaker predicate for the row's
acceptance.

Compilation, regression preservation, required computation, compositional justification, and
independent extension trials remain distinct observations. None implies another merely because they
concern the same code.

In particular, the following cannot establish completion:
- a negative probe demonstrating that unsupported execution is refused;
- preservation of an existing failure;
- semantic resolution without required execution;
- execution using scaffolding where the requirement specifies a registered backend;
- a source change that has not been consumed by the tested tuple.

The plan may display those observations, but they cannot be promoted into "met," "met in the
kernel," or another completion state that releases dependent obligations.

For a required structured construction, successful execution must produce the declared result,
including its defining maps and prescribed lifted structure. A code path that refuses before
sending the required request establishes a missing implementation path. It does not establish that
the kernel portion of the required execution is complete.

The runner establishes execution facts from the actual invocation and response path. A worker's
log, a backend's self-test, a manually supplied "executed" field, or a candidate's claim that it
used a registration is not independent evidence.

**Acceptance belongs to a tuple, not to unrelated successful revisions.** Mathematical, contract,
kernel, leaf, and evaluating revisions are fixed together for the observation. Updating a
dependency invalidates the affected observations until they have been re-established for the new
combination. It does not erase unrelated evidence, and it does not permit combining incompatible
successes.

The plan's status section becomes a view of these existing results and independent decisions, not
another editable ledger.

This implements the existing requirement that every row close only on its full acceptance at the
integration tuple. It does not reduce B0 to the assertions currently easy to execute.

#### 5. Work selection and validation follow actual input dependencies

**A worker cannot manufacture its next task from the most convenient failure, check, or writable
file.**

The existing plan supplies the objectives, their actual dependencies, and their priority. The
controller selects an available obligation from that plan and retains it across continuations.
Source checkpoints do not release the assignment. Neither commit count nor a green local check
selects the successor.

An assignment covers the complete generic mechanism needed to satisfy its obligation. It is not
divided automatically by file, example, issue, upstream commit, or available test. A coherent
change may satisfy several existing rows and span several repository revisions.

The controller distinguishes operations rather than applying one global status to all work: source
editing, focused validation, integration, independent review, and accepted release each consume
different inputs.

A blocker is therefore a missing input or capability of a particular operation. There is no
authoritative free-text `blocked` flag that disables unrelated operations.

Examples of the required behavior:
- An unavailable reviewer prevents a review decision, not source editing.
- A missing publication credential prevents that publication, not implementation.
- A missing backend executable prevents the corresponding execution job; it routes that job to an
  environment containing the engine.
- An unaccepted semantic dependency cannot be represented as accepted, but does not prevent
  independent work against the current accepted release.
- A documentation commit awaiting publication is not an input to already-authorized source
  construction.

**Migration restrictions are attached to the transition that needs them.** A temporary suspension of
broad execution is neither a permanent repository rule nor a remembered instruction. Its
applicability follows the active transition and its unresolved inputs. Once those inputs are
satisfied, the required validation becomes runnable without another owner instruction.

Conversely, while a replacement interface is deliberately incomplete, the controller does not
create tasks to make every transient consumer pass against the interface being removed. It
schedules validation at the coherent integration point specified by the transition.

This eliminates both sides of the research failure: repairing temporary architectures to satisfy
tests, and continuing a source-only prohibition after its condition had ended.

The controller author cannot add new objectives, change priorities, or enlarge the acceptance
denominator through a work-selection patch. Such a patch implements the fixed plan; it does not
author a new plan.

#### 6. Review consumes one complete snapshot and produces an actionable, revisable judgment

**Review inputs are assembled from revision identities, not independently supplied file lists and
diffs.**

A review request identifies the controlling requirements, base tuple, candidate tuple, and
obligations under assessment. The runner derives the relevant changes from those same identities.
The reviewer can retrieve unchanged source needed to follow the affected mechanism.

There is no operation that combines a seal-relative file list with main-relative patches. Missing
or unreadable inputs produce a failed review operation, not a rejection of the candidate.

The existing review mechanism distinguishes a demonstrated defect, missing evidence, an execution
failure, an erroneous earlier finding, and a proposed change to a reserved requirement. A finding
identifies the governing obligation and supporting source, argument, or counterexample.

A reviewer cannot create a new prerequisite merely by including it in prose. A requirement change
remains a proposal to the authority that owns it. A technical defect remains repairable without
asking the owner to reconfirm the original objective.

Identical review requests are not repeatedly resubmitted to obtain a different model answer. A
substantive source revision, new evidence, restored missing context, or a supported correction to
a finding permits reconsideration in the same review discussion. Cosmetic edits do not manufacture
a new review basis.

**The controller can neither accept its own replacement nor make itself irreplaceable.** Its
acceptance depends on the fixed positive and negative requirements, not preservation of its
previous decisions.

No additional reviewer service, verdict hierarchy, exception registry, or approval transaction is
introduced. These are corrections to the existing review request and result interfaces.

### What these policies must make impossible

The required guarantee concerns the actual transition system, not compliance with the prose.

A downstream worker cannot steer an upstream author because it possesses neither that author's
input channel nor the assignment operation. A candidate cannot redefine its acceptance because
authoritative inputs are not taken from its checkout. A `True` answer cannot become the protected
question because evaluation never constructs questions. A missing reviewer cannot stop source
construction because source construction does not consume a review result. A narrow probe cannot
close a broader obligation because completion consumes the full fixed acceptance. A temporary
restriction cannot persist indefinitely because its applicability is derived from the transition
that owns it.

These are inspectable properties of interfaces and data flow. If every authorized transition
preserves them, they remain true after any sequence of authorized transitions, by induction on that
sequence. A surviving alternate credential, legacy endpoint, editable authoritative input, or
self-acceptance operation breaks that argument and must be removed.

This does not replace intelligent assessment of the small trusted kernel and controller. The
owner's specification explicitly retains that assessment. It removes the repeatedly exploited
discretion from routine work, so the assessment is no longer surrounded by an indefinitely
expanding system of local repairs and administrative exceptions.

**The implementation task is to remove the authority-bearing operations that generate the
failures—not to add another mechanism that asks whether an agent has promised not to use them.**

## Packages

| Package (repository) | Depends on | Holds |
| --- | --- | --- |
| `lean_categories` (`lean-categories`) | Mathlib | all mathematics and the catalogue |
| `cas_leaf_contracts` (`lean-cas-dsl-leaf-contracts`) | `lean_categories` | the leaf contract: the registration (operation, input form, backend), the manifest reader, the port protocol and its Python reference implementation |
| `lean-cas-dsl-leaves`, or any leaf package | nothing Lean | a manifest `leaves.json` at the package root and its backend programs; no Lean |
| `cas-dsl` (`lean-cas-dsl`) | `lean_categories`, `cas_leaf_contracts` | the kernel's resolution, admission, realized reading and language, the permanent suite, the harness, the notebook; it reads a leaf package's manifest at run time |

The leaf contract is the kernel's, not `lean-categories'`: it is about what is computable and how
it is executed, of which `lean-categories` owns nothing and which its audit never reads. It is
published apart from the kernel only so that a leaf depends on nothing else of it. It changes with
the kernel, is released, and is re-pinned by the leaves and here; a leaf never changes it to fit.

## Where the semantic registry lives

The semantic registry, the catalogue, is `lean-categories`' (`LeanCategories.Catalogue`, namespace
`CasCatalogue`). It holds the symbolic calculus of category and functor expressions, the witnesses
tying each expression to its Lean category, the schema and validators of semantic rows, the
`normalized_registry` command, and the rows. `lean-cas-dsl` imports it at the pinned revision; its
own registry (`CasContract.Registry.Extension`) records leaf computations only, each against a
registered operation's declared type; nothing in it carries meaning. `cc-sem-upstream` and `cc-sem-derive` made this so on 2026-09-29.
