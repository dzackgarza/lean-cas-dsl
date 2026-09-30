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
| A leaf declares its object to be a group | `subcategory` and `refineObject` are rejected. A realizer names its category only through a denotation functor, which must typecheck into that category's declaration. | — |
| A leaf says which operations an object has | `method` and `property` are rejected. Availability is computed from semantic rows and routes. | — |
| A leaf coins subgroup, kernel, cardinality or basis | `genericSemantics`, `naturalTransformation` and `identification` are rejected | — |
| A leaf forwards an inherited method | No method rows are available to a leaf. An implementation must realize a registered composite, and validation checks its square. | — |
| A leaf narrows a domain or changes a result type | Rows cannot restate a domain. An implementation's type is checked against the composite's realized codomain. | — |
| A leaf inserts a placement or inheritance edge | `forgetfulRoute` and `coercion` are rejected | — |
| Installing or removing a leaf adds or removes methods | `#methods` reads semantic rows only. `StrataProbes` finds the surfaces identical with and without every leaf, while `#gaps` differs. | — |
| A backend's class hierarchy changes DSL inheritance | Programs are opaque behind the port. `connect` refuses any capability that is not declared on a registered operation. | — |
| A backend object becomes the public value | Answers are decoded into the operation's semantic result type. Values are handles of registered realizers, and they mean their denotations. | — |
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
| `lean-cas-dsl` ships a leaf (a `register_leaf`, a "probe" that registers a minimal realization) | `scripts/check_no_leaves.py` (in `just build` and CI) refuses any `register_leaf` and any tracked `CasLeaves/` file. The DSL consuming the leaf packages (`require cas_leaves`) is its purpose: its tests and notebooks run here over the installed leaves. Red on `AdapterProbes` and `CohereExecProbes` until their leaves move to the leaf repository | `gov-no-leaves-here` |

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
