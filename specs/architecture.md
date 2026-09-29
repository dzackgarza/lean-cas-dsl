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
| `lean-cas-dsl` kernel (`CasCatalogue`) | Deterministic interpretation of the pinned `lean-categories` release: what an expression denotes, which operations apply, how they propagate along structural functors, the exact composite a call denotes, typed inputs and outputs, ambiguity, placement and refinement, and the separation of semantic availability from computability. The leaf API, the port protocol, the realization registry and its validation. | Any mathematics. It derives `Lat → R-Mod → Set → Card`; it never states "lattices have cardinality". |
| Leaves (`CasLeaves`, and leaves hosted elsewhere) | Realizations only: (semantic operation or composite, supported presentations) ↦ implementation, plus the programs behind their ports, in any language, arbitrarily ugly internally. | What exists, what category anything is in, which operations it has, what an operation means or returns, which structural functors exist, what is inherited, what acceptance asserts. |
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
| Installing or removing a leaf adds or removes methods | `#methods` reads semantic rows only | `cc-failure-strata` pins it with a probe |
| A backend's class hierarchy changes DSL inheritance | Programs are opaque behind the port. `connect` refuses any capability that is not declared on a registered operation. | — |
| A backend object becomes the public value | Answers are decoded into the operation's semantic result type. Values are handles of registered realizers, and they mean their denotations. | — |
| An acceptance assertion changes because a leaf changed | Policy only | `cc-acceptance-permanent` |
| A computational failure is "fixed" by weakening semantics | Transitional: the semantics are still editable here (`CasCatalogue/Semantics`) | `cc-sem-upstream`, `cc-sem-derive` |
| A research notebook coins missing mathematics | `research` AGENTS.md | — |
| `lean-cas-dsl` itself authors mathematics | **Violated, transitionally.** `CasCatalogue/Semantics/*` is a local semantic registry written with `normalized_registry`. | `cc-sem-upstream`, `cc-sem-derive` |

## Transitional state

`CasCatalogue/Semantics/*` is a second, editable semantic database. It denotes `lean-categories`
and Mathlib declarations, but the choice of rows (which categories are public, which functors are
structural, which operations are methods, which comparisons exist), and some of its definitions,
are authored here. That is the one standing violation of single authority. It is scheduled for
deletion:

* `cc-sem-upstream` moves every semantic row and definition into `lean-categories`, as its
  proof-carrying registry;
* `cc-sem-derive` makes `lean-cas-dsl` read that registry from the pinned release and removes the
  write path (`normalized_registry`) from this repository.

Until then:

* a semantic row added here must be one `lean-categories` owns mathematically;
* it must cite that owner;
* its move is part of `cc-sem-upstream`;
* no semantic row is ever added, removed or weakened to make a leaf compute.
