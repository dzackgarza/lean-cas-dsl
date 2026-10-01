# Contributing

[`specs/architecture.md`](specs/architecture.md) is the contract every contribution conforms to.
This file says where each kind of contribution goes.

## Which repository?

| You need | It goes to |
| --- | --- |
| A category, functor, classifier, operation (method), predicate, coherence, constructor or family that is not yet formal | `lean-categories`: formalize it there (or open the request), merge it to `main`, and `lake update` here. Never coin it here, in a leaf, or in `research`. |
| A computation of a registered operation on one of its declared input forms | A leaf, in `lean-cas-dsl-leaves` or another package written against the leaf contract |
| A proposition the language should always make true | `tests/acceptance/*.cas`, as a permanent test |
| Resolution, calls, the language or surface syntax | The kernel (`CasCatalogue/`) or the notebook (`CasDsl/`), under a plan node in `specs/computational-core-plan.md` |
| The realization registry, the leaf API or the port | The leaf contract (`lean-cas-dsl-leaf-contracts`, `CasContract/`), with the kernel change that needs it |

The semantic registry is `lean-categories`' (`LeanCategories.Catalogue`, rows under
`LeanCategories/Catalogue/Semantics/`). `normalized_registry` refuses every module outside
`lean-categories`; this repository reads the registry at `main`.

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
- Kernel code is total in the same sense, and the banned-construct ratchet stands for that
  invariant, not for the word `partial`. A recursion is made total by proving it terminates
  (structural recursion, or a well-founded measure that decreases). Bounding it by fuel and
  failing when the fuel runs out is a partial map in another encoding: the failure says nothing
  about the input, and a bound argued to be sufficient makes it an `unreachable!` under another
  name. A decoder may fail only on input that is malformed. Proposed by the orchestrator on
  2026-10-01 to clear the ratchet, and withdrawn.
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
  weak, the fix is a formalization request, never kernel code.
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
- Findings go upstream as requests, never as edits.

The leaves are not part of this repository; the dependency that remains is a defect
(`gov-no-leaves-here`).

## A correction is encoded where it will be read, before anything else

A chat ends, and agreement stated in it is lost with it. When the owner corrects the work or
states a rule, the correction is written in the same turn into the document that owns it:
- this file, `lean-categories`' CONTRIBUTING, architecture.md, the plan, or an AGENTS.md;
- where possible, into a gate that fails the build.

Saying "understood", or tracking the correction in a session task list, is not compliance. Both
are ephemeral. Work continues only after the correction is committed. The owner's questions
count as corrections. For example, "why is an inverse defined on an arbitrary matrix?" means that
it must not be.

## Writing a leaf

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
upstream: fix it there. Anything that can be discharged in Lean is never a leaf's: either
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

After adding one, run `python3 scripts/check_acceptance_permanent.py --admit`; the assertion is
then permanent. An assertion that no installed computation answers yet is recorded as a gap
(`#acceptance_gaps`), not a failure.

- State the proposition in the mathematical language, through the public surfaces.
- Write its expected value from a proof, a cited source or an independent oracle before you run
  anything, and record that provenance.
- Never read a leaf, a handle's internals or a backend to decide what to assert.
- An admitted assertion is permanent. If an implementation disagrees, the implementation is wrong.
  Only an upstream correction to the mathematics changes an assertion, in the commit that updates
  to it.

## Gate

`just build` runs the reuse-record check (`scripts/check_reuse_records.py`: the plan's **Next**
node needs `specs/reuse/<node>.md`), then builds the kernel, the leaves, the acceptance probes,
the tools and the notebook. `just test` adds `cas-axiom-audit`, which permits only `propext`,
`Classical.choice` and `Quot.sound`, and the no-sorry check. `just test-ci` also re-executes the
demo notebook through the live kernel.
