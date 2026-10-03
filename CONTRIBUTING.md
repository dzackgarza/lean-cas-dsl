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

During B0 construction, the controller, reviewer prompt, gates, and publication
workflow are themselves implementation work. Correct them under the construction
mandate. Do not submit their replacement to an obsolete policy in order to obtain
permission to perform the replacement.

Run the checks relevant to the actual change. A changed reviewer decision path
needs reviewer tests. A changed kernel mechanism needs its relevant kernel tests.
A descriptive text correction does not acquire a full mathematical build merely
because the repository contains Lean code.

A publication dependency does not suspend implementation or invalidate the
instruction being recorded. Preserve the commit and continue the selected work
while the already-specified publication correction is executed.

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

The independent acceptance author submits the assertion and proposed admission through the
existing acceptance review channel. An accepted admission makes the assertion permanent.
`python3 scripts/check_acceptance_permanent.py` checks the retained ledger; it never updates it. An assertion that no installed computation answers yet is recorded as a gap
(`#acceptance_gaps`), not a failure.

- State the proposition in the mathematical language, through the public surfaces.
- Write its expected value from a proof, a cited source or an independent oracle before you run
  anything, and record that provenance.
- Never read a leaf, a handle's internals or a backend to decide what to assert.
- An admitted assertion is permanent. If an implementation disagrees, the implementation is wrong.
  Only an upstream correction to the mathematics changes an assertion, in the commit that updates
  to it.

## Gate

Run what the change touches:
- **Kernel, language, probes, tools:** `just build` runs the repository checks (authorship
  between the mathematical layers, no leaves, reuse records, permanent acceptance) and compiles the
  kernel, gates, acceptance probes, tools and notebook package. Compilation does not execute the
  suite. `just test` adds `cas-axiom-audit` (only `propext`, `Classical.choice`, `Quot.sound`)
  and the no-sorry check; `just test-ci` re-executes the demo notebook.
- **Acceptance:** `just harness` runs the suite and reports every assertion's outcome;
  `just acceptance BASE` compares that report with a base report, assertion by assertion
  (`scripts/check_acceptance_regression.py`). That is development regression, not B0
  completion, which is judged against the fixed B0 requirements at one revision tuple.
- **Reviewer controller:** `python3 custodian/review/test_review.py` on a scratch copy (its usage
  line).
- **Documentation only:** nothing; CI skips the Lean jobs for it.
