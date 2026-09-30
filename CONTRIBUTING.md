# Contributing

[`specs/architecture.md`](specs/architecture.md) is the contract every contribution conforms to.
This file says where each kind of contribution goes.

## Which repository?

| You need | It goes to |
| --- | --- |
| A category, functor, classifier, operation (method), predicate, coherence, constructor or family that is not yet formal | `lean-categories`: formalize it there (or open the request), release, and re-pin here. Never coin it here, in a leaf, or in `research`. |
| Something that computes a registered operation on some presentation | A leaf, in `lean-cas-dsl-leaves` (`CasLeaves/`) or another package written against the leaf contract |
| A proposition the language should always make true | `tests/acceptance/*.cas`, as a permanent test |
| Resolution, calls, the language or surface syntax | The kernel (`CasCatalogue/`) or the notebook (`CasDsl/`), under a plan node in `specs/computational-core-plan.md` |
| The realization registry, the leaf API or the port | The leaf contract (`lean-cas-dsl-leaf-contracts`, `CasContract/`), with the kernel change that needs it |

The semantic registry is `lean-categories`' (`LeanCategories.Catalogue`, rows under
`LeanCategories/Catalogue/Semantics/`). `normalized_registry` refuses every module outside
`lean-categories`; this repository reads the registry at the pinned revision.

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
- A numeral is the image of the map out of the initial object of its object's category; where
  there is none, it is not a numeral of that object (LC-15).
- A leaf presents the catalogue's object; it never shapes it. A contract rule that would need
  the catalogue to change to suit a leaf's representation is itself a defect.

## Writing a leaf

A leaf is a Lean module ending in a single `register_leaf` contract, under `CasLeaves/` in
`lean-cas-dsl-leaves` or in another package under its own root, depending on the leaf contract and
`lean-categories` only. Its backend program, in any language, sits next to it. `lean-cas-dsl`'s harness (`cas-harness`, `just harness`) runs the permanent suite over the
installed leaves and reports each gap; a leaf package never imports or runs the suite.

**What a leaf may contribute** (`CasContract/Adapter.lean`):

| Contribution | What it says |
| --- | --- |
| `realizer` | These handles realize a registered category, through a denotation functor that must typecheck into that category |
| `action` | This realizes a registered functor's action on these handles; the square is checked |
| `implementation` | This realizes a registered method's composite, typed `TrustedImplementation` or `CertifiedImplementation` over that composite |
| `decider` | This decides a registered property on these handles, three-valued |
| `isomorphism` | Two handles are isomorphic, as an isomorphism in the handle category |
| `limitRealization` | This presents the apex of a registered limit or colimit on these handles |
| `equality` | This decides equality of morphisms of a registered category on these handles |
| `backendOperation` | Backend `b` answers registered operation `o`, with a decoder into `o`'s semantic result type |
| `presentation` | These handles present the values of a registered object (`obj%`), each with its identification |

Everything else is rejected at `register_leaf`, naming the rule it breaks: categories, methods,
properties, subcategories, forgetful routes, identifications, coercions, refinements of objects,
result classes, generic semantics and natural transformations. A leaf module may import only
`CasContract.Leaf`, `CasLeaves.*`, modules of its own package, Mathlib and `lean-categories`.

If a leaf seems to need one of the rejected contributions, or needs to forward an inherited
method, the defect is upstream. Fix it there.

**Backends.** A backend is a child process speaking the port protocol (`CasContract/Port.lean`;
reference implementation `python/cas_port.py` of the contract, put on the adapter's `PYTHONPATH`). Its announced capabilities must be registered
operation ids declared by `backendOperation` rows, or `connect` refuses it. Its answers are
untrusted JSON, decoded into the operation's semantic result type or rejected. A backend's
restrictions restrict its realization, never the operation's domain. Model: the Sage cardinality
leaf, `CasLeaves/Modules/SageCardinality.lean` with its `sage_cardinality.py`.

## Acceptance assertions

Permanent assertions live in `CasAcceptance/Permanent/`:

```lean
#accept "card.z4_cubed" from "Mathlib Fintype.card_fun, ZMod.card: |(ℤ/n)^k| = n^k" :
  (value% cardinality (z4Cubed) in "cat.sets").as = 64 := by
  simp [cardinalDenotation, CardinalHandle.denote]; rfl
#accept_backend "card.sage.z4_cubed" from "agreement with card.z4_cubed" :
  (sageCardinalityOf 4 3) agrees (method% cardinality (z4Cubed) in "cat.sets").as
```

After adding one, run `python3 scripts/check_acceptance_permanent.py --admit`. The text up to
`:=` is then permanent, while the proof after it may change. An assertion that no realization
computes yet is recorded as a gap (`#acceptance_gaps`), not a failure.

- State the proposition in the mathematical language, through the public surfaces.
- Write its expected value from a proof, a cited source or an independent oracle before you run
  anything, and record that provenance.
- Never read a leaf, a handle's internals or a backend to decide what to assert.
- An admitted assertion is permanent. If an implementation disagrees, the implementation is wrong.
  Only an upstream correction to the mathematics changes an assertion, in the commit that re-pins
  it.

## Gate

`just build` runs the reuse-record check (`scripts/check_reuse_records.py`: the plan's **Next**
node needs `specs/reuse/<node>.md`), then builds the kernel, the leaves, the acceptance probes,
the tools and the notebook. `just test` adds `cas-axiom-audit`, which permits only `propext`,
`Classical.choice` and `Quot.sound`, and the no-sorry check. `just test-ci` also re-executes the
demo notebook through the live kernel.
