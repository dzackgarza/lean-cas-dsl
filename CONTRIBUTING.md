# Contributing

[`specs/architecture.md`](specs/architecture.md) is the contract every contribution conforms to.
This file says where each kind of contribution goes.

## Which repository?

| You need | It goes to |
| --- | --- |
| A category, functor, classifier, operation (method), predicate, coherence, constructor or family that is not yet formal | `lean-categories`: formalize it there (or open the request), release, and re-pin here. Never coin it here, in a leaf, or in `research`. |
| Something that computes a registered operation on some presentation | A leaf (`CasLeaves/`, or an external package once `cc-external-leaf` lands) |
| A proposition the language should always make true | `CasAcceptance/`, as a permanent assertion |
| Resolution, realization, the leaf API, the port or surface syntax | The kernel (`CasCatalogue/`) or the notebook (`CasDsl/`), under a plan node in `specs/computational-core-plan.md` |

The semantic registry is `lean-categories`' (`LeanCategories.Catalogue`, rows under
`LeanCategories/Catalogue/Semantics/`). `normalized_registry` refuses every module outside
`lean-categories`; this repository reads the registry at the pinned revision.

## Writing a leaf

A leaf is a Lean module ending in a single `register_leaf` contract, under `CasLeaves/` here or in
another package under its own root (for example `research/leaves`, `ResearchLeaves.*`, pinned to
this repository). Its backend program, in any language, sits next to it. In another package,
`#acceptance_rerun` reruns this repository's permanent assertions unchanged with the new
realizations; a gap closed there shows as `now holds`.

**What a leaf may contribute** (`CasCatalogue/Adapter.lean`):

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
`CasCatalogue.Leaf`, `CasLeaves.*`, modules of its own package, Mathlib and `lean-categories`.

If a leaf seems to need one of the rejected contributions, or needs to forward an inherited
method, the defect is upstream. Fix it there.

**Backends.** A backend is a child process speaking the port protocol (`CasCatalogue/Port.lean`;
reference implementation `port/python/cas_port.py`). Its announced capabilities must be registered
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
