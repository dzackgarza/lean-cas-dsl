# Independent RX05 declaration-environment assessment

## Finding

The four supplied records establish comparison-dependent resolution and invariance under
the tested declaration-order reversal at the public resolver-state interface. They contain
separate inventories and complete typed requests for each state. Removing only
`cmp.rings.carrier` preserves both required route candidates and produces an ambiguity;
reversal preserves the full candidate multiset. With the cell present, reversal preserves
the complete selected request and its actual comparison components.

There is a material scope qualification. The coherent selected request follows the existing
third route through additive commutative monoids. It retains an actual comparison from that
route to the multiplicative route, followed by the required `cmp.rings.carrier`. The latter
cell's designated source is correctly multiplicative, but the request's primary selected
route is not multiplicative. Thus these records establish a comparison-equivalent request,
not an observation that the primary selected route is the multiplicative leg. They must not
be reported as having established that stronger designated-request requirement.

This does not close the whole RX05 trial. The source's complete component, inverse,
naturality, arithmetic-distinction and execution assertions remain unchanged and have their
separate interpretation and execution scope. No runtime answer, kernel implementation, or
leaf implementation was used for this assessment.

## Evidence and producer

- Raw export: `/tmp/kernel-frozen-rx05-four-environments-20261024.json`, 1,853,510 bytes,
  SHA-256 `0b45955f91eada161dccbc69904f1043422fdd946c7debcc27e89be8966434f0`.
- Provenance: `/tmp/kernel-frozen-rx05-four-environments-provenance-20261024.json`,
  SHA-256 `c12278a87e4530bee1e968c9ede28340240487d79f92f968d5db0af57c655abc`.
- Public interface description: `specs/reuse/frozen-observation-controls.md` at kernel
  revision `60beb86d5a715272a47bafc0dce1704717fef606`, together with the public typed
  question-DAG format.
- Independent requirements: [the RX05 source](rx05-carrier-diamond.cas),
  [the fixed question](../questions.md#rx-05-the-actual-ring-carrier-diamond-at-primeresidues5-proof),
  and [the four observation controls](../observation-controls.md).

| Producer component | Git commit | Git tree |
| --- | --- | --- |
| Integrated kernel source | `60beb86d5a715272a47bafc0dce1704717fef606` | `934587f0a8bb0d92512e1e5993153fc0ffb7c4c0` |
| Mathematics | `b08e6b3cac7b2464d21419e05b27c89c2c6858d5` | `0ed39a7c95a6c33fcfb0f545d76dac4b78970d25` |
| Contract checkout | `469f5d90bbef964a2b19d407f81d9ca52a5f033d` | `4633972a6cdf788bb22ed7ca77a0ba478c1b2396` |

The runner source checkpoint is `39e7558c1e2bdc2c472775d0a98ab56a7aad43a3`, integrated
in the listed kernel revision; its recorded source hash is
`715edb55783b4abbe3ad7e49b660518fe8b4e6b853ecefa5d6a75476e752837e`.
The runner source was not read. The provenance states that the contract's compiled runtime
sources agree with `8397df15042598f5ce9a75cdb22675c65b06fc89`; the later checkout changes
only documentation and its manifest.

The toolchain is Lean 4.33.0. The ordered direct imports are
`CasCatalogue.QuestionComparison`, `CasCatalogue.FileItems`, and
`LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions`, also used in the
meta phase. Package selection has SHA-256
`e2c103dcdd2ad903a5e0dc0574627171ef2b5b425816029f9bac0a2f2aeb4a20`.
The provenance records 150 resolved semantic modules and 745 artifacts, including private
and server `.olean` files and meta IR. All 25 recorded artifacts of the three direct imports,
`CasCatalogue.Resolve`, and `CasContract.Port` were independently hashed and matched.
This is an artifact correspondence check, not a separately reproduced build.

## What was independently compared

The export's own cross-environment verdict fields were not accepted as the comparison.
The inventories, resolution records and complete typed payloads were compared directly.
All values and types in the four receiver records, two coherent requests and six candidate
requests have valid local DAG references and closed binding scopes. Meaningful array order,
complete declarations, universe arguments, proof propositions and selected structures were
retained. Candidate comparison ignores enumeration order only and retains multiplicity.

| State | Selected rows | Selected cells | Actual interpretation |
| --- | ---: | ---: | --- |
| `present` | 585 | 13 | One coherent request, using both actual carrier cells |
| `present-reversed` | 585 | 13 | The same complete coherent request and comparison components |
| `absent` | 584 | 12 | Ambiguity with three complete route requests |
| `absent-reversed` | 584 | 12 | The same complete candidate multiset, enumerated in reverse order |

Each absent inventory is exactly the corresponding present inventory with the single
`cmp.rings.carrier` row and cell removed. There are no other deletions, additions, or metadata
changes. Each reordered inventory is a permutation of exactly the same complete rows.
The category, classifier, functor, method and cell sequences are reversed; other row
families remain in their existing order. In particular, the competing multiplicative and
additive functor declarations change relative order. This is the required competing-route
order control, not a claim that every kind of registry row was reversed globally.

All four receiver records contain the actual prime-residue field at 5 with a proof whose
proposition is `Nat.Prime 5`, followed by its genuine field and commutative-ring forgetful
maps. Their comparison object is the existing `ringIntegersMod 5`.
`PrimeResidueFields.underlying_ring` identifies this forgotten object with that selected
residue ring. These are structurally identical complete receiver records across the four
states, not merely the same displayed name or carrier cardinality.

The two required unresolved routes are exactly:

| Route | Ordered edges |
| --- | --- |
| Multiplicative | `fun.rings.multiplicative_monoid`; `fun.monoids.semigroup`; `classifierForget(clf.magmas.associative)`; `classifierForget(clf.sets.binary_operation)` |
| Additive | `fun.rings.additive_group`; `fun.additive_groups.to_groups`; `fun.groups.monoid`; `fun.monoids.semigroup`; `classifierForget(clf.magmas.associative)`; `classifierForget(clf.sets.binary_operation)` |

The third candidate is the already declared route
`fun.rings.additive_commutative_monoid`;
`fun.additive_commutative_monoids.additive_monoid`;
`fun.additive_monoids.underlying`. Its presence does not replace either required candidate.
Every candidate retains its own complete route functor, each actual route step, image of the
selected ring, the ordinary set-cardinality functor, its `Core(Sets)` input, and its formal
result. Neither absent state has a fabricated globally selected `typedRequest`.

## Actual comparisons and the designated-source qualification

The coherent request retains the following actual natural isomorphisms and both directed
components of each at the complete selected ring:

1. `CasCatalogue.Algebra.CommMonoids.ringsAdditiveMonoidCarrierCell`, from the third route
   to `LeanCategories.Algebra.ringCarrierMultiplicative`;
2. `LeanCategories.Algebra.ringCarrierComparison`, from
   `ringCarrierMultiplicative` to `ringCarrierAdditive`.

The second declaration is precisely the required `cmp.rings.carrier`. Its source and target
functors, forward and inverse component types, and receiver agree with the independent
mathematics in `Algebra/Concrete/RingCarrierComparison.lean`,
`Catalogue/Semantics/Algebra/PortComparison.lean`, and `PrimeResidueFields.lean`.
It has not been replaced by an invented identity based on equal endpoints.

The first comparison is also independently present in upstream
`Catalogue/Semantics/Algebra/CommutativeMonoids.lean`. It compares only set-valued composites;
it does not identify additive and multiplicative monoid operations. Its actual source is
the third route. Consequently a coherent three-route request can be mathematically
compared with the requested multiplicative and additive routes through these two cells.
This explains the observed choice without pretending that the chosen primary route is
the multiplicative route.

The fixed controls require the actual carrier cell and its multiplicative designated
source. Those data are present. If completion additionally asserts the source convention
in `PortComparison.lean` that the operation itself is selected on the multiplicative leg,
the current observation does not establish it: the typed operation input explicitly uses
the third route. A comparison-equivalent chosen route and that designated primary request
must remain separate findings. The fixed assertions were not rewritten to erase this
distinction.

## Observation boundary

These are four explicit immutable selections of the public `RegistryState`, as documented
by the public control interface. They exercise the generic resolver directly. They do not
exercise four alternate Lean import graphs, and they do not demonstrate full frontend
evaluation of the unchanged assertion file under each selected state.

The actual scalar answer, whole-map naturality, preservation of distinct arithmetic
operations, successful execution and failure strata were not observed here. The source
equations and their later execution denominator remain fixed. Final frozen artifacts still
need their own provenance and comparison with these reviewed readings. This assessment
changes no permanent baseline or assertion.
