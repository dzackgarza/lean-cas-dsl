# Independent review of the 48 initially readable extension questions

This assessment compares the complete interpretation-only payloads supplied on
2026-10-24 against the independently fixed sources in this proposal. It finds
no new mathematical misreading among the **48 complete readings**. The export
contains all **134 required positive IDs**, of which **86 have empty readings**.
Those 86 remain open interpretation obligations. This is an assessment of an
initial candidate before the final freeze, not a completed 134-question review
or evidence that any computation returned a correct answer.

The inputs were the unchanged `.cas` sources, their existing mathematical
derivations and upstream declarations, the public question-identity format,
the raw readings, and their supplied provenance receipt. No failure report,
execution report, runtime answer, kernel implementation, or leaf implementation
was consulted for this review. The incidental engineering-report exposure
already disclosed in this proposal's README remains disclosed; this assessment
does not replace that history with a stronger independence claim.

## Exact inputs and coverage

The supplied export is
`/tmp/kernel-mvp-frozen-trials-20261024/readings-initial.json`, SHA-256
`51538095a8311bc030c4a3fd6cd070cf13d1aeb6305b3334b5a61ff5568603a0`.
Its 134 unique IDs equal the fixed proposal's complete positive ID set. Every
basename and one-based source line agrees with that source. Every staged
positive `.cas` file is byte-identical to its fixed counterpart in this proposal.
No assertion or baseline was regenerated.

The 48 complete readings comprise 12 `literal`, 34 `homs`, one
`judged:(some true)`, and one `judged:(some false)` claim. Both JSON term tables
of each complete reading were parsed as actual DAGs. Every term reference was
valid; all claim roots and all **2,047 operation-result/metadata term-reference
occurrences** were closed. Parameter lists, complete category bundles, ordered
maps, routes, and exact proof-proposition types were retained in that check.
This is a well-formedness check, separate from the mathematical comparisons below.

| Fixed source file | Complete | Required | Mathematical scope reviewed |
| --- | ---: | ---: | --- |
| `rx01-selected-orders.cas` | 2 | 4 | Cardinalities of the two selected orders |
| `rx02-complete-core-action.cas` | 6 | 7 | Both reversal maps, nonidentity point, whole induced action and composition |
| `rx02-two-subsets.cas` | 1 | 2 | Cardinality of unordered distinct two-element subsets |
| `rx03-complete-automorphism-arrows.cas` | 6 | 14 | Actual inverse arrow, two whole inverse equations, three quotient-class actions |
| `rx03-cyclic-automorphisms.cas` | 8 | 12 | Group-valued construction, complete presentations, inversion and conjugation reuse |
| `rx04-square-bound.cas` | 7 | 7 | Exact subset, finite refinement, predicate and admission |
| `rx05-carrier-diamond.cas` | 8 | 13 | Three cardinalities, both comparison components, inverse equations and naturality |
| `rx06-reindexing.cas` | 4 | 10 | Original dimension, two restricted cardinalities and whole cartesian carrier map |
| `rx07-f9-transport.cas` | 5 | 17 | Both generator images, both ring inverse equations and successive value |
| `rx09-successor-series.cas` | 1 | 6 | Entire successor-coefficient family on the natural numbers |
| Other fixed positive source files | 0 | 42 | No complete reading in this export |
| **Total** | **48** | **134** | **86 open readings** |

The required counts in this table refer to fixed positive questions, not to the
separate RX05 environment controls, RX09 negative admission, or RX10 execution
and ownership observations.

## Mathematical comparisons

### RX01 and RX02

Both RX01 cardinality readings use `setsCardinality` after the actual
`linearOrdersForget` functor, at `FiniteOrders.ordinary 5` and
`FiniteOrders.reverse 5` respectively. Each asks for cardinality five. The two
selected order objects remain distinct; these cardinality statements do not
establish either unreadable order comparison.

RX02 retains `CoreIsomorphisms.finRevIso 5` in both directions and compares each
whole map with the independently specified `Morphisms.finRev 5`. The point
equation has source `Fin 1`, target `Fin 5`, and the admitted points zero and
four. The induced map is the actual `TwoSubsets.onCore.map` on
`finRevCore 5`; its composition is taken in `Core(Sets)` before the functor is
applied. The two inverse/composition equations have the whole two-subset object
as domain. They are not replaced by an identity input or by finitely sampled
equalities. Cardinality is taken on that same two-subset construction, with
expected value ten. These agree with [M01, M02] and the complete core-action
supplement. Singleton exclusion and the remaining point-action equation have
no complete reading here.

### RX03

`Aut` is applied to the selected group `CyclicQuotients.cyclicQuotient 5`, with
the complete category bundle `Groups`. The cardinality question concerns its
automorphism group, rather than the permutations of its underlying set. The
residue comparison's forward and inverse maps retain their full `GrpCat`
endpoints. The two `Aut` action equations retain both directed maps in each
`coreIso`, and the actual morphism argument in each `constructionMap`.

The points called doubling and tripling are the images under
`byUnitMorphism 5` of the units admitted from ring numerals two and three in
the multiplicative monoid of `ZMod 5`. The admission keeps the selected monoid
and its invertibility obligation. The inverse operation is the generic group
inverse on the actual automorphism group. Conjugation uses the complete
selected residue isomorphism, and the reuse equation consumes the result of
the first conjugation in the second.

The six readable arrow supplements compare `groupsBackward` of doubling with
`groupsForward` of tripling, state the two whole group-arrow inverse equations,
and evaluate the actual forward/backward arrows on the quotient classes
`[1]`, `[3]`, and `[2]`. Their expected classes are `[2]`, `[1]`, and `[1]`.
Each class is formed by `quotientMap 5` from the corresponding integer numeral;
the multiplicative identity of the quotient group is not substituted for the
integer class `[1]`. These are the original [M03, M04] questions and the
`AutomorphismArrows` supplement. The group multiplication, power, and remaining
whole coordinate/conjugation questions are still unreadable in this export.

### RX04

The cardinality and classifier questions retain the exact bound parameter three
and the finite refinement of the integer-square-bound set. Forgetting that
refinement uses `clf.sets.finite`. The predicate comparison is an equality in
the power set of all integers with the transpose of `n ↦ n² ≤ 9`; the domain
has not been narrowed to a finite list. The list comparison uses the seven
integers `-3,-2,-1,0,1,2,3` through the existing finite-subset literal interface.
The ambient-integer finiteness question keeps its explicit false orientation.

The admitted subset is compared after the registered
`FiniteSubsets.inclusion : Finset ℤ → Set ℤ`; it is not replaced by a newly
enumerated set. Thus all seven readings preserve [M05] and the stated
admission equation.

### RX05

The three cardinality questions concern the prime residue field at five and
its explicitly chosen multiplicative and additive carriers. The primality
proof's proposition remains `Nat.Prime 5`. Both components of
`cmp.rings.carrier` retain the selected ring, direction, and exact endpoints:
the multiplicative carrier `U_m` and the additive-group carrier `U_a`.
Their inverse equations have the corresponding whole carrier as domain.

Naturality retains the entire integer-coefficient map into this field, with
its two explicitly specified forgotten maps and the comparison component at
the integer ring. This is the original infinite-domain naturality question,
not an equality checked at a chosen integer. These explicit comparison
readings agree with [M06, M07].

The inherited cardinality request takes the additional route `U_t` through
additive commutative monoids and additive monoids. Its underlying cardinality
question agrees with the specified set-level comparison, but this does not
show that resolution selected `U_m` as its primary route. The separate
[RX05 environment assessment](rx05-interpretation-assessment.md) records the
same substantive limitation: comparison-equivalent selection and ambiguity
controls do not establish the stronger designated-primary-source convention.
The five remaining questions, including the arithmetic questions, have no
complete readings here.

### RX06 and RX07

RX06 asks for the dimension of the actual regular module over the selected
`ZMod 5` ring. Both restricted cardinality readings retain the integer ring,
the residue ring, and the actual integer-coefficient homomorphism between
them. One uses the reindexing functor directly, the other the named restricted
regular module. The cartesian reading retains the actual base map and receiver
in its `source`, `target`, and `hom` records, then forgets the whole cartesian
arrow to sets and compares it with `id(ZMod 5)`. This agrees with [M08]; it
does not yet review the unreadable linear-map reindexing or scalar-action
questions.

RX07 retains the two distinct quadratic presentations `F9x` and `F9y` and the
actual `cmp.f9.translation` isomorphism in `CommRingCat`. Its generator
equations read `e(x)=y+2` and `e⁻¹(y)=x-2`, and its whole inverse equations
retain both ring endpoints. The successive-value reading is the composite
that first forms `x+1` in the source ring and then applies that same `e`;
its expected value is the target generator `y`. These are [M09, M10]. No
claim about the unreadable subsequent square, return map, coefficient maps,
or whole generalized-point equations follows from these five readings.

### RX09

The readable equality has the entire natural-number set as domain and the
integer power-series object as codomain. Its left side is
`SuccessorSeries.successorTerms` at the selected integer commutative ring.
The right side retains natural addition by one, the natural-to-integer
inclusion and power-series constant map, and the whole monoid-power map on
the generator paired with the original natural index. The resulting family
is exactly `n ↦ C(n+1) X^n`, as specified in [M14]. It is not the older
square-coefficient family and is not a finite truncation.

This one question does not include the admitted family or the sum as a claim
operand. The five positive coefficient/binder readings remain open. The
separate [RX09 negative assessment](rx09-negative-interpretation-assessment.md)
concerns the constant-one family's exact rejected admission and is not a
substitute for those positive readings.

## Producer scope and limits

The supplied provenance file is
`/tmp/kernel-mvp-frozen-trials-20261024/initial-provenance.json`, SHA-256
`e5d04f18aa38bccfbeac9ede51d3fcd5f18a07005e0afb3893a51b54c7b09dec`.
It identifies the producer as:

| Component | Source commit | Source tree |
| --- | --- | --- |
| Kernel | `e1a77d3cd5e95ce03b3e4878ae3e969e25b23d93` | `a0232a6079c1ebe64bb0137fcc531241d7cab1d9` |
| Mathematics | `b08e6b3cac7b2464d21419e05b27c89c2c6858d5` | `0ed39a7c95a6c33fcfb0f545d76dac4b78970d25` |
| Contract | `469f5d90bbef964a2b19d407f81d9ca52a5f033d` | `4633972a6cdf788bb22ed7ca77a0ba478c1b2396` |

The receipt records hashes of the question-export binary, `Language.olean`,
`Realize.olean`, the harness binary, and the package-selection manifest. The
harness was neither inspected nor executed by this reviewer. These are the
supplied initial producer receipts, not a complete per-module artifact,
toolchain, and ordered-import record. Mutable build paths have since been
used for later candidates; this assessment does not authenticate the initial
artifacts by hashing later contents at the same paths. The final freeze needs
its own complete provenance and interpretation comparison.

The mathematical review uses the raw term DAGs and actual upstream meanings,
not equality of pretty text, artifact hashes, asserted truth values, or
execution outcomes. It preserves all 86 unreadable questions in the required
denominator. No RX08, prescribed multistage lift, RX10 execution-stratum, or
ownership/reconnection conclusion is established by these 48 readings.
