# Independent review of the 48 initially readable extension questions

**Historical assessment retained.** The initial producer's 48-reading review
below remains specific to that producer. The later
[clarified integrated producer assessment](#clarified-integrated-producer-94-complete-readings)
reviews 94 complete readings out of the same 134 required IDs, including 47
newly complete questions. It also records one formerly readable question that
is empty in the later export. Neither section establishes final readiness.

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

## Clarified integrated producer: 94 complete readings

This subsequent independent assessment concerns the closed interpretation-only
payload supplied on 2026-10-24. **All 94 present mathematical meanings agree
with their fixed questions, subject to the already recorded RX05 primary-route
qualification. Forty required readings are empty.** The reviewed RX08 meanings
use the independently specified additive `.kernel()` clarification; this does
not make the original ambiguous `.ker()` source readable. The earlier producer's
findings above remain historical findings, including its readable RX04 predicate.

This review read fixed mathematical sources and their independent derivations,
public mathematical declarations, the public question-format documentation,
protected historical readings, and the supplied interpretation-only payloads.
It did not consult kernel or computational-leaf implementation, backend manifests,
runtime answers, diagnostic/failure JSON, or other agents' engineering inventories.
No Lean process, build, interpreter, execution harness, or computational engine
was launched by this reviewer. The earlier disclosure above remains intact;
there was no new engineering-outcome input to this subsequent review. This is
engineering semantic assessment, not acceptance of a mathematical release,
baseline migration, or computational correctness.

### Closed inputs and exact source selection

The payload is
`/tmp/kernel-mvp-frozen-trials-20261024/readings-clarified-integrated.json`,
2,632,469 bytes, SHA-256
`1602cfa3c7e42b615db0b77f904507083f45d4618079bca4f53d513b85f4e423`.
The supplied producer identities are:

| Component | Source commit | Source tree |
| --- | --- | --- |
| Kernel | `5f7f5a2a0b37e7285e1d186caa062952a7ca52b0` | `8df36b676b78457158215e34b968fcd4523fac00` |
| Mathematics | `82d1370de372a00a86391b74fc2566c9547dfcb6` | `c36cd3ae4d84e303db5b39017066a8b880eba43b` |
| Contract | `90d7d3f1833cff39b77024dcee2dc43213e623ad` | `c2d23e17c75960d4e2ca775b4094e4aecbd9e147` |

The supplied kernel publication is `dd7a448ac1a638882e32aea28b7445ddb577e0aa`,
with the same tree. The reviewer used a separate worktree at the listed local
kernel commit and the clean public mathematics checkout at the listed mathematical
commit. The public mathematical definitions, rather than their declaration names
alone, grounded the comparisons below.

The selected source receipt
`/tmp/kernel-mvp-frozen-trials-20261024/positive-clarified-inputs.json` has SHA-256
`265ec74af707124dea13f22b9e324055567c5625f7d637e8ab8cd375ab3a76e3`.
The fixed `inventory.json` in the same directory has SHA-256
`50d5c313fd5b2ecb6c108d8711d3605dbe9888312f4486d0e0121a5b5995c0d3`.
The reviewer reconstructed the ID/source-line inventory directly from the fixed
`.cas` files, compared it with both supplied inventories, and checked every
selected file's bytes against the independently fixed source and receipt.
All 134 unique IDs occur exactly once; every source basename and one-based
question line agrees. All 14 selected inputs are unchanged except the already
fixed additive RX08 clarification described next.

The original [RX08 source](rx08-ordinary-kernel.cas), SHA-256
`5bcb0bf768bd231dc93dd81fd4344fd12666145163f1df6327ed6731000ce118`,
remains intact. The selected
[clarified proposal](clarifications/rx08-ordinary-module-kernel.cas.proposal),
SHA-256 `38a8c9d4fb8145ea337f33d8aa724effae21ae06c616681c89a077ff2311e89f`,
differs only at the binding `let K := projection.kernel()` in place of
`let K := projection.ker()`. The seven IDs, question lines, assertions, and
mathematical inputs are unchanged. The independent clarification rationale was
read before interpreting the new payload. In the public mathematics,
`meth.kernel` on `ArrowsModules` and the ordinary module `meth.arrow_ker`
select the same `LeanCategories.kernelFunctor`; the former
spelling selects the module owner explicitly without inventing a new kernel.
The group `.ker()` route remains a distinct ambiguity control.

The format document used for the new fields is
`specs/question-identity-format.md` at public documentation commit
`ea69eb2bdd4089667b7003e5de9887f67db52a6c`, SHA-256
`1ae4153ca9f2c2aaedd294ddabe855d9f8758df0f674070f004ca4277f57a42b`.
It was read independently of implementation. Its descriptions of
`operationEquivalence`, nested candidate/source indices, universal families,
and the transparent `Trace.operationResult` marker were necessary to interpret
those records; the reviewer did not infer their meanings from their names.

The driver was inspected only for its ordered imports: `CasTools.QuestionExport`,
then the mathematical modules `Foundation.FiniteOrders`,
`Foundation.TwoSubsets`, `Foundation.IntegerSquareBounds`,
`Algebra.CyclicQuotients`, `Independent.ScalarAndFormExtensions`, and
`Independent.InterfaceCompletionTests`, each mathematical path prefixed by
`LeanCategories.Catalogue.Semantics`. Each ordinary import is followed by its
corresponding meta import. The orchestrator reports that imported artifact
hashes remained unchanged during this run. This semantic review did not
independently authenticate a full toolchain/package/resolved-artifact receipt;
source and payload identities above do not replace that separate provenance
obligation.

### Completeness and closed typed graphs

The 94 complete records comprise 13 `literal`, 73 `homs`, two
`judged:(some true)`, and six `judged:(some false)` claims. Both complete term
tables were parsed for every present record. Term tags, arities, universe-level
syntax, table-local references, absence of unresolved/free terms, bound-variable
scope, and all claim and retained-operation dependencies were checked. All
**10,159 operation-result/metadata term-reference occurrences** are valid and
closed. Candidate and source indices in all six operation-equivalence records
were checked in their own enclosing arrays, separately from term indices.
The check retains parameter, operand, route, and comparison order and operation
record multiplicity. It is a structural reading check, not a fresh Lean
typecheck or an acceptance oracle.

| Fixed selected source | Complete | Required | Current reviewed scope |
| --- | ---: | ---: | --- |
| `rx01-selected-orders.cas` | 4 | 4 | Both selected orders, cardinalities and opposite relation orientations |
| `rx02-complete-core-action.cas` | 7 | 7 | Actual bijection, both maps, whole core action, full direct-image comparison |
| `rx02-two-subsets.cas` | 2 | 2 | Cardinality and singleton exclusion |
| `rx03-complete-automorphism-arrows.cas` | 14 | 14 | Full inverse, coordinate, conjugation and all-integer-class equations |
| `rx03-cyclic-automorphisms.cas` | 12 | 12 | Group construction, selected presentations, both products, power and reuse |
| `rx04-square-bound.cas` | 6 | 7 | Exact finite extent, membership list, classifier and original admission |
| `rx05-carrier-diamond.cas` | 13 | 13 | Complete comparisons and naturality, scalar samples and distinct operations |
| `rx06-reindexing.cas` | 8 | 10 | Selected scalar restriction, cartesian arrow, actions and actual reindexed-map sample |
| `rx07-f9-transport.cas` | 17 | 17 | Both quotient presentations, full coefficient maps and successive generalized maps |
| `rx08-ordinary-kernel.cas` (clarified selection) | 4 | 7 | Whole projection, complete ordinary kernel and both zero composites |
| `rx09-successor-series.cas` | 6 | 6 | Entire admitted infinite family, selected topology, sum and full coefficient map |
| `rx10-fixed-execution-question.cas` | 1 | 1 | One unchanged mathematical question, with the actual full module arrow |
| `rx-lift-prescribed-stages.cas` | 0 | 26 | No complete reading |
| `rx-lift-source-comparison.cas` | 0 | 8 | No complete reading |
| **Total** | **94** | **134** | **40 empty readings** |

The 40 empty records are all 34 questions in the two lift files, plus
`complete.rx04.exact_predicate`, `complete.rx06.whole_reindexed_map`,
`complete.rx06.whole_scalar_action`, `complete.rx08.full_coordinate_inclusion`,
`complete.rx08.full_restricted_pairing`, and
`complete.rx08.restricted_pairing_one`, all with the common
`reconstructed_extensions_20261024.` prefix. Their absence supplies no
mathematical conclusion and no diagnosis of its cause. The count does not
absorb the separate RX05 declaration environments, RX09 negative admission,
or RX10 execution/ownership observations.

There are 47 newly complete readings and 47 readings shared with the initial
export. The earlier `complete.rx04.exact_predicate` reading is now empty.
Its earlier independent review remains valid for that earlier producer; it
does not satisfy the current producer's missing obligation.

### Presentation changes were compared substantively

Among the 47 common complete questions, 24 original claim DAGs and displays
change, and the two already readable judged claims also acquire explicit
execution-proposition/type roots. The remaining 21 full claim graphs are
unchanged. For all 47 original claims, applying only the publicly documented
transparent equation
`Trace.operationResult binding (α := A) value = value` leaves the same
complete original claim DAG as before. Binding strings and their operation
records were still reviewed separately; the equation does not identify two
different operations, routes, selected structures, or witnesses.

Fourteen shared operation tables have additional changes beyond these markers.
They were read as changes to retained mathematical descriptions:

| Questions | Retained-record change and semantic comparison |
| --- | --- |
| RX03 `actual_inverse_arrow`, both `arrow_inverse_*`, `double_class_one`, `double_class_three`, `triple_class_two` | Additional records expose the actual `ZMod 5` ring numerals, their multiplicative-monoid view, the units admission, the unit-group and automorphism-group carriers, and composition with `byUnitMorphism 5`. They retain the same selected coefficients and complete automorphism arrows already present in the claim. The last three also replace the abbreviated group-arrow transport with a complete contextual route. |
| RX03 `inverse`, `conjugation_retains_inverse`, `conjugated_value_reuse` | Contextual routes retain the complete `Groups` and `Sets` bundles and actual forgetful action applications. Receivers remain `byUnitMorphism 5` and the forward/inverse `Aut` action at the same residue comparison. Newly explicit composition records consume the selected point and group inverse. |
| RX04 `exact_members` | Three composition records explicitly form the integers `-1`, `-2`, and `-3` using the original integer-ring negation. |
| RX07 `generator_forward`, `generator_backward`, `successive_value` | Complete category contexts replace abbreviated ring-object and presentation-arrow transports; the ordered routes and actual forward/backward comparison remain the same. Additional product/composition records expose the original addition and negation in the appropriate selected quotient ring. |
| RX09 `full_family` | The numeral-one record now attaches to the point `Fin 1 → ℕ`; a separate retained terminal composite gives the constant-one map on the entire natural-number domain. New composition records expose natural successor and multiplication of the coefficient series by the indexed power. The complete family is unchanged. |

The other 33 shared operation tables have no additional difference after that
single transparent-marker equation, preserving ordered metadata and
multiplicity. These comparisons locate presentation changes; independent
comparison with the fixed mathematical sources below supplies the meaning
assessment.

All eight current judged records retain the original proposition, its exact
execution proposition, and `Prop` type. Here the execution proposition is the
same complete proposition as the recursively retained question; none is
replaced by `True` or `False`. The true orientations are ordinary-order
`0 ≤ 1` and finiteness of the radius-three integer extent. The false
orientations are the reversed-order comparison, singleton membership in the
two-subset image, the square of doubling being the automorphism identity,
finiteness of all integers, equality of the two specified arithmetic results,
and the selected F9 generator image being the unshifted target generator.
The claim prefixes preserve those fixed expectations rather than reporting
an observed result.

### Current mathematical comparisons

#### RX01 and RX02: selected orders and the complete core action

The four [RX01 questions](rx01-selected-orders.cas) retain
`FiniteOrders.ordinary 5` and `FiniteOrders.reverse 5` as complete linear-order
objects. Cardinality uses `linearOrdersForget` at each selected object. The
relation claims use `op.linear_orders.le` with that same selected order and
the ordered points zero and one of `Fin 5`; their opposite truth orientations
agree with [M01](../source-notes.md#m01-selected-finite-linear-orders).
Equal cardinalities have not identified the two relations.

All nine [RX02 questions](rx02-complete-core-action.cas) and
[two-subset questions](rx02-two-subsets.cas) retain `finRevIso 5` and
`finRevCore 5`, including both complete maps and the original `Fin 5`
endpoints. The whole induced action is `TwoSubsets.onCore.map`; the two
core arrows are composed before applying that functor. The complete direct-image
equation retains `TwoSubsets.inclusion` into finite subsets followed by
`FiniteSubsets.inclusion` into the power set, and the actual direct image of
the reversal on the other side. Its source is the entire two-subset object.
The singleton-negative question admits the singleton `{0}` and asks membership
in the image of that actual inclusion. It is not a question about an arbitrary
set map or a repeated pair. These meanings agree with [M02](../source-notes.md#m02-unordered-two-element-subsets),
`CoreIsomorphisms.finRevIso`, and the complete core-action supplement.

#### RX03: automorphisms, actual arrows, and infinite-domain coordinates

All 26 questions in [the construction file](rx03-cyclic-automorphisms.cas)
and [the arrow supplement](rx03-complete-automorphism-arrows.cas) retain the
group-valued `Aut` construction with the complete `Groups` category bundle,
the selected cyclic quotient at five, and its actual group comparison with
`FiniteGroups.cyclic 5`. The forward and inverse presentation maps have
their full group endpoints. Each construction-map record retains both
directions of the input core isomorphism and the actual morphism used by `Aut`.

Doubling and tripling remain the images under `byUnitMorphism 5` of the
admitted multiplicative units with underlying ring numerals two and three.
The selected monoid, invertibility propositions, and complete unit data remain
present. Both products, inversion, fourth power, and the false square-identity
question are operations in this actual automorphism group. The identity is
its monoid identity, and the exponents are the specified natural numbers.

The whole coordinate and conjugation claims use actual
`AutomorphismArrows.groupsForward`/`groupsBackward` and the specified three-map
conjugation by the residue comparison. Expected whole doubling/tripling maps
are admitted group morphisms with their original full functions and group-map
obligations. Their expressions `z^2` and `z^3` use the multiplication on the
selected multiplicative presentation of the additive residue group. The
all-integer-class equations retain all of `ℤ` as domain and the complete
`quotientMap 5` on each side, with the specified integer multiplication.
The three finite samples use classes of integer numerals formed by that same
quotient map. Thus the class of one is not replaced by the group identity.
These comparisons follow [M03–M04](../source-notes.md#m03-cyclic-quotient-automorphisms),
the public `AutomorphismArrows` declarations, and the independent full-arrow
derivations; no permutation count or point sample replaces a whole group map.

#### RX04: the fixed square-bound extent and its admission

The six present [RX04 readings](rx04-square-bound.cas) retain bound three,
the actual integer-square-bound extent, its finite refinement and its original
admitted subset. The membership-list equation contains all seven specified
integers with their integer-ring operations. Admission is observed through
the actual `FiniteSubsets.inclusion : Finset ℤ → Set ℤ`, not a new enumeration.
The finite classifier applies to the exact extent, whereas the false classifier
question applies to the entire integer object. These agree with
[M05](../source-notes.md#m05-the-exact-square-bound-and-finite-refinement).
The universal predicate equation is empty in this producer and remains open.

#### RX05: exact carrier comparisons and operation families

All 13 [RX05 claims](rx05-carrier-diamond.cas) retain the prime-residue field
at five and the complete primality proposition `Nat.Prime 5`. Explicit
multiplicative and additive carrier routes remain ordered. Both components
and both endpoints of `cmp.rings.carrier` are retained at the forgotten
selected ring, and the inverse equations keep the corresponding whole
carriers as domains. Naturality retains the full integer-coefficient map,
its two actual forgotten maps, and the comparison component at the integer
ring. The two evaluations at seven remain specializations of those same maps.
This is the meaning specified by [M06–M08](../source-notes.md#m06-the-prime-residue-field-and-distinct-operations).

The arithmetic claims retain `op.rings.add` and the actual multiplication
operation. The two RX05 operation-equivalence records retain both
`MonoidOperations.mul` after field-forget, multiplicative commutative-monoid,
and monoid steps, and `NamedRings.mul` after field-forget and ring steps.
Each includes both complete declaration applications, result terms, source
contexts, ordered action applications, actual field parameter, universal
families, their dependent types, and a universal identity proposition.
The four analogous RX07 records use the complete commutative-ring context
and the actual selected F9 source or target parameter.

The identity proof's serialized proposition in these six records is reflexive
after identification of the two families; that reflexive shape alone would
not justify equating arbitrary candidates. Here the independently read public
definitions supply the reason: `MonoidOperations.mul` and `NamedRings.mul`
are the whole binary function `(a,b) ↦ a*b`; the actual forgetful functors in
`CommutativeMonoids.lean`, `Algebras.lean`, and `Fields.lean` retain exactly
the multiplication of the same selected ring. The two families therefore
agree over the full dependent field/commutative-ring context, before any
supplied operands. No inference from `1*1` or `2*y` alone is used. Addition
is not in this multiplication-equivalence class; its distinct selected
operation and the original false equality remain present.

The inherited cardinality still uses the third route through additive
commutative monoids and additive monoids. Its mathematical cardinality is
comparison-equivalent to the fixed carrier question, but this export **does
not establish the designated multiplicative primary-route convention**.
The earlier [RX05 environment assessment](rx05-interpretation-assessment.md)
and its scope remain separate. Reviewing these 13 positive claims does not
establish any new four-environment ambiguity/reordering result.

#### RX06 and RX10: actual scalar restriction and whole module-arrow input

The eight present [RX06 questions](rx06-reindexing.cas) keep the regular
module over the actual residue ring, the integer ring, and the actual
integer-coefficient ring homomorphism `q`. Named restriction has ordered
parameters `R,S,q`. Reindexing and the cartesian arrow retain that same base
morphism and the original regular module; the whole cartesian carrier
observation is the identity function on the residue carrier. The original
dimension is over the residue ring. Neither cardinality question asserts
freeness or dimension one over the integers.

Each of the three scalar-action samples applies `op.modules.scalar_action`
at the integer ring and the actual restricted module. The scalar therefore
comes from `ℤ`, including the negative scalar, and the module argument remains
the selected residue element. The reindexed-map sample first admits the
entire `m ↦ 2•m` function as a module morphism over the residue ring. Its
`IsLinearMap` proposition uses that very same function and scalar/module
parameters. The actual module-family reindexing is applied to that whole
module arrow before its underlying map is evaluated at three.

The single [RX10 question](rx10-fixed-execution-question.cas) has the same
complete claim graph as that RX06 sample and retains the same full admitted
module arrow. These meanings agree with [M08](../source-notes.md#m08-scalar-restriction-along-the-selected-coefficient-morphism)
and `IntegerResidueModules.reindex_map_apply`/`reindex_double_three`.
The complete reindexed-map and full scalar-action equations are still empty.
A readable sample, even one containing the complete input arrow, does not
discharge those two missing universal claims. Nor does this interpretation
establish RX10's six execution conditions or live-session ownership/reuse.

#### RX07: successive values and complete generalized maps

All 17 [RX07 questions](rx07-f9-transport.cas) retain the two distinct quotient
presentations over `ZMod 3`, their distinguished roots and coefficient maps,
and both directions of the actual `quadraticComparison`. Its whole inverse
equations are equations of ring morphisms, not only maps of displayed carriers.
Both coefficient equations retain the full coefficient domain. The false
nonidentity question uses the actual forward comparison at the source root.

The successive value graph retains the original `x+1`, its actual image under
the forward map, the square of that returned value in the target ring, and
the selected inverse applied to that square. The full generalized-point
equations have all of `ZMod 3` as their original domain: `f` contains the
source coefficient map, `g` is its actual composite with the presentation,
`h` squares the returned `g(c)`, and `k` applies the actual inverse to `h`.
The inverse-reuse equation retains the same `g`. The three sample questions
specialize those full maps at the original coefficient one. Actual ring
objects and ordered parameters survive the set-level views and documented
parameter identifications. These are precisely the independent requirements
and formulas of [M09–M10](../source-notes.md#m09-public-f9-presentations-generators-and-maps)
and `coverage-and-derivations.md`; an identity carrier map or freshly rebuilt
value has not replaced the nonidentity comparison or its returned results.

#### RX08: ordinary module kernel under the explicit clarification

The four present clarified [RX08 readings](clarifications/rx08-ordinary-module-kernel.cas.proposal)
retain the actual rational one-by-two row `[1,0]`, its complete
`rowLinearMap`, and its exact module endpoints. The expected projection is
admitted as the complete rational module morphism taking the first coordinate
of the forgotten `RationalDiagonal23` source. Its `IsLinearMap` proposition
retains that same full function.

`meth.kernel` is applied directly to the complete module-arrow object with
an empty owner route. Its result is the actual `kernelFunctor` object,
including the kernel and its monic inclusion, not an independently selected
one-dimensional module. The dimension observation is made on that result.
The zero-composite claim reuses its actual `source`, `hom`, and `target`
projections with the original projection. The separate restricted-form
composite retains all five dependent parameters of
`ordinaryKernelRestriction`/`ordinaryKernelInclusion`, including the same
original row morphism and form; it then forgets the actual inclusion to
modules and compares its composite with the whole zero module map on the
same source. This agrees with [M11–M12](../source-notes.md#m11-ordinary-projection-complete-kernel-and-restricted-form)
and the independently fixed clarification.

The coordinate inclusion and both pairing observations are empty. This review
therefore does not establish a complete returned coordinate presentation,
the `3st` pairing claim, the separate universal property observations, or
the universal formed-arrow negative from this export. None of the 34
prescribed-lift questions has a complete reading either; equal carriers or
the readable ordinary kernel supply no substitute for their actual staged
inclusions, full forms, comparisons, cones, or universal factors.

#### RX09: the whole admitted successor family and its selected sum

All six [RX09 positive questions](rx09-successor-series.cas) retain the
infinite natural-number domain and the selected integer commutative ring.
The full family is the original `SuccessorSeries.successorTerms`, compared
with the whole callable `n ↦ C(n+1)X^n`. The admission parameters remain,
in order, the actual `powerSeriesTAdic` Hausdorff topological monoid and
the index set. The admission's `toFun` is the complete successor family;
its exact proof proposition is summability of that family in `Series.tAdic`
with the unconditional natural-number summation filter. It contains no
truncation parameter or substituted finite family.

The binder keeps ordered parameters `R,N`, its actual
`powerSeriesSumDomain`, and the admitted whole family. In the full coefficient
map, the admitted point is carried constantly over the degree domain before
the same sum is observed; this does not change the family's own natural-number
domain. The full coefficient equality ranges over every natural degree and
uses independent integer successor on the expected side. The four scalar
questions use degrees zero, one, three, and five with the fixed expected
integers one, two, four, and six. These meanings agree with
`SuccessorSeries.successorTerms`, `successorTerms_admission`,
`successorTerms_sum`, the public `Series.SummableFamily`/`admit` definitions,
and [M14–M15](../source-notes.md). The old square-coefficient family and
its degree-three value are not substituted. The separately fixed constant-one
negative and its earlier assessment remain outside these six positive readings.

### Permanent questions and remaining scope

This extension export is not a new permanent export. The previously reviewed
153-record permanent payload remains separately identified in
[the permanent assessment](permanent-interpretation-assessment.md), SHA-256
`d11878e7689a377cfa72e051e8ceb530f7f320aae50d36de3a0fef98e70e0147`.
No current permanent producer claim is inferred from it. The protected
permanent source records remain unchanged: admitted-list SHA-256
`af03b1df56a94d49273e334890ce6a3da3170c645abf4d4670c0ff334cb47b29`,
question-list SHA-256
`31187b43d5897f99e2546cfd215264f673f24798b5faaec851764eb2c22ac95a`,
and historical-reading SHA-256
`ba744aef6055bf640eeaf3f99cb87a6c0eb9f0fdb084ce789384204f4d87776b`.
The historical record contains only 142 readings; the eleven previously
missing readings remain explicitly distinguished in the permanent assessment.

The temporary read-only graph aid used here was
`/tmp/final_independent_meaning_review.py`, SHA-256
`d1afb8b0bfd316ccd8bc39d4e433c2798669e019b311d87c06db9b423e93ce83`,
using the previously supplied rendering helper, SHA-256
`2400e054a0aa5fd047b579f81d2749538a0a9a5de7fd8e74804cc38d748ee9df`.
It read fixed source and payload files only and wrote no baseline. Structural
identities and hashes were used to locate changes, not to authorize their
meaning. This assessment preserves all 134 questions in the denominator,
all 40 current gaps, the original RX08 ambiguity control, the RX05 convention
qualification, and the separate execution and ownership obligations.
