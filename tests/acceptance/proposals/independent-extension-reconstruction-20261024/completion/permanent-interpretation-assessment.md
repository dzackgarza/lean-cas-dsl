# Independent review of the 153 permanent interpretations

## Result and scope

The supplied interpretation-only export contains a complete reading for each of the
153 unchanged permanent questions. The readings preserve the mathematical questions in
the fixed `.cas` sources and the independently authored
[`question-specifications.md`](../../../question-specifications.md). This assessment found
no substantive mathematical mismatch in the reviewed producer. It is a review of the
questions being asked, not a claim that 153 assertions have executed successfully.

The review includes all 17 source files and all 11 admitted questions that lack a retained
old reading. It compares the full typed claim and operation DAGs with the source
mathematics. Neither the human-readable proposition display, equal expected truth values,
nor equal hashes was used as a substitute for that comparison.

This assessment used the fixed mathematical questions, upstream mathematical definitions,
the public DSL specification, the public question format, retained historical readings,
and the supplied interpretation-only export. It did not inspect kernel implementation,
leaf implementation, or runtime answer values. The earlier incidental-information
disclosure in this proposal's [README](README.md#incidental-information-exposure) remains
part of the record; this assessment makes no claim of complete downstream blindness.
No permanent inventory, assertion, reading baseline, or expected proposition was changed.

The conclusion applies to the exact producer below. A later final frozen export must be
compared with this reviewed export before this conclusion is attributed to that later
tuple.

## Exact reviewed evidence

All hashes in this document are SHA-256 unless explicitly identified as Git object IDs.

| Supplied artifact | SHA-256 |
| --- | --- |
| `/tmp/kernel-mvp-permanent-readings-20261024.json` | `d11878e7689a377cfa72e051e8ceb530f7f320aae50d36de3a0fef98e70e0147` |
| `/tmp/kernel-mvp-permanent-failures-20261024.json` | `a8ec39e87eb17b900172b81b71c844fba7d332a5030e6b445eac92cf28fcd36f` |
| `/tmp/kernel-mvp-permanent-provenance-20261024.json` | `9e5d1a1dcd54259d2ecca696786f903bdff631a9cabd87a84766f5274c06068f` |

The first artifact has 153 records with 153 distinct IDs, all with complete `question`
and `proposition` fields. The failure artifact reports required count 153, readable count
153, no unreadable IDs, and no diagnostics. Every exported ID, file, and one-based source
line agrees with the independently assembled source map. The producer's versions of all
17 `.cas` files are byte-identical to the fixed mathematical sources used for this review.

The provenance artifact records the following clean source trees:

| Owner | Git commit | Git tree |
| --- | --- | --- |
| Kernel | `164c0b58b46f0f95a6278eec8abf0ee52520b5c6` | `4d12e698d1e46e108d2c888f90a4974eedc8353b` |
| Public contract | `55ae64fef1198b0d51f07306589f91862268c661` | `60ffbb67ebd5b6e90f73cc9c5c11953b3ea5f7a6` |
| Mathematics | `7e848db36ff74faf62b00304cc0186a8bac641b7` | `4a064c765ec6c3d41e643a9875da74c8e6173392` |

The actual reported toolchain is Lean 4.33.0. The ordered import list is
`[CasTools.QuestionExport]`. The provenance retains the package-selection and build
configuration hashes:

| Configuration | SHA-256 |
| --- | --- |
| Kernel `lake-manifest.json` | `e9ba7addcf9d90658f651615df82bfdcd44b14d178b61383196dfe87e09153e6` |
| `/tmp/kernel-mvp-completion-packages-20261024.json` | `e2c103dcdd2ad903a5e0dc0574627171ef2b5b425816029f9bac0a2f2aeb4a20` |
| Kernel `lean-toolchain` | `302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b` |

The provenance also retains nine resolved `.olean` hashes, including `Language`,
`Realize`, `QuestionIdentity`, `FileItems`, `QuestionExport`, `QuestionExportData`,
`CasContract.Port`, `LeanCategories.Catalogue`, and the mathematical semantic registry.
The four module files named by the export's own failure/provenance envelope were resolved
and independently hashed. Their hashes agree with the supplied provenance:

| Imported module artifact | SHA-256 |
| --- | --- |
| `CasCatalogue.Realize` | `2d52d7e36ffadaf0dc9eb84b3238004785e43beb34fab1cd155db68b03a97f6d` |
| `CasTools.QuestionExport` | `8727089e66235c30ce61311cee239afb1a746478e99cbdbe5d9d2990390643e7` |
| `CasContract.Port` | `be9175c7886bec927d68f9e58b4dac0b937bc9ddc8ee325b61ca53fa9039cc44` |
| `LeanCategories.Catalogue` | `a06303838d71b50574bcbb8dae7bf7f16b64131139ecfbc8491275ff15be3175` |

The kernel module paths resolve into `/tmp/kernel-mvp-build-20261024`; the mathematical
and contract artifacts resolve into their recorded worktrees. This check hashes artifact
bytes; it does not inspect their implementations or establish a separately reproduced
build. Source commit labels alone were not treated as artifact authentication.

The public format note reviewed is `specs/question-identity-format.md` at its file revision
`2d69ba2b533c3aa10d3082ebbf058bd13b520bf7`, with content hash
`d718b360f1b508c30c51b30273453897cb61632625608f53faf61ec387dc29f6`.
That note documents the existing representation. In particular, the exported expectation
prefixes are `judged:(some true)` and `judged:(some false)`, retaining the optional
expectation, rather than a newly inferred execution result.

## Fixed sources and retained historical readings

The following protected files have identical bytes in the producing kernel revision and
the independent source checkout:

| Fixed source or inventory | SHA-256 |
| --- | --- |
| `CasAcceptance/Permanent/admitted.json` | `af03b1df56a94d49273e334890ce6a3da3170c645abf4d4670c0ff334cb47b29` |
| `CasAcceptance/Permanent/questions.json` | `31187b43d5897f99e2546cfd215264f673f24798b5faaec851764eb2c22ac95a` |
| `CasAcceptance/Permanent/question_readings.json` | `ba744aef6055bf640eeaf3f99cb87a6c0eb9f0fdb084ce789384204f4d87776b` |
| `tests/acceptance/question-specifications.md` | `c95c92d082362eae9da4eebc274f5400baff7a079715806e22ecad7abb34af20` |

The old `questions.json` and `question_readings.json` contain 142 entries. All 142 retained
source statements agree exactly with the fixed source statements. Those records contain
19 `settled`, 79 `homs`, 26 `literal`, 17 `decision`, and one `implemented` reading.
Their question fields are opaque identities and their displays can omit implicit data;
they do not contain enough information to reconstruct a complete historical typed DAG.
Consequently this assessment does not claim full DAG equality with an unavailable older
representation. It assesses the current complete readings against the independently
fixed mathematical sources, while retaining the older records as historical evidence.

The 11 admitted questions absent from those old reading files are included in the review:

- `calculus.limit_infinity` and `calculus.limit_sinc`;
- `composed.charpoly`, `composed.det`, `composed.root_product`, `composed.root_sum`, and
  `composed.trace`;
- `factorization.over_complexes`;
- `polynomials.factors`, `polynomials.irrational_roots`, and `polynomials.no_rational_roots`.

None was dropped from the denominator or treated as accepted merely because it now has a
nonempty export. Their underlying expressions, domains, admissions, and expected
operands were reviewed as described below.

## How the comparison was made

Each question was decoded as a claim kind, a complete claim term table, and a separate
complete operation term table. Table indices were treated as local references, not stable
mathematical names. The traversal checked all term references and the binding scopes of
the claim operands, operand types, operation results, and operation metadata. It checked
16,207 operation metadata term-reference occurrences without finding an invalid or open
reference. Claims and their retained dependencies were reviewed together, including
proof proposition types, actual category bundles, universe arguments, selected objects,
ordered compositions, parameter presentations, routes, binders, and limit lifts.

The export contains 36 `judged:(some true)`, one `judged:(some false)`, 89 `homs`, 26
`literal`, and one `implemented` question. These are source claim kinds and requested
orientations. In particular, the false finiteness assertion about the integers and the
`sets.implemented.card_fin` implementation request retain their different question
kinds; neither was turned into an ordinary successful equality.

A temporary read-only renderer made the complete tables easier to inspect. Its structural
keys linked equal formal terms across the two local tables; those keys were not expected
answers or an acceptance baseline. Condensed views were supplemented with direct DAG
inspection for admissions, entire binder bodies, literal graphs, matrices, scalar maps,
finite-subset inclusions, composed arrows, and selected limit diagrams. The mathematical
judgment was made from those contents and the independent sources, not from the renderer's
labels or from serialization stability. This review does not independently re-typecheck
every exported term in Lean.

## Complete coverage and mathematical findings

All filenames below are under `tests/acceptance/`. Counts refer to the unchanged permanent
inventory, not newly selected examples.

| Source file | Questions | What the complete reading preserves |
| --- | ---: | --- |
| `algebras_schemes.cas` | 4 | The chosen rational or complex base, polynomial algebra constants maps, all ten variables where specified, and the contravariant `Spec` structure map. Algebra and scheme membership retains its base structure rather than only a carrier. |
| `calculus.cas` | 6 | The actual punctured-domain sinc map at zero, the reciprocal map at positive infinity, their convergence admissions, the ordered integral bounds and integrands, and the entire smooth maps used for Taylor series at zero. |
| `composed.cas` | 8 | The nonzero polynomial and its actual complex coefficient map in root comprehensions, whole finite root sets in sums/products, the monic degree-three companion construction, and the specified order of the two composed real maps. |
| `differentials.cas` | 11 | The rational polynomial ring, relative universal differential into its Kähler module, polynomial derivative as a distinct operation, the full primitive fiber, and its evaluation-at-zero normalization. The scalar half is retained with its unit admission. |
| `ellipses.cas` | 8 | Whole natural arithmetic progressions, the square preimage and its original domain, and primality applied to the specified naturals. The progressions are not finite literal approximations. |
| `factorization.cas` | 6 | Positive-integer and nonzero-polynomial admissions, distinct prime factors versus the separate multiplicity function, the actual complex coefficient map and linear factors, and the strict real approximation inequality. |
| `finite_sets.cas` | 20 | The integer ambient object, all literal extents and Boolean operations, the product and powerset of the selected finite set, the exact comprehension `n² ≤ 20`, and the whole image of naturals under doubling. |
| `fractions.cas` | 6 | The rational denominators admitted as actual units, arithmetic in the selected ring, nonnegative real square roots, and the real codomain of complex absolute value. |
| `functions.cas` | 4 | Both entire real maps, their actual inputs in point observations, and equality of whole maps for the universal evenness question. The universal domain has not been replaced by a single point. |
| `inverses.cas` | 5 | The actual matrix in the unit group of the rational matrix ring, its inclusion and inverse, both multiplication orders in inverse-use questions, the specified right-hand vector, and the rational determinant. |
| `lattices.cas` | 8 | The integer root lattices, chosen bilinear forms, dual maps, actual cokernel parallel pairs with zero in the category of formed modules with varying value module, and the subsequent carrier routes used for cardinality. |
| `linear_algebra.cas` | 12 | The exact rational entries and dimensions of matrices and vectors, column-vector action, rank, the actual matrix defining each kernel, span generators, and the prescribed membership and equality questions. |
| `numbers.cas` | 18 | Integer/rational distinctions, the different moduli of finite residue rings, the ordered canonical inclusions in containment questions, selected arithmetic structures, and real versus complex result codomains. |
| `polynomials.cas` | 10 | The complete integer and rational polynomials, generator and coefficient maps, degree/evaluation operations, nonzero admissions for roots and factors, the empty rational-root question, and exclusion of the actual rational image from the complex root set. |
| `series.cas` | 4 | The entire natural-indexed square-coefficient family, the selected integer power-series ring and topology, its summability proposition, and the four requested coefficient indices. |
| `sets.cas` | 18 | Cardinal arithmetic with its original operands, genuine products and coproducts, the expected-false finiteness question, whole reversal maps, both graph-defined cospan maps, and the finite pullback's selected lift and actual diagram. |
| `several_variables.cas` | 5 | The selected coefficient fields, ten-variable versus two-variable polynomial algebras, correctly bounded variable indices, total degree, and Krull dimension in its extended-natural result type. |
| **Total** | **153** | **No missing or unreadable question.** |

Several cases received explicit deeper inspection because the displayed notation alone
could conceal a different question:

- The finite-set comprehension uses the original bound 20 and exactly the integers
  from -4 through 4. It is distinct from the later extension's square-bound refinement.
- The pullback graph maps retain `Fin 3 → Fin 2` with graph
  `[(0,0),(1,1),(2,1)]` and `Fin 2 → Fin 2` with graph `[(0,1),(1,0)]`, including their
  admissibility propositions. The finite pullback retains `lift.finite_sets.pullbacks`
  and the actual lifted diagram, not a replacement object chosen for its cardinality.
- The matrix and vector literals are the specified rational data: the invertible matrix
  has rows `[1,2]` and `[3,4]`, the input vector is `[1,2]`, and the right-hand vector is
  `[5,11]`. The other kernel-defining matrix has rows `[1,1,-1]`, `[0,0,0]`, and
  `[0,0,0]`. The upstream `LinearAlgebra.lean` definitions make application `mulVec`,
  preserving the intended column convention.
- The lattice discriminant questions retain the chosen cokernel in the category with
  varying value module before the actual carrier route through modules and additive
  groups. They are not cardinalities of an independently selected finite model.
- The differential and primitive questions retain their module-valued targets and
  whole fibers. The normalization is the actual intersection with evaluation at zero,
  with cardinality and singleton equality remaining separate questions.

## Representation changes and their mathematical justification

These are visible presentation changes or elaboration choices, not changes justified by
coincident answers.

**Finite subsets and sets.** Some root and factor equalities use the actual inclusion
`𝒫_fin(X) → 𝒫(X)` before comparing brace expressions. The source specifications state
finite-set equalities. Upstream
`LeanCategories/Catalogue/Semantics/Foundation/FiniteSubsets.lean` defines
`finiteSubsets X := Finset X`, defines `inclusion X` by coercion to `Set X`, and proves
`inclusion_mono` using `Finset.coe_injective`. Equality after this explicit inclusion
therefore reflects equality of the finite subsets. The exported dependencies retain the
finite result, its original object, and this inclusion. This justification does not
permit forgetting root multiplicities where a multiplicity operation was requested;
those questions remain separate.

**Universal function questions.** The universal evenness and composed-function
questions are represented as equalities of complete morphisms in the appropriate set
category. Their full source domains and both maps remain present. Function extensionality
identifies these equalities with the independently specified pointwise universal
questions. No finite sampling or single free-point reading is used.

**Power-series constants.** The retained series family can display its term as
`(C (n : ℤ))^2 * X^n`, whereas the independent mathematical statement writes
`C ((n : ℤ)^2) * X^n`. These are the same family by the power-preservation law of the
constant-coefficient ring homomorphism. The actual natural domain, whole body,
`powerSeriesTAdic` topology, and unconditional summability proposition remain in the
reading. The four coefficient queries do not replace the family or its admission.

**Limit domains and filters.** The sinc limit uses the actual punctured line and the
comap of the punctured-neighborhood filter. The limit at positive infinity uses the
actual group of nonzero real numbers and the comap of `atTop`. Upstream
`Algebra/RealLimits.lean` supplies `limit_eq_iff_tendsto`,
`approachInfinity_infinity`, and `limitAtInfinity_eq_iff_tendsto`. These identify the
admitted limit operations with the requested limits on their genuine domains; they do
not supply arbitrary values for nonconvergent functions. The exported admission
propositions retain the actual functions and these filters. For Taylor questions,
smoothness is retained; this review does not infer analytic convergence from it.

**Canonical scalar maps.** Integer, rational, real, and complex numerals are sometimes
connected by explicit canonical inclusions rather than identical surface numerals.
Their source and target objects and ordered maps remain present. In particular, the
real approximation question may realize absolute value by the canonical real-to-complex
map followed by complex absolute value. Its restriction to real inputs is the ordinary
real absolute value. This is a justified scalar presentation; arbitrary maps between
equal carriers would not have the same justification.

## Limits of this conclusion

This is an interpretation-preservation assessment. It does not establish computational
correctness, successful execution, fresh-registration extensibility, session ownership,
reconnection behavior, or the required execution-failure distinctions. It does not replace
the separate 134-question extension interpretation review, the four route-environment
controls, the constant-one admission rejection, or the six execution conditions.

Some permanent clauses observe only an extent or a cardinality. For example, the original
linear-algebra kernel and span clauses observe their specified subsets, and the pullback
cardinality clause observes the apex. Their preserved readings do not by themselves test
all projections, universal maps, or later reuse of a complete returned structure. Those
stronger requirements must still be assessed in the independently fixed extension
questions that request them explicitly.

The producing mathematics predates the one-line `CommutativeRings` surface-name metadata
repair `b08e6b3cac7b2464d21419e05b27c89c2c6858d5`. That repair does not change definitions
or types, but this report does not pretend its resulting artifacts produced the reviewed
export. The final frozen producer and its exports remain a separate provenance and
comparison obligation. Nothing in this assessment regenerates or activates a protected
baseline.
