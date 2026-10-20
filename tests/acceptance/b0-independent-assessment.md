# Independent acceptance assessment

This assessment uses the approved B0 acceptance table and permanent assertion sources,
without reading the kernel, leaves, candidate interpretations, or harness results.
It records mathematical expectations before execution. It neither admits assertions nor
activates an interpretation baseline, accepts an upstream release, or accepts B0.

The assertion source revision inspected is
`76d37bbfab783eecd3383f965aad1e34d9027fc2`. The published `lean-categories/main`
revision verified with `git ls-remote origin refs/heads/main` on 2026-10-20 is
`a2123729df092e58b6fb0cd39c78db5e1714faf2`. These identify the inspected inputs;
they do not introduce dependency pins. A later dependency update requires its own
interpretation comparison.

## Question preservation

The governing requirement is architecture.md, “Preserve the question by construction,”
and construction directive B. A correct result does not establish the identity of
the question. Every admitted identity, including one that cannot currently be read,
needs its complete typed interpretation and a comparison at the actual mathematical
dependency revision. The source inventory contains 153 distinct identities across
17 `.cas` files; this is an inventory check, not 153 verified interpretations.
The full assertion source inventory remains in scope.

The following distinctions can be specified independently of any candidate:

| Source assertions | Mathematical datum that a comparison must retain |
| --- | --- |
| `numbers.integers.sum`, `numbers.rationals.sum` | The equality relation and its ambient ring, despite both statements displaying `2 + 3 = 5` |
| `numbers.zmod5.sum`, `numbers.zmod7.value` | The modulus and the maps admitting literals into that particular quotient ring |
| `finite_sets.member`, `finite_sets.not_member`, `finite_sets.subset_union` | Membership, nonmembership and inclusion are different relations; their truth values cannot identify them |
| `sets.card.z4_cubed`, `sets.card.z7`, `sets.card.z5_empty_power` | Both the base object and the exponent, including the empty exponent |
| `numbers.containments` | All three inclusion propositions and their conjunction; recording only operands or the final truth value loses the question |
| `sets.limit.pullback.card`, `finite_sets.limit.pullback.card` | The selected cospan, all three objects, both maps, and the category in which its pullback is formed |
| `matrices.kernel` | The rational linear map with matrix `[[1,2],[3,4]]`, its source and target, the kernel construction, and equality to the zero subspace of its source |
| `subspaces.kernel` | The span of `(1,0,1)` and `(0,1,1)` in `ℚ³`, the map `(a,b,c) ↦ (a+b-c,0,0)`, and equality of subspaces of `ℚ³` |
| `composed.root_sum`, `composed.root_product` | The distinct sum/product operations, complex roots of the specified nonzero polynomial, bound variable, index object and its multiplicities convention |
| `calculus.limit_sinc` | The punctured limit at zero; the question does not assert that the partial quotient is defined at zero |
| `calculus.taylor_exp`, `calculus.taylor_sin` | The smooth function, expansion point and membership in real formal power series; membership is not a claim of analytic convergence |
| `integration.primitives`, `integration.normalized` | A coset of constants versus the selected primitive with value zero at zero |
| `algebras.polynomials`, `schemes.affine_line` | The base ring, its constants map, and the induced map on spectra; carrier equality cannot replace an algebra or a scheme over its base |

The complete source-grounded question specifications, including section-local
bindings, relation types, parameters and mathematical justifications for every
admitted identity, are in [question-specifications.md](question-specifications.md).
Their opaque typed comparison must still assess routes, chosen structures and
proof-dependent data. Preservation of a declaration name alone does not establish
preservation of its definition across upstream revisions.

## Independent assessment of `series.*`

The unchanged source in `series.cas` defines

\[
 f=\sum_{n\in\mathbb N}n^2t^n\in\mathbb Z[[t]].
\]

Its terms are the power series
`C ((n : ℤ)^2) * X^n`, indexed by natural numbers. The codomain is power series
over the integers with the `(t)`-adic topology, not the integers with a scalar
infinite-sum operation. Its summability follows because `X^n` divides the nth
term. For a fixed degree `d`, the coefficient of the nth term vanishes unless
`n = d`, when it is `d²`. Thus the sum has coefficient `d²` at degree `d`.

This interpretation is supported directly by the published upstream declarations
in `LeanCategories/Catalogue/Semantics/Algebra/Series.lean`:

- `CasCatalogue.Algebra.Series.summable_of_X_pow_dvd` proves the stated summability.
- `CasCatalogue.Algebra.Series.hasSum_C_mul_X_pow` identifies the sum with
  `PowerSeries.mk c` for `c : ℕ → R`.
- `CasCatalogue.Algebra.Series.tsum_C_mul_X_pow` proves that identification for
  the infinite sum.
- `CasCatalogue.Algebra.Series.powerSeriesSum_C_mul_X_pow` states the same
  identification at the catalogue operation.

The coefficient operation is
`CasCatalogue.Algebra.Calculus.coefficient` in
`LeanCategories/Catalogue/Semantics/Algebra/Calculus.lean`, defined using
Mathlib `PowerSeries.coeff`. The upstream cited mathematical source is
Bourbaki, *Algebra II*, IV.4.2; the formal statements above provide the more
precise source for this particular identification.

Consequently the four existing expectations, fixed before any execution, are:

| Assertion | Typed mathematical question | Expected value |
| --- | --- | --- |
| `series.coefficient_two` | Equality in `ℤ` between `[t²]f` and `4` | `4` |
| `series.coefficient_three` | Equality in `ℤ` between `[t³]f` and `9` | `9` |
| `series.coefficient_zero` | Equality in `ℤ` between `[t⁰]f` and `0` | `0` |
| `series.coefficient_four` | Equality in `ℤ` between `[t⁴]f` and `16` | `16` |

A coefficient-sequence construction and a sum of power-series terms have a
proved mathematical identification for this family. That theorem can justify
an independently assessed migration of a representation. It does not justify
erasing the ring, topology, index object, full family or the proposition of its
summability proof. It does not identify arbitrary infinite sums with coefficient
sequences. This source assessment accepts no historical or candidate fingerprint.

## Independently selected extension specimens

These specimens are selected from the approved mechanism requirements, before
observing candidate behavior. They are mathematical trial expectations, not a
dispatch brief or a request for upstream work. Their formal vocabulary must be
supplied through independently approved published mathematics. No local definition
or missing semantic row is supplied here to stand in for that input.

| Required mechanism | Selected mathematical specimen and expected observation |
| --- | --- |
| New structured object | Two orders on the five-element set, the usual order and its reverse. Each underlying set has cardinality five; the chosen orders remain distinct. Existing applicable set operations are inherited through the actual forgetful functor. |
| New generic operation | Formation of the set of two-element subsets of a finite set. On an existing five-element set its cardinality is ten: the twenty ordered distinct pairs have two orders each. Its arrival must enrich existing applicable objects without changing them. |
| Generic group-valued construction | The automorphism group of the cyclic group of order five has order four, since an automorphism sends a generator to one of four generators. Inversion comes from its group structure, without a construction-specific inverse inventory. |
| Classifier/refinement | The subset `{n ∈ ℤ : n² ≤ 9}` has exactly seven elements, `-3` through `3`. Its formal finiteness proof permits refinement into finite sets, retaining its subset inclusion into `ℤ`; a computed property answer alone cannot establish placement. |
| Competing structural routes | A commutative ring reaches its underlying set through its additive group and through its multiplicative monoid. These are different functors until the supplied comparison identifies the relevant carrier projections. An unresolved comparison requires ambiguity, not precedence. |
| Parameter/base transport | Restrict the one-dimensional `ℤ/5`-module along `ℤ → ℤ/5`. The underlying additive group has five elements, and the integer `2` acts by multiplication by its residue class. The scalar map is part of the question. |
| Nonidentity presentation change | In `𝔽₃[x]/(x²+1)` and `𝔽₃[y]/(y²+y+2)`, send `x` to `y+2`. The relation is preserved since `(y+2)²+1 = y²+y+2` in characteristic three. Transport uses this map, not equality of presentations. |
| Structured result lifting | In `ℚ²` with form `diag(2,3)`, take the map `(a,b) ↦ a`. Its kernel is the second coordinate line, with its inclusion into `ℚ²` and restricted form `[3]`. Returning a dimension or a bare line omits defining structure. |
| Generic application/admission/binder | The family `(n+1)tⁿ` over `ℕ` in `ℤ[[t]]` is summable by divisibility by `tⁿ`, and its coefficient at degree three is four. Reading must preserve the binder, family, coefficient ring and summability proposition. |
| Leaf replacement | Reuse the fixed assertion `sets.card.z4_cubed`, whose expected answer is `64`, under the mandated replacement environments. Only computational outcomes may change; its typed mathematical question and operation availability must be identical. |

The first two specimens supply the two required directions of extension. A trial
counts only after the relevant new formal input exists and the fixed candidate
and old leaves are supplied. An example already present before freezing cannot
alone demonstrate a post-freeze extension. No trial was executed in this assessment.

The selected structured-result specimen above uses the projection
`(a,b)↦a:ℚ²→ℚ` as a module map with a chosen source form `diag(2,3)`.
It cannot be an isometric morphism in fixed-value `Bil(ℚ,ℚ)`: the vector
`(0,1)` maps to zero while its self-pairing is three. Its nonzero restricted
kernel form is a legitimate arbitrary-subobject restriction question, but
this selection does not provide the B0 formed-arrow kernel trial. The exact
source, map and expected restricted form are retained; no easier map is
substituted. The published-signature audit and remaining inputs are detailed
in [b0-formed-positive-specifications.md](b0-formed-positive-specifications.md).

## Compositional arguments and remaining acceptance inputs

The acceptance table requires arguments in addition to examples. The arguments
must establish the generic rules: application at the declared dependent signature;
recognition by declarations with parameters; closure under composition of actual
structural functors; comparison by supplied invertible cells; cartesian reindexing;
composition of prescribed lifts; and refinement only from formal proof. The
execution boundary must consume the same question produced by interpretation.
These are the fixed argument obligations, not established arguments about an
uninspected candidate. None follows from the examples in this file.

The question specifications cover all admitted source identities. Still required
are their complete typed interpretation comparisons at the actual mathematical
revision, the frozen candidate and old-leaf revisions, independently published
trial mathematics, and execution of all required positive computations and
protected negatives.

The protected operations needed are authoritative admission or correction of
initial interpretations, activation of an independently assessed interpretation
migration, and the independent B0 acceptance operation at the supplied candidate.
This author has not been supplied those operations and does not substitute a
role environment variable, manifest edit, source commit or self-issued approval.
Source assessment and specimen selection remain executable without them; the
activation and final judgment remain unperformed.
