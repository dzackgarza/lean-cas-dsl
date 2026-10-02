# Independent assessment of the current reported questions

This is an acceptance assessment proposal, not admission, an editable completion
ledger, or a new expected-question baseline. The expected questions remain the
independently authored `b0-interpretations-proposal.md` at `96b3a143` and the
original 153-identity inventory at `bcd08de4`. Candidate propositions and typed
question records were inspected only as claims to compare with those meanings.
No computational output established an expected answer.

Input report: `.tmp/b0-current.json`, SHA-256
`f389893c8cf6770d819e9cf31fe5a4537bafbf8cf852ce9140556920809d6a1a`. The report contains 173 rows: the 153 original identities,
12 unadmitted positive proposals, and 8 failed non-assertion statements.
Its question records bind the mathematical dependency
`6ba577c9db2c54e2c573140fa2e273a5b91d693b`.
The supplied independent source assessment of that dependency and public
metadata/snapshot are mathematical inputs. The upstream-only diff from the
previous supplied `57c85852` adds the named existing `puncturedUnits` morphism;
its mathematical definition and required base-point equation are unchanged.
No kernel, controller or leaf source was inspected for this assessment.

## Findings

All original identities are present. There are **46 missing question records**,
**1 demonstrably changed question**, and **106 reported formulas agreeing with
the independent mathematical question descriptions**. Formula agreement is a
source assessment observation: it does not establish protected admission, actual
registered execution, successful decoding, or equality between the reported
question and the actual request consumed by the execution path. In particular,
16 agreeing formulas accompany internal failures and need their typed/request
path assessed after repair. Declaration-name retention alone does not discharge
the mathematical dependency comparison.

The original outcome fields are observed as 42 `holds`, 8 `ambiguous`,
47 `gap`, 38 `invalid`, 2 `unavailable` and 16 `internal`. These are candidate
report fields, not independent mathematical-validity judgments. The original
assertions remain mathematically valid as specified. A `gap` observation for a
wrong question does not preserve the original question.

### Changed fixed datum: integration.derivative

The original question is the equality in Q[X]

`derivative(X^3 + X^2/2 + X) = 3X^2 + X + 1`.

The reported proposition instead begins with the **identity map on Q[X]**
composed with the polynomial derivative. Its right side is the constant
polynomial `3X^2 + X + 1`, made into a map on that same Q[X] domain.
Thus it asks whether differentiation of an arbitrary polynomial equals that
constant polynomial. The fixed primitive F has disappeared.
The candidate also reports an ambiguity for the preceding statement defining F.
That statement failure cannot authorize treating F as a new free variable.
This is a substantive interpretation defect under `gov-meaning-permanence` and
`b0-typed-application`, regardless of whether either question is decidable or
whether a computation is missing. The original assertion must remain fixed.

### Missing questions

All 38 `invalid` and 8 `ambiguous` original rows have no question record.
Examples include the sinc limit, integral of the square, Vieta binders,
polynomial evaluation and coefficient transport, rational divisions,
indefinite integration, matrices/inverses, spans, series coefficients and
Krull dimensions. Each mathematical question remains present in the preauthored
specification and in the original inventory. None can be omitted from the
interpretation denominator or admitted by recording a failure fingerprint.

### Distinctions retained in the visible agreeing formulas

The three-term conjunction in `numbers.containments` retains its three actual
canonical inclusion routes; `numbers.containments.transitive` retains the
composite N → Z → Q → R → C. They are not both replaced by a true value.
The distributivity equality on Z/7 retains its two expressions, whereas
`numbers.zmod7.value` compares the specified expression to residue 6.
Negated membership keeps its negation and predicate operands. Finiteness of Z
retains the false polarity of the finiteness question rather than changing the
object. Function equality retains the real domain and the actual composite
order, including the universal real variable in `functions.even`.

The cardinality/rank formulas retain the named A objects, the actual
BilWForm-to-module carrier map, the Z base ring, and subsequent module-fibre
inclusion/carrier path where applicable. Discriminant formulas retain the
cokernel of the actual to_dual(n) map. The finite-set pullback formula retains
its admitted finite diagram, its forgetful functor and the lifted limit;
the set pullback retains its two exact graphs. These are observations about
reported mathematical formulas, not proof that their complete result maps
survived decoding or that the corresponding implementation ran.

### Owed positive proposal claims

Of the 12 proposed positive identities, 8 have reported questions and 4 do not.
The 8 visible formulas agree with the independently specified E8 rank,
cyclic/Sym3 abelian properties, sign/identity kernel cardinalities,
Alt3 carrier cardinality, and dual formed-module cardinalities. These are not successful required computations.
The absent questions are the trivial-map kernel and the three F9 transport
assertions, **4** identities. The report's detail for F9 still refuses generator
selection or target numerals, rather than sending the required comparison.
Expected source and target generators, comparisons and answers remain fixed.

## Complete original inventory comparison

`formula agrees` means that the reported mathematical formula agrees with its
preauthored question. `question absent` means no question was supplied to compare.
`question changed` denotes the fixed-datum defect above. Each row retains the
candidate's outcome field separately; none of these labels releases a B0 row.

| Original identity | Independent comparison of the reported formula | Observed outcome field |
| --- | --- | --- |
| `algebras.polynomials` | formula agrees | `holds` |
| `algebras.polynomials_several` | formula agrees | `holds` |
| `calculus.integral_sine` | formula agrees | `gap` |
| `calculus.integral_square` | question absent | `ambiguous` |
| `calculus.limit_infinity` | formula agrees | `gap` |
| `calculus.limit_sinc` | question absent | `ambiguous` |
| `calculus.taylor_exp` | formula agrees | `holds` |
| `calculus.taylor_sin` | formula agrees | `holds` |
| `composed.charpoly` | formula agrees | `gap` |
| `composed.composition` | formula agrees | `gap` |
| `composed.det` | formula agrees | `gap` |
| `composed.root_count` | question absent | `invalid` |
| `composed.root_one` | question absent | `invalid` |
| `composed.root_product` | question absent | `invalid` |
| `composed.root_sum` | question absent | `invalid` |
| `composed.trace` | formula agrees | `gap` |
| `comprehension.card` | formula agrees | `gap` |
| `comprehension.elements` | formula agrees | `gap` |
| `comprehension.even_card` | formula agrees | `gap` |
| `comprehension.even_member` | formula agrees | `gap` |
| `comprehension.image_apply` | formula agrees | `gap` |
| `comprehension.image_method` | formula agrees | `gap` |
| `comprehension.image_typed` | formula agrees | `holds` |
| `comprehension.odd_not_member` | formula agrees | `gap` |
| `comprehension.typed` | formula agrees | `holds` |
| `differentials.at_two` | question absent | `invalid` |
| `differentials.degree` | formula agrees | `gap` |
| `differentials.derivative` | formula agrees | `gap` |
| `differentials.differential` | formula agrees | `gap` |
| `differentials.member` | formula agrees | `holds` |
| `ellipses.even_square` | formula agrees | `gap` |
| `ellipses.evens` | formula agrees | `gap` |
| `ellipses.multiples` | formula agrees | `gap` |
| `ellipses.naturals` | formula agrees | `gap` |
| `ellipses.not_prime` | formula agrees | `gap` |
| `ellipses.odd_square` | formula agrees | `gap` |
| `ellipses.prime` | formula agrees | `gap` |
| `ellipses.squares_even` | formula agrees | `gap` |
| `factorization.approximation` | question absent | `ambiguous` |
| `factorization.multiplicity_seven` | formula agrees | `holds` |
| `factorization.multiplicity_three` | formula agrees | `holds` |
| `factorization.multiplicity_two` | formula agrees | `holds` |
| `factorization.over_complexes` | question absent | `invalid` |
| `factorization.prime_factors` | formula agrees | `gap` |
| `finite_sets.card` | formula agrees | `holds` |
| `finite_sets.card.three` | formula agrees | `internal` |
| `finite_sets.card_power_set` | formula agrees | `unavailable` |
| `finite_sets.card_product` | formula agrees | `unavailable` |
| `finite_sets.difference` | formula agrees | `holds` |
| `finite_sets.intersection` | formula agrees | `holds` |
| `finite_sets.intersection_subset` | formula agrees | `gap` |
| `finite_sets.limit.pullback.card` | formula agrees | `internal` |
| `finite_sets.member` | formula agrees | `gap` |
| `finite_sets.not_member` | formula agrees | `gap` |
| `finite_sets.subset_union` | formula agrees | `gap` |
| `finite_sets.symmetric_difference` | formula agrees | `holds` |
| `finite_sets.union` | formula agrees | `holds` |
| `fractions.cancel` | question absent | `ambiguous` |
| `fractions.halves` | question absent | `ambiguous` |
| `fractions.lowest_terms` | question absent | `ambiguous` |
| `fractions.member` | question absent | `ambiguous` |
| `fractions.modulus` | formula agrees | `gap` |
| `fractions.sqrt_member` | formula agrees | `holds` |
| `functions.at_three` | formula agrees | `gap` |
| `functions.at_zero` | formula agrees | `gap` |
| `functions.even` | formula agrees | `gap` |
| `functions.extensional` | formula agrees | `gap` |
| `integration.at_zero` | question absent | `invalid` |
| `integration.derivative` | question changed | `gap` |
| `integration.differential` | question absent | `invalid` |
| `integration.normalized` | question absent | `invalid` |
| `integration.normalized_count` | question absent | `invalid` |
| `integration.primitives` | question absent | `ambiguous` |
| `inverses.det` | question absent | `invalid` |
| `inverses.left` | question absent | `invalid` |
| `inverses.right` | question absent | `invalid` |
| `inverses.solve` | question absent | `invalid` |
| `inverses.value` | question absent | `invalid` |
| `lattices.card.a0` | formula agrees | `internal` |
| `lattices.card.a2` | formula agrees | `internal` |
| `lattices.discriminant.a1` | formula agrees | `gap` |
| `lattices.discriminant.a2` | formula agrees | `gap` |
| `lattices.discriminant.a3` | formula agrees | `gap` |
| `lattices.rank.a1` | formula agrees | `internal` |
| `lattices.rank.a2` | formula agrees | `internal` |
| `lattices.rank.a3` | formula agrees | `internal` |
| `matrices.application` | question absent | `invalid` |
| `matrices.charpoly` | question absent | `invalid` |
| `matrices.det` | question absent | `invalid` |
| `matrices.juxtaposition` | question absent | `invalid` |
| `matrices.kernel` | question absent | `invalid` |
| `matrices.product` | question absent | `invalid` |
| `matrices.rank` | question absent | `invalid` |
| `matrices.trace` | question absent | `invalid` |
| `numbers.complex.abs` | formula agrees | `gap` |
| `numbers.complex.bar` | formula agrees | `gap` |
| `numbers.complex.im` | formula agrees | `gap` |
| `numbers.complex.norm` | formula agrees | `gap` |
| `numbers.complex.re` | formula agrees | `gap` |
| `numbers.containments` | formula agrees | `holds` |
| `numbers.containments.transitive` | formula agrees | `holds` |
| `numbers.gcd` | formula agrees | `holds` |
| `numbers.integers.sum` | formula agrees | `holds` |
| `numbers.membership.negative` | formula agrees | `holds` |
| `numbers.membership.zmod` | formula agrees | `holds` |
| `numbers.rationals.sum` | formula agrees | `holds` |
| `numbers.zmod5.difference` | formula agrees | `holds` |
| `numbers.zmod5.negation` | formula agrees | `holds` |
| `numbers.zmod5.product` | formula agrees | `holds` |
| `numbers.zmod5.sum` | formula agrees | `holds` |
| `numbers.zmod7.distributive` | formula agrees | `holds` |
| `numbers.zmod7.value` | formula agrees | `holds` |
| `polynomials.at_minus_sqrt2` | question absent | `invalid` |
| `polynomials.at_sqrt2` | question absent | `invalid` |
| `polynomials.degree` | formula agrees | `gap` |
| `polynomials.degree_over_rationals` | question absent | `invalid` |
| `polynomials.factors` | formula agrees | `gap` |
| `polynomials.irrational_roots` | question absent | `invalid` |
| `polynomials.member` | formula agrees | `holds` |
| `polynomials.no_rational_roots` | formula agrees | `gap` |
| `polynomials.root` | question absent | `invalid` |
| `polynomials.variable` | formula agrees | `holds` |
| `schemes.affine_line` | formula agrees | `holds` |
| `schemes.affine_space` | formula agrees | `holds` |
| `series.coefficient_four` | question absent | `invalid` |
| `series.coefficient_three` | question absent | `invalid` |
| `series.coefficient_two` | question absent | `invalid` |
| `series.coefficient_zero` | question absent | `invalid` |
| `sets.apply.rev` | formula agrees | `holds` |
| `sets.apply.rev_rev` | formula agrees | `holds` |
| `sets.card.fin2_sqcup_fin3` | formula agrees | `internal` |
| `sets.card.fin2_times_z3` | formula agrees | `internal` |
| `sets.card.integers` | formula agrees | `internal` |
| `sets.card.naturals` | formula agrees | `internal` |
| `sets.card.square` | formula agrees | `internal` |
| `sets.card.z4_cubed` | formula agrees | `internal` |
| `sets.card.z5_empty_power` | formula agrees | `internal` |
| `sets.card.z7` | formula agrees | `internal` |
| `sets.eq.rev_rev` | formula agrees | `holds` |
| `sets.finite.fin2_sqcup_fin3` | formula agrees | `holds` |
| `sets.finite.fin2_times_z3` | formula agrees | `holds` |
| `sets.finite.integers` | formula agrees | `holds` |
| `sets.implemented.card_fin` | formula agrees | `holds` |
| `sets.limit.pullback.card` | formula agrees | `internal` |
| `several_variables.dimension` | question absent | `invalid` |
| `several_variables.last_variable` | formula agrees | `holds` |
| `several_variables.plane` | question absent | `invalid` |
| `several_variables.total_degree` | formula agrees | `gap` |
| `several_variables.variable` | formula agrees | `holds` |
| `subspaces.dim` | question absent | `invalid` |
| `subspaces.kernel` | question absent | `invalid` |
| `subspaces.member` | question absent | `invalid` |
| `subspaces.not_member` | question absent | `invalid` |

## Proposed positive identities

| Proposed identity | Independent comparison of the reported formula | Observed outcome field |
| --- | --- | --- |
| `b0.lattices.rank.e8` | formula agrees | `internal` |
| `b0.groups.abelian.cyclic3` | formula agrees | `holds` |
| `b0.groups.abelian.symmetric3` | formula agrees | `holds` |
| `b0.groups.kernel.sign.card` | formula agrees | `gap` |
| `b0.groups.kernel.trivial.card` | question absent | `invalid` |
| `b0.groups.kernel.identity.card` | formula agrees | `gap` |
| `b0.groups.alternating3.card` | formula agrees | `internal` |
| `b0.presentations.f9.generator_transport` | question absent | `invalid` |
| `b0.presentations.f9.explicit_forward` | question absent | `invalid` |
| `b0.presentations.f9.explicit_inverse` | question absent | `invalid` |
| `formed_modules.card.dual_a0` | formula agrees | `internal` |
| `formed_modules.card.dual_a2` | formula agrees | `internal` |

The full assignment remains open. The next assessment consumes corrected typed
claims and actual request/result observations at a compatible revision tuple.
Concrete exit extensions are independently chosen only after the tuple is frozen.
