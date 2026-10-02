# Independent assessment of refreshed B0 questions

This source proposal compares candidate claims with the preauthored mathematical
readings in `b0-interpretations-proposal.md` and
`b0-positive-interpretations-proposal.md`. It is neither admission nor a new
expected-question baseline. Candidate computation results establish no expected
answers. The original 153 assertions and three permanent ledgers remain unchanged.

Input: `.tmp/b0-current-v2.json`, SHA-256
`ebaa52ceb798239a1cbf6becf176b2c4a7f67192ba47039f072f01af48a28603`.
Exact bytes are preserved in
`.tmp/b0-current-v2-preserved-ebaa52ceb798239a1cbf6becf176b2c4a7f67192ba47039f072f01af48a28603.json`.
The supplied build/dependency tuple has mathematical input
`61b110defeab5b6f3042e6473e4356a03124b895`, contract `949db4`, and fresh
7420 build. The supplied independent mathematical source review and public
437-row metadata are inputs. No kernel, controller or leaf implementation was
inspected in this assessment.

## Findings

All 153 original identities are present exactly once. Of them, 105 have reported
question records whose visible mathematical propositions agree with the
preauthored meanings; 48 have no question. No changed mathematical meaning was
found among the reported propositions. This is a source comparison of claims,
not a guarantee that execution consumes the same typed term, or that every
reported operation annotation is faithfully reconstructed by the trusted core.
The earlier assessment remains evidence for unchanged formulas; newly reported
or differently printed propositions were separately compared to the preauthored
mathematics rather than accepted from their outcome.

Original observed outcomes: 53 holds, 49 gap, 37 invalid, 11 ambiguous,
2 unavailable, and 1 internal. These are report fields, not independent
mathematical-validity findings. All original mathematical questions remain owed.

The previous changed `integration.derivative` claim is absent: this report has
an ambiguous reading and no question/proposition. It no longer asserts that
differentiation of an arbitrary polynomial equals the fixed polynomial f.
However, the original obligation remains differentiation of the fixed
F = X^3 + X^2/2 + X, giving f = 3X^2 + X + 1. Withdrawing a changed claim does not
discharge that assertion; the failed preceding definition of F remains material.

The newly formed sinc claim uses the limit point zero, the punctured-domain
function t ↦ sin(t) times the inverse of its actual unit-valued denominator,
and the asserted limit one. This agrees with the independently specified
question. The earlier reviewed dependent inclusion retains the point=0
obligation; this is not an arbitrary-puncture inclusion into units.

The Taylor membership claims retain exp/sin as admitted smooth functions at
zero and land in real formal power series. Polynomial membership claims retain
X^3 - 2X + 1 over integers and 3X^2 + X + 1 over rationals. Multivariable claims
retain ten complex variables (indices 3 and 9), and dimensions ten over complexes
and two over rationals. More explicit identity wrappers and selected structures
do not alter those formulas.

The subsequent reviewed mathematical source adds ScalarAlgebra(R,S,f)=Under.mk f
and evaluation by Polynomial.eval₂ f, and names canonical integer/rational/real
coefficient maps and selected scalar algebras. Inspection of the public math-only
diff confirms the rational-real and real-complex underlying maps are the
previous scalar inclusions. These additions provide the preauthored coefficient
and evaluation meanings; the report's missing such questions cannot be repaired
by selecting a different scalar map merely because its output agrees.

## Positive proposals and execution limitations

Nine of the twelve proposed positives have agreeing reported formulas; three
F9 transport assertions remain unread. The newly formed trivial-kernel question
is cardinality of the actual kernel cone of the trivial map Sym(3) → cyclic(2),
with expected six independently derived beforehand. The sign and identity
kernel questions retain their distinct maps and independent expected three and
one. Their gap outcomes do not supply the required diagram computations.

All three F9 assertions still have no typed question. The map-to assertion reports
free x without its required presentation generator. Explicit forward/inverse
assertions report missing binary addition on F9y/F9x. Their fixed expectations
remain phi(x)=y+2 and phi⁻¹(y)=x+1 for the named F9translation comparison, not a
coefficient map between unrelated polynomial rings. These are substantive missing
readings, not permission to change expected values.

`finite_sets.limit.pullback.card` retains the correct reported cardinality-three
question but has an internal morphism-type mismatch in the execution path.
Formula agreement alone cannot close it. Holds fields similarly do not by
themselves establish registered backend invocation, universal-data reconstruction,
or complete B0 execution. No exit trial has been run before the frozen tuple.

## Identity-level assessment

“Agrees” means the visible mathematical proposition agrees with its preauthored
reading under the supplied reviewed math input. It makes none of the execution
or protected-admission claims excluded above. “Absent” leaves the full original
mathematical question owed.

| Identity | Mathematical claim | Observed outcome |
|---|---|---|
| `algebras.polynomials_several` | Absent | `invalid` |
| `algebras.polynomials` | Absent | `invalid` |
| `schemes.affine_line` | Absent | `invalid` |
| `schemes.affine_space` | Absent | `invalid` |
| `b0.lattices.rank.e8` | Agrees | `holds` |
| `b0.groups.abelian.cyclic3` | Agrees | `holds` |
| `b0.groups.abelian.symmetric3` | Agrees | `holds` |
| `b0.groups.kernel.sign.card` | Agrees | `gap` |
| `b0.groups.kernel.trivial.card` | Agrees | `gap` |
| `b0.groups.kernel.identity.card` | Agrees | `gap` |
| `b0.groups.alternating3.card` | Agrees | `holds` |
| `b0.presentations.f9.generator_transport` | Absent | `invalid` |
| `b0.presentations.f9.explicit_forward` | Absent | `invalid` |
| `b0.presentations.f9.explicit_inverse` | Absent | `invalid` |
| `calculus.limit_sinc` | Agrees | `gap` |
| `calculus.limit_infinity` | Agrees | `gap` |
| `calculus.integral_square` | Absent | `ambiguous` |
| `calculus.integral_sine` | Agrees | `gap` |
| `calculus.taylor_exp` | Agrees | `holds` |
| `calculus.taylor_sin` | Agrees | `holds` |
| `composed.root_count` | Absent | `invalid` |
| `composed.root_one` | Absent | `invalid` |
| `composed.root_sum` | Absent | `invalid` |
| `composed.root_product` | Absent | `invalid` |
| `composed.charpoly` | Agrees | `gap` |
| `composed.det` | Agrees | `gap` |
| `composed.trace` | Agrees | `gap` |
| `composed.composition` | Agrees | `gap` |
| `differentials.member` | Agrees | `holds` |
| `differentials.degree` | Agrees | `gap` |
| `differentials.at_two` | Absent | `invalid` |
| `differentials.differential` | Agrees | `gap` |
| `differentials.derivative` | Agrees | `gap` |
| `integration.primitives` | Absent | `ambiguous` |
| `integration.normalized_count` | Absent | `invalid` |
| `integration.normalized` | Absent | `invalid` |
| `integration.differential` | Absent | `ambiguous` |
| `integration.derivative` | Absent | `ambiguous` |
| `integration.at_zero` | Absent | `ambiguous` |
| `ellipses.naturals` | Agrees | `gap` |
| `ellipses.evens` | Agrees | `gap` |
| `ellipses.multiples` | Agrees | `gap` |
| `ellipses.even_square` | Agrees | `gap` |
| `ellipses.odd_square` | Agrees | `gap` |
| `ellipses.squares_even` | Agrees | `gap` |
| `ellipses.prime` | Agrees | `gap` |
| `ellipses.not_prime` | Agrees | `gap` |
| `factorization.prime_factors` | Agrees | `gap` |
| `factorization.multiplicity_two` | Agrees | `holds` |
| `factorization.multiplicity_three` | Agrees | `holds` |
| `factorization.multiplicity_seven` | Agrees | `holds` |
| `factorization.over_complexes` | Absent | `invalid` |
| `factorization.approximation` | Absent | `ambiguous` |
| `finite_sets.union` | Agrees | `holds` |
| `finite_sets.intersection` | Agrees | `holds` |
| `finite_sets.difference` | Agrees | `holds` |
| `finite_sets.symmetric_difference` | Agrees | `holds` |
| `finite_sets.card` | Agrees | `holds` |
| `finite_sets.card_product` | Agrees | `unavailable` |
| `finite_sets.card_power_set` | Agrees | `unavailable` |
| `finite_sets.member` | Agrees | `gap` |
| `finite_sets.not_member` | Agrees | `gap` |
| `finite_sets.subset_union` | Agrees | `gap` |
| `finite_sets.intersection_subset` | Agrees | `gap` |
| `comprehension.typed` | Agrees | `holds` |
| `comprehension.elements` | Agrees | `gap` |
| `comprehension.card` | Agrees | `gap` |
| `comprehension.image_typed` | Agrees | `holds` |
| `comprehension.even_member` | Agrees | `gap` |
| `comprehension.odd_not_member` | Agrees | `gap` |
| `comprehension.even_card` | Agrees | `gap` |
| `comprehension.image_apply` | Agrees | `gap` |
| `comprehension.image_method` | Agrees | `gap` |
| `formed_modules.card.dual_a0` | Agrees | `holds` |
| `formed_modules.card.dual_a2` | Agrees | `holds` |
| `fractions.member` | Absent | `ambiguous` |
| `fractions.halves` | Absent | `ambiguous` |
| `fractions.cancel` | Absent | `ambiguous` |
| `fractions.lowest_terms` | Absent | `ambiguous` |
| `fractions.sqrt_member` | Agrees | `holds` |
| `fractions.modulus` | Agrees | `gap` |
| `functions.extensional` | Agrees | `gap` |
| `functions.at_zero` | Agrees | `gap` |
| `functions.at_three` | Agrees | `gap` |
| `functions.even` | Agrees | `gap` |
| `inverses.value` | Absent | `invalid` |
| `inverses.solve` | Absent | `invalid` |
| `inverses.left` | Absent | `invalid` |
| `inverses.right` | Absent | `invalid` |
| `inverses.det` | Absent | `ambiguous` |
| `lattices.discriminant.a1` | Agrees | `gap` |
| `lattices.discriminant.a2` | Agrees | `gap` |
| `lattices.discriminant.a3` | Agrees | `gap` |
| `lattices.rank.a1` | Agrees | `holds` |
| `lattices.rank.a2` | Agrees | `holds` |
| `lattices.rank.a3` | Agrees | `holds` |
| `lattices.card.a2` | Agrees | `holds` |
| `lattices.card.a0` | Agrees | `holds` |
| `matrices.product` | Absent | `invalid` |
| `matrices.juxtaposition` | Absent | `invalid` |
| `matrices.application` | Absent | `invalid` |
| `matrices.det` | Absent | `invalid` |
| `matrices.rank` | Absent | `invalid` |
| `matrices.kernel` | Absent | `invalid` |
| `matrices.trace` | Absent | `invalid` |
| `matrices.charpoly` | Absent | `invalid` |
| `subspaces.dim` | Absent | `invalid` |
| `subspaces.member` | Absent | `invalid` |
| `subspaces.not_member` | Absent | `invalid` |
| `subspaces.kernel` | Absent | `invalid` |
| `numbers.integers.sum` | Agrees | `holds` |
| `numbers.zmod5.sum` | Agrees | `holds` |
| `numbers.zmod5.product` | Agrees | `holds` |
| `numbers.zmod5.negation` | Agrees | `holds` |
| `numbers.zmod5.difference` | Agrees | `holds` |
| `numbers.zmod7.distributive` | Agrees | `holds` |
| `numbers.zmod7.value` | Agrees | `holds` |
| `numbers.rationals.sum` | Agrees | `holds` |
| `numbers.containments` | Agrees | `holds` |
| `numbers.containments.transitive` | Agrees | `holds` |
| `numbers.membership.zmod` | Agrees | `holds` |
| `numbers.membership.negative` | Agrees | `holds` |
| `numbers.gcd` | Agrees | `holds` |
| `numbers.complex.re` | Agrees | `gap` |
| `numbers.complex.im` | Agrees | `gap` |
| `numbers.complex.bar` | Agrees | `gap` |
| `numbers.complex.norm` | Agrees | `gap` |
| `numbers.complex.abs` | Agrees | `gap` |
| `polynomials.variable` | Agrees | `holds` |
| `polynomials.member` | Agrees | `holds` |
| `polynomials.degree` | Agrees | `gap` |
| `polynomials.root` | Absent | `invalid` |
| `polynomials.factors` | Agrees | `gap` |
| `polynomials.degree_over_rationals` | Absent | `invalid` |
| `polynomials.at_sqrt2` | Absent | `invalid` |
| `polynomials.at_minus_sqrt2` | Absent | `invalid` |
| `polynomials.no_rational_roots` | Agrees | `gap` |
| `polynomials.irrational_roots` | Absent | `invalid` |
| `series.coefficient_two` | Absent | `invalid` |
| `series.coefficient_three` | Absent | `invalid` |
| `series.coefficient_zero` | Absent | `invalid` |
| `series.coefficient_four` | Absent | `invalid` |
| `sets.card.z4_cubed` | Agrees | `holds` |
| `sets.card.z7` | Agrees | `holds` |
| `sets.card.z5_empty_power` | Agrees | `holds` |
| `sets.card.integers` | Agrees | `holds` |
| `sets.card.naturals` | Agrees | `holds` |
| `sets.card.fin2_times_z3` | Agrees | `holds` |
| `sets.finite.integers` | Agrees | `holds` |
| `sets.finite.fin2_times_z3` | Agrees | `holds` |
| `sets.implemented.card_fin` | Agrees | `holds` |
| `sets.card.square` | Agrees | `holds` |
| `sets.card.fin2_sqcup_fin3` | Agrees | `holds` |
| `sets.finite.fin2_sqcup_fin3` | Agrees | `holds` |
| `sets.eq.rev_rev` | Agrees | `holds` |
| `sets.limit.pullback.card` | Agrees | `holds` |
| `finite_sets.card.three` | Agrees | `holds` |
| `finite_sets.limit.pullback.card` | Agrees | `internal` |
| `sets.apply.rev` | Agrees | `holds` |
| `sets.apply.rev_rev` | Agrees | `holds` |
| `several_variables.dimension` | Agrees | `gap` |
| `several_variables.variable` | Agrees | `holds` |
| `several_variables.last_variable` | Agrees | `holds` |
| `several_variables.total_degree` | Agrees | `gap` |
| `several_variables.plane` | Agrees | `gap` |
