# Reuse assessment for the later interpretation-only payload

This assessment compares only the supplied `id`, `file`, `question` and
`proposition` fields. It uses the independently fixed questions and the complete
[32c per-identity dispositions](interpretation-dispositions-32c3897.md).
No computation outcomes, dispatch information, kernel source or leaves were
supplied or inspected. The input files are unchanged.

| Interpretation-only input | SHA-256 |
| --- | --- |
| `/tmp/b0-poc-32c3897/opaque-interpretations.json` | `04cb0d436731e870bf698f7e921bcfcf9e8aaff948579e7690b35803c399a560` |
| `/tmp/b0-poc-5410e70/opaque-interpretations.json` | `2430e6e161e572122dba67903a85953b98762a0f452cac77c0ce9663a60a7537` |

## Independent comparison and coverage

Both files contain the same 153 original assertion identities exactly once,
and the same additional non-assertion unit-matrix binding row. Their keys are
exactly `id`, `file`, `question`, `proposition`. The original `.cas` inventory
still has 153 identities; proposed additions remain outside this inventory.

For each readable assertion, split the question string at its **first colon
only** into its 40-hex revision label and remaining complete suffix. Independent
full-string comparison found, for every one of the 148 readable identities:

- the complete suffix is byte-identical to its earlier counterpart;
- the entire proposition string is byte-identical;
- the source filename is identical.

The suffix comparison retains the entire encoded proposition, its terms,
proof-proposition types, operations, routes and all later fields. No proof,
type, operand, serialization node, whitespace, operation record or later colon
is removed or normalized. This is an observed equality of supplied claims,
not regeneration of expected interpretations from candidate output.

The five unread assertion rows have exactly the same empty question and
proposition as before: `inverses.value`, `inverses.solve`, `inverses.left`,
`inverses.right`, `inverses.det`. The extra binding row is also identical,
including its original source `let M := [1,2;3,4] in Mat₂(ℚ)ˣ` and absent
question/proposition. No mathematical invalidity or interpreter-failure cause
is inferred from that absence.

Thus the earlier 148 source-grounded mathematical comparisons apply to the
identical supplied claim bodies; the five absent-question discrepancies
persist. This reuses their concrete mathematical arguments, not merely the
fact that the strings are stable. The later payload establishes no new
interpretation for a previously unread identity.

## Revision labels and mathematical provenance

The earlier readable labels all named mathematical revision
`a2123729df092e58b6fb0cd39c78db5e1714faf2`. The later file instead contains:

| Observed readable label | Count |
| --- | --- |
| `eea5c7f3bce7a1d2fdfbd58840c4d4bd75c9a8bc` | 82 |
| `293fccff854f8a1a77d2c6666232eb6c4189a804` | 66 |

These labels are preserved as observed. Controller-supplied provenance says
the process retained the originally imported `eea5c7f3` mathematical
environment while a concurrent manifest refresh changed later labels. That
import provenance cannot independently be authenticated from these four
stripped fields. In particular, a `293fccff` label does not establish that
the process imported that revision.

Independent inspection of the published source difference from `a2123729`
to `eea5c7f3` found only these changed paths: `COMPLAINTS.md`, the mathematical
`Algebra/Units.lean` evidence procedures, `EvidenceTests.lean`, and `justfile`.
In `Units.lean`, `normalizeRingObjects` performs definitional normalization
of the selected ring projections; `isUnitEvidence` and `invertibleEvidence`
invoke it before their existing proof procedures. The denotational units,
admission, inverse and division definitions and their mathematical
propositions are unchanged. This supports the previously stated
proof-representation comparisons for these exact supplied terms against
published `eea5c7f3` mathematics. It does not prove which compiled declarations
the process actually imported.

The additional published changes between `eea5c7f3` and `293fccff` introduce
formed constructions, center/alternation interfaces and structural transport.
They are not evidence that the later question labels were sourced from an
imported updated registry. Byte-identical old question bodies do not establish
the operation surface or generic resolution behavior of that enlarged registry.

Published current main was separately verified as
`805208138f016368f6a4eac415f25f3922a5807d`; its change from `e8e97d2b` is only
independent review text in `COMPLAINTS.md`. This later payload is not a
question-preservation assessment of a process known to import current main.

## Disposition and limits

| Source-level disposition reused from the earlier assessment | Count |
| --- | --- |
| Same source-grounded mathematical claim body | 148 |
| Same missing-question discrepancy | 5 |
| New or changed claim body requiring a new mathematical assessment | 0 |

The mixed revision attribution prevents treating this file as a correctly
revision-bound authoritative interpretation record. A comparison with coherent
import/revision provenance remains required for that purpose. This technical
reuse assessment neither rewrites those labels nor activates a migration,
admits proposed assertions, validates computation, or approves B0.

The per-identity observation table below preserves the later label and the
reused mathematical disposition. `eea5c7f3` and `293fccff` abbreviate the full
observed labels in the table above; `absent` records empty question material.

| Identity | Observed label | Reused source-level disposition |
| --- | --- | --- |
| `algebras.polynomials_several` | `eea5c7f3` | Same mathematical claim |
| `algebras.polynomials` | `eea5c7f3` | Same mathematical claim |
| `schemes.affine_line` | `eea5c7f3` | Same mathematical claim |
| `schemes.affine_space` | `eea5c7f3` | Same mathematical claim |
| `calculus.limit_sinc` | `eea5c7f3` | Same mathematical claim |
| `calculus.limit_infinity` | `eea5c7f3` | Same mathematical claim |
| `calculus.integral_square` | `eea5c7f3` | Same mathematical claim |
| `calculus.integral_sine` | `eea5c7f3` | Same mathematical claim |
| `calculus.taylor_exp` | `eea5c7f3` | Same mathematical claim |
| `calculus.taylor_sin` | `eea5c7f3` | Same mathematical claim |
| `composed.root_count` | `eea5c7f3` | Same mathematical claim |
| `composed.root_one` | `eea5c7f3` | Same mathematical claim |
| `composed.root_sum` | `eea5c7f3` | Same mathematical claim |
| `composed.root_product` | `eea5c7f3` | Same mathematical claim |
| `composed.charpoly` | `eea5c7f3` | Same mathematical claim |
| `composed.det` | `eea5c7f3` | Same mathematical claim |
| `composed.trace` | `eea5c7f3` | Same mathematical claim |
| `composed.composition` | `eea5c7f3` | Same mathematical claim |
| `differentials.member` | `eea5c7f3` | Same mathematical claim |
| `differentials.degree` | `eea5c7f3` | Same mathematical claim |
| `differentials.at_two` | `eea5c7f3` | Same mathematical claim |
| `differentials.differential` | `eea5c7f3` | Same mathematical claim |
| `differentials.derivative` | `eea5c7f3` | Same mathematical claim |
| `integration.primitives` | `eea5c7f3` | Same mathematical claim |
| `integration.normalized_count` | `eea5c7f3` | Same mathematical claim |
| `integration.normalized` | `eea5c7f3` | Same mathematical claim |
| `integration.differential` | `eea5c7f3` | Same mathematical claim |
| `integration.derivative` | `eea5c7f3` | Same mathematical claim |
| `integration.at_zero` | `eea5c7f3` | Same mathematical claim |
| `ellipses.naturals` | `eea5c7f3` | Same mathematical claim |
| `ellipses.evens` | `eea5c7f3` | Same mathematical claim |
| `ellipses.multiples` | `eea5c7f3` | Same mathematical claim |
| `ellipses.even_square` | `eea5c7f3` | Same mathematical claim |
| `ellipses.odd_square` | `eea5c7f3` | Same mathematical claim |
| `ellipses.squares_even` | `eea5c7f3` | Same mathematical claim |
| `ellipses.prime` | `eea5c7f3` | Same mathematical claim |
| `ellipses.not_prime` | `eea5c7f3` | Same mathematical claim |
| `factorization.prime_factors` | `eea5c7f3` | Same mathematical claim |
| `factorization.multiplicity_two` | `eea5c7f3` | Same mathematical claim |
| `factorization.multiplicity_three` | `eea5c7f3` | Same mathematical claim |
| `factorization.multiplicity_seven` | `eea5c7f3` | Same mathematical claim |
| `factorization.over_complexes` | `eea5c7f3` | Same mathematical claim |
| `factorization.approximation` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.union` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.intersection` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.difference` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.symmetric_difference` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.card` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.card_product` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.card_power_set` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.member` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.not_member` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.subset_union` | `eea5c7f3` | Same mathematical claim |
| `finite_sets.intersection_subset` | `eea5c7f3` | Same mathematical claim |
| `comprehension.typed` | `eea5c7f3` | Same mathematical claim |
| `comprehension.elements` | `eea5c7f3` | Same mathematical claim |
| `comprehension.card` | `eea5c7f3` | Same mathematical claim |
| `comprehension.image_typed` | `eea5c7f3` | Same mathematical claim |
| `comprehension.even_member` | `eea5c7f3` | Same mathematical claim |
| `comprehension.odd_not_member` | `eea5c7f3` | Same mathematical claim |
| `comprehension.even_card` | `eea5c7f3` | Same mathematical claim |
| `comprehension.image_apply` | `eea5c7f3` | Same mathematical claim |
| `comprehension.image_method` | `eea5c7f3` | Same mathematical claim |
| `fractions.member` | `eea5c7f3` | Same mathematical claim |
| `fractions.halves` | `eea5c7f3` | Same mathematical claim |
| `fractions.cancel` | `eea5c7f3` | Same mathematical claim |
| `fractions.lowest_terms` | `eea5c7f3` | Same mathematical claim |
| `fractions.sqrt_member` | `eea5c7f3` | Same mathematical claim |
| `fractions.modulus` | `eea5c7f3` | Same mathematical claim |
| `functions.extensional` | `eea5c7f3` | Same mathematical claim |
| `functions.at_zero` | `eea5c7f3` | Same mathematical claim |
| `functions.at_three` | `eea5c7f3` | Same mathematical claim |
| `functions.even` | `eea5c7f3` | Same mathematical claim |
| `inverses.value` | absent | Same missing question |
| `inverses.solve` | absent | Same missing question |
| `inverses.left` | absent | Same missing question |
| `inverses.right` | absent | Same missing question |
| `inverses.det` | absent | Same missing question |
| `lattices.discriminant.a1` | `eea5c7f3` | Same mathematical claim |
| `lattices.discriminant.a2` | `eea5c7f3` | Same mathematical claim |
| `lattices.discriminant.a3` | `eea5c7f3` | Same mathematical claim |
| `lattices.rank.a1` | `eea5c7f3` | Same mathematical claim |
| `lattices.rank.a2` | `eea5c7f3` | Same mathematical claim |
| `lattices.rank.a3` | `eea5c7f3` | Same mathematical claim |
| `lattices.card.a2` | `eea5c7f3` | Same mathematical claim |
| `lattices.card.a0` | `eea5c7f3` | Same mathematical claim |
| `matrices.product` | `eea5c7f3` | Same mathematical claim |
| `matrices.juxtaposition` | `293fccff` | Same mathematical claim |
| `matrices.application` | `293fccff` | Same mathematical claim |
| `matrices.det` | `293fccff` | Same mathematical claim |
| `matrices.rank` | `293fccff` | Same mathematical claim |
| `matrices.kernel` | `293fccff` | Same mathematical claim |
| `matrices.trace` | `293fccff` | Same mathematical claim |
| `matrices.charpoly` | `293fccff` | Same mathematical claim |
| `subspaces.dim` | `293fccff` | Same mathematical claim |
| `subspaces.member` | `293fccff` | Same mathematical claim |
| `subspaces.not_member` | `293fccff` | Same mathematical claim |
| `subspaces.kernel` | `293fccff` | Same mathematical claim |
| `numbers.integers.sum` | `293fccff` | Same mathematical claim |
| `numbers.zmod5.sum` | `293fccff` | Same mathematical claim |
| `numbers.zmod5.product` | `293fccff` | Same mathematical claim |
| `numbers.zmod5.negation` | `293fccff` | Same mathematical claim |
| `numbers.zmod5.difference` | `293fccff` | Same mathematical claim |
| `numbers.zmod7.distributive` | `293fccff` | Same mathematical claim |
| `numbers.zmod7.value` | `293fccff` | Same mathematical claim |
| `numbers.rationals.sum` | `293fccff` | Same mathematical claim |
| `numbers.containments` | `293fccff` | Same mathematical claim |
| `numbers.containments.transitive` | `293fccff` | Same mathematical claim |
| `numbers.membership.zmod` | `293fccff` | Same mathematical claim |
| `numbers.membership.negative` | `293fccff` | Same mathematical claim |
| `numbers.gcd` | `293fccff` | Same mathematical claim |
| `numbers.complex.re` | `293fccff` | Same mathematical claim |
| `numbers.complex.im` | `293fccff` | Same mathematical claim |
| `numbers.complex.bar` | `293fccff` | Same mathematical claim |
| `numbers.complex.norm` | `293fccff` | Same mathematical claim |
| `numbers.complex.abs` | `293fccff` | Same mathematical claim |
| `polynomials.variable` | `293fccff` | Same mathematical claim |
| `polynomials.member` | `293fccff` | Same mathematical claim |
| `polynomials.degree` | `293fccff` | Same mathematical claim |
| `polynomials.root` | `293fccff` | Same mathematical claim |
| `polynomials.factors` | `293fccff` | Same mathematical claim |
| `polynomials.degree_over_rationals` | `293fccff` | Same mathematical claim |
| `polynomials.at_sqrt2` | `293fccff` | Same mathematical claim |
| `polynomials.at_minus_sqrt2` | `293fccff` | Same mathematical claim |
| `polynomials.no_rational_roots` | `293fccff` | Same mathematical claim |
| `polynomials.irrational_roots` | `293fccff` | Same mathematical claim |
| `series.coefficient_two` | `293fccff` | Same mathematical claim |
| `series.coefficient_three` | `293fccff` | Same mathematical claim |
| `series.coefficient_zero` | `293fccff` | Same mathematical claim |
| `series.coefficient_four` | `293fccff` | Same mathematical claim |
| `sets.card.z4_cubed` | `293fccff` | Same mathematical claim |
| `sets.card.z7` | `293fccff` | Same mathematical claim |
| `sets.card.z5_empty_power` | `293fccff` | Same mathematical claim |
| `sets.card.integers` | `293fccff` | Same mathematical claim |
| `sets.card.naturals` | `293fccff` | Same mathematical claim |
| `sets.card.fin2_times_z3` | `293fccff` | Same mathematical claim |
| `sets.finite.integers` | `293fccff` | Same mathematical claim |
| `sets.finite.fin2_times_z3` | `293fccff` | Same mathematical claim |
| `sets.implemented.card_fin` | `293fccff` | Same mathematical claim |
| `sets.card.square` | `293fccff` | Same mathematical claim |
| `sets.card.fin2_sqcup_fin3` | `293fccff` | Same mathematical claim |
| `sets.finite.fin2_sqcup_fin3` | `293fccff` | Same mathematical claim |
| `sets.eq.rev_rev` | `293fccff` | Same mathematical claim |
| `sets.limit.pullback.card` | `293fccff` | Same mathematical claim |
| `finite_sets.card.three` | `293fccff` | Same mathematical claim |
| `finite_sets.limit.pullback.card` | `293fccff` | Same mathematical claim |
| `sets.apply.rev` | `293fccff` | Same mathematical claim |
| `sets.apply.rev_rev` | `293fccff` | Same mathematical claim |
| `several_variables.dimension` | `293fccff` | Same mathematical claim |
| `several_variables.variable` | `293fccff` | Same mathematical claim |
| `several_variables.last_variable` | `293fccff` | Same mathematical claim |
| `several_variables.total_degree` | `293fccff` | Same mathematical claim |
| `several_variables.plane` | `293fccff` | Same mathematical claim |
