# Provisional comparison of the supplied typed questions

The independent question specifications in
[question-specifications.md](question-specifications.md) were committed as
`a6311e1ab86b8aa31741a91c5040a236677edb72` before this comparison input was
supplied. They are the expectations; the supplied output is the claim checked.
No expected question, admitted assertion or authoritative record is regenerated
from that output.

The permitted input is `/tmp/b0-poc-32c3897/opaque-interpretations.json`, containing
only `id`, `file`, `question`, and `proposition`. Its SHA-256 is
`04cb0d436731e870bf698f7e921bcfcf9e8aaff948579e7690b35803c399a560`.
The supplied runtime source identity is
`32c3897163a6f6595b44277b097efad0da9ccfdc`; its questions name mathematical
dependency `a2123729df092e58b6fb0cd39c78db5e1714faf2`, the published mathematics
used to prepare the specifications. This comparison reads neither kernel source
nor computational outputs, dispatch information or leaves.

## Full-inventory discrepancy

All 153 original assertion identities occur in the supplied file, plus one
non-assertion binding row. Five assertion rows have neither a question nor a
proposition:

- `inverses.value`
- `inverses.solve`
- `inverses.left`
- `inverses.right`
- `inverses.det`

The associated non-assertion row contains the source binding
`let M := [1, 2; 3, 4] in Mat₂(ℚ)ˣ`, also without a question or proposition.
The permitted payload does not expose a cause, and this assessment does not
infer one. Independently, the matrix is a valid rational unit: its determinant
is `-2`, and its inverse is `[[-2,1],[3/2,-1/2]]`. Consequently all five fixed
questions remain mathematically meaningful; their absent interpretations are
an unsatisfied question-preservation obligation. No smaller denominator or
replacement assertion repairs that absence.

The other 148 assertion rows contain question material. Presence is not a
finding of preservation. The concrete comparisons below explain selected
canonical identifications; the complete per-identity assessment is in
[interpretation-dispositions-32c3897.md](interpretation-dispositions-32c3897.md).

## Concrete mathematical comparisons

| Identities | Comparison with the independently fixed questions |
| --- | --- |
| `series.coefficient_two`, `series.coefficient_three`, `series.coefficient_zero`, `series.coefficient_four` | All four claims apply `Algebra.Series.admit` at `powerSeriesTAdic` of the integer ring, with index object `naturals` and family `n ↦ (PowerSeries.C (n:ℤ))² * X^n`; then `powerSeriesSum` at those same parameters, then the integer coefficient operation at `2,3,0,4`, and equality to the integer literals `4,9,0,16`. This is the specified series question. `C(n)²=C(n²)` follows because `C` is a ring homomorphism, so that representation difference is justified by `map_pow` while retaining `n`, the integer ring and the family. The serialized proof node retains a `Summable` proposition. This does not accept every proof-node normalization or any historical fingerprint. |
| `calculus.limit_sinc` | The claim applies `RealLimits.admitConvergent` at the real point zero to the sine quotient on `puncturedLine 0`, then `RealLimits.limit` at that same point, and compares the result with the real literal one. The question graph retains `puncturedInclusion`, `puncturedUnits`, `Filter.Tendsto`, `approach`, and its convergence proposition. In published `RealLimits.lean`, `approach` is the pullback of `𝓝[≠] 0` to that punctured line, and the units map followed by units inclusion is `puncturedInclusion`. Thus this is the specified punctured-limit question, rather than a claim about a quotient defined at zero. |
| `calculus.limit_infinity` | The claim uses `infinity`, `admitConvergentAtInfinity`, the reciprocal family on real units, and `limitAtInfinity`, with expected real zero. Published `infinity` selects `+∞`, and `approachInfinity_infinity` identifies its filter with `comap Units.val atTop`. Its domain is a subset containing a positive tail, with the same reciprocal there; this is a justified domain presentation of the specified limit at positive infinity. It does not change the endpoint to negative infinity. |
| `functions.even` | The claim is equality of real maps `neg ≫ h` and `id ≫ h`, retaining `h(t)=t²+1`, selected real negation, power two and constant one. Function extensionality identifies this with the specified `∀t:ℝ, h(-t)=h(t)`. The same input variable is shared on both sides; it is not replaced by a chosen numeral. |
| `composed.composition` | The claim composes the real power-three map before the power-two map and compares it with the real power-six map. Function extensionality gives exactly the specified universally quantified equation `(f∘g)(t)=t⁶`; no reversal of the composite is introduced. |
| `numbers.integers.sum` | The claim forms the integer pair `(2,3)`, applies the selected integer addition and compares with integer five. It retains equality of the unreduced expressions in `ℤ`, rather than an equality of truth values or a rational-ring replacement. |
| `numbers.gcd` | The pair is formed from integer literals `84,30`, passed to published `NumberSystems.gcd : ℤ×ℤ→ℤ`, and compared with integer six. This agrees with the pre-specified integer result type and argument order. |
| `numbers.containments` | The question graph is the right-associated conjunction of the three specified inclusion judgments, with routes `integersRationals`, `rationalsReals`, `realsComplexes`. All four number systems and all three clauses remain present. The serialized right association supplies the concrete grouping required for this candidate comparison. |
| `numbers.containments.transitive` | The claim records the actual ordered route `naturalsIntegers`, `integersRationals`, `rationalsReals`, `realsComplexes` from natural numbers to complex numbers, matching the independently specified composite inclusion. |
| `sets.card.z4_cubed`, `sets.card.z7`, `sets.card.z5_empty_power` | The cardinality questions use `integersModPower 4 3`, `integersModPower 7 1`, and `integersModPower 5 0` respectively, with expected cardinal literals `64,7,1`. Both modulus and exponent survive, including the empty exponent. |
| `sets.implemented.card_fin` | The claim retains an `implemented` question for cardinality of `Fin 3`. It has not been replaced by the mathematical equality `card(Fin 3)=3` or a leaf's implementation-status field. This observation concerns only the question, not whether required execution occurs. |
| `sets.finite.integers` | The claim retains `Classifier.Holds finite integers` with expected judgment `false`. That represents the source's negated finiteness decision, not a positive finiteness assertion or a bare false proposition without its subject. |
| `lattices.rank.a1`, `lattices.rank.a2`, `lattices.rank.a3` | The claims use the actual `bilWFormCarrierDeclaration ℤ` on `rootA 1,2,3`, followed by `rankDeclaration (RingCat.of ℤ)`, with respective cardinal literals `1,2,3`. They preserve the lattice input, integer scalar ring, structural forgetting and cardinal-valued rank. |
| `lattices.discriminant.a2` | The claim constructs the categorical `bilWFormCokernel` of the actual `rootAToDual 2`, then follows the formed-module carrier/module/additive-group/group/set route and applies cardinality, with expected cardinal three. This matches the specified discriminant quotient and route; it is not an arbitrary object with matching cardinality. It does not alone establish that execution returns all quotient data. |
| `sets.eq.rev_rev` | The claim is equality of the two composites `finRev 3 ≫ finRev 3` and the identity of `Fin 3`, with the stated intermediate object. It agrees with the specified map equation. |
| `sets.apply.rev` | The claim applies `finRev 3` to `finPoint 3 0` and compares with `finPoint 3 2`. The chosen finite set and both indices are retained. |
| `sets.apply.rev_rev` | Both applications use `finRev 4`, starting and ending at `finPoint 4 1`, retaining the distinct size-four instance. |
| `polynomials.no_rational_roots` | The claim admits the rational polynomial `x²-2` as nonzero, forms its finite root set over the rationals, applies the finite-subset inclusion into the power set, and compares with the empty rational subset. The independently specified equality of finite subsets is equivalent under this particular injective inclusion: two finite subsets are equal exactly when their extents are equal. This justifies that representation comparison without dropping the coefficient ring, polynomial, nonzero proposition or roots operation. |
| `matrices.kernel` | The claim retains the rational entries in row order `[[1,2],[3,4]]`, constructs that size-two matrix, applies published `LinearAlgebra.ker 2` over the rational ring and compares with the singleton zero vector of its selected size-two module. Published `ker` is the extent `{v ∣ Mv=0}`, matching the fixed subset equality. The displayed zero arises from the formal module-zero operation. This subset question does not itself test the complete structured-result lifting mechanism. |

These are source-grounded mathematical comparisons of the named terms, not
results of a Lean-checked migration procedure. They do not establish correctness
of the serialization/comparison mechanism for arbitrary questions, independence
of the evaluator, execution of these assertions, or protected admission. Exact
proof-artifact replacement and retention of all selected data still require the
protected typed comparison appropriate to each affected record.

Any update of the mathematical dependency or runtime source requires the
applicable comparison again. The thirteen proposed positive assertions in
[b0-required-positives.cas.proposed](b0-required-positives.cas.proposed) are absent
from this earlier snapshot and remain outside its admitted/executed inventory.
