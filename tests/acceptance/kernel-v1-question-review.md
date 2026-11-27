# V1 independent mathematical-question preservation review

## Disposition and scope

**Final semantic assessment: all 153 supplied interpretations preserve the fixed mathematical questions.** No changed operand, relation, ambient mathematical structure, ordered parameter, selected map, or required diagram was identified. The final export closes the two interim readability gaps, `inverses.value` and `polynomials.irrational_roots`. Every one of the 35 previously readable records whose full identity changed was revisited, including changes hidden by identical pretty-printed propositions. There is no remaining missing or changed mathematical question in this reviewed payload.

This review is independent of the implementation authors. The reviewer did not inspect kernel implementation files, any leaf implementation, build output, per-assertion computational outcomes, or root runtime reports. The coordinator separately reported global build status; that statement was excluded from the semantic assessment. Evidence was confined to immutable questions and their specifications/history, protected question records, the supplied interpretation-only payload, and the published mathematical source identified below. The review did not modify an assertion, mathematical definition, contract, or protected JSON baseline. The draft stayed outside the repository while the source/API freeze was pending.

This is a semantic engineering assessment of the questions. It does not accept the upstream mathematical catalogue, authorize a protected-baseline migration, declare B0 accepted, prove that execution consumes the recorded trace, establish implementation coverage, or assess whether any computational answer is correct. A preservation finding here means that the supplied question still asks the fixed mathematical question, with the qualifications below.

## Evidence and provenance

| Evidence | Role |
| --- | --- |
| `INTENT.md` and `AGENTS.md` | Scope, mathematical authority, permanence, and the current owner's authorization for independent V1 review. |
| The 17 permanent `tests/acceptance/*.cas` files at `76d37bbfab783eecd3383f965aad1e34d9027fc2` | Fixed assertion text and bound mathematical context; all 17 current files were verified byte-identical to this fixed source revision. |
| `tests/acceptance/question-specifications.md` | The intended question, especially when the historical interpreter had no readable record. |
| `interpretation-dispositions-32c3897.md`, `interpretation-comparison-32c3897.md`, `interpretation-comparison-5410e70.md`, and `interpretation-comparison-5410e70-inverses.md` | Historical disposition and presentation-change context; these were not treated as authority to alter a question. |
| `CasAcceptance/Permanent/admitted.json` | The complete 153-ID inventory. |
| `CasAcceptance/Permanent/questions.json` and `question_readings.json` | The 142 protected historical identities/readings, retained unchanged. |
| `/tmp/v1-final-question-readings.json` | Final `file`, `id`, full question DAG and operation trace, and proposition reading only; no result fields. |
| `lean-categories` at `dbab309f2ee6a4da2c19e970f4d5d6460d8665a4` | Published definitions and explicit comparison theorems used to interpret the candidate. Source was read with `git show` at this exact revision. |

The reviewed final payload has SHA-256 `ee544370025cf1419cb595e2833da2ff0cc7baa70d13ffe2c0d87a53097dadb3`, independently recomputed from the supplied file. The preserved interim payload has SHA-256 `de8dd498bb6b7d49fec32ca652246d03c3ccb1879333260cf417dd1b0901b7ea`. These digests identify the reviewed evidence; they do not establish mathematical equivalence.

The coordinator identifies the published interpretation producer as `9630f544f0b82581ba0083f7bbd49831ef5967e2`, and the final kernel freeze as `8ca2615e57b7cef1de64a96394dc262984513c43`, with interpretation source unchanged between them. The coordinator identifies the accompanying public contract as `6780f9f0e0ac9acb7355d9281993df44f0d13b54` and describes its latest change as documentation clarification. Those source/publication relationships are coordinator-supplied provenance, not an implementation or publication audit by this reviewer. The mathematical source used for this review remains the exact `dbab309…` revision above. Authorship and publication of a source do not amount to independent mathematical acceptance or approval of a question-baseline migration.

The candidate strings themselves have no revision prefix. Their provenance therefore depends on keeping the exact exported payload attached to this producer/freeze information; a string alone cannot authenticate its imported Lean environment.

### Inventory

- The candidate lists all **153 admitted IDs**, each exactly once, and no extra ID, in the correct 17 files.
- **153** entries contain both an interpreted question and a proposition reading. Relative to the interim payload, **116** records are byte-identical, **35** existing full identities changed, and **2** previously empty readings are now present. There are no proposition-only changes among the 116 unchanged identities.
- **142** IDs have protected historical records. All 142 fixed assertion statements were compared textually to the historical `statement` field and agree exactly. A path-restricted working-tree diff of the permanent `.cas` files and the three protected JSON files was empty during this review.
- **11** IDs have no protected historical interpretation. All eleven were checked directly against their fixed specifications and mathematical definitions, rather than being labelled unchanged from a nonexistent historical identity.

The 11 previously unrecorded IDs are `calculus.limit_sinc`, `calculus.limit_infinity`, `composed.root_sum`, `composed.root_product`, `composed.charpoly`, `composed.det`, `composed.trace`, `factorization.over_complexes`, `polynomials.factors`, `polynomials.no_rational_roots`, and `polynomials.irrational_roots`.

## Method and what the records actually preserve

The review parsed each available full question into its term DAG and separate operation-trace DAG. It inspected the proposition root or judgement tree, relation and polarity, ordered operands, selected rings/fields/modules/algebras, actual source and target maps, bound-variable dependence, admission propositions, diagrams, and route/comparison data. A temporary independent rendering script flattened applications and abbreviated long subterms for reading; the underlying serialized nodes were retained and consulted where presentation mattered. No original graph or question was rewritten.

For equality questions, the typed root keeps the equality type and the two ordered terms. For typing/membership judgements, the record keeps the judgement relation, concrete terms and types, selected context and declaration names, and route declarations. Negation is retained as a separate node; it was not inferred from the expected truth annotation. The `implemented |Fin(3)|` assertion remains an implementation-availability request with its actual cardinality request and type. It has not become the numerical equality `|Fin(3)| = 3`.

The structural audit of all 153 final records found only ordinary term constructors (`const`, `app`, `literal`, `proof`, `bvar`, `lam`, `sort`, `forall`, and `proj`), no metavariable/free-hole node tags, valid backward references for application and proof-type nodes, and valid operation roots. Each string parsed completely as the two serialized graphs with no unexplained suffix. These checks establish readable structural integrity, not Lean typechecking or trace completeness. Proof nodes retain the proposition they prove but not the proof body. Changing a proof of the same proposition is distinct from changing an admitted value or a selected structure; the latter remains mathematical data.

### Identity and proposition presentation changes

The protected identities use `homs` (79), `literal` (26), `settled` (19), `decision` (17), and `implemented` (1). For all 142 historical entries, the final corresponding categories are `homs → homs` (79), `literal → literal` (26), `settled → judged` (19), `decision → judged` (17), and `implemented → implemented` (1). The final inventory contains `homs` (89), `literal` (26), `judged` (37), and `implemented` (1). The full new serialization and its added operation graph are identity-format changes, not a mathematical conclusion.

Only 25 of those 142 final proposition displays match after normalizing whitespace and the common `decision`/`judged` prefix. The remaining 117 display changes were not dismissed as hashes or whitespace. The meaningful changes include more explicit commutative-ring/algebra parameters and routes, selected field and module structure, admitted series summation, group inversion, nullary module zero, and diagram presentation. Their mathematical reasons are described next. The per-ID ledger records the preservation assessment separately from historical identity availability.

## Source-grounded treatment of the substantial presentation changes

### Named rings, fields, algebras, coefficient maps, and evaluation

In `Catalogue/Semantics/Algebra/NamedCommutativeRings.lean`, the named commutative rings are the ordinary rings on ℤ, ℚ, ℝ, ℂ, or `ZMod n`; their comparisons with the earlier ring/carrier presentations are `Iso.refl`. `NamedRings.lean`, `NumberSystems.lean`, and `Fields.lean` likewise retain the named carriers. `Fields.rationals`, `reals`, and `complexes` refine the actual selected commutative rings; their carrier identifications are explicit identities. Consequently, the extra forgetful route in a candidate numeral or operation does not change its ring.

This argument is used only for these exact definitions. It is not an assumption that two structures with the same underlying set are interchangeable. The seven final modular readings now use `NamedRings.ringNumeral (ringIntegersMod n) k`, with n=5 or n=7 as specified. Source `NamedRings.lean` defines this through the unique integer-to-ring map `Int.castRingHom`. The interim terms displayed bounded `finPoint` coordinates; for the specific small numerals in these questions those coordinates denote the same residues. The final terms explicitly retain the selected quotient-ring numeral construction. All additions, products, negations, subtraction order, modulus parameters, targets, and the membership relation were checked directly. In particular, `numbers.membership.zmod` remains membership of the residue numeral 3 in the selected ℤ/5 carrier.

`Algebras.lean` defines an algebra as an actual coslice object `Under K`: its structure map is data. The polynomial algebra is `Under.mk Polynomial.C`, and the multivariate algebra uses `MvPolynomial.C` with the ordered `Fin n` variable type. In the candidate, ℚ-polynomial evaluation in ℝ or ℂ uses `realRationalAlgebra` or `complexRationalAlgebra`, whose structure map is the ordinary `algebraMap`. The corresponding `Polynomials.evaluation_selected` statement identifies evaluation with `eval₂` along that exact map. The candidate has not discarded scalar actions or replaced evaluation by a map with merely matching endpoints. The ℤ-to-ℚ/ℂ polynomial maps retain their actual coefficient maps as well.

The two algebra typing assertions keep their base commutative rings and actual constants maps. The two scheme assertions use the slice over the selected `Spec K`; `Schemes.specPolynomials` and `specMvPolynomials` are `Over.mk (Spec.map C)`, with the contravariant structural map in the proper direction. Their “over ℚ/ℂ” clauses remain part of the question.

### Inversion, division, matrices, and vector zero

`Units.lean` defines the admitted unit from the original element and its `Invertible` data. The inspected inverse questions admit the matrix with rows `(1,2)` and `(3,4)` over the actual rational matrix ring. Its witness is obtained from invertibility of its nonzero determinant. The associated `Eq.mpr` casts relate presentations of this same matrix or rational denominator; their proposition types remain visible. The matrix value is not replaced by the eventual inverse or by a witness-selected answer.

The new group operation is justified by the explicit source theorem
`Units.inverse_eq_groupInverse M : inverse M = groupInverse (groupUnits M) := rfl`.
The carrier inclusion is still composed after the inverse where a matrix value is needed. `solve` uses inverse-then-application to `(5,11)`, `left` keeps `M⁻¹(M v)`, `right` keeps `M(M⁻¹ b)`, and `det` keeps determinant of the inverse with target `-1/2`. The final `inverses.value` root compares the included inverse of this admitted matrix with the rational matrix constructed from ordered rows `(-2,1)` and `(3/2,-1/2)`. Its two denominators are the admitted nonzero rational 2, and its equality type is the carrier of the selected 2×2 rational matrix ring. The fractional signs, row order, ambient ring, and matrix admission all agree with the fixed question; no numerical inverse supplied by a leaf was used in this review.

`LinearAlgebra.lean` uses `Matrix (Fin n) (Fin n) K`, the usual matrix ring, `Matrix.of` on ordered rows, and `mulVec` for application. The three spellings `M*v`, `M v`, and `M(v)` have the same correct matrix-vector interpretation. The rank question remains natural-valued matrix rank; lattice rank is separately cardinal-valued. The subspace questions retain `Submodule.span` over the selected rational field and the complete matrix with first row `(1,1,-1)` and two zero rows for its kernel.

For `matrices.kernel`, the old vector-zero notation is now `Modules.Operations.zero` of `vectorModule ℚ 2`, precomposed with `Foundation.Terminals.singletonComparison.hom`. Source `Modules/Operations.lean` makes this the selected module's additive zero. `Foundation/Terminals.lean` gives the actual map `Fin 1 → PUnit` and inverse. The operation trace records `op.modules.zero`, both ring and module parameters, the comparison direction, and the target carrier. Thus `{0}` remains the singleton containing the zero vector in ℚ².

### Lattice formed cokernels and the underlying carrier route

The candidate retains the actual `rootAToDual n : rootA n → rootADual n` for each n=1,2,3, and the full `bilWFormCokernel` of that morphism. `Lattices/Integral.lean` defines `rootA` using the negative-definite simple-root Gram form, the dual as the integral-pairing submodule of ℚⁿ, and `toDual` with both the coordinate inclusion and the value map ℤ→ℚ. `Limits/Registration.lean` returns the colimit cocone of `parallelPair f 0` in the category of formed modules with varying values. The review did not replace this object by a bare cyclic group or forget the form before taking the cokernel.

The old display transported a canonical parallel-pair diagram before taking its cocone point; the new display gives the standard cocone on the same actual morphism directly. The operation trace still retains that diagram. The carrier route after the formed cokernel is now explicit through the carrier module, module fibre inclusion, additive group, group, monoid, semigroup, magma, and set. `Modules/Total.lean` defines the comparison `additiveGroupCarrierIso` between this route and the direct underlying-module functor, with identity components and naturality by `rfl`; `Modules/CatalogueRegistration.lean` publishes it. These exact comparisons explain the carrier-route change. The ranks and cardinalities retain n and their respective cardinal targets.

### Formal power-series summation

The protected series readings used `Calculus.ofCoefficients` for the coefficient sequence `n ↦ (n² : ℤ)`. The candidate represents the declared formal sum as an actually admitted t-adically summable family `n ↦ C(n)² Xⁿ`, followed by `Series.powerSeriesSum`. Its summability proposition and the selected t-adic topological object remain present. `Series.lean` supplies `hasSum_C_mul_X_pow`, `tsum_C_mul_X_pow`, and `powerSeriesSum_C_mul_X_pow`, which identify this sum with `PowerSeries.mk` of the same coefficient sequence. The constant embedding preserves squares, so `C(n)² = C(n²)` here. The four questions still take coefficients 2,3,0,4 and compare with 4,9,0,16 respectively. This is a mathematical identification of these presentations, not a license to erase the summability domain for arbitrary series.

### Sets, diagrams, and differentials

The finite-set questions retain the full ordered constructors and domains, including difference order, subset direction, outer negation, product and power-set formation, and images of the actual doubling map. Cardinal answers remain cardinals where specified, including ℵ₀. Function equalities retain the full variable-dependent maps; the evenness question has not become a check at a selected numeral.

The set pullback retains both complete finite graph maps: `f : Fin 3 → Fin 2` sends `(0,1,2)` to `(0,1,1)`, while `g : Fin 2 → Fin 2` sends `(0,1)` to `(1,0)`. The `FiniteSets` version retains those maps as finite-category morphisms, the cospan, the finite-to-set forgetful action, `diagramIsoCospan`, `limitConeOfIso`, and the created/lifted limit cone before cardinality. The two coproduct questions keep the tagged coproduct construction. No endpoint-only substitute for either diagram was found.

In `Differentials.lean`, `d` is the universal relative Kähler derivation into `Ω[ℚ[x]/ℚ]`; its coordinate description uses the selected `dx` and a proved module equivalence. The candidate distinguishes that codomain from polynomial differentiation. The primitive set retains `{g | dg = f dx}`, its right side is the full constant coset of `x³ + (1/2)x² + x`, and the normalized questions retain the additional equation `g(0)=0`. In particular, normalization is not silently dropped when taking cardinality.

## Newly readable questions: direct mathematical checks

These rows have no protected historical reading to compare against. “Matches” below means that the candidate operation, domain, and claim agree with the fixed question as interpreted by the cited mathematical definitions; it is not a new acceptance baseline.

| IDs | Direct check of the supplied interpretation |
| --- | --- |
| `calculus.limit_sinc` | Matches the limit of `sin(t)/t` at 0 on the punctured real line. `RealLimits.puncturedLine 0`, its nonzero-to-unit admission, the actual quotient map, and convergence at the punctured-neighborhood filter remain present. `RealLimits.limit_eq_iff_tendsto` explains the limit selector. Target is real 1. |
| `calculus.limit_infinity` | Matches `1/t → 0` as `t → +∞`. The source distinguishes +∞ from −∞; the candidate uses the former, with the `atTop` approach pulled back along the units inclusion. The admitted convergent map and target 0 are retained. |
| `composed.root_sum`, `composed.root_product` | Match the sum/product of the distinct complex roots of the mapped nonzero polynomial `r=x³−2x+1`. They retain its actual roots finite set, the identity summand/factor, respectively the additive and multiplicative commutative structures, and targets 0 and −1. They do not sum coefficients or substitute a list of expected roots. |
| `composed.charpoly`, `composed.det`, `composed.trace` | Match the requested characteristic polynomial, determinant and trace of the companion matrix of `r`. Admission retains `r.Monic ∧ r.natDegree=3`. `LinearAlgebra.companion` specifies subdiagonal ones and final column `−p₀,…,−pₙ₋₁`; the candidate retains n=3, ℚ, the actual polynomial and this constructor. Targets remain `r`, −1 and 0. |
| `factorization.over_complexes` | Matches factors of the actual ℤ-to-ℂ image of `p=x³−2x+1`, admitted nonzero. The expected finite set is exactly `x−1`, `x−((-1+√5)/2)`, `x−((-1−√5)/2)` in ℂ[x]. Both signs, the positive real square root embedded in ℂ, and the invertible constant-polynomial denominator 2 are retained. `Polynomials.factors` is the finite set of normalized irreducible factors. |
| `polynomials.factors` | Matches the finite factors of nonzero `p` over ℤ, with the specified pair `x−1` and `x²+x−1`. The finite-set-to-power-set inclusion preserves equality; it does not change factor multiplicities into a multiset question. |
| `polynomials.no_rational_roots` | Matches the distinct rational roots of admitted nonzero `x²−2` being the empty finite set. `Polynomials.roots` is `p.roots.toFinset`, with `roots_extent` identifying it with the zero set. |
| `polynomials.irrational_roots` | Matches the fixed inclusion `roots(map(ι_ℚ,ℂ,q)) ⊆ Set.univ \ range(ι_ℚ,ℂ)` for `q=x²−2`, admitted nonzero after the actual coefficient map. The left side retains the finite-roots inclusion into `Set ℂ`. The right side is the whole complex set minus the image of the actual composite ℚ→ℝ→ℂ. `PowerSets.image`, `diff`, and `subset` define exactly those operations, and the trace retains their operand order. The question remains this inclusion; it has not been strengthened to an exact enumeration of roots. |

The remaining analytic readings also retain their domains. The square integral is the oriented real integral from 0 to 1 of the actual squared-coordinate function, with rational 1/3 embedded into ℝ. The sine integral is from 0 to π. The Taylor questions keep the admitted smooth sine/exp functions, center 0, and the real power-series target; they remain typing questions, not coefficient identities. `Calculus.taylor` forms coefficients from iterated derivatives and actual factorial units. The decimal approximation retains exact rational bounds `14142135623/10^10` and `1/10^10`, a strict `<`, and the norm of the embedded real difference.

## Final export changes reviewed individually

The final/interim comparison was made on all fields, then on full structured roots and operation metadata with DAG references resolved. It retained universes, binder data, proof-proposition types, ordered arguments, and all metadata fields. Structural equality here is an independent reading aid, not a Lean conversion proof. The differences were then interpreted using the source definitions. No changed string was accepted merely because its pretty proposition or an expected answer stayed the same.

**Twenty-four** changed identities have the same complete typed question root as the interim reading. Their changes are in the operation trace:

| IDs | Trace changes checked and mathematical disposition |
| --- | --- |
| `composed.root_sum`, `composed.root_product`, `composed.charpoly`, `composed.trace` | Numeral metadata names the selected commutative ring directly, and some object metadata changes between a named object and a parameter-equivalence list. The actual complex additive/product structures, admitted polynomial, companion constructor, and targets are unchanged. |
| `differentials.at_two`, `integration.normalized_count`, `integration.normalized`, `integration.at_zero` | Rational numeral metadata and the selected rational-object metadata change. The full evaluation at 2 or 0, primitive set, normalization equation, and expected scalar remain identical. |
| `factorization.over_complexes`, `polynomials.root`, `polynomials.no_rational_roots` | Complex/integer numeral metadata or named-parameter equivalence lists change. The coefficient maps, nonzero-polynomial admission, normalized factor set, evaluation at 1, and empty rational-root set remain identical. |
| `inverses.solve`, `inverses.left`, `inverses.right`, `inverses.det` | Matrix-entry numeral metadata now points to the selected rational commutative ring rather than its forgotten ring presentation; `inverses.det` also changes rational-object metadata. The actual admitted matrix, inverse, division, and ordered applications are identical. |
| `matrices.product`, `matrices.juxtaposition`, `matrices.application`, `matrices.det`, `matrices.rank`, `matrices.kernel`, `matrices.trace`, `matrices.charpoly`, `subspaces.kernel` | The same matrix/scalar numeral metadata change occurs; some rational-object equivalence metadata changes. `matrices.kernel` additionally records the already present vector carrier `Fin 2 → ℚ`, and `subspaces.kernel` records `Fin 3 → ℚ`. All selected matrix/vector/module structures and original equations remain identical. |

The introduced or removed parameter-equivalence lists concern the exact named ℤ, ℚ, or ℂ structures inspected above. Their recorded carrier identifications are the corresponding `Iso.refl` declarations, and field forgetting retains the already selected commutative ring. Replacing such a provenance list by a direct named-object record is a real trace-format change, but it does not alter these fixed questions. This conclusion does not justify erasing a nonidentity comparison or scalar action in another question. Trace root ordering also changes in places; the actual ordered mathematical dependencies are retained in the term DAG and operand metadata.

**Eleven** changed identities also change the full typed question graph:

- `numbers.zmod5.sum`, `numbers.zmod5.product`, `numbers.zmod5.negation`, `numbers.zmod5.difference`, `numbers.zmod7.distributive`, `numbers.zmod7.value`, and `numbers.membership.zmod` have the explicit ring-numeral change described above. Every final relation and operand was read directly.
- `series.coefficient_two`, `series.coefficient_three`, `series.coefficient_zero`, and `series.coefficient_four` have exactly one distinct changed type subexpression each after DAG references are resolved: the bare `Calculus.powerSeries ℤ` carrier becomes the set reached from the selected `Calculus.ringPowerSeries ℤ` along the explicit ring-to-set route. `Calculus.ringPowerSeries` is `RingCat.of (PowerSeries ℤ)` and its identification is `Iso.refl`. The trace now records that ring object and route and adjusts the associated product cone. The full family `C(n)²Xⁿ`, the summability proposition in the t-adic topology, coefficient indices 2,3,0,4, and targets 4,9,0,16 are unchanged. This change was invisible in the pretty proposition and was checked in the full DAG.

The **two newly present** records are checked explicitly in the inverse and roots sections above. All **116 byte-identical** records retain the earlier independent review; they were not rerun through computational implementations. The ledger below marks which final-export treatment each ID received.

## Limits of the finding

No unavailable interpretation remains in the final payload, and no actual changed or missing fixed question was identified. This finding applies to the exact final digest and reported producer/freeze above. A subsequent export or source change requires its own comparison. The review adds a new report only; it does not replace protected identities with the candidate serializations or activate new acceptance records.

This report is not a machine-checked theorem equating every historical and current Lean expression. The cited explicit identities, definitions, and domain theorems support the described presentation comparisons; the reviewer did not manufacture new proofs or silently declare arbitrary transports harmless. The trace can retain relevant data without establishing that an implementation later uses that data faithfully. Likewise, a fully preserved mathematical question may remain computationally unimplemented. Those are separate reviews.

## Per-ID coverage ledger

Each ID occurs once below. **H** means a historical record exists and the final candidate preserves the same fixed mathematical question; **N** means no historical interpretation exists and the candidate was checked directly as described above. In the final-export column, **U** means byte-identical to its reviewed interim record (116 IDs), **D** means changed and individually revisited (35), and **R** means newly readable and directly reviewed (2). Every row is assessed as preserving the specified question. The compact question column reproduces the fixed assertion as shorthand; the source contexts listed for each file were also checked in the candidate. It does not mean that source text, a hash, or an expected answer was used as a substitute for reading the candidate.

### `tests/acceptance/algebras_schemes.cas`

The selected ℂ-algebra in ten variables uses the constants map and ordered variable set Fin 10; the one-variable algebra is over ℚ. The affine schemes are respectively over Spec ℚ and Spec ℂ with their actual structural Spec maps.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `algebras.polynomials_several` | H | U | `R in Algebras/ℂ` |
| `algebras.polynomials` | H | U | `ℚ[x] in Algebras/ℚ` |
| `schemes.affine_line` | H | U | `Spec ℚ[x] in Schemes/ℚ` |
| `schemes.affine_space` | H | U | `Spec R in Schemes/ℂ` |

### `tests/acceptance/calculus.cas`

All limits and integrals are real. The two limits retain their punctured/atTop domains and convergence admissions; the integrals retain ordered endpoints and continuity. Taylor uses smooth exp/sin at center 0 and asks only membership in ℝ[[t]].

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `calculus.limit_sinc` | N | U | `lim_{t → 0} sin(t)/t = 1` |
| `calculus.limit_infinity` | N | U | `lim_{t → ∞} 1/t = 0` |
| `calculus.integral_square` | H | U | `∫_{0}^{1} t² dt = 1/3` |
| `calculus.integral_sine` | H | U | `∫_{0}^{π} sin(t) dt = 2` |
| `calculus.taylor_exp` | H | U | `Tf ∈ ℝ[[t]]` |
| `calculus.taylor_sin` | H | U | `Tg ∈ ℝ[[t]]` |

### `tests/acceptance/composed.cas`

Here r=x³−2x+1 in ℚ[x], roots is the actual complex zero set of r under the selected rational-to-complex algebra map, and C is its monic degree-3 companion matrix. The root sum/product use the distinct finite complex roots. The map composition retains the declared cube and square functions on ℝ.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `composed.root_count` | H | U | `\|roots\| = 3` |
| `composed.root_one` | H | U | `1 ∈ roots` |
| `composed.root_sum` | N | D | `∑_{a ∈ ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots()} a = 0` |
| `composed.root_product` | N | D | `∏_{a ∈ ((map r to ℂ[x]) in ℂ[x] ∖ 0).roots()} a = -1` |
| `composed.charpoly` | N | D | `C.charpoly() = r` |
| `composed.det` | N | U | `C.det() = -1` |
| `composed.trace` | N | D | `C.trace() = 0` |
| `composed.composition` | H | U | `(f ∘ g)(t) = t^6` |

### `tests/acceptance/differentials.cas`

Here f=3x²+x+1 and F=x³+(1/2)x²+x in ℚ[x]. Universal differentials use Ω[ℚ[x]/ℚ] and dx; derivative uses ℚ[x]. Fs is the entire primitive set restricted by h(0)=0, and the constant coset uses all ℚ.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `differentials.member` | H | U | `f ∈ ℚ[x]` |
| `differentials.degree` | H | U | `f.deg() = 2` |
| `differentials.at_two` | H | D | `f(2) = 15` |
| `differentials.differential` | H | U | `d(f) = (6x + 1) dx` |
| `differentials.derivative` | H | U | `(d/dx)(f) = 6x + 1` |
| `integration.primitives` | H | U | `∫ f dx = x³ + (1/2)x² + x + ℚ` |
| `integration.normalized_count` | H | D | `Fs.cardinality() = 1` |
| `integration.normalized` | H | D | `Fs = {x³ + (1/2)x² + x}` |
| `integration.differential` | H | U | `d(F) = f dx` |
| `integration.derivative` | H | U | `(d/dx)(F) = f` |
| `integration.at_zero` | H | D | `F(0) = 0` |

### `tests/acceptance/ellipses.cas`

X is the natural arithmetic progression with start 0 and difference 1; Y has difference 2. The square-preimage set is Z={n∈ℕ:n²∈2ℕ}. Prime/not-prime retain the actual prime predicate and polarity.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `ellipses.naturals` | H | U | `X = ℕ` |
| `ellipses.evens` | H | U | `Y = {2n \| n ∈ ℕ}` |
| `ellipses.multiples` | H | U | `Y = 2ℕ` |
| `ellipses.even_square` | H | U | `4 ∈ Z` |
| `ellipses.odd_square` | H | U | `3 ∉ Z` |
| `ellipses.squares_even` | H | U | `Z = Y` |
| `ellipses.prime` | H | U | `7 ∈ primes` |
| `ellipses.not_prime` | H | U | `9 ∉ primes` |

### `tests/acceptance/factorization.cas`

Natural factorization admits positive 360 and retains the relevant prime parameter, including nonfactor 7. The complex factorization uses p=x³−2x+1 from ℤ[x] and its actual coefficient map. The approximation uses exact decimals as rational numbers and strict inequality.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `factorization.prime_factors` | H | U | `(360).prime_factors() = {2, 3, 5}` |
| `factorization.multiplicity_two` | H | U | `(360).multiplicity(2) = 3` |
| `factorization.multiplicity_three` | H | U | `(360).multiplicity(3) = 2` |
| `factorization.multiplicity_seven` | H | U | `(360).multiplicity(7) = 0` |
| `factorization.over_complexes` | N | D | `((map p to ℂ[x]) in ℂ[x] ∖ 0).factors() = {x - 1, x - (-1 + √5)/2, x - (-1 - √5)/2}` |
| `factorization.approximation` | H | U | `\|√2 - 1.4142135623\| < 0.0000000001` |

### `tests/acceptance/finite_sets.cas`

A={1,2,3} and B={3,4,5} are subsets of ℤ. S={n∈ℤ:n²≤20}; E={2n:n∈ℕ}; m2 is the actual doubling map ℕ→ℕ. Difference and subset directions, cardinal types, all source elements, and the domain of each comprehension remain explicit.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `finite_sets.union` | H | U | `A ∪ B = {1, 2, 3, 4, 5}` |
| `finite_sets.intersection` | H | U | `A ∩ B = {3}` |
| `finite_sets.difference` | H | U | `A \ B = {1, 2}` |
| `finite_sets.symmetric_difference` | H | U | `A △ B = {1, 2, 4, 5}` |
| `finite_sets.card` | H | U | `\|A\| = 3` |
| `finite_sets.card_product` | H | U | `\|A × B\| = 9` |
| `finite_sets.card_power_set` | H | U | `\|𝒫(A)\| = 8` |
| `finite_sets.member` | H | U | `2 ∈ A` |
| `finite_sets.not_member` | H | U | `4 ∉ A` |
| `finite_sets.subset_union` | H | U | `A ⊆ A ∪ B` |
| `finite_sets.intersection_subset` | H | U | `A ∩ B ⊆ A` |
| `comprehension.typed` | H | U | `S in 𝒫(ℤ)` |
| `comprehension.elements` | H | U | `S = {-4, -3, -2, -1, 0, 1, 2, 3, 4}` |
| `comprehension.card` | H | U | `\|S\| = 9` |
| `comprehension.image_typed` | H | U | `E in 𝒫(ℕ)` |
| `comprehension.even_member` | H | U | `8 ∈ E` |
| `comprehension.odd_not_member` | H | U | `9 ∉ E` |
| `comprehension.even_card` | H | U | `\|E\| = ℵ₀` |
| `comprehension.image_apply` | H | U | `m2(ℕ) = E` |
| `comprehension.image_method` | H | U | `m2.image() = E` |

### `tests/acceptance/fractions.cas`

Division keeps the actual nonzero denominator admitted as a unit of the selected rational ring. Square root is the standard nonnegative real root. z=2+2i and the norm has real target.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `fractions.member` | H | U | `7/3 ∈ ℚ` |
| `fractions.halves` | H | U | `1/2 + 1/2 = 1 in ℚ` |
| `fractions.cancel` | H | U | `(7/3) · 3 = 7 in ℚ` |
| `fractions.lowest_terms` | H | U | `6/4 = 3/2` |
| `fractions.sqrt_member` | H | U | `√2 ∈ ℝ` |
| `fractions.modulus` | H | U | `\|z\| = 2√2` |

### `tests/acceptance/functions.cas`

Both h and hp are t↦t²+1 on ℝ. Equality and evenness retain variable dependence on the entire real domain; point evaluations retain their separate selected numerals.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `functions.extensional` | H | U | `h = hp` |
| `functions.at_zero` | H | U | `h(0) = 1` |
| `functions.at_three` | H | U | `h(3) = 10` |
| `functions.even` | H | U | `h(-t) = h(t)` |

### `tests/acceptance/inverses.cas`

M is the admitted unit with rows (1,2),(3,4) in the rational 2×2 matrix ring; v=(1,2), b=(5,11). Selected unit-group inverse and inclusion are retained, with the original matrix determinant witness and ordered applications.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `inverses.value` | H | R | `M⁻¹ = [-2, 1; 3/2, -1/2] in Mat₂(ℚ)` |
| `inverses.solve` | H | D | `M⁻¹ b = v` |
| `inverses.left` | H | D | `M⁻¹(M v) = v` |
| `inverses.right` | H | D | `M(M⁻¹ b) = b` |
| `inverses.det` | H | D | `(M⁻¹).det() = -1/2` |

### `tests/acceptance/lattices.cas`

A(n) is the actual formed negative-definite root lattice on its simple roots. to_dual(n) has both the lattice and value maps; cokernel is the formed-category cokernel before the carrier route. Lattice ranks and cardinalities are cardinal-valued.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `lattices.discriminant.a1` | H | U | `\|cokernel(to_dual(1))\| = 2` |
| `lattices.discriminant.a2` | H | U | `\|cokernel(to_dual(2))\| = 3` |
| `lattices.discriminant.a3` | H | U | `\|cokernel(to_dual(3))\| = 4` |
| `lattices.rank.a1` | H | U | `A(1).rank() = 1` |
| `lattices.rank.a2` | H | U | `A(2).rank() = 2` |
| `lattices.rank.a3` | H | U | `A(3).rank() = 3` |
| `lattices.card.a2` | H | U | `\|A(2)\| = ℵ₀` |
| `lattices.card.a0` | H | U | `\|A(0)\| = 1` |

### `tests/acceptance/linear_algebra.cas`

M has ordered rows (1,2),(3,4), v=(1,2), b=(5,11). The actual rational span W is generated by (1,0,1),(0,1,1) in ℚ³. N has rows (1,1,−1),(0,0,0),(0,0,0). The zero in {0} is the selected ℚ²-module zero.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `matrices.product` | H | D | `M*v = b` |
| `matrices.juxtaposition` | H | D | `M v = b` |
| `matrices.application` | H | D | `M(v) = b` |
| `matrices.det` | H | D | `M.det() = -2` |
| `matrices.rank` | H | D | `M.rank() = 2` |
| `matrices.kernel` | H | D | `M.ker() = {0}` |
| `matrices.trace` | H | D | `M.trace() = 5` |
| `matrices.charpoly` | H | D | `M.charpoly() = x² - 5x - 2 in ℚ[x]` |
| `subspaces.dim` | H | U | `W.dim() = 2` |
| `subspaces.member` | H | U | `(1, 1, 2) ∈ W` |
| `subspaces.not_member` | H | U | `(1, 1, 0) ∉ W` |
| `subspaces.kernel` | H | D | `W = N.ker()` |

### `tests/acceptance/numbers.cas`

All specified integer/rational/residue rings, moduli 5 and 7, and number-system embeddings are retained. z=2+2i; re, im and absolute value have real targets; conjugation and the asserted product z·conj(z) have complex targets. Containment conjunction and its order remain explicit.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `numbers.integers.sum` | H | U | `2 + 3 = 5` |
| `numbers.zmod5.sum` | H | D | `2 + 3 = 0 in ℤ/5` |
| `numbers.zmod5.product` | H | D | `2 · 3 = 1 in ℤ/5` |
| `numbers.zmod5.negation` | H | D | `-2 = 3 in ℤ/5` |
| `numbers.zmod5.difference` | H | D | `2 - 3 = 4 in ℤ/5` |
| `numbers.zmod7.distributive` | H | D | `3 · (4 + 5) = 3 · 4 + 3 · 5 in ℤ/7` |
| `numbers.zmod7.value` | H | D | `3 · (4 + 5) = 6 in ℤ/7` |
| `numbers.rationals.sum` | H | U | `2 + 3 = 5 in ℚ` |
| `numbers.containments` | H | U | `ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ` |
| `numbers.containments.transitive` | H | U | `ℕ ⊆ ℂ` |
| `numbers.membership.zmod` | H | D | `3 ∈ ℤ/5` |
| `numbers.membership.negative` | H | U | `-3 ∈ ℤ` |
| `numbers.gcd` | H | U | `gcd(84, 30) = 6` |
| `numbers.complex.re` | H | U | `z.re() = 2` |
| `numbers.complex.im` | H | U | `z.im() = 2` |
| `numbers.complex.bar` | H | U | `z.bar() = 2 - 2 · i` |
| `numbers.complex.norm` | H | U | `z · z.bar() = 8` |
| `numbers.complex.abs` | H | U | `\|z\| = 2 · sqrt(2)` |

### `tests/acceptance/polynomials.cas`

p=x³−2x+1 in ℤ[x]; q=x²−2 in ℚ[x]. Evaluation and coefficient extension use the specified actual coefficient maps. Factors and roots retain their nonzero admissions and distinct finite-set semantics. ±√2 are the real square root and its negation.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `polynomials.variable` | H | U | `x ∈ ℤ[x]` |
| `polynomials.member` | H | U | `p ∈ ℤ[x]` |
| `polynomials.degree` | H | U | `p.deg() = 3` |
| `polynomials.root` | H | D | `p(1) = 0` |
| `polynomials.factors` | N | U | `(p in ℤ[x] ∖ 0).factors() = {x - 1, x² + x - 1}` |
| `polynomials.degree_over_rationals` | H | U | `(map p to ℚ[x]).deg() = 3` |
| `polynomials.at_sqrt2` | H | U | `q(√2) = 0` |
| `polynomials.at_minus_sqrt2` | H | U | `q(-√2) = 0` |
| `polynomials.no_rational_roots` | N | D | `(q in ℚ[x] ∖ 0).roots() = {}` |
| `polynomials.irrational_roots` | N | R | `((map q to ℂ[x]) in ℂ[x] ∖ 0).roots() ⊆ ℂ - ℚ` |

### `tests/acceptance/series.cas`

The same family n↦C(n)²Xⁿ is admitted as t-adically summable over ℤ in every row; each row then retains its own coefficient index and expected integer.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `series.coefficient_two` | H | D | `[t^2]f = 4` |
| `series.coefficient_three` | H | D | `[t³]f = 9` |
| `series.coefficient_zero` | H | D | `[t^0]f = 0` |
| `series.coefficient_four` | H | D | `[t^4]f = 16` |

### `tests/acceptance/sets.cas`

Each power retains both the set and exponent. A=Fin(2)×ℤ/3. Pullbacks retain f=[0↦0,1↦1,2↦1] and g=[0↦1,1↦0], with the explicit FiniteSets creation/diagram comparison where declared. Coproducts retain tags. Reversal maps retain n and input order.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `sets.card.z4_cubed` | H | U | `\|(ℤ/4)^3\| = 64` |
| `sets.card.z7` | H | U | `\|(ℤ/7)^1\| = 7` |
| `sets.card.z5_empty_power` | H | U | `\|(ℤ/5)^0\| = 1` |
| `sets.card.integers` | H | U | `\|ℤ\| = ℵ₀` |
| `sets.card.naturals` | H | U | `\|ℕ\| = ℵ₀` |
| `sets.card.fin2_times_z3` | H | U | `\|Fin(2) × ℤ/3\| = 6` |
| `sets.finite.integers` | H | U | `ℤ.is_finite() = false` |
| `sets.finite.fin2_times_z3` | H | U | `(Fin(2) × ℤ/3).is_finite()` |
| `sets.implemented.card_fin` | H | U | `implemented \|Fin(3)\|` |
| `sets.card.square` | H | U | `\|A × A\| = 36` |
| `sets.card.fin2_sqcup_fin3` | H | U | `\|Fin(2) ⊔ Fin(3)\| = 5` |
| `sets.finite.fin2_sqcup_fin3` | H | U | `(Fin(2) ⊔ Fin(3)).is_finite()` |
| `sets.eq.rev_rev` | H | U | `rev(3) ∘ rev(3) = id(Fin(3))` |
| `sets.limit.pullback.card` | H | U | `\|pullback(f, g)\| = 3` |
| `finite_sets.card.three` | H | U | `\|Fin(3) in FiniteSets\| = 3` |
| `finite_sets.limit.pullback.card` | H | U | `\|pullback(f', g')\| = 3` |
| `sets.apply.rev` | H | U | `rev(3, 0) = 2 in Fin(3)` |
| `sets.apply.rev_rev` | H | U | `rev(4, rev(4, 1)) = 1 in Fin(4)` |

### `tests/acceptance/several_variables.cas`

R=ℂ[x₀,…,x₉] with exactly ten ordered variables. The two selected indices are 3 and 9. The rational plane uses x·y²+1, two variables, and total degree, distinct from Krull dimension with target WithBot ℕ∞.

| ID | Review | Final export | Fixed question, in the checked context |
| --- | --- | --- | --- |
| `several_variables.dimension` | H | U | `R.dimension() is 10` |
| `several_variables.variable` | H | U | `x_3 ∈ R` |
| `several_variables.last_variable` | H | U | `x_9 ∈ R` |
| `several_variables.total_degree` | H | U | `p.total_degree() = 3` |
| `several_variables.plane` | H | U | `ℚ[x, y].dimension() = 2` |
