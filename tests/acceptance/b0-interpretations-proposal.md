# Independently authored interpretation proposal for the fixed B0 corpus

This is a proposal for independent acceptance, not an admission or release decision.
The denominator is the **153** assertion identities in `CasAcceptance/Permanent/admitted.json`
at `bcd08de4`; no identity is removed because an interpreter cannot read it.
The mathematical dependency being assessed is `lean_categories` at `b249ca2`.
The language authority is the approved `SPEC.md`. No kernel, controller, leaf source,
or candidate execution output was used to establish the questions below.
The existing `bcd08de4` interpretation records were inspected as historical claims;
their hashes and `settled:holds` labels were not used as expected interpretations.

## Conventions and comparison obligation

Each entry below states the **question**, including its relation, operands, ambient
objects and selected data; it does not stand for its Boolean answer. The original
assertion, let-bindings, citation and admitted digest remain fixed at `bcd08de4`.
Z, Q, R, C and N mean their named mathematical objects, with the canonical inclusions
Z → Q → R → C and N → Z. Fin(n) is the set of natural indices below n.
Numerals in an ambient ring are its integer images. A finite numeral compared to
cardinality is its finite cardinal image. A subset equality is extensional in its
specified ambient set. A map equality retains its domain, codomain and composite
order. Unbound variables in map identities are universally quantified.

The structural path is part of a question when needed for propagation. The named
A(n), A_dual(n) and to_dual(n) are exactly the accepted `BilWFormCat Z` objects
and morphism from `Integral.lean`, not an implicit retyping into a differently
parameterized lattice category. Their carrier route is the actual `bilWFormCarrier`
functor to Z-modules, followed by the module carrier functor to sets. A(n)'s value
module is Z, while A_dual(n)'s is Q; the inclusion retains the corresponding
Z-linear map on values. Module rank uses the declared base ring.
Ring carrier observations use the admitted comparison
of structural carrier routes, rather than whichever route happens to be installed
first. A construction retains its domain, codomain, defining arrows and prescribed
lift. Formed-module kernels therefore retain the restricted form; an equality of
underlying carriers cannot replace the question about this structured result.

`in` admissions retain the stated mathematical object with its evidence; a units
admission uses invertibility, a nonzero polynomial admission uses nonzeroness,
Monic(3,Q) uses degree and leading coefficient, C^infinity uses smoothness, and
FiniteSets uses finiteness. Missing implementation evidence cannot replace these
mathematical obligations. Comparison may erase proof presentation but must preserve
the admitted datum and obligation, selected structure, parameters, structural maps,
logical connectives, relation and result type. Logical equivalence or equal truth
values do not suffice.

The two limit questions retain the accepted `RealLimits` domains at `b249ca2`:
`ConvergentAt(0)` has maps from the punctured line R minus {0}, equipped with
convergence along the comap of punctured neighborhoods of 0; the at-infinity
domain has maps on real units, equipped with convergence along the comap of
`atTop` through the units inclusion into R. Both admissions retain the actual
map and its existential convergence proof. The selected finite/infinite point
and approach filter are part of the question. A totalized real function at the
excluded point is not substituted for either admitted domain. The `implemented`
question is intentionally about
execution availability while retaining a fixed semantic cardinality request.

## Mathematical justification

The arithmetic entries follow integer/rational arithmetic and quotient-ring laws.
The gcd uses Euclid: 84=2*30+24, 30=24+6, 24=4*6. Prime factorization is
360=2^3*3^2*5. The strict sqrt approximation follows by squaring the positive exact
rational endpoints 1.4142135623 and 1.4142135624: the former square is below 2 and
the latter above 2. Canonical subset claims use injectivity of the stated embeddings.

Finite subset claims are checked by listing members. Product, sum, function-set and
power-set cardinalities use Mathlib `Fintype.card_prod`, `Fintype.card_sum`,
`Fintype.card_fun`, `Fintype.card_set`, `Fintype.card_fin`, and `ZMod.card`.
The two pullbacks have precisely (0,1), (1,0), (2,0), with the stated projections.
Countability uses `Cardinal.mk_int`, `Cardinal.mk_nat`, and injectivity of n ↦ 2n.
Reversal uses i ↦ n−1−i and applying it twice.

The cubic factorization is (X−1)(X²+X−1), with distinct roots 1 and
(−1±sqrt(5))/2; their sum is 0 and product −1. X²−2 has no rational root
by irrationality of sqrt(2). Companion characteristic polynomial, determinant and
trace follow the standard companion matrix identity. Matrix entries follow direct
multiplication, determinant 4−6=−2, and the displayed adjugate formula.
The subspace is {(a,b,a+b):a,b in Q}; the first two coordinates prove its basis
independent. Differentiation follows the universal relative derivation on Q[X];
its kernel is the constants, giving the entire primitive coset and its normalized
singleton. These meanings are the approved SPEC's sections on polynomials,
matrices, differentials and indefinite integration, not alternative result forms.

The real limits use the classical sine limit and reciprocal limit; integrals use
the primitives t³/3 and −cos(t). Smoothness of exp and sin supplies their formal
Taylor series; no analytic convergence is asserted. Formal series coefficients
follow T-adic summability and the single contributing monomial at each degree.
Krull dimension uses the polynomial-ring dimension theorem over a field, as in
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 11; polynomial
constants supply the algebra structure and contravariant Spec supplies the base map.
The A_n lattice questions use its Cartan form: rank n, absolute Gram determinant n+1,
and discriminant quotient cardinality n+1 (Conway–Sloane, Sphere Packings,
Lattices and Groups, Chapter 4 §6.1; Bourbaki, Lie Groups and Lie Algebras,
Chapter VI, Plate I). These are independent calculations, not backend observations.

## Full inventory of questions

### `algebras.polynomials`

The polynomial ring Q[X], equipped with the constants homomorphism Q → Q[X], is an object of Q-algebras.

### `algebras.polynomials_several`

C[X0,…,X9], equipped with its constants homomorphism C → C[X0,…,X9], is an object of C-algebras.

### `calculus.integral_sine`

The oriented integral from 0 to real pi of the continuous real sine function equals real 2.

### `calculus.integral_square`

The oriented integral on the real interval from 0 to 1 of the continuous real function t ↦ t² equals the real image of 1/3 in Q.

### `calculus.limit_infinity`

The admitted map on real units t ↦ 1/t converges along the comap of the real atTop filter through the units inclusion, and its limit at positive infinity equals real 0. Its domain is real units, not all real numbers.

### `calculus.limit_sinc`

The admitted map from the punctured line R minus {0} to R, t ↦ sin(t)/t, converges along the comap of the punctured neighborhoods of 0, and its limit equals real 1. The denominator uses the admitted map from this punctured line into real units; no value at 0 is prescribed.

### `calculus.taylor_exp`

The Taylor series at real 0 of the real exponential, admitted with its smooth structure, is a member of R[[T]]. This asks membership, not convergence to the function.

### `calculus.taylor_sin`

The Taylor series at real 0 of real sine, admitted with its smooth structure, is a member of R[[T]]. This asks membership, not convergence to the function.

### `composed.charpoly`

The characteristic polynomial over Q of the companion matrix of r=X³−2X+1 admitted as monic of degree 3 equals r in Q[X].

### `composed.composition`

As maps R → R, the composite of t ↦ t³ followed by t ↦ t² equals t ↦ t⁶; the free real variable is universally quantified.

### `composed.det`

The determinant over Q of that companion matrix equals rational −1.

### `composed.root_count`

The set {a in C : a³−2a+1=0}, obtained by extending the coefficients of r in Q[X], has cardinality 3; roots are counted without multiplicity.

### `composed.root_one`

Complex 1 belongs to {a in C : a³−2a+1=0}.

### `composed.root_product`

The product of the identity function over that finite set of complex roots is complex −1; this is a finite-set product, not a multiset product.

### `composed.root_sum`

The sum of the identity function over the finite set of complex roots of the admitted nonzero coefficient extension of r=X³−2X+1 is complex 0.

### `composed.trace`

The trace over Q of that companion matrix equals rational 0.

### `comprehension.card`

The cardinality of S={n in Z : n²≤20} equals finite cardinal 9.

### `comprehension.elements`

S={n in Z : n²≤20} equals the integer subset {−4,−3,−2,−1,0,1,2,3,4} extensionally.

### `comprehension.even_card`

The cardinality of the natural subset E={2n : n in N} equals aleph_0.

### `comprehension.even_member`

Natural 8 belongs to E={2n : n in N}.

### `comprehension.image_apply`

The direct image of all N under the map m2:N → N, n ↦ 2n, equals E={2n : n in N}.

### `comprehension.image_method`

The image subset of the map m2:N → N, n ↦ 2n, equals E={2n : n in N}.

### `comprehension.image_typed`

E={2n : n in N} belongs to the power set of N, using natural multiplication and the natural target.

### `comprehension.odd_not_member`

Natural 9 does not belong to E={2n : n in N}.

### `comprehension.typed`

The set S={n in Z : n²≤20}, with its integer predicate, belongs to the power set of Z.

### `differentials.at_two`

Evaluation of f=3X²+X+1 at rational 2 equals rational 15.

### `differentials.degree`

The polynomial degree of f=3X²+X+1 in Q[X] equals 2.

### `differentials.derivative`

The Q-linear polynomial derivative of f=3X²+X+1 equals 6X+1 in Q[X].

### `differentials.differential`

The universal Q-relative derivation sends f=3X²+X+1 to (6X+1)dX in Ω¹(Q[X]/Q), with the prescribed coordinate isomorphism Ω¹ ≅ Q[X]dX.

### `differentials.member`

The polynomial f=3X²+X+1 belongs to Q[X].

### `ellipses.even_square`

Natural 4 belongs to Z={n in N : n² belongs to 2N}, where Z here is a local set name, not the integers.

### `ellipses.evens`

The progression subset {0+2k : k in N} equals the direct-image subset {2n : n in N}.

### `ellipses.multiples`

The progression subset {0+2k : k in N} equals the subset 2N of natural multiples of 2.

### `ellipses.naturals`

The progression subset {0+k : k in N} equals N.

### `ellipses.not_prime`

Natural 9 does not belong to the subset {n in N : n is prime}.

### `ellipses.odd_square`

Natural 3 does not belong to that local subset Z={n in N : n² belongs to 2N}.

### `ellipses.prime`

Natural 7 belongs to the subset {n in N : n is prime}.

### `ellipses.squares_even`

The subset {n in N : n² belongs to 2N} equals the progression subset {0+2k : k in N} extensionally.

### `factorization.approximation`

In R, the absolute difference between the positive square root of 2 and the exact rational decimal 14142135623/10^10 is strictly less than 1/10^10.

### `factorization.multiplicity_seven`

The exponent of prime 7 in the natural factorization of 360 equals 0.

### `factorization.multiplicity_three`

The exponent of prime 3 in the natural factorization of 360 equals 2.

### `factorization.multiplicity_two`

The exponent of prime 2 in the natural factorization of 360 equals 3.

### `factorization.over_complexes`

The normalized irreducible factors of the admitted nonzero coefficient extension to C[X] of p=X³−2X+1 equal the set {X−1, X−(−1+sqrt(5))/2, X−(−1−sqrt(5))/2}; sqrt(5) is the positive real root embedded in C.

### `factorization.prime_factors`

The set of prime divisors of natural 360 equals the natural subset {2,3,5}.

### `finite_sets.card`

The cardinality of the integer subset A={1,2,3} equals finite cardinal 3.

### `finite_sets.card.three`

The object Fin(3) admitted to the full category of finite sets on a finiteness proof has carrier cardinality 3; the admission retains Fin(3).

### `finite_sets.card_power_set`

The cardinality of the power set of the integer subset A={1,2,3} equals finite cardinal 8.

### `finite_sets.card_product`

The cardinality of the Cartesian product of integer subsets A={1,2,3}, B={3,4,5} equals finite cardinal 9.

### `finite_sets.difference`

In P(Z), A minus B for A={1,2,3}, B={3,4,5} equals {1,2}.

### `finite_sets.intersection`

In P(Z), the intersection of A={1,2,3} and B={3,4,5} equals {3}.

### `finite_sets.intersection_subset`

In P(Z), A intersection B is a subset of A, with A={1,2,3}, B={3,4,5}.

### `finite_sets.limit.pullback.card`

The pullback in finite sets of f':Fin(3) → Fin(2), (0,1,2) ↦ (0,1,1), and g':Fin(2) → Fin(2), (0,1) ↦ (1,0), has carrier cardinality 3. Both projections and the commuting square belong to the result, with these admitted finite objects.

### `finite_sets.member`

Integer 2 belongs to the subset A={1,2,3} of Z.

### `finite_sets.not_member`

Integer 4 does not belong to that subset A.

### `finite_sets.subset_union`

In P(Z), A={1,2,3} is a subset of A union B, with B={3,4,5}.

### `finite_sets.symmetric_difference`

In P(Z), the symmetric difference of those A and B equals {1,2,4,5}.

### `finite_sets.union`

In P(Z), the union of A={1,2,3} and B={3,4,5} equals {1,2,3,4,5}.

### `fractions.cancel`

In Q, the product of the quotient 7/3 and 3 equals 7.

### `fractions.halves`

In Q, the sum of two quotients 1/2 equals 1, with each denominator admitted nonzero.

### `fractions.lowest_terms`

In Q, the quotient 6/4 equals the quotient 3/2, with their nonzero denominators retained.

### `fractions.member`

The quotient of rational 7 by rational 3, with denominator admitted nonzero, belongs to Q.

### `fractions.modulus`

The complex modulus of z=2+2i equals positive real 2sqrt(2).

### `fractions.sqrt_member`

The positive square root of real 2 belongs to R.

### `functions.at_three`

Application of that map h to real 3 equals real 10.

### `functions.at_zero`

Application of h:R → R, t ↦ t²+1, to real 0 equals real 1.

### `functions.even`

For every real t, application h(−t) equals application h(t), with h:R → R, t ↦ t²+1.

### `functions.extensional`

The map h:R → R, t ↦ t²+1, equals the map hp:R → R, t ↦ t^2+1, extensionally.

### `integration.at_zero`

Evaluation of F=X³+X²/2+X at rational 0 equals rational 0.

### `integration.derivative`

The polynomial derivative of F=X³+X²/2+X equals f=3X²+X+1 in Q[X].

### `integration.differential`

The universal Q-relative derivation of F=X³+X²/2+X equals (3X²+X+1)dX in Ω¹(Q[X]/Q).

### `integration.normalized`

The subset of primitives h in Q[X] with h(0)=0 equals the singleton {X³+X²/2+X}.

### `integration.normalized_count`

The subset of that full inverse image consisting of h with h(0)=0 has cardinality 1.

### `integration.primitives`

The full inverse image of (3X²+X+1)dX under the universal Q-relative derivation equals the coset X³+X²/2+X+Q in Q[X]; Q is the constants subspace, not a chosen integration constant.

### `inverses.det`

The determinant in Q of the underlying matrix of that units inverse equals rational −1/2.

### `inverses.left`

The underlying units inverse of M applied to M(v) equals v=(1,2) in Q².

### `inverses.right`

The underlying matrix M applied to its units inverse applied to b=(5,11) equals b in Q².

### `inverses.solve`

The underlying Q-linear map of that units inverse applied to b=(5,11) equals v=(1,2) in Q².

### `inverses.value`

The inverse in the units group of Mat_2(Q) of the admitted matrix M=[[1,2],[3,4]], projected to Mat_2(Q), equals [[−2,1],[3/2,−1/2]]. The units admission is part of the operand.

### `lattices.card.a0`

The carrier cardinality of the selected integral root lattice A_0, with its negative Cartan bilinear form prescribed by `Integral.rootAGram`, equals 1; the structural route forgets the form to its Z-module and then to its set.

### `lattices.card.a2`

The carrier cardinality of the selected integral root lattice A_2, with its negative Cartan bilinear form prescribed by `Integral.rootAGram`, equals aleph_0; the structural route forgets the form to its Z-module and then to its set.

### `lattices.discriminant.a1`

The cardinality of the cokernel of the pairing-induced map from A_1 to its dual, retaining that defining map and cokernel projection, equals finite cardinal 2; the negative Cartan form prescribed by `Integral.rootAGram` is part of the input.

### `lattices.discriminant.a2`

The cardinality of the cokernel of the pairing-induced map from A_2 to its dual, retaining that defining map and cokernel projection, equals finite cardinal 3; the negative Cartan form prescribed by `Integral.rootAGram` is part of the input.

### `lattices.discriminant.a3`

The cardinality of the cokernel of the pairing-induced map from A_3 to its dual, retaining that defining map and cokernel projection, equals finite cardinal 4; the negative Cartan form prescribed by `Integral.rootAGram` is part of the input.

### `lattices.rank.a1`

The Z-module rank of the selected negative-definite integral root lattice A_1, obtained through its actual module structure, equals 1.

### `lattices.rank.a2`

The Z-module rank of the selected negative-definite integral root lattice A_2, obtained through its actual module structure, equals 2.

### `lattices.rank.a3`

The Z-module rank of the selected negative-definite integral root lattice A_3, obtained through its actual module structure, equals 3.

### `matrices.application`

Application of the Q-linear map represented by that M to v=(1,2) equals b=(5,11) in Q².

### `matrices.charpoly`

The characteristic polynomial over Q of M=[[1,2],[3,4]] equals X²−5X−2 in Q[X].

### `matrices.det`

The determinant over Q of M=[[1,2],[3,4]] equals rational −2.

### `matrices.juxtaposition`

The prescribed matrix action of that same M on v, written by juxtaposition, equals b=(5,11) in Q².

### `matrices.kernel`

The kernel subspace of the Q-linear endomorphism of Q² represented by M=[[1,2],[3,4]] equals the zero subspace, with its inclusion in Q².

### `matrices.product`

The prescribed matrix action of M=[[1,2],[3,4]] in Mat_2(Q) on v=(1,2) in Q² equals b=(5,11) in Q².

### `matrices.rank`

The Q-linear rank of M=[[1,2],[3,4]] equals 2.

### `matrices.trace`

The trace over Q of M=[[1,2],[3,4]] equals rational 5.

### `numbers.complex.abs`

The complex modulus of z=2+2i equals the real product 2sqrt(2), with positive square root.

### `numbers.complex.bar`

The complex conjugate of z=2+2i equals 2−2i in C.

### `numbers.complex.im`

The imaginary part of complex z=2+2i equals real 2.

### `numbers.complex.norm`

In C, the product z*conj(z) for z=2+2i equals complex 8; this is an equality of products, not a norm method request.

### `numbers.complex.re`

The real part of complex z=2+2i equals real 2.

### `numbers.containments`

The conjunction of the three subset statements Z ⊆ Q, Q ⊆ R, R ⊆ C under the prescribed canonical injective inclusions; neither a disjunction nor one composite inclusion.

### `numbers.containments.transitive`

The canonical composite inclusion N → Z → Q → R → C identifies N with a subset of C.

### `numbers.gcd`

The nonnegative greatest common divisor of integer 84 and integer 30 equals 6.

### `numbers.integers.sum`

In the integer ring Z, 2+3 equals 5.

### `numbers.membership.negative`

The negative integer numeral −3 belongs to Z.

### `numbers.membership.zmod`

The integer numeral 3 interpreted by the quotient map defines an element of Z/5Z.

### `numbers.rationals.sum`

In Q, the sum of 2 and 3 equals 5.

### `numbers.zmod5.difference`

In Z/5Z, the class of 2 minus the class of 3 equals the class of 4.

### `numbers.zmod5.negation`

In Z/5Z, the additive negative of the class of 2 equals the class of 3.

### `numbers.zmod5.product`

In Z/5Z, the product of the classes of 2 and 3 equals the class of 1.

### `numbers.zmod5.sum`

In the quotient ring Z/5Z, the sum of the residue classes of 2 and 3 equals the class of 0.

### `numbers.zmod7.distributive`

In Z/7Z, 3*(4+5) equals 3*4+3*5. This question is distributivity on these operands, not equality of either side to 6.

### `numbers.zmod7.value`

In Z/7Z, 3*(4+5) equals the class of 6.

### `polynomials.at_minus_sqrt2`

Evaluation of that q after Q → R at negative real sqrt(2) equals real 0.

### `polynomials.at_sqrt2`

Evaluation of q=X²−2 in Q[X] after coefficient extension along Q → R at positive real sqrt(2) equals real 0.

### `polynomials.degree`

The degree of p=X³−2X+1 in Z[X] equals 3.

### `polynomials.degree_over_rationals`

After extension along the prescribed coefficient embedding Z → Q, the degree of p=X³−2X+1 in Q[X] equals 3.

### `polynomials.factors`

The normalized irreducible factors over Z of p=X³−2X+1 admitted as nonzero equal the set {X−1,X²+X−1} in Z[X].

### `polynomials.irrational_roots`

The finite set of roots in C of q=X²−2 after coefficient extension Q → C and nonzero admission is a subset of C minus the canonical image of Q.

### `polynomials.member`

The polynomial p=X³−2X+1 belongs to Z[X].

### `polynomials.no_rational_roots`

The finite set of roots in Q of q=X²−2 admitted as nonzero in Q[X] equals the empty rational subset.

### `polynomials.root`

Evaluation of p=X³−2X+1 at integer 1 equals integer 0.

### `polynomials.variable`

The indeterminate X belongs to Z[X].

### `schemes.affine_line`

Spec Q[X] equipped with Spec of the constants homomorphism is a scheme over Spec Q.

### `schemes.affine_space`

Spec C[X0,…,X9] equipped with Spec of the constants homomorphism is a scheme over Spec C.

### `series.coefficient_four`

The coefficient of T^4 of the T-adically summable series sum over n in N of n²*T^n in Z[[T]] equals integer 16. The summation domain is N and coefficients are integers.

### `series.coefficient_three`

The coefficient of T^3 of the T-adically summable series sum over n in N of n²*T^n in Z[[T]] equals integer 9. The summation domain is N and coefficients are integers.

### `series.coefficient_two`

The coefficient of T^2 of the T-adically summable series sum over n in N of n²*T^n in Z[[T]] equals integer 4. The summation domain is N and coefficients are integers.

### `series.coefficient_zero`

The coefficient of T^0 of the T-adically summable series sum over n in N of n²*T^n in Z[[T]] equals integer 0. The summation domain is N and coefficients are integers.

### `sets.apply.rev`

Application of reversal of Fin(3) to its element 0 equals its element 2.

### `sets.apply.rev_rev`

Application of reversal of Fin(4) to the reversal of its element 1 equals its element 1.

### `sets.card.fin2_sqcup_fin3`

The cardinality of the disjoint coproduct Fin(2) ⊔ Fin(3) equals finite cardinal 5; injections distinguish summands.

### `sets.card.fin2_times_z3`

The cardinality of the Cartesian product Fin(2) × Z/3Z equals finite cardinal 6.

### `sets.card.integers`

The cardinality of the carrier set Z equals aleph_0.

### `sets.card.naturals`

The cardinality of the carrier set N equals aleph_0.

### `sets.card.square`

For the local set A=Fin(2) × Z/3Z, the cardinality of A × A equals finite cardinal 36.

### `sets.card.z4_cubed`

The cardinality of the function set Fin(3) → Z/4Z equals finite cardinal 64.

### `sets.card.z5_empty_power`

The cardinality of the function set Fin(0) → Z/5Z equals finite cardinal 1.

### `sets.card.z7`

The cardinality of the function set Fin(1) → Z/7Z equals finite cardinal 7.

### `sets.eq.rev_rev`

As functions Fin(3) → Fin(3), the composite of reversal i ↦ 2−i with itself equals the identity map of Fin(3).

### `sets.finite.fin2_sqcup_fin3`

The disjoint coproduct Fin(2) ⊔ Fin(3) is finite.

### `sets.finite.fin2_times_z3`

The Cartesian product Fin(2) × Z/3Z is finite. Its underlying set remains the stated product.

### `sets.finite.integers`

The finiteness proposition of the carrier set Z has Boolean value false; mathematically, Z is infinite.

### `sets.implemented.card_fin`

A registered computational realization of the cardinality request on the set Fin(3) is implemented. This is an execution availability assertion about that fixed request, not the proposition that cardinality equals 3.

### `sets.limit.pullback.card`

The pullback in sets of f:Fin(3) → Fin(2), (0,1,2) ↦ (0,1,1), and g:Fin(2) → Fin(2), (0,1) ↦ (1,0), has cardinality 3. The result retains its two projections and commuting square.

### `several_variables.dimension`

The Krull dimension of C[X0,…,X9] equals 10; it is not the dimension of this ring as a C-vector space.

### `several_variables.last_variable`

The indexed indeterminate X9 belongs to C[X0,…,X9], so the upper endpoint of the ellipsis is included.

### `several_variables.plane`

The Krull dimension of Q[X,Y] equals 2.

### `several_variables.total_degree`

The total polynomial degree of XY²+1 in Q[X,Y] equals 3.

### `several_variables.variable`

The indexed indeterminate X3 belongs to C[X0,…,X9].

### `subspaces.dim`

The Q-linear span W of (1,0,1) and (0,1,1) in Q³ has dimension 2.

### `subspaces.kernel`

The subspace W=span_Q{(1,0,1),(0,1,1)} equals the kernel subspace of the Q-linear endomorphism N of Q³ given by the matrix [[1,1,−1],[0,0,0],[0,0,0]], retaining the common ambient Q³ and inclusion.

### `subspaces.member`

The vector (1,1,2) in Q³ belongs to W=span_Q{(1,0,1),(0,1,1)}.

### `subspaces.not_member`

The vector (1,1,0) in Q³ does not belong to that W.
