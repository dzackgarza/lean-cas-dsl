# Mathematical questions of the permanent acceptance assertions

These specifications are independent acceptance source. They were written from the
unchanged `.cas` assertions, their mathematical sources and published formal
mathematics, before inspecting any candidate question or result. Each row fixes a
proposition, its types, parameters and bindings, and a mathematical justification.
The rows are inputs to a later independent typed comparison; this document does
not activate authoritative records or certify a candidate interpretation.

## Conventions and formal sources

The assertion sources are the 17 `.cas` files in this directory at repository
revision `76d37bbfab783eecd3383f965aad1e34d9027fc2`. Their admitted identities are
preserved. `lean-categories/main` was verified at
`a2123729df092e58b6fb0cd39c78db5e1714faf2` on 2026-10-20. Formal references below
are to that published revision, not to another agent's uncommitted work.

`Eq_T(a,b)` means the equality proposition with both operands in the stated type
`T`. `Member_T(a,S)` means membership in a subset `S : Set T`; its negation is a
different proposition. `Subset_T(S,T')` means `∀ z:T, z∈S → z∈T'`. Each listed
proposition is asserted true. The expected operands remain part of the question;
their truth values are never substitutes for the relation or its operands.

`card(X)` is the cardinality of the specified underlying set, an element of
`Cardinal`; a displayed natural number in a cardinal equality is its canonical
finite cardinal. `Fin n` is the set `{0,…,n-1}`. `ℤ/n` is the specified quotient
ring `ZMod n`. `ι_A,B` denotes the canonical inclusion of the named number system
`A` into `B`. Subsets of different number systems are compared only after the
specified inclusions. `ℚ^n` is the selected rational vector module with coordinates
indexed by `Fin n`, not just an unstructured carrier.

All terms in a row are closed under its section's binding context, except the
two explicitly quantified function identities. Earlier sections do not leak their
bindings into later ones. Algebraic admissions retain their propositions: a
nonzero polynomial carries `p≠0`, an invertible matrix carries invertibility,
a smooth function carries `ContDiff ℝ ∞ f`, a continuous integrand carries
continuity, and a series family carries summability in the selected topology.
Changing a proof of one of these propositions is distinct from changing its
proposition or the selected mathematical datum carried through it.

The following published formal modules fix the meanings used here. Paths below
are relative to `LeanCategories/Catalogue/Semantics/` in `lean-categories`.

| Source | Meaning retained |
| --- | --- |
| `Foundation/Cardinality.lean`, `Foundation/Finiteness.lean` | Cardinality in `Disc(Cardinal)` and finiteness as a proposition, separately from computed answers |
| `Algebra/NumberSystems.lean` | Named number systems and canonical injections; ring parameters are data |
| `Algebra/Semirings.lean` | Prime factors of admitted positive naturals, as a finite subset of `Nat.Primes`; multiplicity takes a selected prime and returns a natural |
| `Algebra/Polynomials.lean` | `degree : R[x] → WithBot ℕ`; evaluation along the actual coefficient homomorphism; normalized irreducible `factors` and `roots` are finite subsets, not multisets |
| `Algebra/MvPolynomials.lean` | `n` variables indexed by `Fin n`; `totalDegree : … → ℕ`; `dimension : … → WithBot ℕ∞` |
| `Algebra/LinearAlgebra.lean` | Matrices, selected vector modules, `matrixLinearMap`, kernel/span defining maps, natural matrix rank and subspace dimension |
| `Modules/Rank.lean` | Module rank is cardinal-valued, inherited through actual structure |
| `Algebra/Differentials.lean` | Universal relative derivation and its selected coordinate identification with `R[x] dx`; primitives are its fibers |
| `Algebra/Calculus.lean`, `Algebra/RealLimits.lean` | Interval integral on admitted continuous maps, smooth Taylor operation, actual limit filter and convergence proposition |
| `Algebra/Series.lean` | Sum of admitted summable families in the selected Hausdorff topological monoid, including the `(t)`-adic topology of power series |
| `Algebra/Algebras.lean`, `Algebra/Schemes.lean` | Algebras with their constants map; schemes over a specified base with their structure map |

The source descriptions in each existing assertion cite [SPEC.md](../../SPEC.md)
or named published/formal results. Below, elementary identities are justified by
explicit calculation, construction or proof, without a candidate oracle.

## `algebras_schemes.cas`

Let `R = ℂ[x₀,…,x₉] = MvPolynomial (Fin 10) ℂ`, with the ten distinct generators
in their given order. Let `c_K : K → K[variables]` be the constants homomorphism.
An algebra judgment retains the pair `(ring,c_K)` in `K ↓ CommRing`; a scheme-over
judgment retains the morphism induced contravariantly by `c_K` in `Sch/Spec K`.
Sources: SPEC, “Ellipses” and “Differentials”; published `Algebras` and `Schemes`
modules above, and the polynomial algebra universal property.

| Identity | Mathematical question and justification |
| --- | --- |
| `algebras.polynomials_several` | `(R,c_ℂ)` is a `ℂ`-algebra. Constants give the required unital homomorphism `ℂ→R`. |
| `algebras.polynomials` | `(ℚ[x],c_ℚ)` is a `ℚ`-algebra, with its constants homomorphism. |
| `schemes.affine_line` | `Spec ℚ[x]`, with `Spec(c_ℚ):Spec ℚ[x]→Spec ℚ`, is an object of schemes over `Spec ℚ`. The variance and selected map are essential. |
| `schemes.affine_space` | `Spec R`, with `Spec(c_ℂ):Spec R→Spec ℂ`, is an object of schemes over `Spec ℂ`. |

## `calculus.cas`

Limits and definite integrals here are over the reals. A limit equality states
existence with the given value, not merely a comparison with an arbitrarily
totalized function. The integral is the oriented real interval integral, with the
displayed bounds in that order and a bound variable ranging over `ℝ`.
Let `f(t)=exp(t)` and `g(t)=sin(t)`, both smooth maps `ℝ→ℝ`. `Tf` and `Tg` are their
Taylor series at the real point `0`; the coefficient at degree `n` is the nth
derivative at `0` divided by `n!`. Sources: SPEC, “Elementary calculus”; published
`Calculus` and `RealLimits`; the elementary real limit and integral theorems.

| Identity | Mathematical question and justification |
| --- | --- |
| `calculus.limit_sinc` | `Tendsto (t↦sin(t)/t) (𝓝[≠] (0:ℝ)) (𝓝 1)`. This is the punctured sine quotient limit; its value is `1`. It does not assert a value for the quotient at `0`. |
| `calculus.limit_infinity` | `Tendsto (t↦1/t : ℝ→ℝ) atTop (𝓝 0)`. For positive `t`, the reciprocal tends to zero. The direction is positive infinity. |
| `calculus.integral_square` | `Eq_ℝ(∫ t in (0:ℝ)..1, t², 1/3)`, with admitted continuous integrand. The antiderivative `t³/3` has endpoint difference `1/3`. |
| `calculus.integral_sine` | `Eq_ℝ(∫ t in (0:ℝ)..π, sin t, 2)`, with admitted continuous integrand. Endpoint difference of `-cos t` is `1-(-1)=2`. |
| `calculus.taylor_exp` | `Tf` is an element of `PowerSeries ℝ`. Smoothness of `exp` supplies the admission; this asks membership, not equality to a convergent analytic function. |
| `calculus.taylor_sin` | `Tg` is an element of `PowerSeries ℝ`. Smoothness of `sin` supplies the admission; its expansion point remains `0`. |

## `composed.cas`

Let `r = x³-2x+1 : ℚ[x]`. Let `r_ℂ` be its image under the canonical coefficient
homomorphism `ι_ℚ,ℂ`. Let `roots={a:ℂ | eval(r_ℂ,a)=0}`. The finite roots operation
uses each distinct root once; here all three roots are simple. Let `C` be the
companion matrix of the admitted monic degree-three polynomial `r`, as a rational
`3×3` matrix and its selected endomorphism of `ℚ³`. Let `f(t)=t²`, `g(t)=t³` be
maps `ℝ→ℝ`. Sources: SPEC, “A composed computation”; factorization
`r=(x-1)(x²+x-1)`, the quadratic formula, Vieta's identities, and the companion
matrix characteristic-polynomial theorem.

| Identity | Mathematical question and justification |
| --- | --- |
| `composed.root_count` | `Eq_Cardinal(card(roots),3)`. Its distinct elements are `1,(-1+√5)/2,(-1-√5)/2` in `ℂ`. |
| `composed.root_one` | `Member_ℂ(1,roots)`, because `1³-2·1+1=0`. |
| `composed.root_sum` | `Eq_ℂ(∑ a∈roots(r_ℂ), a, 0)`. The bound variable ranges over the finite distinct complex root set of the admitted nonzero `r_ℂ`; Vieta gives zero. |
| `composed.root_product` | `Eq_ℂ(∏ a∈roots(r_ℂ), a, -1)`. The binder is product, on the same index object; Vieta gives minus the constant coefficient. |
| `composed.charpoly` | `Eq_ℚ[x](charpoly(C),r)`, retaining the companion construction of the monic degree-three `r`. |
| `composed.det` | `Eq_ℚ(det(C),-1)`, from `det(C)=(-1)³r(0)`. |
| `composed.trace` | `Eq_ℚ(trace(C),0)`, minus the coefficient of `x²` in `r`. |
| `composed.composition` | `∀ t:ℝ, Eq_ℝ((f∘g)(t),t⁶)`. The composite applies `g` first: `(t³)²=t⁶`. The variable is universally quantified, not a fresh constant to choose. |

## `differentials.cas`

Let `P=ℚ[x]`, `f=3x²+x+1:P`, `F=x³+(1/2)x²+x:P`. Let
`d=d_{P/ℚ}:P→Ω¹_{P/ℚ}` be the universal relative derivation, with the canonical
coordinate identification `Ω¹_{P/ℚ}≅P dx`. `∫ f dx` is the subset
`{h:P | d(h)=f dx}`. Let `Fs={h:P | d(h)=f dx ∧ eval(h,0)=0}`, with its inclusion
into `P`. All constants in polynomials are mapped from `ℚ` by the constants map.
Sources: SPEC, “Differentials” and “Indefinite integration”; published
`Differentials`; the Leibniz rule and `ker(d)=ℚ` in characteristic zero.

| Identity | Mathematical question and justification |
| --- | --- |
| `differentials.member` | `f` inhabits `P`; the chosen coefficients and variable construct this polynomial. |
| `differentials.degree` | `Eq_(WithBot ℕ)(degree(f),↑2)`. The quadratic coefficient is `3≠0`. |
| `differentials.at_two` | `Eq_ℚ(eval(f,2),15)` with the identity coefficient map; `3·4+2+1=15`. |
| `differentials.differential` | `Eq_(Ω¹_{P/ℚ})(d(f),(6x+1)dx)`. Leibniz gives `d(x²)=2x dx`, and the relative derivation kills rational constants. |
| `differentials.derivative` | `Eq_P(derivative(f),6x+1)`. This is the polynomial coordinate derivative, not the differential-form-valued operation. |
| `integration.primitives` | `Eq_(Set P)({h ∣ d(h)=f dx},{F+c ∣ c:ℚ})`. `d(F)=f dx` and any two primitives differ by an element of `ker(d)=ℚ`. |
| `integration.normalized_count` | `Eq_Cardinal(card(Fs),1)`. In `F+c`, evaluation at zero is `c`, so only `c=0` remains. |
| `integration.normalized` | `Eq_(Set P)(Fs,{F})` by the same constant calculation; this retains the normalization predicate, not only its cardinality. |
| `integration.differential` | `Eq_(Ω¹_{P/ℚ})(d(F),f dx)`, since `d(x³)=3x²dx` and `d((1/2)x²)=x dx`. |
| `integration.derivative` | `Eq_P(derivative(F),f)`. Equality is in polynomials over `ℚ`. |
| `integration.at_zero` | `Eq_ℚ(eval(F,0),0)`. Each monomial of `F` has positive degree. |

## `ellipses.cas`

Let `X={0+k | k:ℕ}:Set ℕ`, `Y={2k | k:ℕ}:Set ℕ`, `f(n)=n²:ℕ→ℕ`,
`Z={n:ℕ | f(n)∈Y}`, and `primes={n:ℕ | Nat.Prime n}`. The ellipses specify
arithmetic progressions, not arbitrary extrapolation. The notation `2ℕ` denotes
the same image subset as `Y`. Sources: SPEC, “Ellipses”; parity, natural-number
arithmetic, and the definition of a prime number.

| Identity | Mathematical question and justification |
| --- | --- |
| `ellipses.naturals` | `Eq_(Set ℕ)(X,Set.univ)`. Every natural is `0+k`. |
| `ellipses.evens` | `Eq_(Set ℕ)(Y,{2n ∣ n:ℕ})`. Both progressions have initial term zero and step two. |
| `ellipses.multiples` | `Eq_(Set ℕ)(Y,2ℕ)`, the subset of multiples of two. |
| `ellipses.even_square` | `Member_ℕ(4,Z)`, since `4²=2·8`. |
| `ellipses.odd_square` | `¬Member_ℕ(3,Z)`, since `3²=9` is odd. |
| `ellipses.squares_even` | `Eq_(Set ℕ)(Z,Y)`. If `2∣n²`, primality of `2` gives `2∣n`; the converse follows by squaring `n=2k`. |
| `ellipses.prime` | `Member_ℕ(7,primes)`, because no integer `2≤d≤√7` divides `7`. |
| `ellipses.not_prime` | `¬Member_ℕ(9,primes)`, since `9=3·3` with both factors nonunits. |

## `factorization.cas`

Prime factors are finite subsets of the prime subtype `Nat.Primes`; multiplicity
is the natural exponent of the indicated admitted prime. The natural input `360`
is admitted with the proposition `0<360`; the prime arguments `2`, `3`, `7` retain
their primality propositions. Let `p=x³-2x+1:ℤ[x]` and `p_ℂ` be its image
along `ι_ℤ,ℂ`. Polynomial factors are normalized irreducible factors, as a finite
subset of the selected polynomial ring; admission retains `p_ℂ≠0`.
Sources: SPEC, “Exact number systems” and “Polynomials”; the displayed exact
factorization and elementary square inequalities for the approximation.

| Identity | Mathematical question and justification |
| --- | --- |
| `factorization.prime_factors` | `Eq_(Finset Nat.Primes)(primeFactors(360),{2,3,5})`, with these numerals admitted as primes, from `360=2³·3²·5`. |
| `factorization.multiplicity_two` | `Eq_ℕ(multiplicity(360,2),3)`, since `8∣360` but `16∤360`. |
| `factorization.multiplicity_three` | `Eq_ℕ(multiplicity(360,3),2)`, since `9∣360` but `27∤360`. |
| `factorization.multiplicity_seven` | `Eq_ℕ(multiplicity(360,7),0)`, since `7∤360`. |
| `factorization.over_complexes` | `Eq_(Finset ℂ[x])(factors(p_ℂ),{x-1,x-(-1+√5)/2,x-(-1-√5)/2})`. Square roots are the positive real square root included into `ℂ`; expansion gives `p_ℂ` and all three monic linear factors are irreducible. |
| `factorization.approximation` | `abs(√2-14142135623/10¹⁰)<1/10¹⁰` in `ℝ`, with the nonnegative square root. Exact squaring gives `(14142135623/10¹⁰)²<2<(14142135624/10¹⁰)²`, proving the strict bound. |

## `finite_sets.cas`

Let `A={1,2,3}:Set ℤ`, `B={3,4,5}:Set ℤ`. The two power-set notations
`𝒫(ℤ)` and `2^ℤ` denote subsets of the same ambient integer set. Let
`S={n:ℤ | n²≤20}`, `E={2n | n:ℕ}:Set ℕ`, and `m2(n)=2n:ℕ→ℕ`.
All unions, intersections, differences and symmetric differences below use this
specified ambient set and its Boolean-algebra operations. Sources: SPEC,
“Finite sets” and “Set comprehensions”; elementary set membership proofs;
Mathlib `Fintype.card_set`, product cardinality, and injectivity of `n↦2n`.

| Identity | Mathematical question and justification |
| --- | --- |
| `finite_sets.union` | `Eq_(Set ℤ)(A∪B,{1,2,3,4,5})` by disjunction of their membership predicates. |
| `finite_sets.intersection` | `Eq_(Set ℤ)(A∩B,{3})` by conjunction of membership. |
| `finite_sets.difference` | `Eq_(Set ℤ)(A\B,{1,2})`; remove precisely the common element `3`. |
| `finite_sets.symmetric_difference` | `Eq_(Set ℤ)(A△B,{1,2,4,5})`; membership is in exactly one of `A,B`. |
| `finite_sets.card` | `Eq_Cardinal(card(A),3)`, counting three distinct integers. |
| `finite_sets.card_product` | `Eq_Cardinal(card(A×B),9)`; all nine ordered pairs, not union elements. |
| `finite_sets.card_power_set` | `Eq_Cardinal(card(Set A),8)`; each of the three elements independently belongs or does not belong. The power set is of the three-element subset, not of all integers. |
| `finite_sets.member` | `Member_ℤ(2,A)`, one of its listed elements. |
| `finite_sets.not_member` | `¬Member_ℤ(4,A)`, distinct from all three listed elements. |
| `finite_sets.subset_union` | `Subset_ℤ(A,A∪B)`; membership in `A` supplies the left disjunct. |
| `finite_sets.intersection_subset` | `Subset_ℤ(A∩B,A)`; projection from a conjunction. |
| `comprehension.typed` | `S` inhabits `Set ℤ`, with defining predicate `n²≤20` in the ordered integers. |
| `comprehension.elements` | `Eq_(Set ℤ)(S,{-4,-3,-2,-1,0,1,2,3,4})`. `16≤20<25` gives exactly `-4≤n≤4`. |
| `comprehension.card` | `Eq_Cardinal(card(S),9)` by the preceding nine-element description. |
| `comprehension.image_typed` | `E` inhabits `Set ℕ`, as the image of the specified natural multiplication map. |
| `comprehension.even_member` | `Member_ℕ(8,E)` with witness `4`. |
| `comprehension.odd_not_member` | `¬Member_ℕ(9,E)`; no natural `n` has `2n=9`. |
| `comprehension.even_card` | `Eq_Cardinal(card(E),ℵ₀)`; the map `n↦2n` is injective and surjective onto its image. |
| `comprehension.image_apply` | `Eq_(Set ℕ)(m2 '' Set.univ,E)`; the argument `ℕ` denotes the entire specified source set. |
| `comprehension.image_method` | `Eq_(Set ℕ)(range(m2),E)`; image/range is formed from this actual map, not a map inferred from its endpoints. |

## `fractions.cas`

Rational division retains a nonzero denominator. Real square roots are
nonnegative. Let `z=2+2i:ℂ`; its norm is a real absolute value. Sources: SPEC,
“Exact number systems”; rational field arithmetic and `abs(a+bi)=√(a²+b²)`.

| Identity | Mathematical question and justification |
| --- | --- |
| `fractions.member` | `7/3` inhabits `ℚ`; its denominator `3` is nonzero. |
| `fractions.halves` | `Eq_ℚ(1/2+1/2,1)` by addition over the common nonzero denominator. |
| `fractions.cancel` | `Eq_ℚ((7/3)·3,7)`; cancellation uses `3≠0`. |
| `fractions.lowest_terms` | `Eq_ℚ(6/4,3/2)`; both denominators are nonzero and cross-products are `12`. |
| `fractions.sqrt_member` | `√2` inhabits `ℝ`, retaining the specified nonnegative root. |
| `fractions.modulus` | `Eq_ℝ(abs(z),2√2)`, since its squared norm is `8` and both sides are nonnegative. |

## `functions.cas`

Let `h(t)=t²+1`, `hp(t)=t^2+1`, both functions `ℝ→ℝ`. Superscript and caret
power denote the same natural power, without changing the selected real ring.
Sources: SPEC, “Functions”; function extensionality and real ring identities.

| Identity | Mathematical question and justification |
| --- | --- |
| `functions.extensional` | `Eq_(ℝ→ℝ)(h,hp)`; for every real argument the two defining expressions agree. |
| `functions.at_zero` | `Eq_ℝ(h(0),1)`, since `0²+1=1`. |
| `functions.at_three` | `Eq_ℝ(h(3),10)`, since `3²+1=10`. |
| `functions.even` | `∀ t:ℝ, Eq_ℝ(h(-t),h(t))`; `(-t)²=t²`. The free displayed `t` is universally quantified. |

## `inverses.cas`

Let `M=[[1,2],[3,4]]` admitted to `Units(Mat₂(ℚ))`, retaining the usual matrix
ring multiplication and evidence `det(M)=-2≠0`. Let `v=(1,2):ℚ²`,
`b=(5,11):ℚ²`, and `J=[[-2,1],[3/2,-1/2]]:Mat₂(ℚ)`. Underlying matrices and
vectors retain the selected rational ring/module structures. Sources: SPEC,
“Vectors and matrices”; the adjugate formula and explicit multiplication
`MJ=JM=I₂`, `Mv=b`.

| Identity | Mathematical question and justification |
| --- | --- |
| `inverses.value` | `Eq_(Mat₂(ℚ))(underlying(M⁻¹),J)`; `(det M)⁻¹ adj(M)=J`. |
| `inverses.solve` | `Eq_(ℚ²)(M⁻¹b,v)`; multiplication gives `(-10+11,15/2-11/2)=(1,2)`. |
| `inverses.left` | `Eq_(ℚ²)(M⁻¹(Mv),v)` from `M⁻¹M=I₂`, retaining the order of applications. |
| `inverses.right` | `Eq_(ℚ²)(M(M⁻¹b),b)` from `MM⁻¹=I₂`; this is the other inverse law. |
| `inverses.det` | `Eq_ℚ(det(M⁻¹),-1/2)`; the determinant is reciprocal to `-2`. |

## `lattices.cas`

`A(n)` is the positive-definite integral root lattice of type `A_n`, with its
chosen integral bilinear form and rank `n`, not merely its free abelian carrier.
`to_dual(n):A_n→A_n^♯` is the form-induced map to its integral dual.
Its cokernel is formed in the category `BilWFormCat ℤ` of formed modules with
varying values, retaining its carrier quotient, value quotient, induced form
and defining quotient map; cardinality is then applied to its underlying set.
The carrier is the integral-module quotient by the image of the carrier map.
This context follows the published `rootAToDual` signature and
`BilWFormCat.cokernelObject`; it corrects the original explanatory category
description without changing any assertion, map or expected value. Rank is
cardinal-valued module rank through the formal lattice-to-module functor.
Sources: Conway–Sloane, *Sphere Packings, Lattices and Groups*, ch. 4 §6.1
(`A_n^♯/A_n≅ℤ/(n+1)`); Bourbaki, *Lie Groups*, ch. VI, Plate I (simple-root
basis); Mathlib `Cardinal.mk_int`, `Cardinal.power_nat_eq`, `Pi.uniqueOfIsEmpty`.

| Identity | Mathematical question and justification |
| --- | --- |
| `lattices.discriminant.a1` | `Eq_Cardinal(card(coker(to_dual(1))),2)`; the discriminant group is cyclic of order two. |
| `lattices.discriminant.a2` | `Eq_Cardinal(card(coker(to_dual(2))),3)`; cyclic of order three. |
| `lattices.discriminant.a3` | `Eq_Cardinal(card(coker(to_dual(3))),4)`; cyclic of order four. |
| `lattices.rank.a1` | `Eq_Cardinal(rank_ℤ(A₁),1)`, using the one-element simple-root basis. |
| `lattices.rank.a2` | `Eq_Cardinal(rank_ℤ(A₂),2)`, using its two-element simple-root basis. |
| `lattices.rank.a3` | `Eq_Cardinal(rank_ℤ(A₃),3)`, using its three-element simple-root basis. |
| `lattices.card.a2` | `Eq_Cardinal(card(A₂),ℵ₀)`, since its additive carrier is `ℤ²`, a countably infinite set. Cardinality follows the actual lattice-to-module-to-set route. |
| `lattices.card.a0` | `Eq_Cardinal(card(A₀),1)`; the empty simple-root basis spans the singleton zero module. |

## `linear_algebra.cas`

Let `M=[[1,2],[3,4]]:Mat₂(ℚ)`, `v=(1,2):ℚ²`, `b=(5,11):ℚ²`.
The matrix acts by its selected rational linear map with standard column vectors.
Let `u₁=(1,0,1)`, `u₂=(0,1,1)` in `ℚ³`,
`W=span_ℚ{u₁,u₂}≤ℚ³`, with its inclusion into the ambient vector module.
Let `N=[[1,1,-1],[0,0,0],[0,0,0]]:Mat₃(ℚ)` act as
`(a,b,c)↦(a+b-c,0,0)`. Kernels retain their defining inclusion; their extents
are compared as subspaces of that same source module. Sources: SPEC, “Vectors
and matrices” and “Subspaces and spans”; the published `LinearAlgebra` module;
the explicit computations in the rows below.

| Identity | Mathematical question and justification |
| --- | --- |
| `matrices.product` | `Eq_(ℚ²)(Mv,b)`; the coordinates are `1+4=5`, `3+8=11`. |
| `matrices.juxtaposition` | `Eq_(ℚ²)(M v,b)` for the same selected linear action; juxtaposition does not change the operation. |
| `matrices.application` | `Eq_(ℚ²)(M(v),b)` for application of that matrix's linear map. |
| `matrices.det` | `Eq_ℚ(det(M),-2)`; `1·4-2·3=-2`. |
| `matrices.rank` | `Eq_ℕ(rank(M),2)`; its nonzero determinant makes its column map invertible. This is natural matrix rank. |
| `matrices.kernel` | `Eq_(Set (ℚ²))({w:ℚ² ∣ Mw=0},{(0,0)})`. This is the extent of the rational linear-map kernel, retaining its source and defining inclusion. Invertibility forces the zero kernel. |
| `matrices.trace` | `Eq_ℚ(trace(M),5)`; sum of diagonal entries `1+4`. |
| `matrices.charpoly` | `Eq_ℚ[x](charpoly(M),x²-5x-2)`; expansion of `det(xI₂-M)` gives the polynomial, with variable and coefficient map fixed. |
| `subspaces.dim` | `Eq_ℕ(dim_ℚ W,2)`; the first two coordinates of a linear relation on `u₁,u₂` force both coefficients to vanish. |
| `subspaces.member` | `Member_(ℚ³)((1,1,2),W)` with coefficients `(1,1)` on `u₁,u₂`. |
| `subspaces.not_member` | `¬Member_(ℚ³)((1,1,0),W)`; the first two coordinates force coefficients one each, whose third coordinate is two. |
| `subspaces.kernel` | `Eq_(Set (ℚ³))(extent(W),{w:ℚ³ ∣ Nw=0})`. Both have precisely the vectors `(a,b,a+b)`, retaining the generated subspace and kernel inclusions into `ℚ³`; equality is of their extents, not their dimensions. |

## `numbers.cas`

Every quotient-ring expression retains its stated modulus. Canonical number-system
containments are the indicated injective maps, not literal equality of carriers.
Let `z=2+2i:ℂ`. Sources: SPEC, “Exact number systems”; Mathlib
`Nat.cast_injective`, `Int.cast_injective`, `Rat.cast_injective`,
`Complex.ofReal_injective`; the explicit arithmetic below.

| Identity | Mathematical question and justification |
| --- | --- |
| `numbers.integers.sum` | `Eq_ℤ(2+3,5)` in the integer ring. |
| `numbers.zmod5.sum` | `Eq_(ZMod 5)(2+3,0)`; `5≡0 mod 5`. |
| `numbers.zmod5.product` | `Eq_(ZMod 5)(2·3,1)`; `6≡1 mod 5`. |
| `numbers.zmod5.negation` | `Eq_(ZMod 5)(-2,3)`; their integer difference is `-5`. |
| `numbers.zmod5.difference` | `Eq_(ZMod 5)(2-3,4)`; `-1≡4 mod 5`. |
| `numbers.zmod7.distributive` | `Eq_(ZMod 7)(3·(4+5),3·4+3·5)`; distributivity in this selected ring. Both sides are `6`, but their separate expression structure remains in the question. |
| `numbers.zmod7.value` | `Eq_(ZMod 7)(3·(4+5),6)`; the integer expression is `27≡6 mod 7`. |
| `numbers.rationals.sum` | `Eq_ℚ(2+3,5)` in the rational ring, distinct from the integer assertion. |
| `numbers.containments` | The conjunction of `ℤ⊆ℚ`, `ℚ⊆ℝ`, and `ℝ⊆ℂ` along their canonical injective embeddings. The three conjuncts and their order/grouping from the source must be retained. |
| `numbers.containments.transitive` | `ℕ⊆ℂ` along the composite `ℕ→ℤ→ℚ→ℝ→ℂ`; composition of injective maps gives the specified inclusion. |
| `numbers.membership.zmod` | The integer numeral `3` is admitted as the residue class `3:ZMod 5` through `ℤ→ZMod 5`. This is quotient-ring membership, not integer membership in `{0,…,4}`. |
| `numbers.membership.negative` | The integer `-3` inhabits `ℤ`. |
| `numbers.gcd` | `Eq_ℤ(gcd(84,30),6)` for the published nonnegative integer gcd operation `ℤ×ℤ→ℤ`; Euclid gives `84=2·30+24`, `30=24+6`, `24=4·6`. |
| `numbers.complex.re` | `Eq_ℝ(re(z),2)` by the selected complex coordinate. |
| `numbers.complex.im` | `Eq_ℝ(im(z),2)` by the imaginary coordinate, a different operation from `re`. |
| `numbers.complex.bar` | `Eq_ℂ(conj(z),2-2i)`, retaining complex conjugation. |
| `numbers.complex.norm` | `Eq_ℂ(z·conj(z),8)`; expansion gives the complex number `4+4`. The relation is in `ℂ`, not an equality of real absolute values. |
| `numbers.complex.abs` | `Eq_ℝ(abs(z),2·sqrt(2))`; the squared modulus is eight and its nonnegative root is `2√2`. |

## `polynomials.cas`

Let `p=x³-2x+1:ℤ[x]`, `q=x²-2:ℚ[x]`. A polynomial defined with a displayed
argument remains a polynomial, with evaluation along the actual coefficient map,
not a replacement function with forgotten ring. `q(±√2)` is evaluated in `ℝ`
along `ι_ℚ,ℝ`; complex roots use `ι_ℚ,ℂ`. Degrees are in `WithBot ℕ`.
Sources: SPEC, “Polynomials”; published `Polynomials`; the quadratic formula and
the irrationality of `√2` (the usual coprime-numerator/denominator parity proof).

| Identity | Mathematical question and justification |
| --- | --- |
| `polynomials.variable` | The canonical indeterminate `x` inhabits `ℤ[x]`. |
| `polynomials.member` | The specified `p` inhabits `ℤ[x]`, with its integer coefficients retained. |
| `polynomials.degree` | `Eq_(WithBot ℕ)(degree(p),↑3)`, since its cubic coefficient is one. |
| `polynomials.root` | `Eq_ℤ(eval(p,1),0)` along the identity coefficient map; `1-2+1=0`. |
| `polynomials.factors` | `Eq_(Finset ℤ[x])(factors(p),{x-1,x²+x-1})`, admitting `p≠0`. Expansion gives `p`; the quadratic discriminant five is not a rational square, so the primitive monic quadratic is irreducible over `ℤ`. |
| `polynomials.degree_over_rationals` | `Eq_(WithBot ℕ)(degree(map(ι_ℤ,ℚ,p)),↑3)`; the canonical injection preserves its leading coefficient one. |
| `polynomials.at_sqrt2` | `Eq_ℝ(eval₂(ι_ℚ,ℝ,q,√2),0)`; the real square is two. |
| `polynomials.at_minus_sqrt2` | `Eq_ℝ(eval₂(ι_ℚ,ℝ,q,-√2),0)`; negation does not change that square. |
| `polynomials.no_rational_roots` | `Eq_(Finset ℚ)(roots(q),∅)`, admitting `q≠0`. A rational square root of two would contradict coprimality by parity. |
| `polynomials.irrational_roots` | `Subset_ℂ(roots(map(ι_ℚ,ℂ,q)),Set.univ\range(ι_ℚ,ℂ))`. Its two roots are the included real numbers `±√2`, neither in the image of the rational inclusion. |

## `series.cas`

Let `H(n)=C((n:ℤ)²)·X^n : PowerSeries ℤ` for `n:ℕ`. Let `f` be the sum of
this family in `PowerSeries ℤ` equipped with the `(t)`-adic topology, with its
summability proposition retained. The bound variable ranges over `ℕ`, and the
sum's codomain is power series, not scalar integers. Each coefficient is an
integer. Source: SPEC, “Ellipses”; Bourbaki, *Algebra II*, IV.4.2; published
`Algebra.Series.summable_of_X_pow_dvd`, `hasSum_C_mul_X_pow`,
`tsum_C_mul_X_pow`, and `powerSeriesSum_C_mul_X_pow`. Each degree `d` receives
only the nth term with `n=d`, so `coeff(d,f)=(d:ℤ)²`. The separate assessment in
[b0-independent-assessment.md](b0-independent-assessment.md) explains the
representation comparison permitted by those theorems.

| Identity | Mathematical question and justification |
| --- | --- |
| `series.coefficient_two` | `Eq_ℤ(coeff(2,f),4)`, retaining index `2:ℕ` and the above bound family. |
| `series.coefficient_three` | `Eq_ℤ(coeff(3,f),9)` by `3²=9`. |
| `series.coefficient_zero` | `Eq_ℤ(coeff(0,f),0)` by `0²=0`; zero coefficient does not erase the family. |
| `series.coefficient_four` | `Eq_ℤ(coeff(4,f),16)` by `4²=16`. |

## `sets.cas`

Cardinality follows the specified set-level construction. `is_finite` asks the
formal finiteness predicate; a returned Boolean never supplies refinement evidence.
Let `A=Fin 2 × ZMod 3`. Let
`f:Fin 3→Fin 2` have values `[0,1,1]` and `g:Fin 2→Fin 2` have values `[1,0]`.
Let `f',g'` be those same functions as morphisms of the finite-set category, with
their finite source/target objects retained. `PB(f,g)` has elements
`{(x,y) | f(x)=g(y)}`, both defining projections, and their commuting equation;
`PB(f',g')` is formed in finite sets, not identified by matching endpoints alone.
`rev_n:Fin n→Fin n` is the function `i↦n-1-i` on its specified domain.
Sources: Mathlib `Fintype.card_fun`, `ZMod.card`, `Cardinal.mk_int`,
`Cardinal.mk_nat`, `Fintype.card_prod`, `Fintype.card_fin`, `Fintype.card_sum`,
`Finite.instProd`, `Finite.instSum`, `Int.infinite`, `Fin.rev_rev`, and
`Types.pullbackLimitCone`, as cited in the permanent source.

| Identity | Mathematical question and justification |
| --- | --- |
| `sets.card.z4_cubed` | `Eq_Cardinal(card(Fin 3→ZMod 4),64)`; there are four choices in each of three ordered coordinates. |
| `sets.card.z7` | `Eq_Cardinal(card(Fin 1→ZMod 7),7)`; retain exponent one and modulus seven. |
| `sets.card.z5_empty_power` | `Eq_Cardinal(card(Fin 0→ZMod 5),1)`; the empty-domain function is unique. |
| `sets.card.integers` | `Eq_Cardinal(card(ℤ),ℵ₀)`; the integers are countably infinite. |
| `sets.card.naturals` | `Eq_Cardinal(card(ℕ),ℵ₀)`; a different source set from the preceding assertion. |
| `sets.card.fin2_times_z3` | `Eq_Cardinal(card(Fin 2×ZMod 3),6)` by the product rule `2·3`. |
| `sets.finite.integers` | The decision of `Finite ℤ` equals `false`, with underlying proposition `¬Finite ℤ` independently established by `Int.infinite`. Its negation/Boolean comparison remains in the question. |
| `sets.finite.fin2_times_z3` | The proposition `Finite (Fin 2×ZMod 3)` holds by finiteness of both factors. |
| `sets.implemented.card_fin` | The fixed cardinality request for `Fin 3` must actually have an implementation. This asserts required execution, not just `card(Fin 3)=3`; it is the original capability assertion, not an added mathematical theorem or a self-reported leaf claim. |
| `sets.card.square` | `Eq_Cardinal(card(A×A),36)`; `A` is the previously fixed six-element product, and the square has ordered pairs. |
| `sets.card.fin2_sqcup_fin3` | `Eq_Cardinal(card(Fin 2⊔Fin 3),5)`; retain tagged disjoint union, not ordinary union. |
| `sets.finite.fin2_sqcup_fin3` | `Finite (Fin 2⊔Fin 3)` by finiteness of the coproduct of the two specified finite sets. |
| `sets.eq.rev_rev` | `Eq_(Fin 3→Fin 3)(rev_3∘rev_3,id_(Fin 3))`. The intermediate and endpoint sets are `Fin 3`; reversal is an involution. |
| `sets.limit.pullback.card` | `Eq_Cardinal(card(PB(f,g)),3)` in sets. Its pairs are exactly `(0,1),(1,0),(2,0)`, with their two projections retained. |
| `finite_sets.card.three` | `Eq_Cardinal(card(Fin 3 admitted to FiniteSets),3)`; retain the chosen formal finiteness admission and its carrier. |
| `finite_sets.limit.pullback.card` | `Eq_Cardinal(card(PB(f',g')),3)` for the finite-set cospan. Its finite pullback has the same three listed pairs and the defining finite-set maps. |
| `sets.apply.rev` | `Eq_(Fin 3)(rev_3(0),2)`, with both numerals admitted to `Fin 3`. |
| `sets.apply.rev_rev` | `Eq_(Fin 4)(rev_4(rev_4(1)),1)`; the inner result is `2` and the outer result `1`, all in `Fin 4`. |

## `several_variables.cas`

Let `R=MvPolynomial (Fin 10) ℂ`, whose variables `x₀,…,x₉` are indexed by all
ten consecutive indices; the ellipsis does not omit the intermediate variables.
Let `p=xy²+1:MvPolynomial (Fin 2) ℚ`, with the two selected generators `x,y`.
Total degree is natural-valued. Krull dimension is valued in `WithBot ℕ∞`, with
natural numerals included by the canonical embedding. Sources: SPEC, “Ellipses”;
published `MvPolynomials`; the polynomial-ring dimension theorem over a field.

| Identity | Mathematical question and justification |
| --- | --- |
| `several_variables.dimension` | `Eq_(WithBot ℕ∞)(ringKrullDim(R),↑10)`. A polynomial ring in ten variables over the field `ℂ` has dimension ten; source `is` denotes this equality. |
| `several_variables.variable` | The generator `x₃=X(3:Fin 10)` inhabits `R`, with its index retained. |
| `several_variables.last_variable` | The generator `x₉=X(9:Fin 10)` inhabits `R`; this is the last, distinct generator. |
| `several_variables.total_degree` | `Eq_ℕ(totalDegree(p),3)`; the nonzero monomial `xy²` has exponent sum three, while the constant has degree zero. |
| `several_variables.plane` | `Eq_(WithBot ℕ∞)(ringKrullDim(ℚ[x,y]),↑2)`; this is Krull dimension of the ring, not vector-space dimension. |

## Comparison obligations

Every identity above requires an opaque candidate operation to return its full
typed question before evaluation, including the context selected by the source.
The comparison must establish these propositions and data against the current
published mathematical dependency. A source-level specification does not prove
that a candidate constructs or executes it. In particular, a candidate's use of
a different structural route needs its supplied mathematical comparison, not a
numerically matching answer.

The required-implementation predicate in `sets.implemented.card_fin` is retained
alongside all mathematical propositions; it cannot be replaced by a Lean proof
of cardinality. The permanent assertion inventory and all its expected answers
remain unchanged. Protected activation of initial records, interpretation
migration and final independent acceptance are separate, unperformed operations.
