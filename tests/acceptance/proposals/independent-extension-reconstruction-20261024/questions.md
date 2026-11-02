# Complete reconstructed mathematical questions

This is an **independent reconstruction**, with new local proposal labels. It is not an assertion
inventory recovered from the old container. Source labels `[M01]`--`[M16]` and `[P01]`--`[P06]`
are resolved in [source-notes.md](source-notes.md). They cite formal mathematics or public
requirements, never an implementation's observed answer.

Composition is written in ordinary mathematical order: `g o f` means first `f`, then `g`.
Where a cited Lean theorem uses `f ≫ g`, it denotes that same composite. All universal equalities
below are equalities of the complete indicated functions or morphisms at their stated endpoints.

## RX-01: a new selected finite order inherits the old cardinality

Select `L = CasCatalogue.Foundation.FiniteOrders.ordinary 5`, the linear order on `Fin 5`
with its usual order. Its public object name is `FinOrder(5)`. Apply the existing forgetful
functor `fun.linear_orders.forget`, then the existing set-cardinality operation. Require

`cardinality(L) = 5`.

The selected comparison `ordinaryCarrier 5` is the identity isomorphism of its forgotten set
with the old `Fin 5`. Retain the order as part of `L`; the answer must not replace `L` by a bare
set before the mathematical question is formed. No order-specific cardinality operation is
introduced. [M01, M13]

The separating selected object is `Lrev = reverse 5`, public name `ReverseFinOrder(5)`.
It also has cardinality five, but its order relation is different: on the indicated finite
ordinals, `0 <= 1` in `L` and not in `Lrev`. These elements are the actual `Fin 5` elements,
not an assertion that every ordered object supports arbitrary integer numerals. [M01]

**Surface limit.** Cardinality has a proposal excerpt. A public spelling for observing the
two selected relations must retain the chosen finite ordinals and both selected order objects.

## RX-02: two-subsets of an existing five-element set

Select the preexisting set `F = Fin 5`. Apply
`CasCatalogue.Foundation.TwoSubsets.twoSubsets F`, equivalently the object action of
`fun.core_sets.two_subsets` at the specified object of `Core(Sets)`.
The output is the set of finite unordered subsets of `F` having exactly two distinct elements.
Require

`cardinality(TwoSubsets(F)) = 10`.

Retain `inclusion F : TwoSubsets(F) -> FiniteSubsets(F)`, which sends a subset to that same
subset. For every embedding `e : F -> G` and every two-subset `s`, the declared map has extent
`e '' s`. The registered functor's morphisms are bijections, as specified by its source
`Core(Sets)`; an arbitrary noninjective set map is not a morphism in that source. The identity
and composition equations are the functor's full equations. [M02]

The control `singleton_not_member` excludes `{a}` for every `a : F`. Writing a repeated pair
does not turn this singleton into a two-subset. Cardinality ten counts unordered distinct pairs,
not ordered pairs or multisets. [M02]

**Surface limit.** The inherited `two_subsets()` and cardinality have a proposal excerpt.
Observing the full bijection action requires a publicly specified map-action form with the
complete bijection and both endpoints; a list of sampled images is insufficient.

## RX-03: the cyclic quotient's actual automorphism group

Select the group

`C = CyclicQuotients.cyclicQuotient 5 = Multiplicative(Z / 5Z)`

and the existing generic construction `Aut : Core(Groups) -> Groups`. Its value is
`A = Aut_Groups(C)`, with the ordinary group operations on categorical automorphisms.
Require

`cardinality(A) = 4`.

Let `e = CyclicQuotients.residueComparison 5 : C ~= Cyclic(5)` be the actual selected
group isomorphism to the existing residue-group presentation. The quotient map sends every
integer `k` to `[k]`, and `e([k])` is the residue of `k`; the selected generator is `[1]`.
No set permutation group replaces `Aut_Groups(C)`. [M03]

Let `u2 = unitTwo`, whose underlying residue is `2` and whose inverse residue is `3`;
let `u3 = unitThree`. Set

`a = byUnit 5 u2 : C ~= C`, `b = byUnit 5 u3 : C ~= C`.

The entire actions in the specified residue coordinates are `z |-> 2z` and `z |-> 3z`.
Require `a^(-1) = b`, both inverse composites equal the identity, and `orderOf(a) = 4`.
In particular, the coordinate actions give `a([1]) = [2]`, `a([3]) = [1]`,
and `b([2]) = [1]`. Group inversion and composition are inherited operations, not new
automorphism-specific routines. [M03]

The map action of `Aut` on the complete core arrow `e` is required to be genuine conjugation:

`Aut(e)(v) = e o v o e^(-1)` for every `v : Aut_Groups(C)`.

Its output at `a` is the complete doubling automorphism of the existing residue group; its
output at `b` is the complete tripling automorphism. The forward and backward components of
`e`, the source category `Groups`, and the two group endpoints remain selected inputs. [M03, M04]

Because this particular automorphism group is commutative, some self-conjugations act trivially.
A numerical equality alone therefore cannot verify that the intended functor action was read.
The interpretation must retain the actual conjugation composite and endpoints.

**Surface status.** The additional public `SPEC.md` [P05] now supplies `Aut(C)` with category
context inferred from `C`, and `map e along Aut` for the construction's map action. The
cardinality is included as a surface excerpt. A complete public term for the selected
`residueComparison 5`, including both directions, and for the actual selected unit/doubling
automorphism inputs still needs to be fixed. No unregistered data declaration is smuggled
through a proof slot. See `public-surface-status.md`.

## RX-04: a finite square-bound comprehension and its classifier

Select the exact integer subset

`S = {n : Z | n^2 <= 9} = {-3,-2,-1,0,1,2,3}`.

It is `IntegerSquareBounds.squareBound 3`, with extent `extent 3` and inclusion
`inclusion 3 : extent 3 -> Z`, `n |-> n`. Require its cardinality to be seven. [M05]

Retain the actual finite-classifier proposition
`Classifier.Holds finite (extent 3)`, the selected refinement `finiteExtent 3`, and
`finiteIdentification 3` through `classifierForget(clf.sets.finite)`. The forgotten finite
object must be this original square-bound subtype. Its complete membership predicate and
original inclusion into all integers remain part of the question. [M05]

For finite-subset admission, retain `admittedSubset 3`, obtained by the old
`FiniteSubsets.admit` with `squareBound_finite 3`, and require the full arrow equation

`FiniteSubsets.inclusion Z o admittedSubset 3 = subset 3`.

The negative control is the independently proved absence of the finite-classifier property
for the entire integer set. It does not change the ambient domain of `S`. [M05]

**Surface limit.** The refined named object and its cardinality have a proposal excerpt.
An explicit observation of the classifier witness/refinement and of the complete admission
equation needs a specified public surface. Merely displaying the seven integers does not
exercise those operations.

## RX-05: the actual ring carrier diamond at `PrimeResidues(5, proof)`

Select `P = PrimeResidueFields.primeResidues 5 hp`, where `hp : Nat.Prime 5` is a
checked proof. It is a field, with its actual residue addition and multiplication.
After forgetting the field structure and commutativity, its ring is exactly the existing
`NamedRings.ringIntegersMod 5`. The proof-valued parameter must be supplied as formal input;
a returned Boolean or computation cannot establish it. [M06, P01]

Retain both complete routes from this ring to sets:

| Route | Ordered edges |
| --- | --- |
| Multiplicative `U_m` | `fun.rings.multiplicative_monoid`; `fun.monoids.semigroup`; `classifierForget(clf.magmas.associative)`; `classifierForget(clf.sets.binary_operation)` |
| Additive `U_a` | `fun.rings.additive_group`; `fun.additive_groups.to_groups`; `fun.groups.monoid`; `fun.monoids.semigroup`; `classifierForget(clf.magmas.associative)`; `classifierForget(clf.sets.binary_operation)` |

The chosen comparison is the existing invertible natural cell **`cmp.rings.carrier`**,
whose designated source is the full multiplicative route. Let its component at the selected
ring be `c_P : U_m(P) ~= U_a(P)`. Require

- `cardinality(U_m(P)) = cardinality(U_a(P)) = 5`;
- `c_P(z) = z` and `c_P^(-1)(z) = z` on every actual residue, with their typed endpoints;
- for every actual ring homomorphism `f : R -> S`, both complete functor map actions retain
  the function `x |-> f(x)` and satisfy the naturality equation for this cell;
- in the earlier operation structures, `1 + 1 = 2`, `1 * 1 = 1`, and the two values differ
  in `ZMod 5`. The cell at sets does not identify those operations. [M06, M07]

The selected actual integer coefficient map of RX-06 can be reused as a nonidentity-source
ring map observation: each route sends its value at `7 : Z` to `2 : ZMod 5`, retaining the
entire map, not just that sample. This value is the residue-class computation `7 = 5 + 2`.
[M06, M08]

The independently specified environments with this cell absent and with registration order
reversed are fixed in [observation-controls.md](observation-controls.md). Both route candidates
must survive when the cell is absent. Equal carriers and registration order supply no cell.

**Surface status.** The proof-argument, cardinality, and separate arithmetic have proposal
excerpts. The additional public `SPEC.md` [P05] supplies explicit functor views and
`component`/`inverse_component` at a complete receiver. Remaining terms must bind the actual
field-forgetful/classifier route to its ring receiver and the complete route map actions.
The exact existing cell cannot be replaced by a newly chosen identity or by an endpoint-equality
convention. See `public-surface-status.md`.

## RX-06: the regular residue module reindexed along the actual quotient

Select `R = RingCat.of Z`, `S = RingCat.of (ZMod 5)`, and

`q = RingCat.ofHom (Int.castRingHom (ZMod 5)) : R -> S`.

This is the existing integer coefficient morphism after forgetting commutativity, as stated
by `quotient_is_integer_coefficients 5`. Select the existing regular module `N = S`, then
the actual module-fibration reindexing `q*`. The new object is precisely

`M = restrictedRegularModule R S q = q*(N)`.

Require `dim_S(N) = 1`, `cardinality(M) = 5`, and the complete scalar-action equation

`r • m = q(r) * m` for every `r : Z` and `m : ZMod 5`.

Its fixed observations are `2 • 3 = 1`, `5 • 1 = 0`, and `(-1) • 2 = 3`.
This does not assert that the restricted integer module has dimension one or is a free
integer module. [M08]

Retain the actual cartesian arrow of the module fibration. Its projection is `q`, and its
underlying additive function is the identity on `ZMod 5`. A coincident carrier alone does
not identify the coefficient rings or their module fibres. [M08]

On every actual `S`-linear arrow `f : N -> N`, require the full map equation

`(q*.map f)(m) = f(m)` for every `m : M`.

In particular select the nonidentity arrow `d = (2 : ZMod 5) • LinearMap.id`.
The reindexed arrow `d_R = q*.map d : M -> M` is the whole function `m |-> 2m`,
and `d_R(3) = 1`. Subsequent computation must use that actual returned map. [M08]

**Surface limit.** `RestrictedRegularModule` has the explicit parameter order `R,S,q`.
The public specification must describe selected reindexing, its cartesian map, and its
action on complete module arrows. A scalar sample, an unchanged set, or a mere declaration
that two carriers have five elements cannot replace those inputs and maps.

## RX-07: F9 transport in both directions and successive computations

Select the existing commutative-ring presentations

`A = F_3[x]/(x^2+1)`, `B = F_3[y]/(y^2+y+2)`

named `F9x` and `F9y`, with their selected generators and coefficient maps.
The actual registered comparison is `e = F9translation : A ~= B`. Require

`e(x) = y + 2`, `e^(-1)(y) = x - 2`,

and both full inverse equations. It fixes the chosen copy of every coefficient of `F_3`.
It is not the identity on the selected generators: `e(x) != y`. [M09, M10]

For successive **element** computation, form `u = x+1`, obtain the actual transported value
`v = e(u)`, then compute `w = v^2`, then transport that computed value back. Require

`v = y`, `w = 2y+1`, `e^(-1)(w) = 2x`.

The operations must consume the previous results. Directly producing the final expression
from an independently chosen substitute input does not exercise this sequence. [M09, M10]

For successive **whole-map** computation, select the entire set morphism

`f : F_3 -> A`, `f(c) = x + i_A(c)`.

Obtain `g = e o f : F_3 -> B`, retaining the same complete domain and selected coefficient
map. Obtain the whole pointwise square map `h(c) = g(c)^2`, then obtain `k = e^(-1) o h`.
Require, for every `c : F_3`,

`g(c) = y + 2 + i_B(c)`,

`h(c) = (y + 2 + i_B(c))^2`,

`k(c) = (x + i_A(c))^2`.

In particular `g(1) = y`, `h(1) = 2y+1`, and `k(1) = 2x`; also require
`e^(-1) o g = f` as complete maps. The arrows are set morphisms with the indicated
nontrivial domain, not claimed to be ring homomorphisms. [M09, M10]

**Surface status.** The public specifications [P01, P05] provide selected generators,
forward/backward presentation transport, whole-domain generalized application, function
definitions and composition. The remaining binding questions are exact structured-object
selection for the overloaded names and the complete presentation arrow as a term usable in
those whole-map expressions. The full functions above, their exact domain, and the actual
comparison remain the requirement. See `public-surface-status.md`.

## RX-08: an ordinary projection with restricted form `[3]`

Take the actual rectangular row matrix `M = [[1,0]]` over `Q`, with one row and two columns.
Let `p = rowLinearMap 2 Q M : Q^2 -> Q`. Its target is the actual regular scalar module `Q`.
The selected formed source is `X = RationalProjection.diagonalSource`, with

`B_X((a,b),(c,d)) = 2ac + 3bd`.

Require the complete ordinary-map equation `p(a,b)=a`. Its kernel is exactly
`K = {(a,b) : Q^2 | a=0}`. The selected coordinate equivalence is
`kappa : Q ~=_Q K`, `kappa(t)=(0,t)`, and `dim_Q K=1`. [M11, M12]

Form the actual `ordinaryKernelRestriction(Q,Q,X,Q,p)` and its associated
`ordinaryKernelInclusion`. Call them `X_K` and `j : X_K -> X`. Require

`j(kappa(t)) = (0,t)` for every `t : Q`,

`p o U(j) = 0`,

`B_(X_K)(kappa(s),kappa(t)) = 3st` for every `s,t : Q`.

Thus the restricted Gram matrix in this specified coordinate is `[3]`, and the value at
`s=t=1` is `3`. Reuse the actual returned kernel object, actual defining inclusion, and
restricted form in the observations. [M11]

The complete kernel has the ordinary module universal property: for every module `T` and
linear `h : T -> Q^2` with `p o h=0`, there is a unique `hbar : T -> K` such that
the original kernel inclusion composed with `hbar` is `h`. In the selected scalar coordinate
the mediator is `t |-> (h(t))_1`. This follows from `mem_kernel` and the inverse of
`kernelCoordinates`; it is not a formed-arrow assertion about `p`. [M11]

The independently required negative is universal over target forms:

for **every** bilinear form `B` on the actual target `Q`, there is no fixed-value formed
arrow `X -> (Q,B)` whose underlying linear map is `p`.

The witness obstructing it is `(0,1)`, with source self-pairing `3` and image zero.
This negative must not be weakened to one chosen target form. [M11]

**Surface limit.** Public syntax must retain the actual `1 x 2` row construction, ordinary
module arrow, five ordered restriction parameters, complete returned kernel and inclusion,
and chosen form. The existing registered morphism `pairing(R,W,X_K)` observes that chosen form
on pairs of actual kernel elements; see [M11]. A square endomorphism, a zero restricted form, or the different formed arrow
of RX-LIFT would change the question.

## RX-09: the entire successor family and genuine series admission

Select the coefficient ring `Z`, the full index object `N`, and the existing selected
`(X)`-adic topological object `powerSeriesTAdic Z`. The new declared whole function is

`a : N -> Z[[X]]`, `a(n) = C(n+1) X^n`.

It is `SuccessorSeries.successorTerms Z`. Its complete coefficient equation is
`coeff_d(a(n)) = n+1` if `d=n`, and zero otherwise. Retain its formal
`successorTerms_summable Z` evidence and its actual admitted `SummableFamily` value.
The admitted value's `toFun` must equal this entire original function. [M14, M15]

Apply the old binder `bind.sets.power_series_sum` to this admitted family. Its complete
sum is `PowerSeries.mk (d |-> d+1)`. Require

`coeff_d(sum a) = d+1` for every `d : N`,

including the fixed coefficient observations at degrees `0,1,3,5`, which are respectively
`1,2,4,6`. In particular the degree-three value is four. The coefficient ring, topology,
infinite domain, whole function, and summability proposition remain part of the question.
[M14, M15]

For the separating family `b : N -> Z[[X]]`, `b(n)=1` for every `n`, require both
`not Summable(b)` in that selected topology and

`not exists F : SummableFamily(powerSeriesTAdic Z,N), F.toFun = b`.

Thus attempting to supply this full function to the admitted binder domain is a mathematical
admission rejection. It is not an execution gap or a failed numeric sum. An external Boolean,
a finite prefix, or a proof of a different family's summability supplies no such admission.
[M14]

**Surface limit.** `SPEC.md` provides infinite-sum and coefficient notation and a general
proof-bearing single-data-field construction form. The complete invocation connecting the
new named whole morphism, its summability proof, the selected admitted-family object and the
old binder still needs an explicit public spelling. The expected answer is fixed above;
no truncated substitute or automatic Boolean admission is proposed.

## RX-10: one true question under execution failures and session ownership

Fix **one** mathematical question with the exact bindings of RX-06:

`Q : (q*.map ((2 : ZMod 5) • LinearMap.id))(3) = (1 : ZMod 5)`.

Both endpoints of the reindexed arrow are the selected restricted integer module `M`, its
input is the residue `3`, its equality target is the residue `1`, and `q` is the actual
integer coefficient map. The whole reindexed callable `d_R` must be available for subsequent
use. This is exactly the proposition of `IntegerResidueModules.reindex_double_three`. [M08]

The question and all bindings are fixed before evaluation. Observe it under correct, missing,
unavailable, malformed, well-typed wrong-answer, and internal-interpreter-failure conditions.
The mathematical assertion names no computation provider, process, handle, or wire datum.
The observer requirements and session controls are in
[observation-controls.md](observation-controls.md). [P02, P03, P04, P06]

**Surface limit.** The same reindexing/map syntax obligation as RX-06 applies. The independent
observer's public harness, exact outcomes and session boundary are now specified in [P06].
Internal-fault and deliberate foreign-session conditions use separate engineering fixtures.
They cannot change the mathematical assertion or promote candidate-generated interpretation
data into the expected interpretation.

## RX-LIFT: a separate genuine formed arrow and two successive lifts

This example is separate from RX-08. Select the formed rational planes

`B_X((a,b),(c,d)) = 2(a+b)(c+d)`,

`B_Y((s,t),(u,v)) = 2su + 5tv`,

and the actual formed arrow `f(a,b) = (a+b,0)`. Its full pairing equation is required.
Select the prescribed module-kernel model `i0 : Q -> Q^2`, `i0(t)=(2t,-2t)`.
Its image is the **entire** module kernel of `U(f)`, and it has the full ordinary kernel
universal property. [M16a]

### First stage

Apply the existing selected restriction lift through the forgetful functor
`U : BilinModule_Q(Q) -> Modules(Q)` to `X` and `i0`. Retain all four actual outputs:

`X1 = firstObject`, `i1 = firstInclusion : X1 -> X`,

`alpha1 = alpha : U(X1) -> Q`, `beta1 = beta : Q -> U(X1)`.

The carrier of `X1` is the range submodule of vectors `(a,-a)`. Require the full equations

`alpha1(a,-a) = a/2`, `beta1(t) = (2t,-2t)`,

`beta1 o alpha1 = id_(U(X1))`, `alpha1 o beta1 = id_Q`,

`U(i1) = i0 o alpha1`,

`B_(X1)(beta1(s),beta1(t)) = 0`.

The fixed observation `alpha1(4,-4)=2` distinguishes the selected coordinate comparison
from the identity. [M16a]

### Second stage and the composed result

Select `Xplus = pairedSource`, with values in `Q x Q` and complete pairing

`B_Xplus((a,b),(c,d)) = (2(a+b)(c+d), ac+bd)`.

Let `V = changeValue(fst) : BilinModule_Q(Q x Q) -> BilinModule_Q(Q)`.
It gives `V(Xplus)=X`. Apply the new selected change-of-values restriction lift to
`Xplus` and **the actual first-stage defining arrow `i1`**. The second comparison
has identity underlying carrier map. [M16a, M16b]

The composed lift is `secondLift.comp firstLift`. Retain the actual final object `X2`,
defining arrow `i2 : X2 -> Xplus`, and forward/backward maps
`alpha2 : U(V(X2)) -> Q`, `beta2 : Q -> U(V(X2))`. Require

`X2 = secondLift.obj Xplus i1`, `i2 = secondLift.hom Xplus i1`,

`alpha2(a,-a)=a/2`, `beta2(t)=(2t,-2t)`,

`beta2 o alpha2 = id_(U(V(X2)))`, `alpha2 o beta2 = id_Q`,

`U(V(i2)) = i0 o alpha2`,

`B_(X2)(beta2(s),beta2(t)) = (0,8st)`.

The fixed observations are `B_(X2)(beta2(1),beta2(1))=(0,8)` and
`i2(beta2(3/2))=(3,-3)`. They retain the extra form and the original factor-two coordinate.
The second stage cannot restart from another chosen module mono or return only `X1`.
[M16a, M16b]

### Nonzero factorization at both stages

Independently fix the whole cone by its matrix

`h(s,t) = (3s-2t,-3s+2t)`

from the rational plane with zero first form, and fix its base mediator by its own row

`g0(s,t) = (3s-2t)/2`.

Require `U(h) = i0 o g0` as a whole-map equation. The first lifted mediator
`h1 : zeroSource -> X1` must satisfy

`i1 o h1 = h`, `alpha1 o U(h1) = g0`,

with uniqueness for every compatible formed arrow at those endpoints. [M16c]

The paired cone source has complete pairing
`((s,t),(u,v)) |-> (0,2(3s-2t)(3u-2v))`.
Its full cone `hplus` has the same underlying matrix and target `Xplus`.
The final mediator `h2 : pairedConeSource -> X2` must satisfy

`i2 o h2 = hplus`, `alpha2 o U(V(h2)) = g0`,

with uniqueness for every compatible formed arrow at those endpoints. These equations reuse
the returned first and final defining maps; they do not introduce replacement inclusions.
The composed factorization must consume the actual first factor in its second stage. [M16c]

Require the independently proved observations

| Input | Cone vector and final lifted mediator's vector | Base mediator |
| --- | --- | --- |
| `(2,1)` | `(4,-4)` | `2` |
| `(1,3)` | `(-3,3)` | `-3/2` |

Every map in this example retains its entire rational domain. The two observations are
additional checks, not a finite definition of any map or of its universal property.

**Surface status.** The additional public `SPEC.md` [P05] supplies explicit lift selection,
all four dependent projections, generalized application, and `factor` with its compatibility
proof. The remaining binding requirements are the full prescribed `i0` as a module map,
the exact selected coefficient/value-module parameters, and a public term denoting the
composed selected lift with its retained first comparison. The second lift must use the
actual first defining arrow. No kernel-specific call, representation inspection, or
unregistered datum placed in a proof slot substitutes for those mathematical inputs.
