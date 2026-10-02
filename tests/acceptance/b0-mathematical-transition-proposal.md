# Mathematical question comparison: b249ca2 to 57c85852

This proposes a mathematical dependency transition for the original 153
questions. It is not protected admission and does not compare candidate
fingerprints. The independently stated questions in
`b0-interpretations-proposal.md` remain the expected mathematical questions.
Source inputs are the supplied mathematical revisions `b249ca2` and
`57c85852de8127b9d229878061bfb26c47998814`, and the approved language SPEC.
Only upstream mathematical definitions were inspected.

## Selected ring parameters

The polynomial, multivariate-polynomial, matrix, monic-polynomial, differential,
algebra and affine-scheme declarations now accept the chosen `CommRingCat`
object directly. Their earlier telescope accepted its carrier plus a ring
instance. The original assertions specify Z, Q, R or C with their named ring
structures. At those selected objects the carriers, ring operations, constants
homomorphisms and defining polynomials are unchanged. This comparison retains
the actual named ring, not an arbitrary instance on an equal carrier.

The polynomial generator remains X, coefficient inclusion remains Polynomial.C,
degree remains Polynomial.degree, the admitted nonzero datum remains (p,p≠0),
and factors and roots retain their finite-set result forms. Matrix action is
still mulVec, determinant and trace are still those of the selected ring, and
the companion matrix still has the specified coefficients in its last column.
The monic admission retains both monicity and degree. Universal relative
differentiation is still KaehlerDifferential.D relative to the actual base ring;
the primitives are still its full inverse image. Polynomial and multivariate
algebras still use their actual constants map, and the scheme maps still use
contravariant Spec of that same map. These are comparisons of functions and
structured data, not observations that the assertions happened to be true.

## Actual coefficient maps and evaluation

Polynomial coefficient transport now accepts the actual arrow f:R → S and
applies Polynomial.map(f.hom), rather than extracting an implicit algebraMap.
Evaluation now accepts an object of Under(R), retaining the selected coefficient
arrow to its target. In the original corpus the relevant maps are the prescribed
Z → Q, Z → C, Q → R and Q → C inclusions. Their actions on each coefficient
are exactly the original canonical embeddings. Evaluation at ±sqrt(2) is in R
with the specified Q → R map; extending the cubic or quadratic to C uses its
actual original coefficient inclusion. Identity evaluation in Z or Q uses the
identity coefficient arrow. An alternate ring arrow is not allowed merely
because its source and target have the same display names.

Thus the intended questions retain both the polynomials and the actual maps.
The new telescope makes these data explicit; it does not authorize copying
parameters or dropping a defining map. A candidate claim must show these
specific selected arrows, not just a declaration named `map` or `evaluation`.

## Chosen fields for spans and dimension

Span and dimension now take a `FieldCat` object. Its field structure is
recovered from the field property of its own chosen commutative ring, via
`IsField.toField`. For the original spans in Q³, the ring is the named rational
ring and its compatible field structure. The vector operations, generated
submodule and dimension remain those over that Q. Uniqueness of inverses
compatible with a chosen field multiplication justifies this recovery; an
unrelated field structure on the same carrier would change the question.
The two original span generators and the actual ambient Q³ and kernel inclusion
remain fixed. No original dimension question is replaced by a dimension over
another base field.

## Units and inversion

Units and division now take the selected `MonCat` object directly. For the
original rational divisions and the admitted matrix M in Mat_2(Q) units, the
chosen monoid is the original multiplicative monoid. The unit admission retains
the actual element and its two-sided inverse witness. `admit_inclusion` and
`admit_inverse_inclusion` identify the admitted datum and its witness's inverse.

The units construction now also exposes its group through the units functor.
The source theorem `inverse_eq_groupInverse` states equality of the earlier
units inverse map with inversion in that selected group, and
`unitsIdentification` is the carrier identification for that exact units
object. This establishes the operator comparison independently of its value
on the specific matrix. A route through a different group or monoid is not
covered by that theorem. The old unit-valued inversion is not replaced by an
inverse on an arbitrary matrix carrier.

The Taylor-series coefficient still divides the same iterated derivative by
the same factorial unit in the real multiplicative monoid. The two limit
domains still have the original punctured-line/real-units maps and approach
filters; the `MonCat.of R` packaging of real units changes none of those
functions, admitted convergence conditions or chosen limit points.

## Additions and original named formed objects

The original integral A/A_dual/to_dual declarations in `Integral.lean` are
unchanged between these inputs. Their selected negative Cartan form, carrier,
value modules and value map remain the original data. New E₈, finite-group and
quotient-presentation declarations support the owed positive proposals, but
do not change the expected meanings of the original 153 questions.

The introduction of additional group objects named ZMod makes selection of
actual structure especially material. Original quotient-ring arithmetic stays
in its named ring, and new `in Groups` assertions select the named cyclic group.
Carrier equality or declaration order cannot perform that selection. The
original set/cardinality questions retain their original object parameters and
accepted structural carrier comparisons.

## Remaining assessment

The comparisons above establish how the independently specified mathematical
questions are expressed with the finished source's explicit selected objects
and maps. Actual candidate typed-question claims still require comparison to
these questions at the tested tuple. No candidate reading or computation has
been inspected or promoted into an expected interpretation here, and no
protected semantic dependency transition has been performed by this proposal.
