# Questions of the additional B0 positives

These source additions discharge the acceptance author's authorship obligation
where the published mathematical vocabulary supplies an expression. They leave
protected admission, typed interpretation comparison and computational execution
unperformed. Their mathematical expectations precede any candidate execution.
No original `.cas` assertion or authoritative acceptance record is changed.
The proposed positives are not yet part of the admitted or executed inventory.
The `.cas.proposed` source preserves their concrete expressions for protected
independent admission, without adding them to the suite's `.cas` input set.

The approved requirement is the “Required computational assertions” paragraph and
the `cc-specimens`, `cc-realizer-first`, `cc-forms-general` and stage-C rows of
[computational-core-plan.md](../../specs/computational-core-plan.md). Published
mathematics was inspected at `lean-categories/main`
`a2123729df092e58b6fb0cd39c78db5e1714faf2`, verified live on 2026-10-20.

## Binding contexts and result types

The proposed file [b0-required-positives.cas.proposed](b0-required-positives.cas.proposed) uses only
published mathematical names and the notation specified in [SPEC.md](../../SPEC.md),
including category selection, registered generators and the two directions of a
named presentation comparison. The generic application syntax is the existing
mathematical language. Source notation has not been tested against a candidate.

`E8` is the published negative-definite integral `E₈` lattice, retaining its
bilinear form and chosen `ℤ`-module `Fin 8 → ℤ`; rank is cardinal-valued module
rank inherited through its actual structural functors. Its sign convention does
not change that rank. Sources: Bourbaki, *Lie Groups*, ch. VI, Plate VII;
`LeanCategories/Lattices/Valued/Standard.lean`, `e8Lattice`, `e8Lattice_gramMatrix`;
the named object registration in
`LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/Lattices.lean`.

`S3 = GrpCat.of (Equiv.Perm (Fin 3))`. `C3` is the additive cyclic group
`Multiplicative (ZMod 3)`. Both are selected as objects of `Groups`, rather than
selecting another structure sharing their carrier. `sigma:S3→Multiplicative
(ZMod 2)` is parity (positive sign maps to zero). `zero_map` is the trivial
homomorphism with those same source and target groups. `identity_map:S3→S3` is
the identity. For each map the kernel is a subgroup together with its defining
inclusion into the actual source group, through the published `Subgroups.kernel`
and group-arrow `ker` operation. Cardinality then uses its domain group and
underlying set; a bare integer is not a complete answer to the kernel construction.

Sources: published
`LeanCategories/Catalogue/Semantics/Algebra/FiniteGroups.lean`,
`Subgroups.lean`, and `Properties.lean`; Mathlib `Equiv.Perm.sign`,
`alternatingGroup`, `MonoidHom.ker`, `Subgroup.subtype`, and `Fintype.card_perm`.
The published kernel theorems apply to the actual maps with their chosen
endpoints. They do not identify maps solely by endpoint equality.

`X=F9x=𝔽₃[x]/(x²+1)` and `Y=F9y=𝔽₃[y]/(y²+y+2)` are distinct selected
commutative-ring presentations. Their generators are their own residue classes
`x̄` and `ȳ`. `c_X,c_Y:ZMod 3→X,Y` are their registered coefficient maps.
`φ=F9translation:X≅Y` is the specified nonidentity comparison. Its forward
map satisfies `φ(x̄)=ȳ+2`, since `(ȳ+2)²+1=ȳ²+ȳ+2=0` in characteristic
three; its inverse satisfies `φ⁻¹(ȳ)=x̄-2`. Constants are retained through
`c_X,c_Y`, not inferred by identifying presentations. No assertion equates the
two presentation objects or uses an external equality operation.

Sources: published
`LeanCategories/Catalogue/Semantics/Algebra/PolynomialPresentations.lean`,
particularly `quadraticComparison_root`, `quadraticComparison_inv_root`,
`quadraticComparison_constants` and the registered comparison
`cmp.f9.translation`; the independently formalized polynomial-translation
isomorphism in `LeanCategories/Algebra/Concrete/PolynomialPresentation.lean`.

Two further fixed stage-B/C positives are expressible in the published vocabulary.
The admission `(3 in ℚˣ)` retains `3≠0` and the selected rational multiplicative
group of units; its inverse has underlying rational `1/3`. Refinement of
`Fin 2 × ZMod 3` into finite sets retains the actual product set and a formal
finiteness proof, independently of any computed finiteness answer. Sources:
published `Algebra/Units.lean` and `Foundation/Finiteness.lean`; rational field
arithmetic and Mathlib finite-product theorems cited in the assertion source.

## Per-identity specifications

All following propositions are expected true. Cardinal numerals are their
canonical finite cardinals. Boolean comparisons retain the underlying
commutativity proposition and its negation, not only the Boolean value.

| Source identity | Typed question and independent justification |
| --- | --- |
| `lattices.rank.e8` | Equality in `Cardinal`: `rank_ℤ(E8)=8`. The eight coordinate vectors of its selected module form a basis; the Gram form is retained even though rank forgets it. |
| `units.rationals.three_inverse` | Equality in `ℚ`: the underlying value of the group inverse of the admitted unit `3:ℚˣ` equals `1/3`. The unit admission and its nonzero proposition are retained. The independent calculation is `3·(1/3)=(1/3)·3=1`. |
| `refinement.finite_product_card` | Equality in `Cardinal`: `card((Fin 2 × ZMod 3) admitted to FiniteSets)=6`. Its carrier remains the same ordered-pair product and its finiteness admission is formal proof, not an implementation's property claim. |
| `groups.kernel.sign_card` | Equality in `Cardinal`: `card(ker(sigma))=3`. `sign_kernel` identifies the kernel with `alternatingGroup (Fin 3)`; `alternating_three_card` proves its order three. The defining inclusion remains part of the kernel request. |
| `groups.kernel.trivial_card` | Equality in `Cardinal`: `card(ker(zero_map))=6`. `trivial_kernel` gives the whole source subgroup, whose underlying group has `3!=6` elements. |
| `groups.kernel.identity_card` | Equality in `Cardinal`: `card(ker(identity_map))=1`. `identity_kernel` gives precisely the identity subgroup of `S3`. |
| `groups.alternating.three_card` | Equality in `Cardinal`: `card(Alt(3))=3`, where `Alt(3)` is the subgroup object with inclusion into `S3`. The independently proved `alternating_three_card` supplies the expected value. This cardinality observation does not itself test all returned inclusion data. |
| `groups.abelian.cyclic_three` | `∀ a b:C3, a*b=b*a` for the selected cyclic-group law. This is addition in `ZMod 3`, which is commutative. The classifier's proof and a computational property answer remain separate. |
| `groups.abelian.symmetric_three` | The formal commutativity predicate on `S3` has decision `false`, equivalently `¬∀ a b:S3, a*b=b*a`. For `p=(0 1)`, `q=(1 2)`, `(pq)(0)=1`, `(qp)(0)=2`, so they differ. |
| `presentations.f9.forward_generator` | Equality in the underlying set of `Y`: `φ(generator(X))=generator(Y)+c_Y(2)`. The endpoints, generator identities, coefficient map and comparison all remain in the question. |
| `presentations.f9.inverse_generator` | Equality in the underlying set of `X`: `φ⁻¹(generator(Y))=generator(X)-c_X(2)`. The inverse direction is not an interchangeable forward map. |
| `presentations.f9.forward_constant` | Equality in the underlying set of `Y`: `φ(c_X(2))=c_Y(2)` for the chosen `2:ZMod 3`. This is the stated coefficient-preservation theorem, not carrier identity. |
| `presentations.f9.inverse_constant` | Equality in the underlying set of `X`: `φ⁻¹(c_Y(2))=c_X(2)`. Apply the inverse to the preceding coefficient-preservation equation and use the isomorphism inverse law. |

The already admitted `lattices.rank.a2` states the required `rank(A₂)=2`.
It is preserved and has not been duplicated or replaced.

## Positives requiring an additional mathematical input

The fixed `cc-specimens` example is
`U=(ℤ²,b)`, `b((a,b),(c,d))=ad+bc`, a formed module with specified integral
value module. Its required cardinality is `ℵ₀`: projection to its selected
carrier is `ℤ²`, a countably infinite set. The form, its coefficient ring,
value module and actual forgetful route must remain in the question. `cc-realizer-first`
also names the zero form on `ℤ⁰`, whose carrier has cardinality one; different
input presentations must remain presentations of their respective selected objects.

The published catalogue has the `Bil` category, its structural forgetful functor
and `pairing`, but no registered named `U` or a registered object constructor
accepting its module and bilinear map. The formal mathematical construction
`BilinModuleCat.ofBilinMap` exists upstream; existence of an unregistered Lean
constructor is not an expression in the derived mathematical language. A search
of the published catalogue for `hyperbolic`, `Hyperbolic`, `hyperbolicPlane`,
`ofBilin`, `fromForm`, `bilinModuleObject`, and names `U`, `BilinModule`, `Form`
found no such object registration. The named lattice objects are not this
specified formed-module input. The exact missing input is its independently
published mathematical object registration, or a general registered constructor
for an object of `Bil` with the stated module, values and bilinear map. No
substitute notation or local mathematics is introduced here.

The `cc-forms-general` example additionally fixes the A₂ discriminant form:
on the discriminant class represented by the first dual-basis vector its
self-pairing is `[2/3]≠0` in `ℚ/ℤ`. The existing admitted discriminant-cardinality
assertion is preserved; it does not test this pairing. Published names
`A_discriminant(2)` and `to_discriminant(2)` provide the object and quotient map,
and `pairing` exists for a fixed-valued `Bil` receiver. A source assertion of
this value still needs a registered selected dual-basis element in `A_dual(2)`
and an exposed value-group element `[2/3]:ℚ/ℤ`, together with the varying-value
pairing's declared argument/result type. This assessment has not established
those registrations and does not manufacture them from a coordinate vector.
The expected proposition is fixed here independently; its language expression
remains an explicit mathematical-vocabulary dependency.

The complete structured formed-module kernel and retained nonidentity
presentation transport remain obligations beyond the scalar cardinality
observations. The thirteen added source assertions neither replace those
requirements nor claim execution of their expected computations.
