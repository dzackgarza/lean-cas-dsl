# Formed-module questions from the published construction interface

The fixed B0 `cc-specimens` requirement is the formed module
`U=(ℤ², ((a,b),(c,d))↦ad+bc)` with cardinality `ℵ₀` through its structural
carrier functor. `cc-realizer-first` also requires the zero form on `ℤ⁰` with
cardinality one. The selected-structure row requires different chosen forms on
one carrier to remain distinct. These requirements and expected mathematics
were fixed before the new construction interface or any candidate output.

Published latest `lean-categories/main` was verified on 2026-10-20 as
`c551267613c610f8eb66ac028874495c1c98ddc5`. Its mathematical interface
`LeanCategories/Catalogue/Semantics/Modules/Bilinear/Valued/Constructions.lean`
now supplies registered `BilinearMaps`, `BilinearForm`, `FormedModule`, and
`formed_pairing`. Its `bilinearMaps`, `admitBilinear`, `bilinear`, `formed`
and `pairing` declarations retain the selected scalar ring, carrier modules,
value module and actual bundled bilinear map. This resolves the absent
registered formed-object constructor recorded against earlier published
revision `a2123729df092e58b6fb0cd39c78db5e1714faf2`.

The source in [b0-formed-positives.cas.proposed](b0-formed-positives.cas.proposed)
is unactivated proposed assertion source. It belongs to neither the admitted
nor executed inventory. No existing assertion, expected value or protected
record is changed. Its use of coordinate-pattern lambdas follows the
mathematical notation of [SPEC.md](../../SPEC.md), “Subspaces and spans”;
whether the candidate supports this notation and the dependent constructor
applications remains a language obligation, not an upstream mathematical one.
No candidate reading or computation was inspected to choose these expressions.

## Typed binding context and mathematical justification

Select `R=ℤ` as a commutative ring, `M=Vec(ℤ,2)` as its selected module
`Fin 2→ℤ`, and `W=RegularModule(ℤ)` as its regular scalar module. The form
`b:M→ₗ[ℤ]M→ₗ[ℤ]W` is

\[
 b((a,b),(c,d))=ad+bc.
\]

It is additive and scalar-linear in each variable by distributivity in `ℤ`.
For example, replacing the first vector by its sum adds the two corresponding
expressions, and replacing it by `r(a,b)` multiplies the expression by `r`;
the corresponding two laws hold for the second vector. These are the full
`IsBilinearMap` laws used by published `admitBilinear`, not a finite sample
substituted for bilinearity evidence.

`U=BilinearForm(R,M,W,b)` is an object of fixed-value `Bil(ℤ,ℤ)`.
`Uv=FormedModule(R,M,W,b)` is the corresponding object of `BilWFormCat ℤ`
with the actual selected value module. Both have carrier `M`; their category
and value data are retained separately. `bu=formed_pairing(R,Uv)` is the
declared arrow `M×M→W`, not an untyped external function.

Let `M₀=Vec(ℤ,0)` and let `z:M₀→ₗ[ℤ]M₀→ₗ[ℤ]W` be the zero bilinear map.
It obeys all four bilinearity laws; `Z=BilinearForm(R,M₀,W,z)` has carrier
`Fin 0→ℤ`, which contains exactly the empty function. This is the specified
rank-zero example, not a rank-two zero form with a different carrier.

Let `b3=3b`, a second bilinear map on the same `M` and with the same `W`.
`Uv3=FormedModule(R,M,W,b3)` retains that different chosen datum. At
`u=(2,-1)`, `v=(3,4)` in `M`, `b(u,v)=8-3=5` and `b3(u,v)=15`.
Thus these two forms are mathematically distinct, independently of how their
carrier values are presented or computed.

The cardinality expectations use the elementary fact that `ℤ²` is countably
infinite (Mathlib `Cardinal.mk_int`, `Cardinal.power_nat_eq`) and that a function
out of `Fin 0` is unique (Mathlib `Pi.uniqueOfIsEmpty`). The pairing expectations
are the displayed integer calculations. Published `BilinModuleCat.ofBilinMap`
and `BilWFormCat.of` give the carrier and form identifications directly; no
implementation's answers or self-description supply them.

## Per-identity questions

| Proposed identity | Mathematical proposition and expected value |
| --- | --- |
| `formed.card.hyperbolic_fixed` | Equality in `Cardinal`: cardinality of the underlying set of the specified fixed-value `U` is `ℵ₀`, through its actual formed-module/module/set route. |
| `formed.card.hyperbolic_variable` | Equality in `Cardinal`: cardinality of the underlying set of the specified variable-value `Uv` is `ℵ₀`; its selected `W` and pairing remain in the input. |
| `formed.card.zero_rank_zero` | Equality in `Cardinal`: cardinality of the carrier of the specified zero form on `M₀` is one. |
| `formed.pairing.hyperbolic` | Equality in the selected integer value module: `formed_pairing(R,Uv)(u,v)=5`, with the ordered vectors, their module and selected form retained. |
| `formed.pairing.scaled_hyperbolic` | Equality in that same integer value module: `formed_pairing(R,Uv3)(u,v)=15`. Equal carriers never select between `b` and `3b`. |

These source observations do not discharge the requirement to run different
input presentations of `U`, verify complete structured replies, or conduct
post-freeze independent extension trials. They do not replace the independently
selected exit specimens recorded in `b0-independent-assessment.md`.

## Remaining mathematical inputs

The existing A₂ discriminant-pairing requirement is still the equality
`b([e₁],[e₁])=[2/3]≠0` in the discriminant value quotient. The new
`formed_pairing` now provides the varying-value pairing signature. The
published named `A_dual(2)` object still exposes no distinguished dual-basis
element or admission map for the rational coordinate vector representing that
element. The new `formed_value_map(ℤ,to_discriminant(2))` supplies the actual
projection from the dual's value module into the discriminant's value quotient;
applying that declared map to the rational `2/3` specifies the expected class
without inventing a quotient literal. The selected dual-basis element remains
the precise missing mathematical input to the pairing assertion. `A(2)` is an object of
`BilWFormCat ℤ`; it cannot silently be passed as an integral-lattice object to
the new generic metric-dual/discriminant constructors. Its already admitted
discriminant cardinality remains unchanged and is not this form assertion.

For the independently chosen structured-result trial, the input is the actual
module morphism `(a,b)↦a : ℚ²→ℚ`, with form `diag(2,3)` on its source. The new
bilinear constructors supply that form. The inspected published catalogue has
`matrix_linear_map(n,K,M)` for square matrices, but has not supplied a registered
general linear-functional constructor or coordinate-projection module morphism
for this exact nonsquare source/target pair. A set-map expression alone does
not give the selected module morphism. Replacing it by a square endomorphism
with the same kernel would change the fixed trial input, so no such replacement
is made. Its actual declared module morphism and the prescribed restricted-form
kernel construction remain inputs to that trial.

At published main `e8e97d2b13fad4b868b0f8447a5e511a47732436`, the new
`formed_morphism` declaration exposes the genuine formed-morphism law with
both carrier and value-module maps. This does not turn the selected projection
into a fixed-value formed morphism. With `e₂=(0,1)`, its carrier map sends
`e₂` to zero, while the selected form has `b(e₂,e₂)=3`. An isometric
fixed-value morphism would require `3=b_Y(0,0)=0`, a contradiction. Therefore
the stated kernel line with restricted form `[3]` is an assertion about
restriction along an arbitrary module subobject; it cannot be presented as
the kernel of a morphism in fixed-value `Bil(ℚ,ℚ)` or count as the required
formed-arrow trial. The selected map, source form and expected restricted
form are preserved; no different morphism is substituted.

For a variable-value formed morphism the same source data instead require a
specified value map `α` annihilating that self-pairing and satisfying the law
on every pair. No such extra map or target form was part of the selected
trial. Supplying one would be new mathematical data, not a spelling correction.
The new constructor alone does not provide it.

The published complete-cokernel example supplies a different, valid formed
endomorphism of hyperbolic `U`: carrier multiplication by two and value
multiplication by four, with the full identity
`4b(x,y)=b(2x,2y)`. Its prescribed nonzero modulo-two descent is proved in
`Modules/Bilinear/Valued/CokernelLiftTests.lean`. Those source-owned module
maps are constructed there by `ModuleCat.ofHom`; they are not registered
public map names. The inspected public constructor `formed_morphism` consumes
module maps and a pairing-law proof, rather than admitting a general pair of
function literals as module maps. Hence it does not yet supply source-language
expressions for those specific maps or justify manufacturing them locally.
This different mathematical example does not replace the fixed projection
trial or its expected data.

For the chosen exit trials requiring a new generic operation or new formal
object absent from the published vocabulary, their independently published
mathematical extension and a frozen candidate remain needed. These formed
source additions resolve an existing B0 input; they do not establish every
independently chosen trial or authorize upstream work from this assessment.
