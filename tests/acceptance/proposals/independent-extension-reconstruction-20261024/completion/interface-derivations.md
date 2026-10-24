# Complete source observations for the fixed extension questions

These additions retain the questions in `../questions.md`, every original `.cas`
assertion, and every expected mathematical value. They use the independent
mathematical extensions at `a1e04b78b4c23b192d65ea87cb1447cb2d58a4bc` and the
complete interface declarations at `3ffa71fc01f5733c6ad03ac2f068fecf64da500b`.
The source-check theorem `paired_factor_comparison` has the same statement at
the proof-only correction `7e848db3`; its selected maps and hypotheses are
unchanged. No expected value comes from a CAS execution or implementation.

## Three previously absent direct observations

### Two-subsets and the actual specified bijection

`rx02-complete-core-action.cas` selects `core_rev(5)`, whose source and target
are both the core of the original `Fin 5`. Its retained isomorphism is
`fin_reversal(5)`. Both arrows of that isomorphism are the existing `rev(5)`;
in particular the forward map takes `0` to `4`. The comparison therefore does
not silently turn an arbitrary set morphism into a core arrow.

The full direct-image observation is

\[
\operatorname{extent}(\operatorname{TwoSubsets}(r)(s))
  =\{r(x)\mid x\in\operatorname{extent}(s)\}
\]

for every two-element subset `s`. `extent` retains the actual
`TwoSubsets.inclusion : TwoSubsets(Fin 5) → Finset(Fin 5)` and then
`FiniteSubsets.inclusion : Finset(Fin 5) → Set(Fin 5)`. The annotations in the
source must use these declared inclusions. This is the entire function on the
two-subset object. The additional composition and inverse observations use
the complete mapped reversal twice, including its original core endpoints.

Sources: `Foundation.CoreIsomorphisms` (`finRevIso_hom`, `finRevIso_inv`,
`finRevCore_comp`); `Foundation.TwoSubsets` (`inclusion`, `map_extent`,
`onCore.map_id`, `onCore.map_comp`); Mathlib `Fin.rev_involutive`.

### Actual automorphism arrows and all quotient classes

`rx03-complete-automorphism-arrows.cas` projects the actual forward and backward
group arrows of the selected doubling automorphism and of its inverse. The
complete projected action after the fixed residue comparison is doubling or
tripling on every residue. In the selected group `Multiplicative(ZMod 5)`,
these actions are the whole group maps `z ↦ z²` and `z ↦ z³`, since that
group's multiplication is addition of residues.

The integer-class maps explicitly use `cyclic_quotient_map(5)`. Thus the
observations at `[1]`, `[2]`, and `[3]` are not numeral expressions for the
group's multiplicative identity. The whole integer-domain equations are

\[
a([k])=[2k],\qquad b([k])=[3k]\qquad(k\in\mathbb Z).
\]

Both conjugation observations retain the actual complete comparison `e`:

\[
\operatorname{forward}(\operatorname{Aut}(e)(a))=e\circ a\circ e^{-1},
\qquad
\operatorname{backward}(\operatorname{Aut}(e)(a))=e\circ a^{-1}\circ e^{-1}.
\]

Sources: `Algebra.CyclicQuotients` (`byUnit_coordinate`, `byUnit_two_inverse`,
`residueComparison_quotient`); `Algebra.AutomorphismArrows`
(`forward_backward`, `backward_forward`, `forward_conjugate`,
`backward_conjugate`); Mathlib `toAdd_pow`.

### Source-correct reuse of the actual first factor

`rx-lift-source-comparison.cas` selects the already supplied
`pulled_back_forward` and `pulled_back_backward` at the fixed cone. Let
`V = changeValue ℚ (ℚ × ℚ) fst`. Their exact endpoints are

\[
c:V(\mathrm{pairedConeSource})\longrightarrow\mathrm{zeroSource},
\qquad
c^{-1}:\mathrm{zeroSource}\longrightarrow V(\mathrm{pairedConeSource}).
\]

Their underlying vector functions are identities, but the complete formed
objects are retained. The original cone is not monic: the vector `(2,3)` has
zero image. These arrows therefore use the general `pulledBackIso`; they do
not arise from a monomorphism-lift call on the cone.

If `h₁` is the actual first returned factor, the second input is
`h₁ ∘ c`, with the exact domain `V(pairedConeSource)`. The complete
compatibility is

\[
V(\mathrm{pairedCone})=i_1\circ h_1\circ c.
\]

The separately selected second factor and the composed factor both have
domain `pairedConeSource`. Each factors the original whole paired cone
through the same final defining map. Their equality follows from the selected
unique-factor law, or equivalently cancellation by that monic defining map.
The additional observation

\[
\mathrm{second.forward}\circ V(h_2)=h_1\circ c
\]

retains the actual first factor; it is not a replacement by a separately named
map with equal carrier values. The formal compatibility proof uses the
first selected lift's `factor_hom` theorem and the source comparison triangle.
It does not use a proof or equality claim returned by a computation.

Sources: `Modules.Bilinear.Valued.ChangeValueComparisons`
(`pulledBackForward_backward`, `pulledBackBackward_forward`,
`pulledBackForward_hom`); `Catalogue.Lift` (`MonoLift.factor_map`,
`factor_hom`, `factor_unique`); the original `[M16a-c]` fixed planes and cones.

The source and target observations require the endpoints of the actual typed
`cone` and `pairedCone`. The public spelling `cone.source()` must be documented
for complete typed morphisms, beyond the earlier promise for whole Arrow
objects. This is a surface obligation on these fixed inputs, not permission
to replace either formed source by its vector carrier.

## Exact coordinate types

`interface-expected-facts.lean` checks the six full module equalities recorded
in `coordinate-presentations.md`, the two actual rectangular rows, and the
regular scalar module. Each ambient plane or cone carrier in those equations
is exactly `ModuleCat.of ℚ (Fin 2 → ℚ)`. The row `[1,0]` has type
`Matrix (Fin 1) (Fin 2) ℚ`; so does `[3/2,-1]`. Their target is exactly
`ModuleCat.of ℚ ℚ`.

No new product-to-vector isomorphism is needed for the existing `Vec(Q,2)`
uses. The selected value projection still has type
`LinearMap.fst ℚ ℚ ℚ : (ℚ × ℚ) →ₗ[ℚ] ℚ`, and the paired forms retain the
actual componentwise product module `ModuleCat.of ℚ (ℚ × ℚ)` as value module.
The comparison `c` remains necessary even though its two source carriers are
the same vector module. The proof file also retains the full ordinary module
kernel universal property via Mathlib `ModuleCat.kernelIsLimit`.

The earlier `expected-facts.lean` receives only missing proof context: the
explicit `IntegerSquareBounds` import and the existing monicity proof at the
displayed second-stage target. Its universe-generic carrier-route equation is
proved by its two defining route equations, instead of applying a source lemma
restricted to universe zero. Every proposition remains unchanged.

## Exact scopes of the ten extension mechanisms

All paths below are relative to this completion directory. A scope can have
several independent source files when it has both a positive computation and
a separate rejection or comparison question.

| Mechanism | Fixed source inputs | Mathematical observation |
| --- | --- | --- |
| 1. A new object inherits existing operations | `rx01-selected-orders.cas` | `FinOrder(5)` and `ReverseFinOrder(5)` each inherit cardinality five while retaining their different orders. |
| 2. A new generic operation acts on old objects | `rx02-two-subsets.cas`; `rx02-complete-core-action.cas` | Two-subsets of the original `Fin 5` have cardinality ten, exclude singletons, and have the entire specified-bijection action and inclusion. |
| 3. Constructed and refined objects inherit their interfaces | `rx03-cyclic-automorphisms.cas`; `rx03-complete-automorphism-arrows.cas`; `rx04-square-bound.cas` | The actual `Aut` group inherits inverse/composition, and the finite square-bound subtype retains its original membership and inclusion after refinement. |
| 4. Two structures on one carrier remain distinct | `rx01-selected-orders.cas`; `rx05-carrier-diamond.cas` | Ordinary/reverse orders and the additive/multiplicative ring operations remain selected separately despite equal carriers. |
| 5. Competing routes require their actual comparison | `rx05-carrier-diamond.cas` and its four environments in `../observation-controls.md` | Both full routes, `cmp.rings.carrier`, its inverse and naturality; omission of that cell leaves ambiguity regardless of registration order. |
| 6. Nonidentity presentation transport | `rx07-f9-transport.cas` | `e(x)=y+2`, both whole inverse maps, preserved coefficients, and successive value/map reuse over the original `ZMod 3` domain. |
| 7. Parameter and base transport | `rx06-reindexing.cas` | The original quotient `ℤ → ZMod 5`, changed scalar action, full reindexed arrow and cartesian data remain selected. |
| 8. Complete structured output and successive prescribed lifts | `rx08-ordinary-kernel.cas`; `rx-lift-prescribed-stages.cas`; `rx-lift-source-comparison.cas` | The ordinary kernel and restricted coefficient three remain separate from the scaled two-stage formed restriction with coefficient eight and full-domain universal factors. |
| 9. Fresh computation registration using only the public contract | `rx09-successor-series.cas`; separate `rx09-constant-one-rejection.cas` | The new entire successor family uses the old summation binder; every coefficient is `d+1`, and constant one has no summable-family admission. Registration is an external execution input, not an assertion edit. |
| 10. Execution failures preserve interpretation and strata | `rx10-fixed-execution-question.cas` with the conditions in `../observation-controls.md` | The same full reindexed-map question has expected residue one under all six execution conditions; ownership and reconnection controls preserve its mathematical meaning. |

The mathematical declaration environment must explicitly import
`Foundation.IntegerSquareBounds` as well as the original four modules listed
in `README.md`; `Independent.ScalarAndFormExtensions` does not import it.
The supplemental second-factor proof also uses the supplied general cone
compatibility theorem from `Independent.InterfaceCompletionTests`, so that
mathematical source module is included in the six-module list. This additional
import supplies no computation and no new registration.

The external route, execution-failure and ownership conditions are not supplied
by these mathematical files. Their exact required outcomes remain in the
original observation controls. A proof check does not establish public-language
interpretation, actual dispatch, a frozen execution trial, permanent admission,
or any broader acceptance result.
