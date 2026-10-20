# Independent assessment of product refinement and F9 transport questions

## Fixed sources and inspected input

The sole candidate interpretation input is
`/tmp/b0-poc-5410e70/product-f9-opaque-interpretations.json`, SHA-256
`fd1a2dff5d72d6d0cdd349f22936a2b4e61455da3ef400ae75d1ece485e0e157`.
It contains five rows with only `id`, `file`, `question`, `proposition`.
All five question labels name `805208138f016368f6a4eac415f25f3922a5807d`.
Both JSON graphs in each question (`literal`/`homs`, and `operations`) were
inspected; parsing them consumes the whole question, with no leftover suffix.
No implementation, computation outcome, backend or sibling diagnostic was read.

Independent expectations are the five corresponding assertions in
[b0-required-positives.cas.proposed](b0-required-positives.cas.proposed),
authored in `b4b8edd` with the meaning-preserving public-name correction in
`fd58286`, and [their independent specifications](b0-required-positive-specifications.md).
The other proposed assertions are outside this five-row comparison.
Published mathematics inspected is local `lean-categories/main`
`805208138f016368f6a4eac415f25f3922a5807d`, with Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. No build or dependency refresh
was performed. Labels alone do not authenticate the running imported environment.

## Product: exact object and refinement

The first graph retains the actual product type
`T = Fin 2 × underlying(ringIntegersMod 3)`, in that order.
The second factor is the multiplicative-forgetful route from the selected
ring `ZMod 3` through monoids, semigroups, magmas and sets. This route forgets
structure; it does not change its carrier to the group of units or select
`ZMod 2`. Published Mathlib `Data/ZMod/Defs.lean` defines
`ZMod (n+1) = Fin (n+1)`, so the proof type displayed as
`Finite (Fin 2 × Fin (2+1))` is exactly the required product carrier.

The finite-set object is `ObjectProperty.FullSubcategory.mk` for the predicate
`Finite`, with this actual `T` and its finiteness proof. Cardinality is applied
after the finite classifier's actual forgetful functor to sets. The graph
retains the refined object; it does not replace the question by cardinality
of an unrelated six-element type. The `operations` graph retains the set
product limit, `proofRefinement` for `clf.sets.finite`, and `meth.cardinality`
with the finite-classifier forgetful route and that refinement as receiver.

Sources: published `Foundation/Finiteness.lean: finiteHolds_iff`, the definition
of the finite full subcategory in `Limits/Lifts.lean`, and
`Foundation/Cardinality.lean: setsCardinality`, `CardinalLiteral.denote`;
Mathlib `Finite.instProd`, `Fintype.card_prod`, `Fintype.card_fin`, `ZMod.card`.
They give finiteness independently and `#T = 2·3 = 6` as a cardinal equality.
No enumeration from a candidate is used.

## F9: retained presentations and selected comparison

Write `X=AdjoinRoot(f)` for `f=x²+1` over `ZMod 3` and
`Y=AdjoinRoot(g)` for `g=y²+y+2` over that same coefficient ring.
Published `Algebra/Concrete/PolynomialPresentation.lean` defines exactly
`firstPolynomial`, `secondPolynomial`, and the selected algebra isomorphism
`comparison = (translate firstPolynomial 2).trans translatedComparison`.
The relation `taylor 2 f = g` is proved there. These are distinct presentations,
not two spellings silently identified by carrier equality.

Published `Catalogue/Semantics/Algebra/PolynomialPresentations.lean` declares
`first`, `second`, `firstGenerator`, `secondGenerator`, `firstConstants`,
`secondConstants`, `quadraticComparison` and the registry comparison
`cmp.f9.translation` with those endpoints. The two constants maps have domain
`ZMod 3` and are their own `AdjoinRoot.of` maps. The selected generators are
the respective `AdjoinRoot.root` point maps from `Fin 1`.
`firstIdentification` and `secondIdentification` are `Iso.refl _` for the
chosen ring-to-set presentations; this does not identify X with Y.

Every transported map in the questions is `Functor.map` of
`quadraticComparison.hom` or `.inv` under the full route
commutative rings → rings → multiplicative monoids → semigroups → magmas → sets.
It retains the selected ring comparison. The operation records explicitly
retain `cmp.f9.translation`, direction and endpoint object IDs: forward rows
have `False` and X→Y, inverse rows have `True` and Y→X. Their typed terms
independently confirm `.hom` versus `.inv`; no meaning is inferred from the
Boolean flag alone. `morphismTransport`, compositions and `presentationApply`
records retain the same selected maps and argument points.

On generator right sides, `ringNumeral 2` is the canonical integer cast into
the chosen ring Y or X. This equals its coefficient map applied to `2:ZMod 3`,
because the coefficient map is unital and preserves numerals. The inverse
right side is addition of the negation of that numeral, exactly subtraction
of 2 in X, not a target-ring subtraction or an inverted direction.

For constant rows the actual input point is `finPoint (2+1) 2 h`, followed
by the selected coefficient map. By Mathlib's displayed definition of ZMod
and `Foundation/Morphisms.lean: finPoint`, this is exactly the residue class
`2:ZMod 3`; its bound proof `2<2+1` preserves the correct domain. It is not
the number 2 in an arbitrary carrier or a generator of the quotient.

## All five dispositions

All four F9 roots are equalities of set morphisms from `Fin 1` to the named
presentation's carrier. Evaluation at the sole point and function
extensionality identify these with the fixed value equalities; their full
composition order is retained. The cardinality root is equality in the published discrete category of cardinals,
with the selected set wrapped by `Core.mk`; its discrete objects retain exactly
the underlying cardinal. Unwrapping these declared wrappers gives the fixed
equality in `Cardinal`, without choosing a different set.
Each has a second root `Sort 0`.

| Identity | Complete mathematical proposition retained | Independent source and disposition |
| --- | --- | --- |
| `refinement.finite_product_card` | `Cardinality(forgetFinite(⟨Fin 2 × ZMod 3, proofFinite⟩)) = CardinalLiteral(6)` | Finite-product/cardinality theorems above. Source-grounded match. |
| `presentations.f9.forward_generator` | `generator(X) ≫ underlying(φ.hom) = ⟨generator(Y),2_Y⟩ ≫ add_Y`, in `Hom(Fin 1,Y)` | `quadraticComparison_root` and `quadraticComparison_generator`: φ(x̄)=ȳ+2. Source-grounded match. |
| `presentations.f9.inverse_generator` | `generator(Y) ≫ underlying(φ.inv) = ⟨generator(X),neg_X(2_X)⟩ ≫ add_X`, in `Hom(Fin 1,X)` | `quadraticComparison_inv_root` and `quadraticComparison_inv_generator`: φ⁻¹(ȳ)=x̄−2. Source-grounded match. |
| `presentations.f9.forward_constant` | `(point(2:ZMod 3) ≫ c_X) ≫ underlying(φ.hom) = point(2:ZMod 3) ≫ c_Y`, in `Hom(Fin 1,Y)` | `quadraticComparison_constants 2`, retaining the actual coefficient maps. Source-grounded match. |
| `presentations.f9.inverse_constant` | `(point(2:ZMod 3) ≫ c_Y) ≫ underlying(φ.inv) = point(2:ZMod 3) ≫ c_X`, in `Hom(Fin 1,X)` | `quadraticComparison_inv_constants 2`, independently also by applying φ⁻¹ to coefficient preservation. Source-grounded match. |

Here φ denotes only the specified `quadraticComparison`. No row has a free
variable or replaces a selected point by universal quantification over a
different domain. The singleton binder of each point map is immaterial by
extensionality, while the coefficient ring and the two quotient relations remain fixed.

## Every retained proof proposition type

Proof bodies are erased in the supplied encodings; their proposition types
were inspected in both graphs. Node indices below are local to each graph.

| Question | First graph proof nodes | Operation graph proof nodes |
| --- | --- | --- |
| Product refinement | `197→196`: `Finite(Fin 2 × Fin (2+1))` | `165→164`: same `Finite` proposition; `194→193`: reflexive equality of the underlying refined product set with itself. |
| Forward generator | None | None |
| Inverse generator | None | None |
| Forward constant | `175→174`: `2<2+1` in ℕ | `211→210`: same bound; `177→176`: reflexive equality of the selected `CommRingCat.of (ZMod 3)` object with itself. |
| Inverse constant | `175→174`: `2<2+1` in ℕ | `211→210`: same bound; `177→176`: same reflexive commutative-ring object equality. |

The constants' `parameterEquivalence` record cites the published
`NamedCommutativeRings.integersModCarrierIdentification` at parameter 3,
whose definition is `Iso.refl _`. Thus its reflexive object comparison does
not select another coefficient ring. The proof types have independent proofs
from finite products, arithmetic and reflexivity; none constitutes a leaf
certificate or independently checked serialized proof.

## Limits

There are five source-grounded mathematical matches, no concrete mathematical
discrepancy and no undetermined mathematical comparison among these five.
This is a source assessment of complete supplied claims and their declared
routes. It does not Lean-check serialization typing, prove that a runtime
consumes those records, authenticate imports or establish computed answers.
No proposed assertion was modified, admitted or added to the executed suite;
no authoritative record was regenerated and no protected acceptance was issued.
