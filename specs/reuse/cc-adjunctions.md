# Reuse record: `cc-adjunctions`

## Queries

Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `Adjunction homEquiv unit counit` | TauCeti `Adjunction/Mates.lean`, downstream users of Mathlib `Adjunction` |
| `Adjunction const lim limAdjunction` | none (spelling); direct check below |
| `Adjunction.mkOfHomEquiv` | mathlib4 order categories (`BddLat`, `PartOrd`) |
| `Functor.const sectionsFunctor adjunction` | none (only `Sites/GlobalSections.lean`, through `lim`) |
| `constant functor right adjoint sections types` | none in Lean |
| `free forgetful adjunction MonCat` | mathlib4 `Algebra/Category/Grp/Adjunctions.lean`, `Ring/Adjunctions.lean` |

Direct checks recorded at that date in Mathlib: `Limits/HasLimits.lean` (`constLimAdj : const J ⊣ lim`),
`Algebra/Category/MonCat/Adjunctions.lean` (`MonCat.adj : free ⊣ forget MonCat`).

## Owner

For the ordinary-category fragment, reuse Mathlib's `Adjunction F G`, including its
selected unit, counit, triangle identities and induced `homEquiv`. These are actual
fields and constructions, not merely a proposition that some adjunction exists
([Mathlib v4.33.0, `Adjunction.Basic`, lines 108–118](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/CategoryTheory/Adjunction/Basic.lean#L108-L118)).
`constLimAdj` and the available free–forgetful adjunctions supply particular such
structures. Equality of adjunction records requires the appropriate data equality;
Mathlib's extensionality lemma uses equality of their units
([lines 193–199](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/CategoryTheory/Adjunction/Basic.lean#L193-L199)).

Distinguish the category of adjunctions, the homotopy fibre of chosen adjunction
structures over a fixed ordered pair `(F, G)`, and the space of right adjoints to a
fixed left adjoint. These are the distinct constructions in
[FOUNDATIONS, Definitions 1.2–1.4 and Remark 1.6](https://github.com/dzackgarza/lean-categories/blob/8782c22ba613a022a84a1e910b6489cc2503e29a/FOUNDATIONS.md#L8411-L8527).
Contractibility of the last space under the stated hypotheses does not make a strict
record of unit and counit fields literally unique or discard its usable data. The
older phrase “a set (subsingleton up to iso)” supplied neither the required category
nor its cells. Ordinary Mathlib adjunction and equivalence records supply their
ordinary fragments; their existence alone does not provide the required higher
categories or coherent identifications.

Subsequent transposition, unit/counit evaluation and constructions derived from an
adjunction retain the selected structure and its complete parameters. Replacing that
structure by another requires the accepted comparison and the corresponding transport
of the data being used. For example, on rational vector spaces `Id ⊣ Id` admits unit
`a·id` and counit `a⁻¹·id` for any nonzero rational `a`; its transpose sends `f` to
`a·f`. Fixing the two functors therefore does not determine the selected transpose.
This is a mathematical distinction, not a claim of a reproduced runtime defect.

Where accepted mathematics supplies a fully faithful presentation functor, its
hom-set equivalence can transport the selected transpose. Full faithfulness is an
additional mathematical hypothesis; it does not follow from a presentation datatype,
a denotation function or a wire decoder. Leaf replies provide computational data, not
this proof. The historical `realizedCell`, `realizedLimitCone` and presented-value
transpose implementations do not reinstate leaf-supplied denotation witnesses or turn
an untrusted answer into a proved adjunction.

The required higher data and any missing registration or realization are owned by
CC-HIGHER/#82 and the existing interpretation, computation and independent-validation
work. Identify them for each claimed construction. This does not require unrelated
higher-categorical formalization before an ordinary selected adjunction can be used.

## Historical implementation decision (2026-09-29)

The following records the inspected implementation and reuse rationale at that date;
it is not a current package-wide absence claim or a new authority for mathematical
scope:

- `LeanCategories.Foundation.constSectionsAdj : Δ ⊣ sections` used Mathlib's
  `Types.sectionOfCone` and `Adjunction.mkOfHomEquiv`. The recorded reason for that
  definition was that the inspected `constLimAdj` factored through chosen `lim`, whose
  transposes did not reduce as needed, and the search found no Mathlib adjunction with
  that `sectionsFunctor` as its right adjoint.
- The recorded integration work comprised the `adjunction` registry row naming a
  Mathlib `Adjunction` between registered functors, validation of that declaration,
  and transpose on presented values through the supplied formal comparison. It does
  not establish that all categories of adjunctions, selected unit/counit actions or
  higher coherence are registered and consumed today.
