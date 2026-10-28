# Reuse record: `cc-forms-general`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `discriminant form lattice dual quotient Q/Z` | none in the corpus index |
| `bilinear form finite abelian group values Q/Z` | none |

Direct checks: lean-categories `Lattices/Valued/Discriminant.lean` (`discriminantGroup`,
`discriminantForm`, `discriminantFormModule` of an integral lattice), Mathlib
`LinearMap.BilinForm.dualSubmodule`, and the registered value-change and base-change functors of
lattices (`fun.lattice.change_value`, `fun.lattice.base_change`).

## Owner

Presentation types, their denotations, and the mathematical structures and laws
they present belong to lean-categories and its mathematical dependencies. The
kernel consumes their registered interfaces; leaf implementations compute on their
public presentations.

- Formed modules with values in the selected module `W` are `BilinModuleCat R W`;
  preserve the selected ring, carrier, value module and pairing, and the actual maps
  needed by a subsequent construction. A matrix presentation does not erase those
  selections.
- In [`LeanCategories.Lattices.Valued.Discriminant`](https://github.com/dzackgarza/lean-categories/blob/3bd4d3d9695f288749c860368174462c4d689b7c/LeanCategories/Lattices/Valued/Discriminant.lean),
  `discriminantForm` and `discriminantBilinObject`, over the stated commutative
  integral domain `R`, use the declared `IsFractionFieldPerfect R L` hypothesis and take values in
  `FractionValueQuotient R = Frac(R)/R`. `discriminantFormModule` and
  `discriminantProjection` additionally require finite generation as stated in their
  signatures. Reuse the actual quotient projection and its domain; a discriminant
  invariant alone does not supply that morphism.
- [`LeanCategories.Lattices.Valued.DiscriminantFunctor`](https://github.com/dzackgarza/lean-categories/blob/3bd4d3d9695f288749c860368174462c4d689b7c/LeanCategories/Lattices/Valued/DiscriminantFunctor.lean)
  already defines `integralDiscriminantFormFunctor` on
  `Core (FractionFieldPerfectFiniteProjectiveLatticeCat ℤ)` with target
  `Core (NonsingularDiscriminantFormCat ℤ)`. This source supplies transport along
  lattice isometries; it does not assert a functor on arbitrary lattice morphisms.
- The registered lattice change-of-values operation is
  `fun.lattice.change_value`. The formed-module change-of-values operation used by
  RX-LIFT is the distinct `fun.bilin_module.change_value`, with its own selected
  parameters and registered lift.

## Current V1 reuse and placement decision (2026-10-28 UTC)

**Use the existing forms and computations for V1; do not begin a new Hex foundation
or a wholesale numeric, matrix, polynomial or normal-form migration.** The first
RX-LIFT computation already has formal source declarations and an independently
authored rational-matrix/callable implementation. Its unresolved interpretation,
retention and public-contract obligations are not an absent basic algebra library.
This decision does not claim that the inspected implementation passes on the current
integrated revision.

The upstream catalogue reuses `LeanCategories.Catalogue.Lift` and
`LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels` for
`MonoLift`, its computational signatures, `Kernels.forgetMonoLift` and its laws.
Its existing `ChangeValueLifts` and `ChangeValueComparisons` modules supply the
second lift and the selected comparison maps. The exact imports and independent
specimen sources are fixed in [#23](https://github.com/dzackgarza/lean-cas-dsl/issues/23).
These are mathematical inputs consumed through the accepted catalogue, not new
domain-specific kernel imports. In particular, the formally chosen
`MonoLift.factorComputation` is noncomputable; its existence is not an executable
factor algorithm.

The computational source is
[`lean-cas-dsl-leaves/diagnostics/extensions-20261024`](https://github.com/dzackgarza/lean-cas-dsl-leaves/tree/2f35244884649c9268567bb9968840a34559a11c/diagnostics/extensions-20261024),
including its own `leaves.json`, `lifts.py`, `native_linear.py`, `engine.py`,
`endpoints.py` and `wire.py`. Reconcile and deliver that independently authored
package through the leaf repository's existing release path; adapt its public
contract use there as needed. Do not replace it by the older finite-graph-only
bilinear leaf or copy its mathematics and algorithms into the kernel. The kernel
supplies the complete declared inputs and retains the returned objects, maps,
comparisons and ownership. `CasContract` owns generic wire grammar and helpers;
native Sage/passagemath data and algorithms remain in the leaf.

[Hex's published split](https://github.com/leanprover/hex/blob/main/README.md)
between computational libraries and corresponding Theory libraries is compatible
with upstream ownership of mathematical forms. It is not adopted as a V1
dependency by this record. A later, separately adopted form can use an individual
library and its actual denotation/correspondence at that upstream owner, without
making the kernel select algebra algorithms or giving leaf data mathematical
authority. Transitive mathematical dependencies are not a new kernel-owned
semantic implementation. The existing acceptance/evidence model is unchanged;
this does not adopt certificate-primary acceptance or claim uninspected Hex
theorems are complete.

The discriminant requirements above remain part of the construction review and
their existing domain work. They do not become an additional prerequisite for the
first RX-LIFT refactor trial.

## Historical implementation decision (2026-09-29)

The recorded work was registration of the discriminant construction already
declared in lean-categories, and a leaf realizing finite formed modules with
`ℚ/ℤ` values. This records the reuse rationale at that date, not a present absence
claim about the functor or permission to omit the hypotheses and variance above.
