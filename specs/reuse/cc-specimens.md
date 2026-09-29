# Reuse record: `cc-specimens`

## Queries
Corpus (`<lean-categories>/scripts/formalization_corpus.py search`), 2026-09-29.

| query | hits used |
|---|---|
| `LinearMap.BilinForm TensorProduct lift module` | HassePrinciple `QuadraticForm/Basic.lean`, TauCeti `QuadraticForm/BaseChange.lean`, atlas-lean |
| `lattice integral bilinear form Zlattice` | none |
| `GaloisField finite field isomorphism presentations` | odd-order (Suzuki appendix), CompPoly binary towers |
| `orthogonal group bilinear form isometry` | TauCeti `Geometry/Hodge/HodgeForm.lean`, HassePrinciple |

Direct checks in Mathlib: `LinearAlgebra/BilinearForm` (`LinearMap.BilinForm`,
`TensorProduct.lift`: a bilinear form is a map `M ⊗ M → R`), `LinearAlgebra/QuadraticForm/Isometry`,
`FieldTheory/Finite/GaloisField` (`GaloisField p n`, uniqueness up to isomorphism
`FiniteField.algEquivOfCardEq`), `LinearAlgebra/Matrix/…` for Gram presentations.

## Owner
- Formed modules: Mathlib bilinear forms as maps out of `M ⊗ M` (`TensorProduct.lift`); lattices
  over them are the registered classifier refinements (`cc-fib`); the specimens use the registered
  semantics (`CasCatalogue.Semantics.Modules.Bilinear`, `Lattices`).
- Finite fields: Mathlib `GaloisField` and `FiniteField.algEquivOfCardEq` for the identification of
  two presentations; the ring diamond is the registered one (`cc-cohere-exec`).
- The orthogonal subgroup: Mathlib isometries of a bilinear form; the hostile specimen is the
  research repository's own subgroup notion, which the contract rejects.

## New code, and why no dependency supplies it
Only specimen leaf contracts (realizers, actions, deciders) and the deficiency records; any missing
mathematics found becomes a node, not specimen code.
