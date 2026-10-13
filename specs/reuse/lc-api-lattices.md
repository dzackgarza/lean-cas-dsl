# Reuse record: `lc-api-lattices`

## Queries
`formalization_corpus.py search`:
- "root lattice A_n Gram matrix": TauCeti's integral-lattice roadmap (suggestions, no definitions);
- "dual lattice discriminant group": the same roadmap only;
- "Cartan matrix A_n": Mathlib `CartanMatrix.A` (`Mathlib/LinearAlgebra/Matrix/Cartan.lean`),
  TauCeti root-system diagram permutations.

## Owner
- Mathlib `CartanMatrix.A n`: the Gram matrix of the root lattice `A_n`.
- The catalogue's valued bilinear forms (`cat.bil_wform`, `fun.bil_wform.*`) and its registered
  cokernel.

## New code, and why no dependency supplies it
Object rows naming `A(n)` (the free ℤ-module with Gram matrix `CartanMatrix.A n`) and its dual
`A(n)^♯` (valued in ℚ), and the morphism family `to_dual : L → L^♯`, in the valued-forms category.
No dependency registers lattices as objects of a category of valued forms.
