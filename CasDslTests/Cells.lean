/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasDsl.Notebook
public meta import CasDsl.Notebook

@[expose] public section

/-!
# The demo notebook's cells, checked

Generated with `notebooks/demo.ipynb` by `scripts/demo_notebook.py`: every code cell of the
notebook elaborates here, with its expected value.
-/

namespace CasDslTests.Cells


open CategoryTheory CasCatalogue

#cas "assert ℤ ⊆ ℚ and ℚ ⊆ ℝ"

#cas "assert 2 + 3 = 0 in ℤ/5"

#cas "assert rev(3) ∘ rev(3) = id(Fin(3))"

#cas "assert |Fin(3)| = 3"

#resolve cardinality in "cat.finite_sets"

#methods "cat.finite_sets"

example : (cell% "cell.sets.list.reverse" ≫ "cell.sets.list.reverse"⁻¹ at (CasCatalogue.Foundation.Objects.integers) in "cat.sets") = 𝟙 _ := by simp

end CasDslTests.Cells
