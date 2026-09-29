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


open CategoryTheory CasCatalogue CasCatalogue.Foundation.Actions CasCatalogue.Foundation.Cardinality

def A : SetHandles := SetHandle.prod (.finite 2) (.zmod 3)
def Z : SetHandles := SetHandle.zmod 0
def F3 : SetHandles := SetHandle.finite 3
def revRev : F3 ⟶ F3 := InducedCategory.homMk (TypeCat.ofHom fun i : Fin 3 => i.rev.rev)

#eval method% cardinality (A) in "cat.sets"

#guard method% cardinality (A) in "cat.sets" == ⟨CardinalHandle.finite 6⟩

#eval (ask% is_finite (Z) in "cat.sets").answer

#guard (ask% is_finite (Z) in "cat.sets").answer == some false

#eval (refine% (A) in "cat.sets" to "cat.finite_sets").isSome

#guard (refine% (A) in "cat.sets" to "cat.finite_sets").isSome

#eval (eq% (revRev) (𝟙 F3) in "cat.sets").answer

#guard (eq% (revRev) (𝟙 F3) in "cat.sets").answer == some true

#eval (show List (Fin 3) from (cell% "cell.sets.list.reverse" at (F3) in "cat.sets").hom ([0, 1, 2] : List (Fin 3)))

#guard (show List (Fin 3) from (cell% "cell.sets.list.reverse" at (F3) in "cat.sets").hom ([0, 1, 2] : List (Fin 3))) == [2, 1, 0]

#resolve cardinality in "cat.finite_sets"

end CasDslTests.Cells
