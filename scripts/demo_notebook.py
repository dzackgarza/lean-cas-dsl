"""Generate `notebooks/demo.ipynb` and `CasDslTests/Cells.lean` from one list of cells, so every
code cell of the demo notebook is elaborated, with its expected value, by `lake build CasDslTests`.

Run from the repository root: `python3 scripts/demo_notebook.py`.
"""

import json

CELLS = [
    ("md", "# CasDsl — computing through the categorical core\n\nEvery cell is a Lean command over "
     "the core's surfaces. Values are handles of registered realizers; operations resolve along "
     "registered functors; results are Lean terms whose meaning is checked by the kernel. The "
     "notebook package itself declares nothing."),
    ("code", "open CategoryTheory CasCatalogue CasCatalogue.Foundation.Actions "
     "CasCatalogue.Foundation.Cardinality"),
    ("md", "Handles of the registered realization of sets: `Fin 2 × ℤ/3`, `ℤ`, `Fin 3`, and a map "
     "built as `rev ∘ rev`."),
    ("code", "def A : SetHandles := SetHandle.prod (.finite 2) (.zmod 3)\n"
     "def Z : SetHandles := SetHandle.zmod 0\n"
     "def F3 : SetHandles := SetHandle.finite 3\n"
     "def revRev : F3 ⟶ F3 := InducedCategory.homMk (TypeCat.ofHom fun i : Fin 3 => i.rev.rev)"),
    ("md", "## Methods by composition\n\n`cardinality` is owned by sets (on their core); it runs "
     "on the realization of the receiver."),
    ("code", "#eval method% cardinality (A) in \"cat.sets\""),
    ("guard", "method% cardinality (A) in \"cat.sets\" == ⟨CardinalHandle.finite 6⟩"),
    ("md", "## Properties are decided; refinements re-type the same object"),
    ("code", "#eval (ask% is_finite (Z) in \"cat.sets\").answer"),
    ("guard", "(ask% is_finite (Z) in \"cat.sets\").answer == some false"),
    ("code", "#eval (refine% (A) in \"cat.sets\" to \"cat.finite_sets\").isSome"),
    ("guard", "(refine% (A) in \"cat.sets\" to \"cat.finite_sets\").isSome"),
    ("md", "## Equality is the category's, three-valued\n\nOn an enumerated domain it is decided "
     "(`rev ∘ rev = id`); on `ℤ` it is undecided, never `false` for equal maps."),
    ("code", "#eval (eq% (revRev) (𝟙 F3) in \"cat.sets\").answer"),
    ("guard", "(eq% (revRev) (𝟙 F3) in \"cat.sets\").answer == some true"),
    ("md", "## Natural transformations: registered cells, evaluated\n\nList reversal, a natural "
     "automorphism of the list monad, at `Fin 3`."),
    ("code", "#eval (show List (Fin 3) from (cell% \"cell.sets.list.reverse\" at (F3) in "
     "\"cat.sets\").hom ([0, 1, 2] : List (Fin 3)))"),
    ("guard", "(show List (Fin 3) from (cell% \"cell.sets.list.reverse\" at (F3) in "
     "\"cat.sets\").hom ([0, 1, 2] : List (Fin 3))) == [2, 1, 0]"),
    ("md", "## Resolution is inspectable\n\nFinite sets reach `cardinality` along the forgetful "
     "functor of the finiteness classifier."),
    ("code", "#resolve cardinality in \"cat.finite_sets\""),
    ("md", "## Limits, colimits, adjunctions, backends\n\nThe acceptance probes run the rest through "
     "the same surfaces: pullbacks and coproducts of finite sets, products through `Δ ⊣ lim`, "
     "products of groups returned along the faithful forgetful functor, the discriminant of `A₂` "
     "as a registered cokernel of formed modules, and kernels and cardinalities computed by GAP "
     "and Sage through their leaves."),
]

HEADER = """/-
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
"""


def main() -> None:
    nb = {"cells": [], "metadata": {"kernelspec": {"display_name": "CasDsl (Lean 4)",
          "language": "lean4", "name": "casdsl"}, "language_info": {"name": "lean4"}},
          "nbformat": 4, "nbformat_minor": 5}
    test = [HEADER]
    for i, (kind, src) in enumerate(CELLS):
        if kind == "md":
            nb["cells"].append({"cell_type": "markdown", "id": f"c{i}", "metadata": {},
                                "source": src})
        elif kind == "code":
            nb["cells"].append({"cell_type": "code", "id": f"c{i}", "metadata": {},
                                "source": src, "outputs": [], "execution_count": None})
            test.append(src)
        else:
            test.append("#guard " + src)
    test.append("end CasDslTests.Cells")
    with open("notebooks/demo.ipynb", "w") as f:
        json.dump(nb, f, indent=1, ensure_ascii=False)
        f.write("\n")
    with open("CasDslTests/Cells.lean", "w") as f:
        f.write("\n\n".join(test) + "\n")


if __name__ == "__main__":
    main()
