"""Generate `notebooks/demo.ipynb` and `CasDslTests/Cells.lean` from one list of cells, so every
code cell of the demo notebook is elaborated, with its expected value, by `lake build CasDslTests`.

Run from the repository root: `python3 scripts/demo_notebook.py`.
"""

import json

CELLS = [
    ("md", "# CasDsl — computing through the categorical core\n\nEvery cell is a Lean command over "
     "the core's surfaces. A statement of the language names objects, operations and literals of "
     "the catalogue; it is read from the catalogue alone, then decided in Lean where Lean decides "
     "it, and otherwise computed by the installed leaves' registrations, whose answers are decoded "
     "and compared, never believed. The notebook package itself declares nothing."),
    ("code", "open CategoryTheory CasCatalogue"),
    ("md", "## What Lean decides needs no leaf\n\nThe catalogue's judgements and the arithmetic of "
     "`ℤ` and `ℤ/5` are proved by decision, checked by Lean's kernel."),
    ("code", "#cas \"assert ℤ ⊆ ℚ and ℚ ⊆ ℝ\""),
    ("code", "#cas \"assert 2 + 3 = 0 in ℤ/5\""),
    ("code", "#cas \"assert rev(3) ∘ rev(3) = id(Fin(3))\""),
    ("md", "## What a leaf computes is a gap until a registration answers it\n\n`|Fin(3)| = 3` is "
     "read as the cardinality functor applied to `Fin 3`; with no registration of "
     "`meth.cardinality` on `obj.sets.fin` installed it is reported as a gap, and with one it holds "
     "or is wrong."),
    ("code", "#cas \"assert |Fin(3)| = 3\""),
    ("md", "## Resolution is inspectable\n\nFinite sets reach `cardinality` along the forgetful "
     "functor of the finiteness classifier, and the operation surface of a category is computed "
     "from the catalogue."),
    ("code", "#resolve cardinality in \"cat.finite_sets\""),
    ("code", "#methods \"cat.finite_sets\""),
    ("md", "## Natural transformations: registered cells, composed\n\nList reversal, a natural "
     "automorphism of the list monad, composed with its inverse, is the identity at `ℤ`: a theorem "
     "about the registered isomorphism."),
    ("code", "example : (cell% \"cell.sets.list.reverse\" ≫ \"cell.sets.list.reverse\"⁻¹ at "
     "(CasCatalogue.Foundation.Objects.integers) in \"cat.sets\") = 𝟙 _ := by simp"),
    ("md", "## The suite\n\n`tests/acceptance/*.cas` states the rest in the same language: limits "
     "and colimits, polynomials, matrices, calculus. `lake build CasAcceptance.Suite` runs it, and "
     "`cas-harness --manifest leaves.json` runs it over a given leaves manifest."),
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
