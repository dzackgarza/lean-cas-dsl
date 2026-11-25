# Engine survey for the category implementations of lean-cas-dsl

Snapshot. All web sources and the container were read on 2026-11-25. Versions change; this record does not refresh itself.

## How to read this record

Each claim has an evidence mark.

| Mark | Meaning |
| --- | --- |
| [W Sn] | Read in a web source in this session. `Sn` is the source ID in the last section. |
| [C] | Verified in the container `sage-research` in this session, by a command or by a file listing. |
| [R] | Recalled. No source was read in this session. Verify before you rely on it. |
| [I] | Inference from marked facts. |

Some pages are longer than the reader limit of 100000 characters. For those pages the source list gives the part that was read. A claim with a [W] mark is about that part only.

"Lattice" has two meanings in this record. "Lattice (order)" is a poset with meets and joins. "Lattice (quadratic form)" is a finitely generated free $\mathbb{Z}$-module with a symmetric bilinear form.

## Container result

Command from the task:

```
DOCKER_HOST=unix:///run/user/$(id -u)/docker.sock $HOME/bin/docker exec -i sage-research bash -c 'python3 -m pip list 2>/dev/null | grep -i -E "passagemath|sage|sympy|gap|flint|pari|julia|oscar|macaulay|networkx|mpmath|singular" ; which gap julia M2 Singular gp maxima 2>/dev/null'
```

Output (exit status 0):

```
cypari2                            2.2.6
juliacall                          0.9.36
juliapkg                           0.1.28
mpmath                             1.3.0
networkx                           3.7
python-flint                       0.9.0
sage-categories                    0.1.0       /repos/sage-categories
sage-categories-homotopy           0.1.0       /repos/sage-categories/native/homotopy-python
sage-extensions                    0.1.0       /repos/sage-extensions
sage-indefinite-port               0.1.0       /repos/sage-indefinite-port
sage-julia-bridge                  0.1.0       /repos/sage-julia-bridge
sage-lsp                           0.3.3       /repos/sage-lsp-server
sage-mypy-category-plugin          0.0.0       /repos/sagemath-mypy-plugin
sage-stubs                         10.7.0      /repos/sage-stubs
sympy                              1.14.0
tree-sitter-sage                   0.5.1       /repos/tree-sitter-sage
/sage/.venv/bin/gap
/usr/local/bin/julia
/usr/bin/M2
/usr/bin/Singular
/sage/.venv/bin/gp
/sage/.venv/bin/maxima
```

The `sage-*` rows are local projects under `/repos`. They are not SageMath and not passagemath. The pip name `sage-categories` is a local package; it is not the Sage module `sage.categories`. [C]

More read-only probes in the same container gave these facts. [C]

| Item | Result |
| --- | --- |
| SageMath library | 11.0.beta5 (2026-10-28), built from source in `/sage`, importable as `sage` from `/sage/.venv/bin/python3`. pip does not list it. |
| Python | 3.14.10 |
| passagemath | Not installed |
| GAP | 4.16.1. `LoadPackage` gives `true` for `digraphs`, `CAP`; `TestPackageAvailability` is positive for `forms`, `recog`, `smallsemi`, `loops`, `hap`, `sonata`, `polycyclic`, `homalg`, `modulepresentationsforcap`, `orb`, `grape`, `images`. It is negative for `semigroups` and `kbmag`. `libgap.LoadPackage("semigroups")` returns `fail`. |
| Julia | 1.12.7. Default environment: Oscar 1.8.2, Hecke 0.39.22, Nemo 0.56.2, AbstractAlgebra 0.50.5, GAP.jl 0.17.11, Singular.jl 0.28.19, Polymake.jl 0.13.14. The depot also holds source for Catlab and PythonCall; Catlab is not in the default `Project.toml`. |
| Macaulay2 | 1.24.11 at `/usr/bin/M2`, with packages `Posets`, `Graphs`, `Polyhedra`, `LLLBases`, `Matroids`, `Complexes`, `Normaliz`, `InvariantRing`, `Python` |
| Singular | 4.4.1 (Jan 2025) |
| PARI/GP | 2.17.4 |
| Maxima | 5.49.0 (on ECL 26.5.5) |
| Other binaries | FriCAS 1.3.11, Giac 1.9.0, polymake 4.12, Normaliz 3.11.1, `latte-count`, `lrs`, `4ti2-hilbert`, Lean 4.36.0-rc2 with `lake` and `elan` |
| Other Python packages | z3-solver 5.3.3.0, fpylll 0.6.4, PyNormaliz 2.24, igraph 1.0.0, pplpy 0.9.0, pycddlib 3.0.2, lrcalc 2.1, primecountpy 0.2.1 |
| Not installed | `libsemigroups_pybind11`, `symengine`, `pynauty` (not in the pip list of the Sage environment) |
| python-flint build | `flint.__version__` is 0.9.0 and `flint.__FLINT_VERSION__` is 3.1.0 |
| Import cost | `from sage.all import *` took 11.2 s in one run |

Julia packages were not loaded, because a load can start precompilation and the task excludes builds. The load time of Oscar through `juliacall` is not measured.

## Candidate table

Date checked is 2026-11-25 for each row. "Upstream" is the newest release found. "Container" is the installed state.

| Name | Upstream version (date) | License | Source URL | Python access | Container |
| --- | --- | --- | --- | --- | --- |
| SageMath | 10.10 (2026-09-28) [W S2] | GPL-2.0-or-later [W S1] | https://github.com/sagemath/sage | Native Python. PyPI `sagemath` 10.10 has a source distribution only [W S1]. | Yes, 11.0.beta5 from source [C] |
| passagemath | 10.8.14 (2026-11-16) [W S1] | GPL-2.0-or-later [W S1, S9] | https://github.com/passagemath/passagemath | Native Python. Wheels for Linux and macOS, Python 3.11 to 3.14 [W S1, S9]. | No [C] |
| SymPy | 1.14.0 (2025-04-27) [W S1] | BSD (3-clause text) [W S1, S65] | https://github.com/sympy/sympy | Native Python | Yes, 1.14.0 [C] |
| Oscar.jl | 1.8.2 (2026-09-02) [W S2] | GPL-3.0-or-later [W S65] | https://github.com/oscar-system/Oscar.jl | Julia, through `juliacall` | Yes, 1.8.2 [C] |
| Nemo.jl | 0.57.2 (2026-11-02) [W S2] | Mixed; see `LICENSE.md` [W S65]. Main text BSD 2-clause [R]. | https://github.com/Nemocas/Nemo.jl | Julia, through `juliacall` | Yes, 0.56.2 [C] |
| AbstractAlgebra.jl | 0.51.4 (2026-11-13) [W S2] | `LICENSE.md` permits distribution as a whole under GPL v3+ [W S65]. Own text BSD 2-clause [R]. | https://github.com/Nemocas/AbstractAlgebra.jl | Julia, through `juliacall` | Yes, 0.50.5 [C] |
| Hecke.jl | 0.41.2 (2026-11-16) [W S2] | BSD 2-clause [W S65] | https://github.com/thofma/Hecke.jl | Julia, through `juliacall` | Yes, 0.39.22 [C] |
| PythonCall.jl / `juliacall` | 0.9.37 (2026-10-19) [W S1] | MIT [W S2] | https://github.com/JuliaPy/PythonCall.jl | It is the bridge. It can use an existing Julia through `PYTHON_JULIACALL_EXE` and `PYTHON_JULIACALL_PROJECT` [W S44]. | Yes, 0.9.36 [C] |
| GAP | 4.16.1 (2026-08-23) [W S2, S32] | GPL-2.0 [W S2]; "or later" [R] | https://github.com/gap-system/gap | Sage `libgap` (in process) [W S22]; Sage pexpect interface; `passagemath-gap`; `gappy`; GAP.jl inside Julia | Yes, 4.16.1 [C] |
| GAP package Semigroups | 5.7.1 (2026-11-11) [W S33] | GPL-3.0-or-later [W S33] | https://github.com/semigroups/Semigroups | Through GAP | Not loadable [C] |
| GAP package Digraphs | 1.15.0 (2026-07-06) [W S34] | GPL-3.0-or-later [W S34] | https://github.com/digraphs/Digraphs | Through GAP | Loadable [C] |
| CAP project (GAP packages) | CAP 2026.10-01 [W S56] | GPL-2.0-or-later [W S56] | https://github.com/homalg-project/CAP_project | Through GAP | Loadable [C] |
| `gappy` (`gappy-system`) | 0.1.0a3 (2021-02-15); last push 2024-06-07 [W S1, S2] | GPL-3.0 [W S35] | https://github.com/embray/gappy | Native Python on libgap. Alpha, stale [I]. | No [C] |
| `passagemath-gap` | 10.8.14 [W S1] | GPL-2.0-or-later [W S1] | https://pypi.org/project/passagemath-gap/ | Wheel with GAP, `libgap` interface, pexpect interface, and GAP packages. Extras for `semigroups`, `smallsemi`, `hap`, `polycyclic` and others [W S10]. | No [C] |
| Macaulay2 | 1.26.06 (2026-06-10) [W S45] | GPL: "either version 2 of the License, or"; the end of that sentence was not read [W S46] | https://github.com/Macaulay2/M2 | Separate process. Sage interface `sage.interfaces.macaulay2`; `passagemath-macaulay2` wheel ships M2 [W S10]; `macaulay2-jupyter-kernel` 0.8.2 [W S1]. The M2 package `Python` calls Python from M2, not M2 from Python [R]. | Yes, 1.24.11 [C] |
| python-flint | 0.9.0 (2026-07-03) [W S1] | MIT AND LGPL-3.0-or-later [W S1] | https://github.com/flintlib/python-flint | Native Python (wheels) | Yes, 0.9.0 on FLINT 3.1.0 [C] |
| FLINT | 3.6.0 (2026-06-29) [W S2] | LGPL-3.0 [W S2] | https://github.com/flintlib/flint | python-flint; Sage; Nemo | Yes, inside Sage and python-flint [C] |
| PARI/GP | 2.19.1 (2026-11-14) [W S48] | GPL-2.0-or-later [W S48] | https://pari.math.u-bordeaux.fr/ | `cypari2` (in process); Sage | Yes, 2.17.4 [C] |
| `cypari2` | 2.2.9 (2026-11-22), needs Python 3.13 or later [W S1] | GPL-2.0-or-later [W S1] | https://github.com/sagemath/cypari2 | Native Python | Yes, 2.2.6 [C] |
| Singular | 4.4.1p5 (2026-02-16) [W S2] | GPL version 2 or version 3 [W S55] | https://github.com/Singular/Singular | Sage libSingular (in process) and pexpect; Singular.jl; `passagemath-singular` wheel; `PySingular` 0.9.7 from 2019 [W S1, S10] | Yes, 4.4.1 [C] |
| Maxima | 5.50.0 (2026-08-17) [W S54] | GPL [W S53] | https://maxima.sourceforge.io/ | Sage `maxima_lib` (in process on ECL) and pexpect `maxima` [W S10]; `passagemath-maxima` wheel | Yes, 5.49.0 [C] |
| mpmath | 1.4.1 (2026-03-15) [W S1] | BSD-3-Clause [W S1] | https://github.com/mpmath/mpmath | Native Python | Yes, 1.3.0 [C] |
| NetworkX | 3.7 (2026-09-21) [W S1] | BSD-3-Clause [W S1, S65] | https://github.com/networkx/networkx | Native Python | Yes, 3.7 [C] |
| hex (Lean 4) | Tag v0.10.0; no GitHub release objects [W S2] | Apache-2.0 [W S2] | https://github.com/leanprover/hex | None found. The README shows Lean use only [W S3]. | Not checked. Lean 4.36.0-rc2 is present [C]. |
| sagebrush | 0.10.3 (2026-11-21) [W S1] | (MIT OR Apache-2.0) AND Artistic-2.0 [W S1] | https://github.com/sagemathinc/sagebrush | Native Python wheel `pip install sagebrush`; also an MCP server [W S5] | No [C] |
| Lean 4 and Mathlib | 4.36.0 (2026-11-16) [W S2] | Apache-2.0 [W S2] | https://github.com/leanprover/lean4 | None directly; the kernel of lean-cas-dsl is the Lean side | Lean 4.36.0-rc2 [C] |
| CompPoly (Lean) | No release read; last push 2026-11-20 [W S2] | Apache-2.0 [W S2] | https://github.com/Verified-zkEVM/CompPoly | None | Not checked |
| LeanSage, lean-m2 | Last push 2026-10-09 and 2025-06-07 [W S2] | MIT; not stated [W S2] | https://github.com/oOo0oOo/LeanSage , https://github.com/riyazahuja/lean-m2 | They call Sage or M2 from Lean; the direction is opposite to the Python SDK [W S64] | Not checked |
| FriCAS | 1.4.0 (2026-10-16) [W S2, S58] | Modified BSD [W S58] | https://github.com/fricas/fricas | Separate process. Sage interface `sage.interfaces.fricas` [C]; `passagemath-fricas` exists [W S1] | Yes, 1.3.11 [C] |
| Giac | Upstream not checked. `giacpy` 0.7.5 (2026-01-10) [W S1] | GPLv2 or later (`giacpy`) [W S1] | http://www.imj-prg.fr/~frederic.han/xcas/giacpy/ | Sage `libgiac`; `giacpy`; `passagemath-giac` [W S1] | Yes, 1.9.0 [C] |
| SymEngine | 0.15.0 (2026-08-26); `symengine` wheel 0.15.0 [W S1, S2] | MIT [W S1, S63] | https://github.com/symengine/symengine.py | Native Python wheel | No [C] |
| galgebra | 0.6.0 (2026-04-01) [W S1] | BSD-3-Clause [W S2] | https://github.com/pygae/galgebra | Native Python on SymPy [W S63] | Not checked |
| Normaliz / PyNormaliz | 3.11.1 / 2.24 (2026-02-02) [W S1, S2] | GPL-3.0 [W S59] | https://github.com/Normaliz/Normaliz | `PyNormaliz` (in process) | Yes, both [C] |
| polymake | 4.15 (2025-09-30) [W S2] | GPL [W S65] | https://github.com/polymake/polymake | Polymake.jl inside Julia; Sage interface; `JuPyMake` 0.9 from 2019; `passagemath-polymake` [W S1] | Yes, 4.12 [C] |
| lrslib | 7.3 (page dated 2024-05-31) [W S61] | GPL [W S61] | https://cgm.cs.mcgill.ca/~avis/C/lrs.html | None found; `pylrs` is not on PyPI [W S1, S61] | Yes, `lrs` binary [C] |
| fplll / fpylll | 5.5.0 (2024-11-12) / 0.6.4 (2025-05-29) [W S1, S2] | LGPL-2.1 / GPLv2+ [W S2, S62] | https://github.com/fplll/fpylll | Native Python | Yes, fpylll 0.6.4 [C] |
| LattE integrale | 1.7.6 (2021-03-18) [W S2] | GPL [W S63] | https://github.com/latte-int/latte | Separate process; `passagemath-latte-4ti2` [W S1] | Yes, `latte-count` [C] |
| e-antic / pyeantic | 2.1.1 (2026-06-14) [W S2] | LGPL-3.0-or-later [W S63] | https://github.com/flatsurf/e-antic | `pyeantic` through cppyy; not on PyPI [W S1, S63] | Not checked |
| Catlab.jl | 0.17.7 (2026-11-24) [W S2] | MIT [W S2] | https://github.com/AlgebraicJulia/Catlab.jl | Julia, through `juliacall` | Source in depot; not in default environment [C] |
| `libsemigroups_pybind11` | 1.4.4 (2026-05-08), wheels [W S1] | GPL-3.0-or-later [W S1] | https://pypi.org/project/libsemigroups-pybind11/ | Native Python | No [C] |
| z3-solver | 5.4.1.0 (2026-11-11) [W S1] | MIT [W S1] | https://github.com/Z3Prover/z3 | Native Python | Yes, 5.3.3.0 [C] |
| pynauty | 2.8.8.1 (2024-06-06) [W S1] | GPLv3 [W S1] | https://github.com/pdobsan/pynauty | Native Python | No [C] |

Name traps: the PyPI projects `oscar` and `pyoscar` are not the OSCAR computer algebra system [W S1]. Magma is proprietary and is not a candidate; Sage has an interface file for it [C].

## What "hex" and "sagebrush" are

### hex

"hex" is `leanprover/hex`: "Verified computational algebra in Lean 4: an aggregator for the released hex libraries" [W S3]. Development is in the monorepo `kim-em/hex-dev` (created 2026-04-22; `leanprover/hex` created 2026-06-24) [W S2]. Confidence: high. The GitHub search for Lean repositories named "hex" returns this project and its split libraries, and the Lean package registry lists `@leanprover/hex` [W S64].

Facts from the README, which was read in full [W S3]:

- Each computational library is free of Mathlib. Correspondence proofs with Mathlib are in separate `*-theory` libraries.
- Use is from Lean: a `[[require]]` entry in `lakefile.toml`, then `import Hex` and `#eval`.
- Released components: foundations, truncated power series, exact word arithmetic, CRT and rational reconstruction, certified primality, ECPP certificates, dense and sparse univariate polynomials, fast dense algorithms, modular arithmetic, sparse multivariate polynomials, matrices, polynomials over $\mathbb{F}_p$, integer polynomials, quotient rings $\mathbb{F}_p[x]/(f)$, Hensel lifting, complex and real root isolation, row reduction, factorization over finite fields, Conway polynomials, finite fields, packed $\mathrm{GF}(2)$ polynomials, canonical finite fields, determinants (Leibniz and Bareiss), Gram-Schmidt, LLL, factorization of integer polynomials (Berlekamp-Zassenhaus), permutation groups, graph canonical labelling, resultants and discriminants, algebraic numbers, number field towers, and a decision tactic `rcf` for real closed fields.
- The LLL library has an optional fpLLL foreign-function interface [W S2 repository description].
- `lean-toolchain` on `main` is `leanprover/lean4:v4.35.0-rc3` [W S2].

Consequences [I]: hex is the only candidate that computes inside Lean. It has no Python entry, no category framework, and no sets, orders, semigroups, modules as objects, quadratic forms beyond LLL and Gram matrices, or calculus. It is less than one year old. It is a candidate for the Lean side of a check, not for a Python-driven category implementation.

### sagebrush

"sagebrush" is `sagemathinc/sagebrush`: "Fast, certified, parallel engines for research mathematics in Rust, usable from Python and JavaScript (early experiment)" [W S2, S5]. The README calls it "an early experiment from the founder of SageMath". The repository was created on 2026-10-02 [W S2]. Confidence: high for the identification. It is the only mathematics project among the GitHub repositories named "sagebrush", and it names Sage compatibility as a goal. I have no statement from the owner that this is the project meant.

Facts from the README, which was read in full [W S5]:

- Pure Rust engines, no C libraries, no GPL code linked. License MIT OR Apache-2.0; the wheel also holds Cremona curve data under Artistic-2.0.
- `pip install sagebrush` gives a wheel of about 7 MB for Python 3.10 or later. `from sagebrush.sage import *` gives Sage names in plain Python. `from sagebrush import nf, mf, ap, poly, linalg, modsym` gives the engines.
- Engines: modular symbols and newforms; $a_p$ of elliptic curves; number fields, class groups and units; integer factoring; Hermite and Smith normal forms; exact LLL; matrices over $\mathbb{Z}$ and $\mathbb{Q}$ (determinant, solve, inverse, echelon form, rank, kernel, characteristic polynomial); polynomials over $\mathbb{Z}$, $\mathbb{Z}/n$, $\mathbb{Q}$; multivariate polynomials with Gröbner bases over $\mathbb{Q}$; Galois groups; permutation groups (order, membership, orbits, stabilizers, blocks, derived series); symbolic calculus (`diff`, `limit`, `integrate`, `taylor`, `series`, `solve`, `desolve`).
- Each result has a status: proven, conditional on GRH, or heuristic.
- The limit engine gives the Sage answer on 61 of 62 textbook limits. The integrator finds at least 167 of 171 first-year integrals.

The Sage name index `lib/_sage_names.py` on `master` was searched in full. It has entries for `Set`, `Subsets`, `Permutations`, `Partitions`, `PolynomialRing`, `MatrixSpace`, `PermutationGroup`, `GF`, `Zmod`, `Hom`, `VectorSpace`, `Graph`, `limit`, `integrate`. It has no entry for `Poset`, `LatticePoset`, `Sets`, `Magmas`, `Semigroups`, `Monoids`, `Category`, `FreeMonoid`, `AbelianGroup`, `FreeModule`, `IntegralLattice`, `QuadraticForm`, `TorsionQuadraticModule`, `cartesian_product` [W S5].

Consequences [I]: sagebrush has a real Python entry and a permissive license. It has no category framework and no orders, semigroups, quadratic modules, or lattices (quadratic form). It is an early experiment. It does not meet the "mature" requirement now. It is a possible later fallback for linear algebra over $\mathbb{Z}$ and $\mathbb{Q}$, polynomials, permutation groups, and calculus.

### Other Lean-native computation

- Mathlib is a proof library. Its polynomials are not a practical computation type; a 2025 Zulip thread says so [W S64]. Mathlib has `Finset`, `Cardinal`, `Ordinal` as proof objects [R].
- CompPoly: "Computable Polynomials in Lean" [W S2].
- MonomialOrderedPolynomial: a verified data structure for polynomial identity tests, on Mathlib types [W S64].
- LeanSage and lean-m2 send computation from Lean to Sage or Macaulay2 [W S64].
- The search found no general Lean 4 computer algebra system with a stable release other than hex [W S64].

## Cross-cutting layer: parents, morphisms, functors

This layer decides which engine can be the frame for all families.

| Engine | What it has |
| --- | --- |
| Sage | A category framework with axioms, functors, maps, homsets, morphisms, and "Coercion via construction functors" (`pushout`) [W S6]. Functorial constructions: Cartesian product, tensor product, signed tensor product, dual, algebra functor, subquotient, quotient, subobject, isomorphic object, homset categories, realizations [W S6]. Categories present for Sets, Magmas, Semigroups, Monoids, Groups, Semirings, Rings, Rngs, Commutative rings, Fields, Modules, Algebras, Posets, Lattice posets, Finite sets, Enumerated sets, Pointed sets, Sets with partial maps, G-sets, Groupoid, Additive magmas, Partially ordered monoids, and many more [W S6]. No category for quadratic or bilinear modules, Boolean algebras, or cardinals [W S6][C]. |
| passagemath | The same framework as a wheel. `passagemath-categories` holds structure, coercion, categories and functorial constructions, sets, basic rings ($\mathbb{Z}$, $\mathbb{Q}$, $\mathbb{Z}/n$), commutative polynomials, power series [W S10]. |
| AbstractAlgebra.jl | Documented interfaces: ring, Euclidean ring, univariate polynomial ring, field, module, map, linear solving. Maps: functional maps, cached maps, map with inverse [W S43]. No set, order, semigroup or category objects seen [W S43]. |
| GAP | Domains, collections, mappings (chapter 32), relations (33), orderings (34), then one chapter for each algebraic structure [W S32]. Filters and categories of objects are a type system, not a category of morphisms [R]. |
| CAP (GAP) | "Algorithmic Category Theory". Packages for Cartesian categories, monoidal categories, Freyd categories, category of matrices over a field, category of module presentations, additive closures, groups as categories, a compiler for categorical algorithms [W S56]. Kernels, cokernels and limits are primitives [R]. |
| Catlab.jl | "A framework for applied and computational category theory". The category of finite sets, product and coproduct, equalizer and coequalizer, pushouts, C-sets, functors, data migration [W S57]. |
| SymPy `sympy.categories` | "Still in its pre-embryonic stage". Abstract objects, morphisms and diagrams for drawing; no computation [W S27]. |
| FriCAS | A fork of Axiom [W S58]. Axiom has a category and domain type system with `SetCategory`, `Monoid`, `Group`, `Ring`, `Field`, `Module` [R]. |

Conclusion [I]: Sage (or passagemath) is the only surveyed engine with a Python entry whose own structure follows the categorical scaffolding of the task. It is the natural frame. Other engines supply operations to it.

## Category families

Each table gives the operations that an engine supplies natively. Names are API names. A blank cell means "nothing found in the sources read".

### Sets

| Operation | Sage | SymPy | GAP | Other |
| --- | --- | --- | --- | --- |
| Constructors | `Set`, `FiniteEnumeratedSet`, `Family`, `ConditionSet`, `RealSet`, `IntegerRange`, `NonNegativeIntegers`, `PositiveIntegers`, `Primes`, `DisjointUnionEnumeratedSets`, `RecursivelyEnumeratedSet`, set from iterator [W S8]; `image_set.py` present [C] | `FiniteSet`, `Interval`, `Range`, `ImageSet`, `ConditionSet`, `Naturals`, `Integers`, `Rationals`, `Reals`, `Complexes`, `EmptySet`, `UniversalSet`, `ComplexRegion` [W S23] | Lists and strictly sorted lists (chapter 21), collections (30), domains (31) [W S32] | Maxima sets `{a,b}` [C]; Catlab `FinSet` [W S57] |
| Union, intersection, difference | Methods of `Set` [R] | `Union`, `Intersection`, `Complement`, `SymmetricDifference`, `DisjointUnion` [W S23] | `Union`, `Intersection`, `Difference` [R] | PARI `setunion`, `setintersect`, `setminus`, `setdelta`, `setbinop` [W S49] |
| Equality, membership, inclusion | `is_parent_of`, `__contains__`, element equality tests `_test_elements_eq_symmetric`, `_test_elements_eq_transitive` [W S7] | `contains`, `is_subset`, `is_superset`, `is_proper_subset`, `is_disjoint` [W S23]; `FiniteSet(1,2) == FiniteSet(2,1)` is true [C] | `in`, `IsSubset`, `=` [R] | Maxima `subsetp` [C]; PARI `setsearch`, `setisset` [W S49] |
| Cardinality | `cardinality`, `is_finite`, `is_empty` [W S7]; infinite sets give `+Infinity` [C] | `len` for finite sets, `is_finite_set` [C]; `len(S.Naturals)` raises `TypeError` [C] | `Size` [R] | Maxima `cardinality` [C] |
| Maps, composition, application | `Hom(A, B)` in `Sets()` [C]; base class for maps, homsets, morphisms [W S6]; `FiniteSetMaps` [W S8][C] | `ImageSet` [W S23]; `Lambda` [R] | Chapter 32 Mappings [W S32]; `CompositionMapping`, `Image`, `PreImage` [R] | Catlab `FinFunction` [R] |
| Image, kernel pair, quotient | `Sets.MorphismMethods`: `image`, `is_injective` [W S7]; `Sets().Quotients()`, `Subquotients()`, `Subobjects()`, `IsomorphicObjects()` [W S7]; disjoint-set structure [W S8] | | Chapter 33 Relations [W S32]; equivalence classes [R] | |
| Products, limits, colimits | `cartesian_product` with `cartesian_projection`, `cartesian_factors` [W S7]; disjoint union [W S8] | `ProductSet`, `DisjointUnion` [W S23] | `Cartesian` [R] | Catlab: product, coproduct, equalizer, coequalizer, pushout [W S57]; CAP `CartesianCategories` [W S56]; Maxima `cartesian_product` [C] |
| Enumeration | Iteration, `an_element`, `some_elements` [W S7] | Lazy iteration of `Naturals`, `Integers`, `Rationals`, `ImageSet` [W S23] | `Enumerator`, `Iterator` [R] | |
| Canonical form | | Automatic normal form of unions and intervals: `Union(Interval(0,1), Interval(1,2))` gives `Interval(0, 2)` [C] | Strictly sorted list [R] | |

Recommendation. Primary: Sage (`sage.categories.sets_cat`, `sage.sets`). Reasons: it has parents, elements, maps and homsets for sets; infinite sets are lazy; the category framework already names the functorial constructions. Fallback: SymPy sets for symbolic subsets of number sets (intervals, condition sets, image sets), because SymPy simplifies them and Sage does not [I]. A second engine (Catlab or CAP) is necessary only if the interface includes equalizers, pullbacks, coequalizers or pushouts as constructors.

### Finite sets, countable sets, enumerated sets

| Operation | Sage | SymPy | GAP / other |
| --- | --- | --- | --- |
| Constructors | Categories "Finite sets", "Enumerated sets", "Finite Enumerated Sets", "Infinite Enumerated Sets" [W S6]; `Sets().Finite().Enumerated()` [C]; `FiniteEnumeratedSet`, `RecursivelyEnumeratedSet`, totally ordered finite sets [W S8] | `FiniteSet`, `Range` [W S23] | GAP lists; Catlab `FinSet` [W S57] |
| Cardinality and finiteness | `cardinality` [C]; `NN` is in "facade infinite enumerated commutative semirings" [C] | `len` [C] | `Size`, `IsFinite` [R] |
| Enumeration | Iteration; `rank`, `unrank`, `first`, `next` of enumerated sets [R] | Lazy iteration of infinite sets; `Range` with infinite start cannot be iterated [W S23] | `Enumerator`, `Iterator` [R] |
| Maps | `FiniteSetMaps(A, B)` with `cardinality` [C]; `Hom(A, B)` [C] | | GAP `Tuples`, mappings [R] |
| Subsets and combinatorial sets | `Subsets(A).cardinality()` [C]; permutations and combinations are in `passagemath-categories` [W S10] | `powerset` [C]; `sympy.combinatorics` subsets, partitions, Gray code [W S24] | GAP chapter 16 Combinatorics [W S32] |
| Canonical form | Totally ordered finite sets [W S8] | Sorted `FiniteSet` [R] | Sorted lists [R] |

Recommendation. Primary: Sage. Fallback: SymPy. One engine covers the interface. Countability of an infinite set is a category membership in Sage (`InfiniteEnumeratedSets`), not a computed cardinal [I].

### Pointed sets

| Operation | Sage | Other |
| --- | --- | --- |
| Category | `PointedSets()` exists [W S6][C]. The file `pointed_sets.py` defines `super_categories` only [C]. | |
| Base point, pointed maps, wedge, smash | Nothing in the category [C]. Sage simplicial sets have pointed versions with wedge and smash [R]. | |
| Partial maps | `SetsWithPartialMaps` exists; it defines `super_categories` only [C]. | |

Recommendation. Primary: Sage sets with a stored base point. The interface of pointed sets (base point, base-point preserving maps, product, wedge, smash) is small glue over the Sets implementation. No engine supplies it directly; see the gaps.

### Boolean algebras and power sets

| Operation | Sage | SymPy | Other |
| --- | --- | --- | --- |
| Power set | `Subsets(S)` [C]; `posets.BooleanLattice(n)` [C] | `PowerSet`, `FiniteSet.powerset()` [W S23][C] | Maxima `powerset` [C]; M2 `booleanLattice` [W S46][C] |
| Meet, join, complement | `meet`, `join`, `complements`, `is_complemented`, `is_distributive` of `LatticePoset` [W S12][C] | `And`, `Or`, `Not`, `Xor`, `Nand`, `Nor`, `Implies`, `Equivalent`, `ITE` [W S26] | GAP chapter 20 Booleans [W S32] |
| Equality and equivalence of terms | `propcalc.formula(...).equivalent(...)`, `is_satisfiable` [C]; modules `propcalc`, `boolformula`, `booleval`, `logictable`, `logicparser` [W S18] | `satisfiable`, `bool_map`, `truth_table` [W S26][C] | z3 [C] |
| Canonical forms | Boolean polynomial rings (`pbori`) give algebraic normal form [C: file present][R] | `to_cnf`, `to_dnf`, `to_anf`, `SOPform`, `POSform`, `ANFform`, `simplify_logic` [W S26] | Binary decision diagrams: `dd` 0.6.0 on PyPI [W S1] |
| Morphisms, quotients, products | Lattice `quotient`, `congruence`, `sublattice`, poset `product` [W S11, S12] | | |
| Enumeration and cardinality | `Subsets(S).cardinality()` [C] | `len(powerset)` [C] | |

Recommendation. Primary: Sage, for power sets and finite Boolean lattices as lattice posets, and `sage.logic` for propositional terms. Fallback: SymPy `sympy.logic.boolalg` for normal forms of Boolean terms; z3 for large satisfiability problems. Sage has no category of Boolean algebras [W S6][C]; the category layer is glue.

### Cardinals

| Operation | Sage | SymPy | Other |
| --- | --- | --- | --- |
| Finite cardinals | `cardinality()` gives an `Integer` [C] | `len` [C] | Every engine |
| Infinite cardinals | `ZZ.cardinality()` and `RR.cardinality()` both give `+Infinity` of type `PlusInfinity` [C]. No cardinal class in the Sage source tree [C]. | No cardinal class [C]. `sympy.sets.ordinals` has `Ordinal`, `OmegaPower`, `omega` with ordinal arithmetic in Cantor normal form: `1 + omega` gives `w`, `omega*2 + 3` gives `w*2 + 3` [C]. | Mathlib `Cardinal` as a proof object [R] |
| Cardinal arithmetic, comparison | | | |

Recommendation. Finite cardinals: Sage `Integer`. Infinite cardinals: no surveyed engine supplies them. This family cannot be glue over an engine now. Options for the owner [I]: restrict the first implementation to finite cardinals plus a formal symbol for each named infinite cardinal with no arithmetic, or keep infinite cardinal arithmetic on the Lean side where Mathlib has the theory.

### Order structures (posets, lattices in the order sense)

| Operation | Sage | GAP Digraphs | Macaulay2 `Posets` | Oscar | NetworkX |
| --- | --- | --- | --- | --- | --- |
| Constructors | `Poset`, `LatticePoset`, `MeetSemilattice`, `JoinSemilattice`; categories Posets, Lattice posets, Finite posets, Finite lattice posets [W S6, S11, S12] | Digraph that is a partial order [W S34] | `poset`, `booleanLattice`, `chain`, `divisorPoset`, `partitionLattice` [W S46] | `partially_ordered_set`, `partially_ordered_set_from_inclusions`, `face_poset`, `lattice_of_flats` [W S37] | `DiGraph` [W S51] |
| Comparison, covers | `is_lequal`, `is_less_than`, `compare_elements`, `covers`, `upper_covers`, `lower_covers` [W S11] | | | | `ancestors`, `descendants` [W S51] |
| Meet, join | `meet`, `join`, `meet_matrix`, `join_matrix` [W S11, S12][C] | `PartialOrderDigraphMeetOfVertices`, `PartialOrderDigraphJoinOfVertices` [W S34][C] | `posetMeet`, `posetJoin` [W S46] | Not on the page [W S37] | None; `lowest_common_ancestor` only [W S51][C] |
| Predicates | `is_join_semilattice`, `is_meet_semilattice`, `is_chain`, `is_graded`, `is_bounded`, `is_distributive`, `is_modular`, `is_complemented` [W S11, S12] | `IsPartialOrderDigraph`, `IsPreorderDigraph`, `IsLatticeDigraph`, `IsMeetSemilatticeDigraph`, `IsDistributiveLatticeDigraph`, `IsModularLatticeDigraph` [W S34][C] | `isLattice`, `isDistributive`, `isModular`, `isGraded`, `isBounded` [W S46][C] | | `is_directed_acyclic_graph` [W S51] |
| Cardinality, enumeration | `cardinality`, `list`, `linear_extensions`, `chains`, `antichains`, `maximal_chains` [W S11] | | `linearExtensions`, `chains`, `antichains` [W S46][C] | `elements`, `maximal_chains`, `atoms`, `coatoms` [W S37] | `antichains`, `topological_sort`, `all_topological_sorts` [W S51] |
| Ideals, filters, intervals | `order_ideal`, `order_filter`, `interval`, `open_interval` [W S11] | | `orderIdeal`, `filter` [W S46] | | |
| Products, duals, sums | `product`, `dual`, `disjoint_union`, `ordinal_sum`, `ordinal_product`, `subposet`, `completion_by_cuts` [W S11] | | `product`, `dual`, `subposet` [W S46] | | |
| Quotients, congruences | Lattice `quotient`, `congruence`, `congruences_lattice`, `sublattice` [W S12] | | | | |
| Isomorphism, canonical form | `is_isomorphic`, `canonical_label` [W S11] | Automorphism group and canonical labelling [R] | `areIsomorphic`, `isomorphism` [W S46] | | `is_isomorphic` [C] |
| Invariants | `moebius_function`, `zeta_polynomial`, `characteristic_polynomial`, `order_polytope` [W S11] | | `moebiusFunction`, `zetaPolynomial` [W S46] | `order_polytope`, `chain_polytope` [W S37] | `transitive_closure`, `transitive_reduction`, `antichain_width` [W S51] |

Limits of the engines: Oscar posets must have a rank function and unique minimal and maximal elements (artificial nodes can be added) [W S37]. NetworkX has no poset type [W S51]. SymPy has no poset module in its combinatorics index [W S24].

Recommendation. Primary: Sage posets (`sage.combinat.posets`). It covers the whole finite interface. Fallback: GAP Digraphs through `libgap`, then Macaulay2 `Posets`. NetworkX is useful only as a graph layer below Sage. One engine is sufficient for finite orders. Order-preserving maps as objects are glue; see the gaps.

### Magmas, semigroups, monoids

| Operation | GAP | Sage | Other |
| --- | --- | --- | --- |
| Constructors | Chapters 35 Magmas, 36 Words, 37 Associative words, 38 Rewriting systems, 51 Semigroups and monoids, 52 Finitely presented semigroups and monoids, 53 Transformations, 54 Partial permutations [W S32]; `MagmaByMultiplicationTable`, `Monoid(...)` of transformations [C] | Categories Magmas, Semigroups, Monoids, Finite semigroups, Finite monoids, finitely generated, aperiodic, H/J/L/R-trivial [W S6]; `FreeMonoid`, `FreeAbelianMonoid`, indexed, string, trace, plactic, Hecke monoids, `AutomaticSemigroup` [W S13]; `Magmas().example()` is a free magma [C] | Semigroups package: transformations, partial permutations, bipartitions, matrices over semirings, finitely presented [W S33]; `libsemigroups_pybind11` [W S1]; Normaliz for affine monoids [W S59][C] |
| Product, identity | `*`, `MultiplicativeNeutralElement` [C] | `product`, `one` [W S14] | |
| Predicates | `IsAssociative`, `IsCommutative`, `IsGroup`, `IsRegularSemigroup` [C] | Category axioms; `TestSuite` [W S7] | Semigroups: regular, simple and other properties [W S33] |
| Cardinality, enumeration | `Size`, `Idempotents` [C] | `AutomaticSemigroup`: `cardinality`, `list`, `construct`, `cayley_graph`, `idempotents`, `j_classes` [W S14] | |
| Membership | `in` [R] | `retract` raises `ValueError` for a non-member; it can loop for an infinite semigroup [W S14] | |
| Morphisms, kernels, quotients | Mappings; congruences in the kernel library [R] | `lift`, `retract`, `ambient` [W S14] | Semigroups: congruences, ideals, Green's structure, presentations, maximal subsemigroups [W S33] |
| Products | `DirectProduct` [R] | Cartesian product functor [W S6] | |
| Canonical forms | Rewriting systems, chapter 38 [W S32] | `reduced_word` (shortest in length-lexicographic order) [W S14] | |
| Limits | | `AutomaticSemigroup` is "designed primarily for finite semigroups" [W S14]. It is not in the global namespace of `sage.all` [C]. | Semigroups package is not loadable in the container [C]. |

Recommendation. Primary: GAP (kernel library plus the Semigroups package), called through Sage `libgap`. Reasons: only GAP has finite magmas from a table, transformation and finitely presented semigroups, rewriting systems, congruences and Green's relations. Fallback: Sage `sage.monoids` (free, automatic, trace monoids) and `libsemigroups_pybind11`. The Sage categories give the frame; GAP gives the operations. Two layers, one Python entry.

### Groups

| Operation | GAP | Sage (GAP inside) | Oscar | SymPy |
| --- | --- | --- | --- | --- |
| Constructors | Chapters 39 Groups, 42 Permutations, 43 Permutation groups, 44 Matrix groups, 45 Polycyclic groups, 46 Pc groups, 47 Finitely presented groups, 50 Group libraries [W S32] | Permutation, matrix, free, finitely presented, braid, Artin, abelian, additive abelian, semidirect product, affine groups [W S20] | Groups: basics, kinds of groups, libraries [W S36] | `PermutationGroup`, named groups, finitely presented groups, polycyclic groups [W S24] |
| Order, membership, predicates | `Size`, `in`, `IsAbelian` [R] | `order`, `is_abelian` [R] | | `contains`, `is_subgroup`, `is_normal`, `is_abelian`, `is_solvable`, `is_nilpotent`, `is_transitive`, `is_primitive` [W S28]; `order` [C] |
| Homomorphisms, kernel, image | Chapter 40 Group homomorphisms [W S32]; `GroupHomomorphismByImages`, `Kernel`, `Image` [C] | "Group homomorphisms for groups with a GAP backend", "Kernel Subgroups", "Permutation group homomorphisms", "Homomorphisms of abelian groups" [W S20] | "Group homomorphisms" [W S36] | `homomorphism(...)` with `kernel`, `image`, `is_surjective` [C] |
| Quotients, products | `G/N`, `DirectProduct` (chapter 49 Group products) [W S32][C] | Semidirect product, direct product [W S20] | "Quotient groups", "Products" [W S36] | `DirectProduct` [W S28] |
| Subgroups and series | Derived series, centre, Sylow subgroups [R] | Conjugacy classes, class functions [W S20] | "Subgroups", "Characters", "Tables of Marks" [W S36] | `derived_series`, `lower_central_series`, `composition_series`, `center`, `centralizer`, `normal_closure`, `coset_table` [W S28] |
| Enumeration | `Elements`, `ConjugacyClasses` [R] | Iteration [R] | | `generate`, `elements`, `conjugacy_classes` [W S28] |
| Canonical forms | Presentations and Tietze transformations (chapter 48), rewriting systems (38) [W S32] | Canonical labels by partition backtrack [W S20] | | |

Other engines: hex has verified permutation-group algorithms [W S3]. sagebrush has permutation groups with proven orders by a deterministic Schreier-Sims test [W S5].

Recommendation. Primary: GAP through Sage (`sage.groups` and `libgap`). Reason: coverage and maturity; Sage group classes already wrap it. Fallback: Oscar (the same GAP kernel through GAP.jl, plus Hecke finitely generated abelian groups with morphisms [W S36]). SymPy is a pure-Python fallback for small permutation groups. One engine covers the interface.

### Semirings

| Operation | Sage | GAP Semigroups | Other |
| --- | --- | --- | --- |
| Constructors | Category Semirings [W S6][C]; `NonNegativeIntegerSemiring` with category "facade infinite enumerated commutative semirings" [C]; tropical semiring, tropical polynomials and matrices (files in `sage/rings/semirings`) [C]; a "Semirings" section in the reference [W S19] | Matrices over semirings: Boolean matrices, matrices over finite fields, certain tropical matrices [W S33] | Oscar has a Tropical Geometry part [W S36] |
| Operations, predicates | Parent and element arithmetic [R] | | |
| Morphisms, quotients, ideals | | | |

Recommendation. Primary: Sage. It has the category and the two standard examples. Fallback: GAP Semigroups for finite semirings of matrices. Homomorphisms, congruences and quotients of semirings are not supplied by any engine in the sources read; see the gaps. Rings are semirings; the ring engines apply to that part.

### Rings and commutative rings

| Operation | Sage | Oscar / AbstractAlgebra | Macaulay2 / Singular | Other |
| --- | --- | --- | --- | --- |
| Constructors | Categories Rings, Rngs, Commutative rings, Domains, Integral domains, GCD domains, UFDs, PIDs, Euclidean domains, Dedekind domains, Noetherian rings, Division rings [W S6]; integers, rationals, finite rings, p-adics, polynomial and power series rings, noncommutative polynomials, quaternion algebras [W S19] | Rings: integers, univariate and multivariate polynomials, Euclidean rings, series rings [W S36]; AbstractAlgebra: generic residue rings, total ring of fractions, free associative algebras, a universal ring [W S43] | Singular: "polynomial computations, with special emphasis on commutative and non-commutative algebra, algebraic geometry, and singularity theory" [W S55]; Macaulay2: "research in algebraic geometry and commutative algebra" [W S45] | GAP chapter 56 Rings [W S32]; python-flint `fmpz`, `fmpq`, `nmod`, `fmpz_mod` [W S47]; SymPy domains and `old_poly_ring` [C] |
| Ideals | Categories Ring ideals, Commutative ring ideals [W S6]; Gröbner bases through Singular [R] | Commutative Algebra: ideals, affine algebras, localizations, Gröbner bases [W S36]; AbstractAlgebra ideals [W S43] | Ideal arithmetic, primary decomposition [R] | SymPy `Ideal`: `contains`, `intersect`, `quotient`, `saturate`, `product`; many property tests not implemented [W S25][C] |
| Membership, equality | Parent and coercion framework [W S6] | Ring interface [W S43] | | |
| Homomorphisms, kernels, quotients | Ring homomorphisms, quotient rings [R] | Affine algebra homomorphisms [R] | `map`, `kernel` [R]; kernel and image of a module map ran [C] | |
| Products | Cartesian product functor [W S6] | | | |
| Canonical forms | Normal forms modulo Gröbner bases [R] | Gröbner bases [W S36] | Gröbner bases [R] | |

Recommendation. Primary: Sage. It has the generic layer and calls FLINT, Singular, PARI and NTL. Fallback: Oscar for commutative algebra (localizations, affine algebras) and Macaulay2 for homological commutative algebra. One engine covers the standard interface.

### Fields

| Operation | Sage | Oscar / Nemo / Hecke | Other |
| --- | --- | --- | --- |
| Constructors | Categories Fields, Finite fields, Number fields, Quotient fields, Function fields, complete discrete valuation fields [W S6]; real and complex numbers, finite rings and fields, p-adic numbers, number fields, function fields [W S19] | Fields: rationals, local fields, finite fields, algebraic and real or complex number fields [W S36]; AbstractAlgebra: fraction fields, rational function fields, finite fields, real field [W S43] | GAP chapters 58 Fields and division rings, 59 Finite fields, 60 Abelian number fields, 18 Cyclotomic numbers [W S32]; python-flint `fq_default`, `arb`, `acb` [W S47]; PARI [W S48]; e-antic for real embedded number fields [W S63] |
| Arithmetic, equality | Exact [R] | Exact [R] | Ball arithmetic in `arb`, `acb` [R] |
| Morphisms, extensions | Embeddings, extensions [R] | Number field maps [R] | hex number field towers [W S3] |
| Enumeration, cardinality | Finite fields iterate [R] | | |
| Canonical forms | Conway polynomials [R] | | hex Conway polynomials and canonical finite fields [W S3] |

Other engines: sagebrush has number fields with class groups and units [W S5]. hex has verified finite fields and algebraic numbers [W S3].

Recommendation. Primary: Sage. Fallback: Oscar (Nemo and Hecke), which is the strongest free engine for number fields [R]. python-flint is a light fallback for prime fields, finite fields and ball arithmetic. One engine covers the interface.

### Modules

| Operation | Sage | Oscar / AbstractAlgebra / Hecke | Macaulay2 | SymPy | CAP |
| --- | --- | --- | --- | --- | --- |
| Constructors | Categories Modules, Modules with basis, Vector spaces, finite dimensional modules with basis, graded and filtered modules, bimodules, left and right modules [W S6]; "Vectors and Modules", "Tensors on Free Modules of Finite Rank" [W S19]; finitely generated modules over a PID (`fg_pid`) [C: file present] | AbstractAlgebra: finitely presented modules, free modules and vector spaces, submodules, quotient modules, direct sums, module homomorphisms [W S43]; Oscar: Linear Algebra modules and Commutative Algebra modules with homological algebra [W S36]; Hecke abelian groups with morphisms [W S36] | Modules over polynomial rings [R] | `FreeModule`, `SubModule`, `QuotientModule`, `SubQuotientModule` [W S25] | Category of module presentations; category of matrices over a field [W S56] |
| Homomorphisms, kernel, image | Module morphisms; `right_kernel` of a matrix [C] | Module homomorphisms [W S43] | `kernel`, `image` [C] | `homomorphism`, `kernel`, `image`, `is_injective`, `is_surjective`, `quotient_domain`, `restrict_codomain` [W S25][C] | Kernels and cokernels as primitives [R] |
| Quotients, sums, tensor products | Quotient modules; tensor product and Cartesian product functors [W S6] | Quotient modules, direct sums [W S43] | `coker`, `Hom`, `Ext`, `Tor` [R] | `module_quotient`, `intersect`, `syzygy_module` [W S25] | |
| Membership, equality | Submodule membership [R] | | | `contains` [W S25] | |
| Canonical forms | Echelon basis, Smith form: `elementary_divisors` [C] | Matrix normal forms [W S43] | Gröbner bases of modules [R] | | |
| Limits | | | | "Useful functionality is only implemented for polynomial rings over fields"; free modules of finite rank only [W S25] | |

Recommendation. Two engines are necessary. Primary: Sage for modules over $\mathbb{Z}$, fields, $\mathbb{Z}/n$ and modules with basis. Second engine: Oscar (or Macaulay2) for finitely presented modules over polynomial rings and their homological operations. CAP is the closest match to a categorical interface (kernels, cokernels, lifts as primitives), with GAP as its host.

### Algebras

| Operation | Sage | GAP | Other |
| --- | --- | --- | --- |
| Constructors | Categories Algebras, Algebras with basis, Associative algebras, Commutative algebras, Unital algebras, Lie algebras, Hopf algebras, Group algebras, Monoid algebras, Matrix algebras, Semisimple algebras, graded, filtered and super variants [W S6]; "Algebras", "Quaternion Algebras", "Noncommutative Polynomials" [W S19] | Chapters 62 Algebras, 63 Finitely presented algebras, 64 Lie algebras [W S32] | Oscar: Noncommutative Algebra, Lie Theory, matrix spaces and algebras [W S36]; AbstractAlgebra free associative algebras, matrix algebras [W S43]; galgebra for geometric algebra on SymPy [W S63] |
| Functorial construction | "Group algebras and beyond: the Algebra functorial construction"; `Sets().Algebras(base_ring)` [W S6, S7] | | |
| Ideals, quotients, morphisms | Algebra ideals categories [W S6] | | |

Recommendation. Primary: Sage. It has the widest set of algebra categories and the algebra functor from sets, monoids and groups. Fallback: GAP for finite-dimensional algebras given by structure constants and for Lie algebras; Oscar and Hecke for algebras over number fields. One engine covers the standard interface.

### Polynomial rings

| Operation | Sage | python-flint | Oscar / Singular / Macaulay2 | SymPy |
| --- | --- | --- | --- | --- |
| Constructors | "Commutative Polynomials", "Power Series and Laurent Series", "Noncommutative Polynomials" [W S19]; commutative polynomials are in `passagemath-categories` [W S10] | `fmpz_poly`, `fmpq_poly`, `nmod_poly`, `fmpz_mod_poly`, `fq_default_poly`, `arb_poly`, `acb_poly`; multivariate `fmpz_mpoly`, `fmpq_mpoly`, `nmod_mpoly`, `fmpz_mod_mpoly`; series types [W S47] | Univariate and multivariate polynomials, Gröbner bases [W S36] | `Poly`, `groebner` [C] |
| Arithmetic, gcd, factorization | [R] | `factor` ran on `fmpz_poly` [C] | [R] | [R] |
| Ideals, quotient rings, evaluation maps | Through Singular [R] | None [I] | Yes [W S36] | `old_poly_ring(...).ideal(...).contains` [C] |
| Canonical forms | Gröbner bases, normal forms [R] | Factorization into irreducibles [C] | Gröbner bases [W S36] | `GroebnerBasis` [C] |

Other engines: hex has verified dense, sparse and multivariate polynomials, Hensel lifting, factorization over $\mathbb{F}_p$ and $\mathbb{Z}$, resultants [W S3]. sagebrush has polynomials over $\mathbb{Z}$ and $\mathbb{Q}$ and Gröbner bases over $\mathbb{Q}$ [W S5]. AbstractAlgebra has univariate and multivariate polynomials, generic Laurent polynomials and a universal ring [W S43].

Recommendation. Primary: Sage. Fallback: python-flint for arithmetic, gcd and factorization with no Sage import (MIT wrapper, fast, light). Oscar or Singular for heavy Gröbner computations. One engine covers the interface.

### Bilinear and quadratic modules

| Operation | Sage | Hecke / Oscar | PARI | GAP |
| --- | --- | --- | --- | --- |
| Constructors | `QuadraticForm` and related modules: binary forms, ternary forms, constructions, genus, p-adic normal forms, `qfsolve` [W S21]; `TorsionQuadraticModule` [W S16]; free quadratic modules [C: files present] | Number Theory: quadratic and hermitian forms: spaces, lattices, integer lattices, genera, discriminant groups [W S36]; `torsion_quadratic_module` [W S40] | Gram matrices [W S49] | Package `forms` is available [C]; forms over finite fields [R] |
| Evaluation | `b`, `q`, `inner_product`, `quadratic_product` on torsion modules [W S16] | `gram_matrix_bilinear`, `gram_matrix_quadratic` [W S40] | `qfeval` [W S49] | |
| Invariants | `brown_invariant`, `genus`, `is_genus`, `value_module`, `value_module_qf` [W S16] | `brown_invariant`, `genus`, `is_genus`, `is_degenerate`, `radical_bilinear`, `radical_quadratic`, `value_module`, `modulus_bilinear_form` [W S40] | `qfsign`, `qfgaussred`, `qfjacobi`, `qfcholesky` [W S49][C] | |
| Canonical forms | `normal_form`; "Normal forms for p-adic quadratic and bilinear forms" [W S16, S21] | `normal_form` [W S40] | `qfgaussred` [W S49] | |
| Isometry tests | | `is_isometric_with_isometry`, `is_anti_isometric_with_anti_isometry` [W S40] | `qfisom` for positive definite forms [W S49][C] | |
| Submodules, orthogonal complements, sums | `orthogonal_submodule_to`, `primary_part`, `submodule_with_gens`, `all_submodules`, `twist` [W S16] | `orthogonal_submodule`, `direct_sum`, `submodules`, `stable_submodules`, `rescale`, `cover`, `relations`, `lift` [W S40] | | |
| Morphisms | | `TorQuadModuleMap` is a return type [W S40] | | |
| Solving | "Solving quadratic equations" [W S21] | | `qfsolve`, `qfparam` [W S49] | |

Recommendation. Primary: Sage, because it is native Python and has torsion quadratic modules, genera and normal forms. Second engine: Hecke through Oscar. It is necessary for quadratic and hermitian spaces over number fields, isometry tests with an explicit isometry, and maps of torsion quadratic modules. Sage has no category for quadratic modules [W S6][C]; that layer is glue.

### Lattices (quadratic forms)

| Operation | Sage | Hecke / Oscar | PARI | Other |
| --- | --- | --- | --- | --- |
| Constructors | `IntegralLattice`, `IntegralLatticeDirectSum`, `IntegralLatticeGluing`, `local_modification` [W S15] | `integer_lattice`, `root_lattice`, `hyperbolic_plane_lattice`, `hyperkaehler_lattice`, `k3_lattice`, `leech_lattice`, `mukai_lattice`, `rescale`, `direct_sum`, `biproduct` [W S39] | Gram matrix [W S49] | |
| Invariants | `signature`, `signature_pair`, `is_even`, `is_primitive`, `genus`, `discriminant_group`, `quadratic_form`, `minimum`, `maximum` [W S15] | `rank`, `det`, `scale`, `norm`, `level`, `iseven`, `is_integral`, `is_definite`, `signature_tuple`, `mass`, `genus_representatives` [W S39] | `qfsign` [W S49] | |
| Sublattices, overlattices | `sublattice`, `overlattice`, `maximal_overlattice`, `orthogonal_complement`, `dual_lattice`, `direct_sum`, `tensor_product`, `twist` [W S15] | `orthogonal_submodule`, `primitive_closure`, `dual`, `glue_map`, `overlattice`, `primitive_extension`, `maximal_integral_lattice`, `kernel_lattice`, `invariant_lattice`, `coinvariant_lattice`, `irreducible_components`, `intersect`, `embed`, `embed_in_unimodular` [W S39] | | |
| Membership, equality | | `is_sublattice`, `is_sublattice_with_relations`, `in`, `divisibility` [W S39] | | |
| Isometry tests | | `is_isometric`, `is_locally_isometric`; no definiteness condition stated [W S39] | `qfisom` (positive definite) [W S49][C] | |
| Isometry group | `orthogonal_group`: "Currently, we can only compute the orthogonal group for positive definite lattices" [W S15]; the indefinite case raises `NotImplementedError` [C]; order of $O(A_2)$ is 12 [C] | Hecke `automorphism_group_generators`, `automorphism_group_order`: "Given a definite lattice" [W S39]; Oscar `isometry_group(L::ZZLat)`: "definite or of rank 2" [W S42] | `qfauto` (positive definite), `qfautoexport`, `qforbits` [W S49][C] | |
| Reduction, short vectors | `LLL`, `short_vectors`, `enumerate_short_vectors`, `enumerate_close_vectors` [W S15] | `lll`, `short_vectors`, `shortest_vectors`, `close_vectors`, `kissing_number`, `vectors_of_square_and_divisibility` [W S39] | `qflll`, `qflllgram`, `qfminim`, `qfcvp`, `qfrep` [W S49] | python-flint `fmpz_mat.lll()` [C]; fpylll LLL and BKZ [W S62]; hex verified LLL [W S3] |
| Root lattices | | `root_lattice_recognition`, `ADE_type`, `coxeter_number`, `highest_root` [W S39] | | |
| Lattices with isometry, embeddings | | `ZZLatWithIsom`, enumeration of isometry classes, `primitive_embeddings`, equivariant primitive extensions [W S41]; "Vinberg's algorithm" is a sidebar entry [W S36]; `image_in_Oq` is in the source [W S42] | | |

Other engines: GAP chapter 25 "Integral matrices and lattices" [W S32]. Normaliz, LattE and 4ti2 count and list lattice points of polyhedra; that is a different object [W S59, S63].

Recommendation. Two engines are necessary. Primary: Sage (`IntegralLattice`), the Python-native parent with genus and discriminant group. Second engine: Hecke through Oscar, for mass and genus representatives, isometry tests without a definiteness condition, root lattice recognition, lattices with isometry, primitive embeddings, and Vinberg. PARI is the kernel for the definite case in both. No engine returns generators of $O(L)$ for an indefinite lattice of rank 3 or more; see the gaps.

### Calculus: limits, series, derivatives, integrals

| Operation | SymPy | Sage symbolic ring | Maxima | mpmath | Other |
| --- | --- | --- | --- | --- | --- |
| Limits | `limit` gave 1 for $\sin(x)/x$ at 0 [C]; "Limits of Sequences" page [W S30] | `limit` gave 1 [C] | `limit` [R] | Numeric `limit` [C] | sagebrush `limit` [W S5] |
| Series | `series` with order term [C]; series expansions, sequences, Fourier series, formal power series [W S30] | `.series` [C]; `taylor` [R] | Series expansions [W S53] | "Sums, products, limits and extrapolation" [W S52] | python-flint series types [W S47]; SymEngine [R] |
| Derivatives | `diff` [C] | `diff` [C] | Yes [W S53] | Numeric `diff` [C] | |
| Integrals | `integrate` tries `ratint`, `trigintegrate`, `deltaintegrate`, `singularityintegrate`, `risch_integrate`, Meijer G-functions, `manualintegrate`, `heurisch`. The Risch part "only supports a small subset of the full algorithm" [W S31] | `integrate(..., algorithm=...)`; integrators in `external.py`: `maxima_integrator`, `sympy_integrator`, `mma_free_integrator`, `fricas_integrator`, `libgiac_integrator` [C] | Integrals, Laplace transforms, differential equations [W S53] | `quad` [C] | FriCAS [W S58]; Giac [C]; sagebrush integrator, each answer checked by differentiation [W S5] |
| Sums | `summation` gave $\pi^2/6$ [C] | `sum` gave $\pi^2/6$ [C] | | `nsum` [C] | |
| Unevaluated forms | `Limit`, `Integral`, `Derivative`, `Sum` objects [R] | Held operations [R] | Noun forms [R] | | |

Recommendation. Primary: SymPy. Reasons: native Python, BSD license, inspectable expression trees, unevaluated objects, no second process. Fallback: the Sage symbolic ring, which sends the same request to Maxima, FriCAS or Giac; use it where SymPy returns an unevaluated integral or limit. mpmath gives numeric checks. Two engines are necessary for integrals in practice, because the SymPy Risch part is partial [W S31].

### Linear algebra: vectors, matrices, kernels, determinants

| Operation | Sage | python-flint | SymPy | PARI | Other |
| --- | --- | --- | --- | --- | --- |
| Constructors | "Matrices and Spaces of Matrices", "Vectors and Modules" [W S19]; matrix over $\mathbb{Z}$ [C] | `fmpz_mat`, `fmpq_mat`, `nmod_mat`, `fmpz_mod_mat`, `arb_mat`, `acb_mat` [W S47] | `Matrix`; dense, sparse, immutable, matrix expressions, normal forms [W S29] | Matrices [W S49] | AbstractAlgebra matrices, matrix spaces, matrix algebras [W S43]; GAP chapters 23 Row vectors, 24 Matrices, 61 Vector spaces [W S32] |
| Determinant, rank | `det` [C] | `det` [C] | `det`, `rank` [C] | `matdet`, `matrank` [W S49] | hex determinants (Leibniz, Bareiss) [W S3]; mpmath `det` [C] |
| Kernel, image | `right_kernel().basis()` [C] | `nullspace` [C] | `nullspace` [C] | `matker`, `matkerint`, `matimage`, `matsupplement`, `matintersect` [W S49][C] | M2 `kernel`, `image` [C]; hex row reduction and nullspace [W S3] |
| Solving | [R] | [R] | [R] | `matsolve`, `matinverseimage` [W S49] | AbstractAlgebra linear solving interface [W S43] |
| Normal forms | `elementary_divisors` [C]; echelon, Hermite, Smith [R] | `hnf`, `snf`, `lll` [C] | `smith_normal_form`, `hermite_normal_form` [C] | `mathnf`, `matsnf`, `matfrobenius` [W S49][C] | sagebrush Hermite, Smith, LLL [W S5] |
| Characteristic data | [R] | [R] | [R] | `charpoly`, `minpoly`, `mateigen` [W S49] | |
| Maps between spaces | Homsets of free modules [R] | None [I] | None [I] | None [I] | CAP category of matrices over a field [W S56] |

Recommendation. Primary: Sage. It has vector spaces and modules as parents, linear maps as morphisms, and any base ring. Fallback: python-flint for exact matrices over $\mathbb{Z}$, $\mathbb{Q}$, $\mathbb{Z}/n$, finite fields and balls. One engine covers the interface.

### Group-valued constructions: orthogonal groups, automorphism groups, stabilizers

| Construction | GAP | Sage | Oscar | Other |
| --- | --- | --- | --- | --- |
| Classical orthogonal groups over finite fields | `GO(e, d, q)`; `Size(GO(1,4,3))` is 1152 [C] | "Orthogonal Linear Groups", "Orthogonal Linear Groups with GAP", symplectic and unitary groups [W S20] | [R] | |
| Isometry group of a lattice | | `orthogonal_group` for definite lattices; it accepts given generators for a subgroup, also for indefinite lattices [W S15]; "Groups of isometries" [W S20] | `isometry_group` for lattices that are definite or of rank 2; algorithm choice `:direct` and others [W S42] | PARI `qfauto` [W S49][C] |
| Orthogonal group of a torsion quadratic module | | `TorsionQuadraticModule.orthogonal_group`; with no generators "a slow brute force approach is used"; the order for the discriminant group of $A_2$ is 2 [W S16][C]; module `sage.groups.fqf_orthogonal` present [C] | `orthogonal_group(T::TorQuadModule)` in `src/Groups/abelian_aut.jl` [W S42] | |
| Automorphism group of a group | `AutomorphismGroup`; order 24 for $S_4$ [C] | "Automorphisms of abelian groups" [W S20]; `libgap` [C] | [R] | |
| Automorphism group of a combinatorial object | Digraphs [R] | "Automorphism groups and canonical labels" by partition backtrack [W S20]; poset `canonical_label` [W S11] | | hex verified graph canonical labelling [W S3]; pynauty [W S1] |
| Stabilizers, orbits, actions | Chapter 41 Group actions [W S32]; `Stabilizer` [C] | `stabilizer` of a permutation group [C] | `stabilizer`, `orbit`, `orbits`, `gset`, `action_homomorphism`, `on_tuples`, `on_sets`, `on_lines`, `on_subgroups`, `blocks`, `is_transitive`, `is_primitive` [W S38] | SymPy `stabilizer`, `orbit` [C][W S28]; sagebrush orbits and stabilizers [W S5] |

Recommendation. Primary: GAP through Sage. It supplies the group object, actions, stabilizers and automorphism groups, and the Sage examples for lattice isometry groups need `sage.libs.gap` [W S15]. Second engine: Oscar, for isometry groups with algorithm choice, orthogonal groups of torsion quadratic modules as automorphism groups of abelian groups, and stabilizers in lattice computations. PARI is the kernel for definite lattices.

## Recommendation summary

| Family | Primary | Fallback or second engine | Engines needed |
| --- | --- | --- | --- |
| Sets | Sage | SymPy sets; Catlab or CAP for general limits and colimits | 1 (2 with general limits) |
| Finite, countable, enumerated sets | Sage | SymPy | 1 |
| Pointed sets | Sage sets plus glue | None | 1 plus glue |
| Boolean algebras, power sets | Sage | SymPy `boolalg`; z3 | 1 |
| Cardinals | Sage `Integer` for finite | None for infinite | Gap |
| Order structures | Sage posets | GAP Digraphs; Macaulay2 `Posets` | 1 |
| Magmas, semigroups, monoids | GAP (with Semigroups) through `libgap` | Sage `sage.monoids`; `libsemigroups_pybind11` | 1 behind the Sage frame |
| Groups | GAP through Sage | Oscar; SymPy | 1 |
| Semirings | Sage | GAP Semigroups | 1; morphisms are a gap |
| Rings, commutative rings | Sage | Oscar; Macaulay2 | 1 |
| Fields | Sage | Oscar (Nemo, Hecke); python-flint | 1 |
| Modules | Sage | Oscar or Macaulay2 for modules over polynomial rings; CAP | 2 |
| Algebras | Sage | GAP; Oscar and Hecke | 1 |
| Polynomial rings | Sage | python-flint; Oscar or Singular | 1 |
| Bilinear and quadratic modules | Sage | Hecke through Oscar | 2 |
| Lattices (quadratic forms) | Sage | Hecke through Oscar; PARI | 2 |
| Calculus | SymPy | Sage symbolic ring to Maxima, FriCAS, Giac; mpmath | 2 for integrals |
| Linear algebra | Sage | python-flint | 1 |
| Group-valued constructions | GAP through Sage | Oscar; PARI | 2 for lattice groups |

## Gaps

Each row is a negative finding. "Conclusion" is an inference.

| Gap | Searched | Found | Conclusion | Confidence | Unknown |
| --- | --- | --- | --- | --- | --- |
| Infinite cardinals and their arithmetic | Sage source tree in the container (search for a cardinal class or "aleph" in `.py` and `.pyx` files); Sage sets index [S8]; runs of `ZZ.cardinality()` and `RR.cardinality()`; SymPy package search for "aleph" or a cardinal class; `len(S.Naturals)` | Sage gives `+Infinity` for both. No cardinal class in Sage or SymPy; the search hits are in LaTeX printing and tests. SymPy has ordinals. | No surveyed engine supplies infinite cardinals. | Medium | GAP, Oscar, Macaulay2 and Maxima were not searched for this. A small dedicated package can exist. |
| Operations of pointed sets (base point, pointed maps, wedge, smash) | `pointed_sets.py` and `sets_with_partial_maps.py` in the container; Sage categories index [S6] | Each category defines `super_categories` only. | The category is a label. The operations are glue over Sets. | Medium | Catlab and CAP were not checked for coslice categories. |
| Equalizers, pullbacks, coequalizers, pushouts of sets in Sage or SymPy | Sets category page [S7] (first 100000 of 137075 characters); Sage sets index [S8]; SymPy sets page [S23] | Cartesian products, disjoint unions, quotients and subobjects as category constructions. No constructor for the four limits. Catlab names them for finite sets [S57]. | A second engine or glue is necessary for general limits in sets. | Medium | The last 37075 characters of [S7] were not read. |
| A category of bilinear or quadratic modules | Sage categories index [S6]; listing of `sage/categories` in the container | No such category. Objects exist as classes. | The category layer for these families is glue; operations come from Sage and Hecke. | High for Sage | The Hecke type hierarchy was not read in source. |
| A category of Boolean algebras | Sage categories index [S6]; listing of `sage/categories`; SymPy logic page [S26] | None. SymPy describes propositional logic, not Boolean algebras in general. | The category layer is glue over lattice posets and formulas. | High for Sage | Infinite Boolean algebras were not searched. |
| Generators of $O(L)$ for an indefinite lattice $L$ of rank 3 or more | Sage lattice page [S15] and a run in the container; Hecke lattice page [S39]; Oscar source docstring [S42]; PARI page [S49] | Sage: `NotImplementedError`. Hecke: definite only. Oscar: definite or rank 2. PARI: positive definite. | No surveyed engine supplies this directly. Partial tools: Oscar `image_in_Oq` and Vinberg's algorithm. | High for these four; medium in general | The local project `sage-indefinite-port` in the container was not inspected. GAP and Macaulay2 were not searched. The meaning of `image_in_Oq` is recalled, not read. |
| Homomorphisms, congruences and quotients of semirings | Listing of `sage/rings/semirings`; Sage categories index [S6]; Semigroups page [S33] | A category, the semiring of non-negative integers, tropical objects, matrices over semirings in GAP. No morphism or quotient API seen. | Glue is necessary for the morphism side. | Low | The category file `semirings.py` and the tropical modules were not read. |
| Order-preserving maps as objects with composition | Sage posets page [S11] (first 100000 of 257505 characters); Oscar posets page [S37]; NetworkX page [S51] | No morphism entry in the Sage summary tables. No map functions in Oscar or NetworkX. | Glue: a set map plus a monotonicity check. | Medium | The last 157505 characters of [S11]. Predicates for poset morphisms in the Sage category are recalled to exist. The Digraphs homomorphism finder is recalled, not read. |
| Finite magma from a multiplication table in Sage | Sage monoids index [S13]; categories index [S6] | Free and automatic structures only. GAP has `MagmaByMultiplicationTable` [C]. | Use GAP for this constructor. | Medium | Sage operation tables were not read. |
| Infinite posets | [S11], [S37] | Sage constructors on the page are finite posets. Oscar posets are finite and ranked. | Infinite orders are glue over a comparison function. | Medium | The `Posets()` category methods for facade posets were not read. |
| A Python entry for hex | hex README in full [S3]; hex manual front page [S4] | Lean use only. | hex cannot be driven from the Python SDK without a new bridge. | High for the README | Other manual chapters were not read. |
| Sets, orders, semigroups, quadratic modules in sagebrush | README in full [S5]; `lib/_sage_names.py` in full | No such names except `Set`, `Subsets`. | sagebrush does not cover these families now. | Medium | The engine crates and the documentation site were not read. |

## Constraints for planning

1. **One `sage` package for each environment.** The container has SageMath 11.0.beta5 built from source [C]. passagemath installs the same top-level package `sage` (its examples import `sage.interfaces.maxima` and `sage.features`) and its README asks for a fresh virtual environment [W S9, S10]. The two cannot share an environment [I]. A choice is necessary: the container Sage, or passagemath in a separate environment.
2. **passagemath is the pip-installable route.** PyPI `sagemath` 10.10 and `sagemath-standard` 10.7 are source distributions only [W S1]. passagemath 10.8.14 has wheels and needs Python 3.11 to 3.14 [W S1]. Its version number is in the 10.8 line [I], while the container has 11.0.beta5 [C].
3. **Engines that pip cannot install.** Oscar, Nemo, Hecke, AbstractAlgebra and Catlab come from the Julia package manager; `juliacall` can use an existing Julia and project [W S44]. Lean and hex come through `elan` and `lake`. `pyeantic` and `pylrs` are not on PyPI [W S1]. `gappy-system` (2021 alpha), `PySingular` (2019) and `JuPyMake` (2019) are stale [W S1]. passagemath distributions exist for GAP, Macaulay2, Singular, Maxima, FriCAS, Giac, polymake, and LattE with 4ti2 [W S1]. The wheels for GAP, Macaulay2, Singular and Maxima ship the binaries [W S10]; the content of the other four was not read. Without passagemath these engines are system packages.
4. **Engines that run as a separate process.** Macaulay2 (pexpect interface) [W S10]; FriCAS; the pexpect interfaces of GAP, Singular and Maxima [W S10]; polymake outside Julia; LattE, lrs, 4ti2 binaries [C]; Lean and hex. In-process engines: Sage libraries, `libgap` [W S22], `maxima_lib` [W S10], libSingular [W S10], `cypari2`, python-flint, PyNormaliz, fpylll, and Julia through `juliacall`.
5. **Single-instance rules.** The Sage `Gap` object "must be instantiated exactly once" [W S22]. `juliacall` multi-threading "is experimental"; Julia needs its own signal handling for threads, and then Ctrl-C does not raise `KeyboardInterrupt` [W S44]. Oscar loads its own GAP, Singular and FLINT libraries inside Julia; a Python process that also has Sage then holds two copies of each [I]. This was not tested. The local project `sage-julia-bridge` exists in the container [C] and was not inspected.
6. **Missing GAP package.** Semigroups is not loadable in the container [C]. It is the main engine for semigroups and monoids. `passagemath-gap[semigroups]` supplies it in the passagemath route [W S10]. In the container, the install is a change to the image.
7. **Version drift in the container.** Upstream is newer for PARI (2.19.1 against 2.17.4), Macaulay2 (1.26.06 against 1.24.11), Maxima (5.50.0 against 5.49.0), FriCAS (1.4.0 against 1.3.11), polymake (4.15 against 4.12), mpmath (1.4.1 against 1.3.0), Hecke (0.41.2 against 0.39.22), Nemo (0.57.2 against 0.56.2), AbstractAlgebra (0.51.4 against 0.50.5), cypari2 (2.2.9 against 2.2.6), z3 (5.4.1.0 against 5.3.3.0). python-flint 0.9.0 is linked to FLINT 3.1.0; FLINT upstream is 3.6.0 [W S1, S2][C].
8. **Lean toolchain.** hex `main` pins Lean 4.35.0-rc3 [W S2]. The container has Lean 4.36.0-rc2 [C]. The project instructions of lean-cas-dsl name Lean 4.33.0 for the kernel branch. A hex dependency adds a toolchain constraint.
9. **Licenses.** Copyleft (GPL family): SageMath, passagemath, GAP and its packages, CAP, Singular, Macaulay2, Maxima, PARI, cypari2, Oscar, Singular.jl, Normaliz, polymake, fpylll, LattE, lrslib, Giac, `libsemigroups_pybind11`, pynauty. Weak copyleft: FLINT, GAP.jl, Polymake.jl, fplll, e-antic. Permissive: SymPy, mpmath, NetworkX, python-flint wrapper, Hecke, PythonCall, Catlab, SymEngine, galgebra, FriCAS, z3, hex, Lean, Mathlib, sagebrush. Nemo and AbstractAlgebra have mixed license files [W S65]; their main text is recalled as BSD 2-clause [R]. The Giac license itself was not read; `giacpy` is GPLv2 or later [W S1]. No candidate is proprietary. Glue that imports a GPL engine in process and is then distributed must follow the GPL [I]. Magma is proprietary and is not used. The Sage integrator `mma_free_integrator` calls an external web service [R].
10. **Maturity.** hex and sagebrush were both created in 2026 [W S2]. sagebrush calls itself an early experiment [W S5]. The task requires mature computation; these two do not qualify now [I].
11. **Start-up cost.** `from sage.all import *` took 11.2 s in one container run [C]. Oscar load time through `juliacall` was not measured.

## Sources

Web sources, read on 2026-11-25.

| ID | Source | Part read |
| --- | --- | --- |
| S1 | PyPI JSON API, `https://pypi.org/pypi/<name>/json`, for each PyPI name in this record | Version, license, upload date, Python requirement, package types |
| S2 | GitHub API through `gh`: latest release or tag, license, creation and push dates, descriptions, for each repository URL in the candidate table; `lean-toolchain` of https://github.com/leanprover/hex ; repository search for "hex" (Lean) and "sagebrush" | Fields named |
| S3 | https://github.com/leanprover/hex (README) | Full |
| S4 | https://github.com/kim-em/hex-dev (README, keyword lines) and https://kim-em.github.io/hex-dev/ | README keyword lines; manual front page |
| S5 | https://github.com/sagemathinc/sagebrush : `README.md`, `PRODUCT.md`, `lib/_sage_names.py` | README full; first 60 lines of `PRODUCT.md`; name index searched in full |
| S6 | https://doc.sagemath.org/html/en/reference/categories/index.html (Sage 10.10) | Full |
| S7 | https://doc.sagemath.org/html/en/reference/categories/sage/categories/sets_cat.html | First 100000 of 137075 characters |
| S8 | https://doc.sagemath.org/html/en/reference/sets/index.html | Full |
| S9 | https://github.com/passagemath/passagemath (README) | First 100000 of 101404 characters |
| S10 | PyPI long descriptions of `passagemath-categories`, `passagemath-gap`, `passagemath-macaulay2`, `passagemath-singular`, `passagemath-maxima`, `passagemath-standard` (through S1) | Sections "About", "What is included", "Examples", extras lists |
| S11 | https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/posets/posets.html | First 100000 of 257505 characters |
| S12 | https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/posets/lattices.html | First 100000 of 234837 characters |
| S13 | https://doc.sagemath.org/html/en/reference/monoids/index.html | Full |
| S14 | https://doc.sagemath.org/html/en/reference/monoids/sage/monoids/automatic_semigroup.html | Full |
| S15 | https://doc.sagemath.org/html/en/reference/modules/sage/modules/free_quadratic_module_integer_symmetric.html | Full |
| S16 | https://doc.sagemath.org/html/en/reference/modules/sage/modules/torsion_quadratic_module.html | Full |
| S17 | https://doc.sagemath.org/html/en/reference/calculus/index.html | Full |
| S18 | https://doc.sagemath.org/html/en/reference/logic/index.html | Full |
| S19 | https://doc.sagemath.org/html/en/reference/index.html | Full |
| S20 | https://doc.sagemath.org/html/en/reference/groups/index.html | Full |
| S21 | https://doc.sagemath.org/html/en/reference/quadratic_forms/index.html | Full |
| S22 | https://doc.sagemath.org/html/en/reference/libs/sage/libs/gap/libgap.html | Full |
| S23 | https://docs.sympy.org/latest/modules/sets.html (SymPy 1.14.0) | Full |
| S24 | https://docs.sympy.org/latest/modules/combinatorics/index.html | Full |
| S25 | https://docs.sympy.org/latest/modules/polys/agca.html | Full |
| S26 | https://docs.sympy.org/latest/modules/logic.html | Full |
| S27 | https://docs.sympy.org/latest/modules/categories.html | Full |
| S28 | https://docs.sympy.org/latest/modules/combinatorics/perm_groups.html and https://docs.sympy.org/latest/modules/combinatorics/group_constructs.html | First 100000 of 134134 characters; full |
| S29 | https://docs.sympy.org/latest/modules/matrices/index.html | Full (index only) |
| S30 | https://docs.sympy.org/latest/modules/series/index.html | Full (index only) |
| S31 | https://docs.sympy.org/latest/modules/integrals/integrals.html | First 100000 of 163547 characters |
| S32 | https://docs.gap-system.org/doc/ref/chap0_mj.html (GAP 4.16.1) | Characters 0 to 200000 of 260218; chapters 16 to 64 |
| S33 | https://semigroups.github.io/Semigroups/ | Full |
| S34 | https://digraphs.github.io/Digraphs/ and https://digraphs.github.io/Digraphs/doc/chap6_mj.html | Full |
| S35 | https://github.com/embray/gappy | Repository page |
| S36 | https://docs.oscar-system.org/stable/ | Front page and sidebar |
| S37 | https://github.com/oscar-system/Oscar.jl/blob/v1.8.2/docs/src/Combinatorics/posets.md | Full |
| S38 | https://docs.oscar-system.org/stable/Groups/action/ | Full |
| S39 | https://docs.oscar-system.org/stable/Hecke/manual/quad_forms/integer_lattices/ | Full |
| S40 | https://docs.oscar-system.org/stable/Hecke/manual/quad_forms/discriminant_group/ | Full |
| S41 | https://docs.oscar-system.org/stable/NumberTheory/QuadFormAndIsom/introduction/ | Full |
| S42 | https://github.com/oscar-system/Oscar.jl/blob/v1.8.2/src/Groups/matrices/isometry_group.jl (docstrings); GitHub code search in `oscar-system/Oscar.jl` for `image_in_Oq` and `orthogonal_group(T::TorQuadModule` | Docstrings of `isometry_group`; file paths of hits |
| S43 | https://nemocas.github.io/AbstractAlgebra.jl/stable/ | Front page and sidebar |
| S44 | https://juliapy.github.io/PythonCall.jl/stable/juliacall/ | Full |
| S45 | https://macaulay2.com/ | Full |
| S46 | https://macaulay2.com/doc/Macaulay2/share/doc/Macaulay2/Posets/html/index.html ; license lines of https://github.com/Macaulay2/M2 (README) | Full; license lines |
| S47 | https://python-flint.readthedocs.io/en/latest/ | Front page and type list |
| S48 | https://pari.math.u-bordeaux.fr/ | Full |
| S49 | https://pari.math.u-bordeaux.fr/dochtml/html-stable/Vectors__matrices__linear_algebra_and_sets.html | Function names and the entries for `qfauto`, `qfisom` |
| S50 | https://cypari2.readthedocs.io/en/latest/ | First 100000 of 250557 characters (index); no claim depends on it |
| S51 | https://networkx.org/documentation/stable/reference/algorithms/dag.html (NetworkX 3.7) | Full |
| S52 | https://mpmath.org/doc/current/ (page for 1.3.0) | Front page |
| S53 | https://maxima.sourceforge.io/ | Full |
| S54 | https://sourceforge.net/projects/maxima/files/Maxima-source/ | Folder list |
| S55 | https://github.com/Singular/Singular (`README.md` first 40 lines, `COPYING` first 30 lines) | Parts named |
| S56 | https://github.com/homalg-project/CAP_project (`README.md` first 70 lines, `CAP/PackageInfo.g` version and license lines) | Parts named |
| S57 | https://algebraicjulia.github.io/Catlab.jl/stable/ and https://algebraicjulia.github.io/Catlab.jl/stable/apis/categorical_algebra/ | Full |
| S58 | https://fricas.github.io/ | Full |
| S59 | https://www.uni-osnabrueck.de/fb6/mathematik/normaliz | Full |
| S60 | https://polymake.org/doku.php/start | Full |
| S61 | https://cgm.cs.mcgill.ca/~avis/C/lrs.html | Full |
| S62 | https://github.com/fplll/fpylll | Repository page |
| S63 | README keyword lines of https://github.com/flatsurf/e-antic , https://github.com/symengine/symengine.py , https://github.com/pygae/galgebra , https://github.com/latte-int/latte | Keyword lines only |
| S64 | Web search results: https://reservoir.lean-lang.org/@leanprover/hex , https://reservoir.lean-lang.org/@WuProver/MonomialOrderedPolynomial , https://leanprover-community.github.io/archive/stream/113488-general/topic/SOTA.20on.20symbolic.20algebraic.20systems.20written.20in.20Lean4.html , https://reservoir.lean-lang.org/@oOo0oOo/LeanSage | Search summaries only; the pages were not opened |
| S65 | License files through the GitHub API for Oscar.jl, Nemo.jl, AbstractAlgebra.jl, Hecke.jl, Singular.jl, Polymake.jl, SymPy, NetworkX, SageMath, passagemath, Semigroups, Digraphs, polymake, SymEngine | First lines |

Container evidence [C]: the command of the task, plus read-only commands in `sage-research` for versions, file listings under `/sage/src/sage`, Julia manifests, GAP package availability, and short runs in Sage, SymPy, python-flint, cypari2, NetworkX, mpmath, PyNormaliz, GAP, Macaulay2 and Maxima. One temporary script was written to `/tmp` in the container and removed.

Pages that failed to load and gave no evidence: the PyPI HTML pages (the JSON API was used), `https://www.singular.uni-kl.de/` (redirect page only), `https://homalg-project.github.io/CAP_project/` (redirect page only), the Maxima manual pages for sets (HTTP 404), and `https://doc.sagemath.org/html/en/reference/groups/sage/groups/fqf_orthogonal.html` (HTTP 404; the module file is present in the container).
