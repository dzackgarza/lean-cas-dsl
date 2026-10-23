# Kernel V1: connected CAS computations

These examples use the existing mathematical language, `.cas` file scope,
`#cas_tests` notebook command, and CAS harness. Each workflow retains computed
intermediate values and feeds them to later operations. The expected values were
specified independently before execution; the four source files are copied
unchanged from those specifications.

The notebook is supplied without captured outputs. A fresh execution report is
required to establish that a run succeeded. These demonstration assertions are
not additions to `CasAcceptance/Permanent/admitted.json`, and a successful demo
alone is not permanent mathematical admission, independent extension acceptance,
or acceptance of V1 or B0.

## The four workflows

| File | Connected computation | Expected observations |
| --- | --- | --- |
| [01-selected-arithmetic.cas](kernel-v1/01-selected-arithmetic.cas) | Compute an integer, reuse its square in exact rational arithmetic, and perform the corresponding operations in the explicitly selected ring `ℤ/5`. | `-12`, `144`, `144/35`, `99/35`, `3` in the integer/rational chain; `3`, `4`, `1` in the modular chain. Eight assertions. |
| [02-finite-pullback.cas](kernel-v1/02-finite-pullback.cas) | Construct a nontrivial pullback in `FiniteSets`, obtain its cardinality through the structural route to sets, and reuse its underlying set in a product. | The retained pullback has three elements; its product with itself has nine. Two assertions. |
| [03-matrix-iteration.cas](kernel-v1/03-matrix-iteration.cas) | Apply the same rational `3 × 3` matrix successively to three retained vectors. | `(-3,8,8)`, `(5,32,-6)`, `(75,14,-28)`. Three assertions. |
| [04-presentation-transport.cas](kernel-v1/04-presentation-transport.cas) | Transport a field element along a selected nonidentity presentation comparison, square the transported result, and transport the computed square back. | `1+2x` maps to `2+2y`; its square is `y+2`; the return value and the source square are both `x`. Four assertions. |

These are 17 assertions in four workflows. The finite workflow reuses a
constructed apex; the matrix workflow reuses returned vectors. The pullback's
cardinality observations alone do not test every projection or universal
property. Checks of complete defining-map behavior and the wider V1 interface
remain part of the separate kernel and integration evidence.

## Prerequisites

Use one coherent, already available source combination and the Lean toolchain
specified in `lean-toolchain`. The runner uses only the installed engines and
existing checkouts. It does not run dependency updates, engine installers, or
build commands.

The default checkout layout is:

- `lean-cas-dsl/`: this repository.
- `lean-cas-dsl-leaf-contracts/`: the public contract checkout, including
  `python/cas_port.py`.
- `lean-cas-dsl-leaves/`: the existing leaves checkout.
- `lean-cas-dsl-leaves-diagnostic/`: the diagnostic checkout, with
  `diagnostics/v1/leaves.json`.

The diagnostic source for this configuration is
`5a9e82377007689547f3532955e3803a93b08b5b` in the diagnostic checkout.
Its manifest supplies 19 registrations. A local checkout may be elsewhere:
`--diagnostic-manifest` and `--leaves-manifest` accept explicit manifest paths.
No local package override or machine-specific path is committed here.

`CAS_SAGE_PYTHON` must identify an executable Python interpreter in which Sage is
already installed. This is a path to an executable, not a shell command such as
`sage -python`. The host's ordinary `python3` must also be available for the
manifest launchers. `--prepare-only` verifies the paths and writes configuration;
it does not import Sage or test engine availability.

Build the required source targets through the project's existing build process
before running the demo. The specific targets used here are:

```bash
lake build cas-harness CasDsl.Notebook
```

For a deliberately selected local source combination, pass the same **external**
Lake package manifest to the build and to the runner:

```bash
lake --packages=/absolute/path/to/source-packages.json build cas-harness CasDsl.Notebook
python3 scripts/run_kernel_v1_demo.py \
  --packages /absolute/path/to/source-packages.json \
  --contract /absolute/path/to/lean-cas-dsl-leaf-contracts \
  --sage-python /absolute/path/to/python-with-sage
```

The runner passes this file to Lake's existing `--packages` option. It does not
rewrite `lake-manifest.json`, dependency declarations, or package revisions.
`--lake` can select an explicit toolchain executable when it is not on `PATH`.

## Run from the command line

From this repository's root, run:

```bash
python3 scripts/run_kernel_v1_demo.py \
  --contract ../lean-cas-dsl-leaf-contracts \
  --sage-python /absolute/path/to/python-with-sage
```

Alternatively, set the two existing documented host environment selectors:

```bash
export CAS_LEAF_CONTRACT_PATH="$PWD/../lean-cas-dsl-leaf-contracts"
export CAS_SAGE_PYTHON=/absolute/path/to/python-with-sage
python3 scripts/run_kernel_v1_demo.py
```

The runner writes its configuration and output to `../kernel-v1-run/` by default.
Choose a different directory outside the repository with `--output`.

It invokes the built `cas-harness` executable through `lake env`, with
`--computation-only`. The executable is built with the project's existing
`supportInterpreter` setting so imported commands are available during execution. Consequently the assertions use
the realization path instead of succeeding solely through Lean proof discharge.
There is no extra CAS interpreter in this script.

The output directory contains:

| File | Purpose |
| --- | --- |
| `leaves.json` | The explicit selected execution configuration. |
| `inventory.json` | Demo IDs read before execution, so a missing result cannot shrink the run. This is separate from the protected acceptance inventory. |
| `inputs.json` | Invocation, source paths, and SHA-256 digests of the exact `.cas` files, original manifests, and optional package manifest used. |
| `execution.log` | The actual harness output, also streamed to the terminal. |
| `report.json` | Actual per-assertion outcomes, semantic questions, and available dispatch records. |

A successful invocation exits with status zero only when the harness exits
successfully, every expected assertion occurs exactly once and has outcome
`holds`, every other reported statement also holds, and **each workflow has at
least one completed backend dispatch**. A missing report, duplicate or missing
assertion, gap, unavailable engine, wrong answer, malformed data, ambiguity, or
internal error fails the demo.

The general CAS harness deliberately permits implementation gaps and unavailable
engines in a coverage report. The demo runner applies the stricter requirement
above because these examples are intended to execute. Dispatch records establish
that requests occurred; they do not establish mathematical truth independently
of the asserted results. Successful bare `let` items are not separate report
rows, so the dispatch counts are counts of calls retained in assertion rows, not
necessarily every call made during the session.

## Use the existing notebook

Open [kernel-v1.ipynb](../notebooks/kernel-v1.ipynb) with the existing
**CasDsl (Lean 4)** kernel configured for this repository and its
`CasDsl.Notebook` prelude. The kernelspec's project directory must be this
checkout, so relative `.cas` and report paths resolve consistently. The worker
and prelude must use the same built source combination and Lean toolchain.

Prepare the same selected configuration and start Jupyter with the engine and
contract environment inherited by the kernel:

```bash
export CAS_LEAF_CONTRACT_PATH="$PWD/../lean-cas-dsl-leaf-contracts"
export CAS_SAGE_PYTHON=/absolute/path/to/python-with-sage
python3 scripts/run_kernel_v1_demo.py --prepare-only
jupyter lab notebooks/kernel-v1.ipynb
```

If Jupyter is already running, start a server/kernel with these environment
variables rather than assuming a later shell export changes an existing process.
The existing integration's [plugin instructions](https://github.com/dzackgarza/lean-jupyter-kernel/blob/main/docs/plugins.md)
describe kernelspec registration when it is not yet configured. The demo adds no
notebook feature or new state layer.

The notebook's only executable cell is the existing command:

```lean
#cas_tests "examples/kernel-v1" manifest "../kernel-v1-run/leaves.json" reporting "../kernel-v1-run/notebook-report.json" inventory "../kernel-v1-run/inventory.json" computing
```

If you choose custom paths, `--prepare-only` prints the corresponding command
with absolute paths. Replace the notebook cell with that command. After running
the cell, apply the same strict report checks from the terminal:

```bash
python3 scripts/run_kernel_v1_demo.py \
  --check-report ../kernel-v1-run/notebook-report.json
```

The notebook command itself follows the general harness outcome policy; this
report check is what makes a missing implementation or unavailable engine a
failed demonstration. Only validate a report after that notebook invocation has
completed successfully; an earlier report is not evidence about a later failed
cell.

### Edit and rerun a connected chain

Edit the `.cas` file, then rerun its `#cas_tests` invocation or the runner. Each
file has its own `let` scope and uses the harness to preserve computed data for
later items. Blank lines separate items. A `let` in one file does not become a
binding in another file.

A standalone `#cas "..."` command starts with an empty CAS scope and closes its
harness afterward. A `let` executed with `#cas` therefore does **not** persist
into a later notebook cell. Keep a dependent computation in one `.cas` file and
run it with `#cas_tests`, as these examples do.

For exploratory changes, copy a workflow outside the repository and retain the
original independently specified examples. Run the copy with `--suite`:

```bash
python3 scripts/run_kernel_v1_demo.py \
  --suite /absolute/path/to/my-experiment.cas \
  --contract ../lean-cas-dsl-leaf-contracts \
  --sage-python /absolute/path/to/python-with-sage
```

For a copied workflow in the notebook, run `--prepare-only --suite /path/to/my-experiment.cas`
and paste the printed command so its temporary inventory matches that file. Pass
the same `--suite` when using `--check-report`.

New expected values should be established by mathematics before inspecting the
implementation's answer. A failed result does not authorize changing an existing
expectation to match the implementation.

## Why this manifest is explicit

The generated configuration takes **all** registrations from the diagnostic
manifest and exactly these two from the existing `sage-set-limits` backend:

| Operation | Input form | Selected backend |
| --- | --- | --- |
| `lim.sets.pullback` | `cat.sets` | `sage-set-limits` |
| `meth.cardinality` | `cat.sets` | `sage-set-limits` |

The diagnostic registration supplies set products. The other registrations in
the existing leaves manifest, including its product registration and specialized
cardinality registrations, are not selected for this run. This caller choice
avoids overlapping implementations; it does not create a kernel priority rule.
Exact-form and category-wide registrations have equal standing under the
[public manifest contract](https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts/blob/main/api/manifest.md).

A backend process runs in its manifest's directory. When composing this mixed
manifest in a separate output directory, the runner resolves selected backend
script paths against each **original** manifest directory and writes absolute
paths into the generated `args`. The public schema has no effective `cwd` or
`env` fields, and none is added. The contract and engine choices are ordinary
inherited host environment variables.

## Independent mathematical derivations

### Exact arithmetic and selected rings

In `ℤ`, `17-29=-12` and `(-12)^2=144`. The selected map to `ℚ` and ordinary exact
field operations give

\[
\frac{144}{35}-\frac97=\frac{144-45}{35}=\frac{99}{35},
\qquad
\frac{99}{35}\frac{35}{33}=3.
\]

Every denominator is nonzero. In `ℤ/5`, the corresponding retained subtraction
is `3`, its square is `4`, and adding `2` yields `1`. These are equations in their
selected rings, not identifications of integer and residue elements. The source
uses no `gcd` operation. Its ordinary literal and selected-ring syntax follows
`tests/acceptance/numbers.cas` and `fractions.cas`.

### Finite pullback and reuse

The maps have tables `f=[0,1,1]` and `g=[1,0]`, with common target `Fin(2)`.
Solving `f(a)=g(b)` gives exactly

\[
P=\{(0,1),(1,0),(2,0)\}.
\]

Thus `|P|=3`, and the set product `P×P` has `3·3=9` elements. The selected
finite-set construction is transported through its registered creation lift;
the subsequent product explicitly selects `Sets`. The mathematical definitions
are Mathlib's `Types.pullbackLimitCone` and `Types.binaryProductLimitCone`,
registered by the upstream
[limit API](https://github.com/dzackgarza/lean-categories/tree/ee957329414a58759d26e23fa22e8d0a31040fc8/LeanCategories/Catalogue/Semantics/Limits).

### Matrix iteration

With

\[
A=\begin{pmatrix}1&2&-1\\0&1&3\\2&-1&1\end{pmatrix},
\qquad v_0=(2,-1,3),
\]

ordinary row-by-column multiplication gives:

| Step | Three row sums | Retained vector |
| --- | --- | --- |
| `A(v₀)` | `2-2-3`, `-1+9`, `4+1+3` | `(-3,8,8)` |
| `A(v₁)` | `-3+16-8`, `8+24`, `-6-8+8` | `(5,32,-6)` |
| `A(v₂)` | `5+64+6`, `32-18`, `10-32-6` | `(75,14,-28)` |

The formal operation is `Matrix.mulVec`, exposed by
[`LinearAlgebra.apply`](https://github.com/dzackgarza/lean-categories/blob/e213e79ea5c089cd67db8188f0c1c2169d4fc095/LeanCategories/Catalogue/Semantics/Algebra/LinearAlgebra.lean).
The selected scalar ring `ℚ` and dimension three remain part of the input and
result types. Transpose multiplication would give `(8,0,-2)` at the first step,
and reusing `v₀` each time would not give the later vectors.

### Nonidentity field presentation change

The source is `X=F₃[x]/(x²+1)` and the target is
`Y=F₃[y]/(y²+y+2)`. The selected comparison sends `x` to `y+2`, so

\[
1+2x\longmapsto 1+2(y+2)=2+2y.
\]

In `Y`, `y²=2y+1`, hence `(2+2y)²=y+2`. The inverse comparison sends this
computed value back to `x`. Independently, in `X`, `x²=2`, so `(1+2x)²=x`.
This separates actual transport from merely changing an endpoint label. The
registered comparison and its generator equations are in
[`PolynomialPresentations`](https://github.com/dzackgarza/lean-categories/blob/ee957329414a58759d26e23fa22e8d0a31040fc8/LeanCategories/Catalogue/Semantics/Algebra/PolynomialPresentations.lean).

### Source provenance

The arithmetic and matrix questions were supplied in the independent
`mathematical-review.md`; the pullback and presentation-change questions were
supplied in the earlier `mathematical-specification.md`. Their derivations are
reproduced above so the examples do not depend on temporary review paths.
The source digests below identify the files copied unchanged into this directory.

| Current file | Independent source filename | SHA-256 |
| --- | --- | --- |
| `01-selected-arithmetic.cas` | `v1-selected-arithmetic.cas` | `bb4831b81fa7d220e72e0095f4f0ff0b78b886e0cfc184d966a4bdd24dc4a365` |
| `02-finite-pullback.cas` | `v1-finite-chain.cas` | `45725a1b6d3134b9b07d6d6c02402c2c6ccdc54ad271e82d46240d09522588da` |
| `03-matrix-iteration.cas` | `v1-matrix-repeated-application.cas` | `11e91508c6f869fb1b730c4dab8199482f7361904c12f4c824b23bde83bcd6b3` |
| `04-presentation-transport.cas` | `v1-f9-chain.cas` | `c0807240419d707a0e8bf595226d172705d1f0f65bfd7bdec9a244d8dcf82b89` |

The review document digest is
`87e6ddc9651a3a3b38797e4ff53b67fdb594528afe016b8992ead0ae7789e8d1`;
the earlier specification digest is
`60c4e3b51eac723edb9fe2794e3f1049ffc740da147ff6537b123e37bcdadefb`.
These hashes preserve provenance and do not confer mathematical acceptance.
