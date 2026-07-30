# lean-cas-dsl

**A categorically organized CAS in Lean 4** — a computer algebra system
whose user-facing interfaces are organized by the mathematical categories
where operations first make sense, running as a Jupyter kernel via
[lean-jupyter-kernel](https://github.com/dzackgarza/lean-jupyter-kernel).

```text
let n := 360 in ℤ
n.factor()                 -- 2^3 * 3^2 * 5   (a Sage-computed, trusted value —
                            --  but no expression ever names a backend)
let F := ℤ/4 in SmallModules(ℤ)
F.annihilator()            -- (4)             (annihilator is declared once, on
                            --  the appropriate module category and inherited)
ℚ[3]                       -- NoImplementation: nth is *semantically* available
                            --  (ℚ is countable) — there is just no route yet
```

Three invariants, enforced end to end:

1. **Backend-blind syntax.** Ordinary expressions never name Sage, GAP, or
   an algorithm. A developer-owned routing layer selects implementations
   *after* the mathematical operation is resolved; `#explain_route`,
   `#capabilities`, and `#capability_gaps` are the only places backend
   identity is visible.
2. **Category-owned methods, inherited by functor composition.** `factor`,
   `det`, `annihilator`, `nth`, and `cardinality` are declared where the
   mathematical operation first makes sense. An object receives a method
   whenever its category has a registered structural functor to that source
   category—not only when it lies in a subtype/full subcategory. Thus a
   formed module or lattice can inherit `cardinality` through its projection
   to modules and the underlying-set functor, without leaf-specific
   forwarding code. Method resolution lives behind one boundary
   (`CasDsl/Resolve.lean`); `F.cardinality()` resolves to application of the
   resulting composite functor.
3. **Semantic availability ≠ computability.** What is mathematically
   meaningful is decided by the Lean-owned category/operation graph; what is
   currently executable is decided by backend realization records attached
   to those operations or normalized composites. A missing implementation is
   a structured, auditable `NoImplementation` gap—never a hidden method, a
   narrowed category, or a fake value.

The worked proof is
[`notebooks/categorical-cas.ipynb`](notebooks/categorical-cas.ipynb) — a
pedagogical notebook covering trusted assertions (`assert 2 + 3 = 0 in
ℤ/5`), Sage-backed factorization over ℤ and ℚ[x], `gcd(84, 30)` in the
prefix spelling SPEC.md uses, the registered `ℤ ⊆ ℚ` preferred canonical map
(`map p to ℚ[x]`), calling a polynomial as a function (`q(1)`), membership
in a polynomial ring (`x ∈ ℤ[x]`), `p.deg()` and `p.roots()` — whose empty
result over ℚ is an answer, not a failure — exact matrix inverses over ℚ,
inherited `annihilator`,
progression sets with Haskell-style ellipses, countable indexing
(`ℤ[3]` under the registered `0, 1, −1, 2, −2, …` choice), exact algebraic
numbers (`√2 ∈ ℝ`, `2 + 2i ∈ ℂ`, `|2 + 2i| = 2√2` — never a decimal) with
the ⊆-chain read off the canonical-map registry, the cubic split over ℂ[x],
numerical approximation as an operation ON an exact value
(`map √2 to ℝ/O(1/10^{10})`, whose decimal is certified against the value it
presents and whose tolerance is a request rather than a quotient),
and two cells that **fail on purpose**: one square root over ℚ is the
documented ceiling, and `Mat₂(ℤ/5).det()` is the structured capability gap.

## Quickstart

Requires: [elan](https://github.com/leanprover/elan), `uv`, `just`, and
SageMath on `PATH` (the direct backend; without it, Sage-routed operations
fail honestly as capability gaps).

```bash
lake exe cache get && lake build CasDsl nbdsl_worker
just setup            # venv + kernel adapter + casdsl kernelspec
jupyter lab notebooks/categorical-cas.ipynb   # kernel: "CasDsl (Lean 4)"
```

`just test` runs the full gate: Lean build + no-sorry, the Sage adapter
roundtrip (against real Sage), and the 12-test E2E suite through the
installed kernelspec.

## Architecture

```text
surface expression  (CasDsl/Syntax.lean, Eval.lean — backend-blind casTerm language)
  -> Lean object + typed category expression
  -> semantic method resolution        (operation functor + structural composite)
  -> backend realization selection      (chosen | gap | ambiguous)
  -> executor                           (Native.lean in-process, or a direct adapter)
  -> trusted typed Value                (ordinary CAS trust, no proof laundering)
  -> notebook state                     (persistent env extensions; snapshot-safe)
```

The current implementation realizes parts of this through local category
profiles, method rows, and route rows. Those are implementation scaffolding,
not a second ontology. The convergence work is explicit:

- [`lean-lattices`](https://github.com/dzackgarza/lean-lattices) owns the
  checked categories, structural functors, classifiers, constructors,
  operation functors, and coherences;
- lean-lattices #49 and this repository's #14 own pinned Lake consumption of
  that registry;
- lean-lattices #28/#53 and this repository's #15 own replacement of local
  method ownership by the imported semantic operation graph;
- this repository's #19–#23 own versioned Sage observation, applicability,
  realization routes, and executed parity.

A local profile may cache the structural facts needed by the elaborator, and
an optimized Sage method may realize a whole composite directly. Neither may
redefine the mathematical source of the operation or erase typed parameters,
operation ports, or route provenance.

The Sage bridge is a **direct adapter** (`CasDsl/Backends/Sage.lean` +
`backends/sage_adapter.py` under `sage -python`, framed typed JSON —
`CasDsl/Port.lean` is generic and contains no Sage branches). Sage brokers
nothing: future GAP/Singular/Macaulay2 bridges are parallel direct
adapters registering realizations against the *existing* mathematical
operations.

All notebook/session state is held in persistent environment extensions per
the [plugin state law](https://github.com/dzackgarza/lean-jupyter-kernel/blob/main/docs/plugins.md),
so cell atomicity, restart replay, and the olean session cache come from the
notebook core. Once the semantic registry is imported, local state stores
references, derived closures, realization choices, and bindings—not an
independent category graph.

Design contract, decisions, ceilings, and open questions: [DESIGN.md](DESIGN.md).
Deferred work is tracked in the issues.

## Layout

`CasDsl/` (engine: value model, registries, resolver, router, native
executors, port, Sage adapter, surface syntax, diagnostics, standard
universe) · `CasDslTests/` (elaboration-time `#guard`/`run_cmd` suites) ·
`backends/` (the Python half of the Sage adapter) · `tests/` (adapter
roundtrip + kernel E2E) · `notebooks/` (the live acceptance notebook).
