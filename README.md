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
                           --  Modules(ℤ); it arrives by subcategory inheritance)
ℚ[3]                       -- NoImplementation: nth is *semantically* available
                           --  (ℚ is countable) — there is just no route yet
```

Three invariants, enforced end to end:

1. **Backend-blind syntax.** Ordinary expressions never name Sage, GAP, or
   an algorithm. A developer-owned routing layer selects implementations
   *after* the mathematical operation is resolved; `#explain_route`,
   `#capabilities`, and `#capability_gaps` are the only places backend
   identity is visible.
2. **Category-owned methods.** `factor`, `det`, `annihilator`, `nth`,
   `cardinality` are declared on categories. Objects carry rich category
   profiles (`ℤ` is simultaneously a set, a countable set, a commutative
   ring, a euclidean domain, …) and receive methods by membership and by
   registered subcategory inclusion — never by forwarding code on a leaf
   class. Method resolution lives behind one boundary
   (`CasDsl/Resolve.lean`), which is also where receivers are transported
   along registered preferred functors — `F.cardinality()` on the ℤ-module
   ℤ/4 resolves as `UnderlyingSet(F).cardinality()` — with no change to any
   declaration, to the syntax, or to a backend.
3. **Semantic availability ≠ computability.** What is mathematically
   meaningful is decided by the category layer; what is currently
   executable is decided by a separate capability registry. A missing
   implementation is a structured, auditable `NoImplementation` gap —
   never a hidden method, a narrowed category, or a fake value.

The worked proof is
[`notebooks/categorical-cas.ipynb`](notebooks/categorical-cas.ipynb) — a
pedagogical notebook covering trusted assertions (`assert 2 + 3 = 0 in
ℤ/5`), Sage-backed factorization over ℤ and ℚ[x], the `ℤ ⊆ ℚ` preferred
embedding (`map p to ℚ[x]`), calling a polynomial as a function
(`q(1)`), exact matrix inverses over ℚ, inherited `annihilator`,
progression sets with Haskell-style ellipses, countable indexing
(`ℤ[3]` under the registered `0, 1, −1, 2, −2, …` choice), and a final
cell that **fails on purpose** with the structured capability gap.

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
  -> object + category profile        (registered ProfileRules; rich, not nominal)
  -> method resolution                (Resolve.lean — direct + inherited; ONE boundary)
  -> capability routing               (Route.lean — chosen | gap | ambiguous)
  -> executor                         (Native.lean in-process, or a direct adapter)
  -> trusted typed Value              (Value.lean — ordinary CAS trust, no proofs)
  -> notebook state                   (Registry.lean — env extensions; snapshot-safe)
```

The Sage bridge is a **direct adapter** (`CasDsl/Backends/Sage.lean` +
`backends/sage_adapter.py` under `sage -python`, framed typed JSON —
`CasDsl/Port.lean` is generic and contains no Sage branches). Sage brokers
nothing: future GAP/Singular/Macaulay2 bridges are parallel direct
adapters registering routes against the *existing* mathematical methods.

All semantic state (categories, methods, routes, profile rules, bindings)
lives in persistent env extensions per the
[plugin state law](https://github.com/dzackgarza/lean-jupyter-kernel/blob/main/docs/plugins.md),
so cell atomicity, restart replay, and the olean session cache come from
the notebook core for free.

Design contract, decisions, ceilings, and open questions: [DESIGN.md](DESIGN.md).
Deferred work is tracked in the issues.

## Layout

`CasDsl/` (engine: value model, registries, resolver, router, native
executors, port, Sage adapter, surface syntax, diagnostics, standard
universe) · `CasDslTests/` (elaboration-time `#guard`/`run_cmd` suites) ·
`backends/` (the Python half of the Sage adapter) · `tests/` (adapter
roundtrip + kernel E2E) · `notebooks/` (the live acceptance notebook).
