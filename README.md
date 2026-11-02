# lean-cas-dsl

A computer algebra language over Lean 4, where every object, operation and structural route is
mathematics formalized in [`lean-categories`](https://github.com/dzackgarza/lean-categories),
and computations can run through ordinary backends (Sage, GAP, or others) registered
against catalogue operations. Their answers are decoded and compared, never believed
([`specs/leaf-registration.md`](specs/leaf-registration.md)). It runs as a Jupyter kernel through
[lean-jupyter-kernel](https://github.com/dzackgarza/lean-jupyter-kernel).

```lean
#cas "assert 2 + 3 = 0 in ℤ/5"
-- holds                        (decided in Lean; no leaf is consulted)
#cas "assert |Fin(3)| = 3"
-- gap: no admitted registration computes meth.cardinality on the form obj.sets.fin
--                              (holds once a leaf registers it; wrong if it answers 4)
#resolve cardinality in "cat.finite_sets"
-- cat.finite_sets --forget[clf.sets.finite]--> cat.sets ;
--   meth.cardinality = fun.sets.cardinality on the core
```

`cardinality` is declared once as `Core(Set) → Disc(Card)` in `lean-categories`.
A selected structural functor to sets induces the core action through which an object
receives this invariant; no second cardinality declaration is needed. Arbitrary set maps
do not induce arrows between unequal cardinals in the discrete target. The assertion
above is permanent and names no leaf: whatever computation is installed for cardinality is run,
and its answer either meets the assertion or does not.

## Architecture

[`specs/architecture.md`](specs/architecture.md) is the contract. It covers:

- who owns what;
- the one-way workflow;
- the payload at each boundary;
- the invariants and trust boundaries;
- the states the leaf API must make impossible.

| Silo | Owns |
| --- | --- |
| `lean-categories` | All mathematics: categories, functors, classifiers, operations, coherences |
| catalogue (`LeanCategories.Catalogue`, in `lean-categories`) | The semantic registry: the symbolic calculus, the registered categories, functors, classifiers, methods, cells, limits and adjunctions, each checked against its mathematics |
| kernel (`CasCatalogue`) | Deterministic interpretation of the upstream mathematics: resolution, ambiguity, the semantic reading of statements, their discharge in Lean and their realization through registrations (encoding, decoding, comparison), the language, the harness. |
| leaf contract (`CasContract`, repository `lean-cas-dsl-leaf-contracts`) | Kernel-owned, published separately: the shape of a leaf's manifest, the port protocol, the failure strata, and the kernel's reading of the semantic registry. Depends on `lean-categories` only. |
| leaves (`lean-cas-dsl-leaves`, or any other package) | Opaque computations, each registered against an operation's declared type (operation id, input form, implementation): glue from the declared input form to a mature engine's routine and back ([leaf guidance](https://github.com/dzackgarza/lean-cas-dsl-leaves/blob/e2f8537/AGENTS.md)). A leaf ships no mathematics and no Lean, and nothing it says is believed; it never sees this repository's tests. |
| acceptance (`tests/acceptance/`) | The only correctness evidence: permanent, leaf-blind assertions in the mathematical language, whose expected values come from proof, citation or an independent oracle |
| notebook (`CasDsl`) | Surface syntax only |

Semantic availability and computability are separate. An operation that applies but has no
realization is a `NoImplementation` gap, and never a missing method. The semantic contract is described in
[`specs/computational-core.md`](specs/computational-core.md), with technical scope and verification
notes in [`specs/computational-core-plan.md`](specs/computational-core-plan.md). The roadmap and
delivery order are in [issue #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10). The semantic registry
is `lean-categories`' (`LeanCategories.Catalogue`); this repository reads it at `main` and writes
no semantic row.

## Project status

The source inspected for the 2026-11-02 documentation update does not establish completed
kernel readiness or V1 acceptance. [HANDOFF.md](HANDOFF.md) identifies the inspected revisions
and their evidence. Current milestone requirements and decisions are in the issues below.

### Where to continue

- [#10](https://github.com/dzackgarza/lean-cas-dsl/issues/10): roadmap, priorities and delivery order.
- [#85](https://github.com/dzackgarza/lean-cas-dsl/issues/85): replacement decision and required outcome.
- [#66](https://github.com/dzackgarza/lean-cas-dsl/issues/66) and
  [#69](https://github.com/dzackgarza/lean-cas-dsl/issues/69): implementation work.
- [#24](https://github.com/dzackgarza/lean-cas-dsl/issues/24): independent acceptance.

Repository documentation describes the source, interfaces, policies and verification commands.
Update it to reflect issue decisions; it does not supersede them or maintain a separate work order.
See [CONTRIBUTING.md](CONTRIBUTING.md#behavioural-contribution-policies) for contribution policies
and [Construction and verification](specs/computational-core-plan.md#construction-and-verification)
for the documented development loop.

## Layout

- `CasCatalogue/`, the kernel over the leaf contract (`CasContract`, a dependency):
  - resolution (`Resolve`, `ResolveSyntax`) and composites of registered cells (`CellCall`);
  - the semantic reading (`Semantic`, `Trace`), the language (`Language`), the admission of
    registrations (`Admission`), the codec (`Codec`), the realized reading (`Realize`) and the
    suite's runner (`TestSuite`).
- `tests/acceptance/*.cas`: the permanent suite, in the language.
- `CasAcceptance/`: the probes and the standard catalogue's ids.
- `CasTools/`: `cas-registry-export`, `cas-axiom-audit` and `cas-harness` (the suite over a
  leaves manifest).
- `CasDsl/`, `CasDslTests/`: the notebook prelude, the boundary check, and the demo's cells,
  generated by `scripts/demo_notebook.py`.
- `notebooks/demo.ipynb`: the demo, re-executed by `scripts/reexec_notebooks.py`.

## Quickstart

Requires [elan](https://github.com/leanprover/elan), `uv` and `just`.

```bash
just setup    # Mathlib cache, venv, casdsl kernelspec
B0_INTEGRATION=1 just build  # the integration gate: static checks, kernel, acceptance, tools and notebook
B0_INTEGRATION=1 just test-ci  # the gate, then the demo notebook through the live kernel
just harness path/to/leaves.json   # the suite over a leaves manifest, to .tmp/harness.json
just acceptance base.json          # the suite here, compared with a base run assertion by assertion
```
