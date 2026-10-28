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

In short:

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
realization is a `NoImplementation` gap, and never a missing method. The requirements are in
[`specs/computational-core.md`](specs/computational-core.md), and the execution order is in
[`specs/computational-core-plan.md`](specs/computational-core-plan.md). The semantic registry
is `lean-categories`' (`LeanCategories.Catalogue`); this repository reads it at `main` and writes
no semantic row.

## Current milestone: kernel ready before substantial leaves

The [kernel-MVP gate](specs/computational-core-plan.md#kernel-mvp-proved-readiness-for-substantial-leaf-development)
is **proved readiness for sustained independent leaf work**, not increasing
the number of implemented backend methods. The kernel must generically
interpret every admitted mathematical question and formed request in the
declared B0 extension language; propagate operations compositionally;
execute structural actions, comparisons, refinements and complete result
lifts; and publish all required request/reply encodings before leaves
depend on them. A missing implementation is acceptable only if adding
an ordinary registration can fill it *without changing the kernel,
contract or upstream mathematics*.

A frozen kernel/contract must pass independently chosen extension trials
for every supported mechanism, including new object/old operation,
new operation/old object, nonidentity transport, structured results and
bad or absent leaves, **without patches**. Only small independent
diagnostic specimen leaves run before this gate. Broad leaf implementation
starts after it. The gate does not eliminate the complete real-backend
execution and independently accepted assertions required for full B0.

As of the 2026-10-29 documentation reconciliation, this gate has **not** been established; the
[construction handoff](HANDOFF.md) and the
[plan's evidence section](specs/computational-core-plan.md#kernel-mvp-proved-readiness-for-substantial-leaf-development)
record the unresolved work. Do not treat a compiling kernel, a falling
request-gap count, or a new leaf registration as milestone completion.

### Where to continue

[Issue #10](https://github.com/dzackgarza/lean-cas-dsl/issues/10) gives the current order:
interpret and compute the existing structured construction with its selected nonidentity
comparison and subsequent defining-map use; establish preservation under the claimed
mathematical operations and public-only unchanged-consumer use before extending coverage;
finish #24's full independent acceptance. #66 and #69 work together on the existing first
RX-LIFT construction; build its actual dependencies and replace/remove its defective paths
before completing the remaining corpus. Do not first repair the whole legacy implementation.
The full combined build and acceptance remain delivery requirements. #23/#82 review the
exact construction requirements alongside implementation; unrelated upstream work does not block it.
Research issues #71–#81 are consolidated historical guidance, not parallel work queues.

The implementation sources are selected: [Lean application/binder reuse](specs/reuse/cc-dsl-language.md),
[the retained-plan owner and bounded PolyFun transition adaptation](specs/reuse/cc-realize-2cat.md),
and [the existing mathematical forms](specs/reuse/cc-forms-general.md).
#24 integrates the already-authored rational lift/factor leaf package through the public
contract. These are implementation tasks, not another import-versus-rewrite decision phase.

The candidate's diagnostic manifest still selects pending mathematical work from
[lean-categories #93/#94](https://github.com/dzackgarza/lean-categories/pull/93).
The [handoff](HANDOFF.md) distinguishes that source from current main and records the
integration dependency. Source existence on a branch is not latest-main delivery or acceptance.

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
just build    # the gate: the static checks, then the kernel, acceptance, tools and notebook
just test-ci  # the gate, then the demo notebook through the live kernel
just harness path/to/leaves.json   # the suite over a leaves manifest, to .tmp/harness.json
just acceptance base.json          # the suite here, compared with a base run assertion by assertion
```
