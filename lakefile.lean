import Lake
open Lake DSL

/-
A categorically organized CAS hosted in Lean, shipped as an nbdsl DSL plugin
(see lean-jupyter-kernel, docs/plugins.md). The package provides the CasDsl
library plus the prelude module `CasDsl.Notebook`; it depends on the notebook
core only through the `Worker` library of «nbdsl-worker».
-/
package «cas-dsl» where
  version := v!"0.1.0"

require «nbdsl-worker» from git
  "https://github.com/dzackgarza/lean-jupyter-kernel"
    @ "main" / "worker"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

/- The mathematics: categories, functors, fibrations and their theory. This package owns
the CAS machinery over it (registry, resolution, realizations, backends). -/
require lean_categories from git
  "https://github.com/dzackgarza/lean-categories" @ "0102b2f4401ef6bd52c15b4504f4f85a69383ab7"

/- The notebook package: the prelude `CasDsl.Notebook` over the core and the standard universe.
Syntax only: it declares nothing and registers nothing (`CasDslTests.Boundary`). -/
lean_lib CasDsl where
  -- the prelude module `CasDsl.Notebook` imports the root, not vice versa,
  -- so the lib must glob submodules or the kernelspec's olean is never built
  globs := #[.andSubmodules `CasDsl]

/-- The core: the kernel (symbolic category and functor expressions, the registry, resolution,
realization and decision machinery, the leaf contract) and the semantic registry
(`CasCatalogue.Semantics`: categories, functors, classifiers and operations registered from
`lean-categories`). Only this library and `CasAcceptance` may register semantics. It keeps
`lean-categories`' elaboration options, which its registration rows rely on. -/
@[default_target]
lean_lib CasCatalogue where
  globs := #[.andSubmodules `CasCatalogue]
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]

/-- Backend leaves. Each leaf imports only the leaf API `CasCatalogue.Leaf`, other leaves, Mathlib
and `lean-categories`, and contributes only through `register_leaf` (CC-ADAPTER, spec §5). -/
lean_lib CasLeaves where
  globs := #[.andSubmodules `CasLeaves]
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]

/-- Acceptance probes of the core over the standard universe (semantics and leaves); building
the library runs them. -/
lean_lib CasAcceptance where
  globs := #[.andSubmodules `CasAcceptance]
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]

/-- The registry exporter and the axiom audit. -/
lean_lib CasTools where
  globs := #[.submodules `CasTools]

/-- Export the normalized registry manifest as JSON. -/
lean_exe «cas-registry-export» where
  root := `CasTools.ExportMain
  supportInterpreter := true

/-- Kernel-axiom audit of the core, the leaves and the probes; the audit runs while
`CasTools.AxiomAudit` elaborates. -/
lean_exe «cas-axiom-audit» where
  root := `CasTools.AxiomAuditMain
  supportInterpreter := true

/-- The notebook package's boundary and the demo notebook's cells, elaborated with their expected
values (generated with `notebooks/demo.ipynb` by `scripts/demo_notebook.py`). -/
lean_lib CasDslTests
