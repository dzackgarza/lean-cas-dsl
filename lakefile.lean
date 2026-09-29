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

/- All mathematics, including the CAS's semantic registry (`LeanCategories.Catalogue`). This
package owns the CAS machinery over it (resolution, realizations, the leaf API, the notebook). -/
require lean_categories from git
  "https://github.com/dzackgarza/lean-categories" @ "536555f4eecf164e8fab5c1e096472bc6d9fcb0f"

/- The notebook package: the prelude `CasDsl.Notebook` over the core and the standard universe.
Syntax only: it declares nothing and registers nothing (`CasDslTests.Boundary`). -/
lean_lib CasDsl where
  -- the prelude module `CasDsl.Notebook` imports the root, not vice versa,
  -- so the lib must glob submodules or the kernelspec's olean is never built
  globs := #[.andSubmodules `CasDsl]

/-- The core: resolution, realization and decision machinery, the realization registry and the
leaf contract, over `lean-categories`' semantic registry (`LeanCategories.Catalogue`), which it
reads at the pin and never writes (`specs/architecture.md`). It keeps `lean-categories`'
elaboration options. -/
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

/-- The permanent acceptance suite, in the language (`CasCatalogue.TestSuite`). -/
input_dir acceptanceSuite where
  path := "tests/acceptance"
  text := true
  filter := .extension "cas"

/-- Acceptance probes of the core over the standard universe (semantics and leaves); building
the library runs them, and `CasAcceptance.Suite` runs the suite (rebuilt when a test changes). -/
lean_lib CasAcceptance where
  globs := #[.andSubmodules `CasAcceptance]
  needs := #[acceptanceSuite]
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
