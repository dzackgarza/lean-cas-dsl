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
package owns the CAS machinery over it (resolution and propagation, the language, the permanent
tests, the harness, the notebook). -/
require lean_categories from git
  "https://github.com/dzackgarza/lean-categories" @ "main"

/- The leaf contract: the shape of a leaf's manifest, the port protocol and the failure strata,
published on its own so that a leaf depends on nothing of the kernel
(`lean-cas-dsl-leaf-contracts`). The leaves themselves (`lean-cas-dsl-leaves`) are not a Lake
dependency: a leaf ships no Lean, and the kernel imports nothing from it
(`specs/leaf-registration.md`). The suite finds their manifest `leaves.json` through
`CAS_LEAVES` (`CasCatalogue.Realize.Harness.load`). -/
require cas_leaf_contracts from git
  "https://github.com/dzackgarza/lean-cas-dsl-leaf-contracts" @ "main"

/- The notebook package: the prelude `CasDsl.Notebook` over the core and the standard universe.
Syntax only: it declares nothing and registers nothing (`CasDslTests.Boundary`). -/
lean_lib CasDsl where
  -- the prelude module `CasDsl.Notebook` imports the root, not vice versa,
  -- so the lib must glob submodules or the kernelspec's olean is never built
  globs := #[.andSubmodules `CasDsl]

/-- The core: resolution, propagation, calls and the language, over the leaf contract
(`cas_leaf_contracts`) and `lean-categories`' semantic registry (`LeanCategories.Catalogue`), which it
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

/-- The kernel-purity gate (`CasGates.KernelPurity`): the build fails when the kernel or the leaf
contract refers to mathematics or runs proof search of its own (`specs/architecture.md`, "What must
be impossible"). A default target, so that no build of the kernel skips it. -/
@[default_target]
lean_lib CasGates where
  globs := #[.submodules `CasGates]

/-- Acceptance probes of the core over the catalogue; building the library runs them. The
permanent suite (`tests/acceptance`) is not compiled: `cas-harness` executes it, and
`scripts/compare_acceptance.py` judges a head against its base assertion by assertion. -/
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

/-- Run the acceptance suite over a leaves manifest (`CasTools.Harness`). -/
lean_exe «cas-harness» where
  root := `CasTools.HarnessMain
  supportInterpreter := true

/-- Kernel-axiom audit of the core and the probes; the audit runs while `CasTools.AxiomAudit`
elaborates. -/
lean_exe «cas-axiom-audit» where
  root := `CasTools.AxiomAuditMain
  supportInterpreter := true

/-- The notebook package's boundary and the demo notebook's cells, elaborated with their expected
values (generated with `notebooks/demo.ipynb` by `scripts/demo_notebook.py`). -/
lean_lib CasDslTests
