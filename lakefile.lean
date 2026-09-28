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
  "https://github.com/dzackgarza/lean-categories" @ "aaf7af3ea111f0740388abbaaa36719c508c8e08"

@[default_target]
lean_lib CasDsl where
  -- the prelude module `CasDsl.Notebook` imports the root, not vice versa,
  -- so the lib must glob submodules or the kernelspec's olean is never built
  globs := #[.andSubmodules `CasDsl]

/-- The semantic registry: symbolic category and functor expressions, their checked
denotations in `lean-categories`, and the normalized registry with its exporter. It keeps
`lean-categories`' elaboration options, which its registration rows rely on. -/
lean_lib CasCatalogue where
  globs := #[.andSubmodules `CasCatalogue]
  leanOptions := #[
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩]

/-- Export the normalized registry manifest as JSON. -/
lean_exe «cas-registry-export» where
  root := `CasCatalogue.Tools.ExportMain
  supportInterpreter := true

/-- Kernel-axiom audit of the registry; the audit runs while `CasCatalogue.Tools.AxiomAudit`
elaborates. -/
lean_exe «cas-axiom-audit» where
  root := `CasCatalogue.Tools.AxiomAuditMain
  supportInterpreter := true

/-- Elaboration-time tests (`#guard` + `run_cmd` assertions); not part of
the shipped prelude import graph. -/
lean_lib CasDslTests
