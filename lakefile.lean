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
    @ "0008bda2c69f76abceab92a0b4a4e1b32d65f5c9" / "worker"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib CasDsl where
  -- the prelude module `CasDsl.Notebook` imports the root, not vice versa,
  -- so the lib must glob submodules or the kernelspec's olean is never built
  globs := #[.andSubmodules `CasDsl]

/-- Elaboration-time tests (`#guard` + `run_cmd` assertions); not part of
the shipped prelude import graph. -/
lean_lib CasDslTests
