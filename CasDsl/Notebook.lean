/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasDsl

/-!
The prelude: the module the `casdsl` kernelspec imports (lean-jupyter-kernel `docs/plugins.md`).
It is the whole catalogue with the language; a notebook sees exactly what the core reads from
`lean-categories`, and computes through whatever leaves' manifest is installed.
-/
