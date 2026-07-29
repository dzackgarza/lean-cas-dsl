/-
The prelude manifest: the module the `casdsl` kernelspec imports.

This is the plugin manifest in the sense of lean-jupyter-kernel
`docs/plugins.md` — the worker starts by importing exactly this module, and
whatever it transitively imports is what a notebook cell can see.

The prelude is the WHOLE library (`sage.all`-style), not a curated subset:
the root `CasDsl` module already pulls the surface syntax, the evaluator,
the diagnostics commands and the standard universe, and a notebook that saw
only part of that would be a second, silently different universe. Nothing
else belongs here — this file exists to name the entry point, not to
configure it.
-/
import CasDsl
