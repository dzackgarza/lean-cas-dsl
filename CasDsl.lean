/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue

/-!
# CasDsl — the notebook surface

Syntax only. A notebook cell is a Lean command over the core's surfaces: a statement of the
language (`#cas "assert |Fin(3)| = 3"`), read from the catalogue and decided in Lean or through
the installed leaves' registrations (`CasCatalogue.TestSuite`); `#resolve` and `#methods`, the
resolution and the operation surface a category has; `cell%`, a composite of registered cells.

This package declares nothing and registers nothing: every value is a term of the catalogue's
mathematics, every operation a registered semantic operation, and every backend is reached only
through its registration in the leaves' manifest. There are no categories, typing rules, codecs or
executors here (`CasDslTests.Boundary` checks it).
-/
