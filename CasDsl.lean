/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue
public import CasLeaves

/-!
# CasDsl — the notebook surface

Syntax only. A notebook cell is a Lean command over the core's surfaces — `method%`, `ask%`,
`refine%`, `eq%`, `cell%`, `memo%`, `run%`, `transport%`, `exec%`, `#resolve`, `#methods`,
`#audit` — applied to handles of registered realizers, with the registered limits, colimits,
adjunctions and backend leaves of the standard universe (`CasCatalogue`, `CasLeaves`).

This package declares nothing and registers nothing: every value is a kernel term from a
registered constructor or realizer, every operation a registered semantic operation, equality the
category's registered equality, and every backend is reached through its leaf. There are no
categories, typing rules, codecs or executors here (`CasDslTests.Boundary` checks it).
-/
