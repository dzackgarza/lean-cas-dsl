/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasTools.Harness

@[expose] public section

/-- Lake entry point for the harness. -/
def main (args : List String) : IO UInt32 :=
  CasCatalogue.Tools.Harness.main args
