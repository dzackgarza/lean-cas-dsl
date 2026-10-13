/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasTools.ExportFull

@[expose] public section

/-- Lake entry point for the Lean-registry exporter. -/
def main : IO UInt32 :=
  CasCatalogue.Tools.ExportFull.main
