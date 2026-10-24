/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasTools.QuestionExport
public meta import CasTools.QuestionExport

@[expose] public section

/-- Entry point for the interpretation-only fixed-question exporter. -/
def main (args : List String) : IO UInt32 :=
  CasCatalogue.Tools.QuestionExport.main args
