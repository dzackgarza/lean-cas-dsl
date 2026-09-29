/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics
public import CasLeaves
public import CasCatalogue.ResolveSyntax
public meta import CasCatalogue.ResolveSyntax

@[expose] public section

/-!
# Operation surfaces and implementation gaps, elaborated in one import set

The semantic registry and every leaf are imported. `CasAcceptance.StrataProbes` compares these with the other import set: the surfaces agree
and the gaps differ (`specs/architecture.md`, "Implementations are semantically neutral").
-/

namespace CasCatalogue.Surface

def realizedSurfaces : List String :=
  [closure_report% "cat.sets", closure_report% "cat.finite_sets", closure_report% "cat.groups",
   closure_report% "cat.bilin_module"]

def realizedGaps : List String :=
  [gaps_report% "cat.sets", gaps_report% "cat.finite_sets", gaps_report% "cat.groups",
   gaps_report% "cat.bilin_module"]

end CasCatalogue.Surface
