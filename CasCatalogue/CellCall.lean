/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.CellSyntax
public meta import CasCatalogue.CellSyntax

@[expose] public section

/-! The elaborator of `cell%` (`CasCatalogue.CellSyntax`). -/

open Lean Elab Term

namespace CasCatalogue

@[term_elab cellCall] meta def elabCellCallSyntax : TermElab := fun stx _ => do
  let some category := stx[7].isStrLit? | throwUnsupportedSyntax
  elabCellCall stx[1] ⟨stx[4]⟩ category

end CasCatalogue
