/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.LimitCall
public meta import CasCatalogue.LimitCall

public section

/-! # Elaborators of `limit%` and `colimit%` (`CasCatalogue.LimitCall`) -/

open Lean Elab Term

namespace CasCatalogue

@[term_elab limitCall] meta def elabLimitCallSyntax : TermElab := fun stx _ => do
  let some category := stx[6].isStrLit? | throwUnsupportedSyntax
  elabLimitCall false stx[1].getId.eraseMacroScopes.toString ⟨stx[3]⟩ category

@[term_elab colimitCall] meta def elabColimitCallSyntax : TermElab := fun stx _ => do
  let some category := stx[6].isStrLit? | throwUnsupportedSyntax
  elabLimitCall true stx[1].getId.eraseMacroScopes.toString ⟨stx[3]⟩ category

end CasCatalogue
