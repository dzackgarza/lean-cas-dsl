/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.ObjectCall
public meta import CasCatalogue.ObjectCall

public section

/-! # Elaborator of `obj%` (`CasCatalogue.ObjectCall`) -/

open Lean Elab Term

namespace CasCatalogue

@[term_elab objectCall] meta def elabObjectCallSyntax : TermElab := fun stx _ => do
  let some objectId := stx[1].isStrLit? | throwUnsupportedSyntax
  let some category := stx[4].isStrLit? | throwUnsupportedSyntax
  let args := stx[2].getArgs.map fun group => (⟨group[1]⟩ : Term)
  let realizer? := if stx[5].isNone then none else stx[5][1].isStrLit?
  elabObjectCall objectId args category realizer?

@[term_elab homCall] meta def elabHomCallSyntax : TermElab := fun stx _ => do
  let some category := stx[13].isStrLit? | throwUnsupportedSyntax
  elabHomCall ⟨stx[2]⟩ ⟨stx[6]⟩ ⟨stx[10]⟩ category

end CasCatalogue
