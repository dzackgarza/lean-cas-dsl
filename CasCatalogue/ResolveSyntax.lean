/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public meta import CasCatalogue.Resolve

@[expose] public section

/-!
# Surface syntax for method resolution

* `#resolve name in "cat.id"` reports the route of `x.name` for `x` in the registered category
  `cat.id` (`CasCatalogue.reportResolution`), or why there is none; `via "fun.id"` requires the
  route to pass through a registered functor, selecting a port.
* `#methods "cat.id"` reports the generated operation surface of a category (CC-CLOSURE), and
  `closure_report% "cat.id"` is the same report as a string literal.

`via` is a non-reserved token. What a call is worth is not a Lean term of these surfaces: a
statement of the language (`CasCatalogue.Language`) is read semantically and then decided
(`CasCatalogue.Realize`).
-/

open Lean Elab Term Command

namespace CasCatalogue

syntax (name := methodsCommand) "#methods " str : command

/-- `closure_report% "cat.id"`: the operation surface as a string literal. -/
syntax (name := closureReportTerm) "closure_report% " str : term

syntax (name := resolveCommand) "#resolve " ident " in " str (&" via " str)* : command

/-- The strings of a trailing `(&" via " str)*` group. -/
meta def viaStrings (group : Syntax) : Array String :=
  group.getArgs.filterMap fun through => through[1].isStrLit?

@[command_elab methodsCommand] meta def elabMethodsCommand : CommandElab := fun stx => do
  let some category := stx[1].isStrLit? | throwUnsupportedSyntax
  liftTermElabM <| reportClosure category

@[term_elab closureReportTerm] meta def elabClosureReportTerm : TermElab := fun stx _ => do
  let some category := stx[1].isStrLit? | throwUnsupportedSyntax
  return toExpr (← closureReport category)

@[command_elab resolveCommand] meta def elabResolveCommand : CommandElab := fun stx => do
  let some category := stx[3].isStrLit? | throwUnsupportedSyntax
  liftTermElabM <| reportResolution stx[1].getId.eraseMacroScopes.toString category (viaStrings stx[4])

end CasCatalogue
