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

* `method% name (x) in "cat.id"` elaborates `x.name` for `x` in the registered category
  `cat.id` (`CasCatalogue.elabMethodCall`); `via "fun.id"` requires the route to pass through a
  registered functor, selecting a port.
* `#resolve name in "cat.id"` reports the route, or why there is none.

`via` is a non-reserved token.
-/

open Lean Elab Term Command

namespace CasCatalogue

syntax (name := methodCall) "method% " ident " (" term ") " "in " str (&" via " str)* : term

syntax (name := resolveCommand) "#resolve " ident " in " str (&" via " str)* : command

/-- The strings of a trailing `(&" via " str)*` group. -/
meta def viaStrings (group : Syntax) : Array String :=
  group.getArgs.filterMap fun through => through[1].isStrLit?

@[term_elab methodCall] meta def elabMethodCallSyntax : TermElab := fun stx _ => do
  let some category := stx[6].isStrLit? | throwUnsupportedSyntax
  elabMethodCall stx[1].getId.eraseMacroScopes.toString ⟨stx[3]⟩ category (viaStrings stx[7])

@[command_elab resolveCommand] meta def elabResolveCommand : CommandElab := fun stx => do
  let some category := stx[3].isStrLit? | throwUnsupportedSyntax
  liftTermElabM <| reportResolution stx[1].getId.eraseMacroScopes.toString category (viaStrings stx[4])

end CasCatalogue
