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
* `ask% name (x) in "cat.id"` decides the property `name` of `x` (CC-PROP): a `Decision` from the
  classifier's registered decision procedure, applied to the image of `x` along the route.
* `#resolve name in "cat.id"` reports the route, or why there is none.
* `#methods "cat.id"` reports the generated operation surface of a category (CC-CLOSURE).
* `run% name (x) in "cat.id"` (optionally `using "impl.id"`) is `x.name` with its epistemic
  status and provenance (CC-TRUST); `#audit name in "cat.id"` lists its one owner and every
  realization (CC-ROUTE).
* `transport% (x) from K₁ to K₂` moves an element along a registered isomorphism (CC-CARRIER).

`via` is a non-reserved token.
-/

open Lean Elab Term Command

namespace CasCatalogue

syntax (name := methodCall) "method% " ident " (" term ") " "in " str (&" via " str)* : term

syntax (name := propertyQuery) "ask% " ident " (" term ") " "in " str (&" via " str)* : term

syntax (name := methodsCommand) "#methods " str : command

syntax (name := runCall) "run% " ident " (" term ") " "in " str (&" using " str)? (&" proved")? :
  term

syntax (name := auditCommand) "#audit " ident " in " str : command

syntax (name := transportCall) "transport% " "(" term ")" &" from " ident &" to " ident : term

syntax (name := resolveCommand) "#resolve " ident " in " str (&" via " str)* : command

/-- `exec% e`: the executable form of `e` (`executable`), for evaluating realized actions whose
denotations are noncomputable. -/
syntax (name := execTerm) "exec% " term:max : term

/-- The strings of a trailing `(&" via " str)*` group. -/
meta def viaStrings (group : Syntax) : Array String :=
  group.getArgs.filterMap fun through => through[1].isStrLit?

@[term_elab methodCall] meta def elabMethodCallSyntax : TermElab := fun stx _ => do
  let some category := stx[6].isStrLit? | throwUnsupportedSyntax
  elabMethodCall stx[1].getId.eraseMacroScopes.toString ⟨stx[3]⟩ category (viaStrings stx[7])

@[term_elab propertyQuery] meta def elabPropertyQuerySyntax : TermElab := fun stx _ => do
  let some category := stx[6].isStrLit? | throwUnsupportedSyntax
  elabPropertyQuery stx[1].getId.eraseMacroScopes.toString ⟨stx[3]⟩ category (viaStrings stx[7])

@[term_elab runCall] meta def elabRunSyntax : TermElab := fun stx _ => do
  let some category := stx[6].isStrLit? | throwUnsupportedSyntax
  let implementation := if stx[7].getNumArgs > 0 then stx[7][1].isStrLit? else none
  elabRun stx[1].getId.eraseMacroScopes.toString ⟨stx[3]⟩ category implementation
    (stx[8].getNumArgs > 0)

@[command_elab auditCommand] meta def elabAuditCommand : CommandElab := fun stx => do
  let some category := stx[3].isStrLit? | throwUnsupportedSyntax
  liftTermElabM <| reportAudit stx[1].getId.eraseMacroScopes.toString category

@[term_elab transportCall] meta def elabTransportSyntax : TermElab := fun stx _ =>
  elabTransport ⟨stx[2]⟩ ⟨stx[5]⟩ ⟨stx[7]⟩

@[term_elab execTerm] meta def elabExecTerm : TermElab := fun stx expected? => do
  let e ← elabTerm stx[1] expected?
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  Meta.mkExpectedTypeHint (← executable e) (← executableType (← Meta.inferType e))

@[command_elab methodsCommand] meta def elabMethodsCommand : CommandElab := fun stx => do
  let some category := stx[1].isStrLit? | throwUnsupportedSyntax
  liftTermElabM <| reportClosure category

@[command_elab resolveCommand] meta def elabResolveCommand : CommandElab := fun stx => do
  let some category := stx[3].isStrLit? | throwUnsupportedSyntax
  liftTermElabM <| reportResolution stx[1].getId.eraseMacroScopes.toString category (viaStrings stx[4])

end CasCatalogue
