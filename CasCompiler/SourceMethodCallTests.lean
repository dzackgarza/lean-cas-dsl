module

import CasCompiler.Read
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/- `m(X)` for a registered method `m` is `X.m()`: `cardinality(Fin(3))` is the method of the
bars `|Fin(3)|`. The name `cardinality` names a method and no object, map or construction. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "`{text}` did not parse"
    session.read ⟨source⟩
  let bars ← read "|Fin(3)|"
  let called ← read "cardinality(Fin(3))"
  called.source.withOpen fun bindings expression => do
    let expected ← bars.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq expression expected do
      throwError "`cardinality(Fin(3))` is not `|Fin(3)|`: {expression}"
