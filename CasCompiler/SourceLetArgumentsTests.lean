module

import CasCompiler.Read
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler

/- `let f(x, y) := e in D` is `let f := (x, y) ↦ e in D`: the public definition of a map with
several parameters (tests/acceptance, statement form `casLetArgs`). -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let file ← SourceFile.parse "source-let-args.cas"
    "let direct := (x, y) ↦ x in (ℤ × ℤ) → ℤ\nlet written(x, y) := x in (ℤ × ℤ) → ℤ\n"
  let mut session ← SourceSession.empty identities
  let mut values := #[]
  for item in file.items do
    let `(cas_item| $statement:cas_stmt) := item
      | throwError "a definition did not parse"
    let .definition next value ← file.withContext (session.readStatement statement)
      | throwError "a definition did not extend its source context"
    session := next
    values := values.push value
  let #[direct, written] := values | throwError "two definitions were expected"
  written.source.withOpen fun bindings expression => do
    let expected ← direct.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq expression expected do
      throwError "`let f(x, y) := e` is not `let f := (x, y) ↦ e`: {expression}"
