module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import CasCompiler.Parse
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest



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
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm written
    let expected ← session.readTerm direct
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "`let f(x, y) := e` is not `let f := (x, y) ↦ e`: {expression}"
    return expression
