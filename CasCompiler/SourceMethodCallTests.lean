module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler
open CasCompiler.SourceTest



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "`{text}` did not parse"
    session.read ⟨source⟩
  let bars ← read "|Fin(3)|"
  let called ← read "cardinality(Fin(3))"
  discard <| session.elaborateScoped Syntax.missing do
    let expression ← session.readTerm called
    let expected ← session.readTerm bars
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "`cardinality(Fin(3))` is not `|Fin(3)|`: {native[0]!}"
    return expression
