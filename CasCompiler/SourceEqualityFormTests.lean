module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

open Lean Meta Elab Term CasCompiler

/- `a is b` is `a = b` (the grammar form `casIs`, `CasCompiler/Syntax.lean`): within a term it is
the same equality of the operands' common set. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "`{text}` did not parse"
    session.read ⟨source⟩
  let equation ← read "(2 in ℤ) = (3 in ℤ)"
  let written ← read "(2 in ℤ) is (3 in ℤ)"
  written.source.withOpen fun bindings expression => do
    let expected ← equation.source.inContext (← ContextTelescope.capture bindings)
    unless ← isDefEq expression expected do
      throwError "`a is b` is not `a = b`: {expression}"
