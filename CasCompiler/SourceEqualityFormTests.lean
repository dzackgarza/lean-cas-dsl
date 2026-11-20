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

/- `p and q` inside a term is the conjunction of the two statements as read, as it is at the top
of a question. Formation does not decide either statement. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "`{text}` did not parse"
    session.read ⟨source⟩
  let first ← read "(2 in ℤ) = (3 in ℤ)"
  let second ← read "(5 in ℤ) = (5 in ℤ)"
  let both ← read "((2 in ℤ) = (3 in ℤ)) and ((5 in ℤ) = (5 in ℤ))"
  both.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let expected ← mkAppM ``And #[← first.source.inContext context, ← second.source.inContext context]
    unless ← isDefEq expression expected do
      throwError "`p and q` is not the conjunction of `p` and `q`: {expression}"
