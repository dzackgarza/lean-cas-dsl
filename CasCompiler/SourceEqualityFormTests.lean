module

import CasCompiler.Read
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Algebra.NamedRings

open Lean Meta Elab Term CasCompiler CasCompiler.SourceTest



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let read := fun (text : String) => do
    let .ok source := Parser.runParserCategory (← getEnv) `cas_term text
      | throwError "`{text}` did not parse"
    session.read ⟨source⟩
  let equation ← read "(2 in ℤ) = (3 in ℤ)"
  let written ← read "(2 in ℤ) is (3 in ℤ)"
  checkSelected written fun expression => do
    let expected ← session.readTerm equation
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "`a is b` is not `a = b`: {native[0]!}"



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
  checkSelected both fun expression => do
    let first ← session.readTerm first
    let second ← session.readTerm second
    let expected ← mkAppM ``And #[first, second]
    checkOriginal #[expression, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "`p and q` is not the conjunction of `p` and `q`: {native[0]!}"
