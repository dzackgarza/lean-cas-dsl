module

import CasCompiler.Read
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects

open Lean Meta Elab Term CasCompiler

private def readSource (session : SourceSession) (text : String) : TermElabM SourceTerm := do
  let .ok stx := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the categorical source binding did not parse"
  session.read ⟨stx⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let refined ← readSource empty "Fin(3) in FiniteSets"
  let first ← empty.defineTerm `X refined
  let same ← readSource first "X in FiniteSets"
  unless same.source.expression == mkBVar 0 do
    throwError "source qualification replaced the retained object by its definition"
  let aliased ← first.defineTerm `Y same
  let plain ← readSource aliased "Fin(3)"
  let shadowed ← aliased.defineTerm `X plain
  let retained ← readSource shadowed "Y in FiniteSets"
  unless retained.source.expression == mkBVar 1 do
    throwError "a shadowed source definition changed its earlier selected category"
  let plain ← readSource shadowed "X in Sets"
  unless plain.source.expression == mkBVar 0 do
    throwError "source qualification lost the actual latest lexical binding"
  let failure : Option Exception ← try
    discard <| readSource shadowed "X in FiniteSets"
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "equal carriers silently changed a retained object's selected category"
  unless (← failure.toMessageData.toString).startsWith
      "the retained source value has a different selected category" do throw failure
