module

import CasCompiler.Resolve
import CasContract.Failure
import LeanCategories.Catalogue.Semantics.Foundation.Lists
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import CasContract.Failure
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists

open Lean Meta Elab Term CasCompiler CasCatalogue

/-- An established invalid source selection is not an internal compiler failure.
Unexpected checker/resource exceptions are deliberately not accepted by this control. -/
private def expectInvalidSelection (action : TermElabM Unit) : TermElabM Unit := do
  let outcome ← try
    action
    pure none
  catch error => pure (some error)
  match outcome with
  | none => throwError "a missing or unlicensed required selection was admitted"
  | some error =>
    unless CasCatalogue.Exception.stratum? error == some Stratum.invalid do
      throwError "the selection boundary lost its invalid stratum: {error.toMessageData}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let entry ← selectCategory (← semanticState) "Sets"
  let levels := (← checkedDeclaration entry.declaration).levelParams.map Level.param
  let sets ← session.namedCategory Syntax.missing "Sets" levels #[]
  expectInvalidSelection do
    discard <| session.cell Syntax.missing ⟨"cell.absent.required-selection-control"⟩ #[] sets
  expectInvalidSelection do
    discard <| session.cell Syntax.missing NaturalTransformationId.listUnit #[] sets true
  -- A present directed cell and a legitimately invertible comparison remain usable.
  let unit ← session.cell Syntax.missing NaturalTransformationId.listUnit #[] sets
  let reverse ← session.cell Syntax.missing NaturalTransformationId.listReverse #[] sets
  unless unit.isomorphism.isNone && reverse.isomorphism.isSome do
    throwError "the source-selected cells lost their actual invertibility distinction"
  expectInvalidSelection do
    discard <| session.inverseCell Syntax.missing unit
  expectInvalidSelection do
    discard <| session.composeCells Syntax.missing reverse unit
