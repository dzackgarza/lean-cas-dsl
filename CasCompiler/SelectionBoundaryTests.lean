module

import CasCompiler.Resolve
import CasContract.Failure
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import CasContract.Failure
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.Algebra.MonoidOperationAgreement

open Lean Meta Elab Term CasCompiler CasCatalogue

/-- Accept only the required semantic rejection; unexpected checker failures fail the control. -/
private def expectInvalidSelection (action : TermElabM Unit) : TermElabM Unit := do
  let outcome ← try
    action
    pure none
  catch error => pure (some error)
  match outcome with
  | none => throwError "a missing or unlicensed required selection was admitted"
  | some error =>
    unless CasCatalogue.Exception.stratum? error == some Stratum.invalid do
      throw error

private def expectSourceAmbiguity (action : TermElabM Unit) : TermElabM Unit := do
  let outcome ← try
    action
    pure none
  catch error => pure (some error)
  match outcome with
  | none => throwError "missing whole-family agreement silently selected a reading"
  | some error =>
    unless CasCatalogue.Exception.isSemanticAmbiguity error do
      throw error

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
  let unit ← session.cell Syntax.missing NaturalTransformationId.listUnit #[] sets
  let reverse ← session.cell Syntax.missing NaturalTransformationId.listReverse #[] sets
  unless unit.isomorphism.isNone && reverse.isomorphism.isSome do
    throwError "the source-selected cells lost their actual invertibility distinction"
  expectInvalidSelection do
    discard <| session.inverseCell Syntax.missing unit
  expectInvalidSelection do
    discard <| session.composeCells Syntax.missing reverse unit

  let identity ← session.identityFunctor Syntax.missing sets
  let lists ← session.namedFunctor Syntax.missing FunctorId.setsList #[] sets
  let entered ← liftM (m := IO) (IO.mkRef false)
  expectInvalidSelection do
    discard <| session.requireSelectedCell Syntax.missing lists lists none
    liftM (m := IO) (entered.set true)
  if ← liftM (m := IO) entered.get then
    throwError "a continuation ran after required selected data were absent"
  expectInvalidSelection do
    discard <| session.requireSelectedCell Syntax.missing lists lists (some unit)
  let selectedUnit ← session.requireSelectedCell Syntax.missing identity lists (some unit)
  unless selectedUnit.isomorphism.isNone do
    throwError "requiring a directed cell invented an inverse"

  -- Two actual source programs with the same boundary may both be selected.
  -- Retain each program; there is no requirement to identify their chosen actions.
  let inverse ← session.inverseCell Syntax.missing reverse
  let double ← session.composeCells Syntax.missing reverse inverse
  let selectedReverse ← session.requireSelectedCell Syntax.missing lists lists (some reverse)
  let selectedDouble ← session.requireSelectedCell Syntax.missing lists lists (some double)
  let .registered reverseEntry _ _ := selectedReverse.derivation
    | throwError "selected reversal was replaced by another source derivation"
  unless reverseEntry.id == NaturalTransformationId.listReverse do
    throwError "selected reversal lost its original source declaration"
  let .vertical _ _ := selectedDouble.derivation
    | throwError "selected composite was replaced by another source derivation"
  let objectType ← session.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← sets.value.source.inContext context]
  let objects ← session.assumeTerm `X objectType
  let object ← objects.term (← `(term| $(mkIdent `X):ident))
  expectInvalidSelection do
    discard <| objects.requiredCellComponent Syntax.missing lists lists none object
  for original in #[reverse, double] do
    let component ← objects.requiredCellComponent Syntax.missing lists lists (some original) object
    component.value.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let actual ← original.transformation.source.inContext context
      let argument ← object.source.inContext context
      let expected ← mkAppM ``CategoryTheory.NatTrans.app #[actual, argument]
      unless ← isDefEq value expected do
        throwError "selected component use changed the actual chosen action"
      checkWithKernel value
  let otherSets ← session.namedCategory Syntax.missing "Sets"
    (levels.map fun _ => .param `otherUniverse) #[]
  let otherLists ← session.namedFunctor Syntax.missing FunctorId.setsList #[] otherSets
  expectInvalidSelection do
    discard <| session.requireSelectedCell Syntax.missing otherLists otherLists (some reverse)

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let session ← SourceSession.empty identities
  let rings ← session.categoryFamily Syntax.missing "Rings" [.zero]
  let additions ← SourceRoutes.forOperation rings.expression "+"
  let multiplications ← SourceRoutes.forOperation rings.expression "·"
  let #[addition] ← additions.operationFamilies session Syntax.missing #[] rings
    | throwError "the original ring addition family is absent"
  let #[multiplication] ← multiplications.operationFamilies session Syntax.missing #[] rings
    | throwError "the original ring multiplication family is absent"
  let converted ← session.requireOperationAgreement Syntax.missing addition addition
  let supplied ← session.requireOperationAgreement Syntax.missing addition addition
    (some converted.proof)
  supplied.proof.source.withOpen fun bindings proof => do
    let context ← ContextTelescope.capture bindings
    let goal ← supplied.proposition.source.inContext context
    unless ← isDefEq (← inferType proof) goal do
      throwError "supplied agreement lost its exact whole-family equation"
    checkWithKernel (← mkExpectedTypeHint proof goal)
  expectSourceAmbiguity do
    discard <| session.requireOperationAgreement Syntax.missing addition multiplication
  let unrelated ← session.term (← `(term| True.intro))
  -- Bad supplied evidence is not ignored even when conversion would otherwise succeed.
  expectInvalidSelection do
    discard <| session.requireOperationAgreement Syntax.missing addition addition (some unrelated)
  expectInvalidSelection do
    discard <| session.requireOperationAgreement Syntax.missing addition multiplication
      (some converted.proof)
  let sets ← session.namedCategory Syntax.missing "Sets" [.zero] #[]
  let reverse ← session.cell Syntax.missing NaturalTransformationId.listReverse #[] sets
  expectInvalidSelection do
    discard <| session.requireOperationAgreement Syntax.missing addition addition
      (some reverse.transformation)
