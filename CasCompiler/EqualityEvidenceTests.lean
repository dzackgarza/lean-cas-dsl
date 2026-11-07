module

import CasCompiler.Equality
import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import Lean.Elab.Command
meta import CasCompiler.Equality
meta import LeanCategories.Catalogue.Semantics.Foundation.PowerSets

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `h (← `(True))
  let category ← session.categoryFamily Syntax.missing "LinearOrders" [.zero]
  let routes ← SourceRoutes.forOperation category.expression "≤"
  let #[family] ← routes.operationFamilies session Syntax.missing #[] category
    | throwError "the actual source order binding is absent"
  let refinement ← session.operationRefinement Syntax.missing family
  let equality := refinement.asEquality
  let some conversion ← session.operationConversion Syntax.missing family family
    | throwError "the whole source-family conversion is absent"
  let identity := conversion.asEquality
  let symmetric ← session.equalitySymmetry Syntax.missing equality
  let transitive ← session.equalityTransitivity Syntax.missing identity equality
  let loop ← session.equalityTransitivity Syntax.missing equality symmetric
  for (evidence, reversed, reflexive) in
      #[(equality, false, false), (symmetric, true, false),
        (transitive, false, false), (loop, false, true)] do
    evidence.proof.source.withOpen fun bindings proof => do
      let context ← ContextTelescope.capture bindings
      let original ← family.term.source.inContext context
      let general ← refinement.term.source.inContext context
      let expected ← if reversed then mkEq general original
        else mkEq original (if reflexive then original else general)
      unless ← isDefEq (← evidence.proposition.source.inContext context) expected <&&>
          isDefEq (← inferType proof) expected do
        throwError "licensed equality composition changed its complete source-family equation"
      checkWithKernel (← mkExpectedTypeHint proof expected)
  let functionType ← session.elaborate Syntax.missing fun context => do
    let type ← inferType (← family.term.source.inContext context)
    mkArrow type type
  let functions ← session.assumeTerm `F functionType
  let functions ← functions.assumeTerm `G functionType
  let F ← functions.term (← `(term| $(mkIdent `F):ident))
  let G ← functions.term (← `(term| $(mkIdent `G):ident))
  let congruent ← functions.equalityCongruence Syntax.missing F equality
  congruent.proof.source.withOpen fun bindings proof => do
    let context ← ContextTelescope.capture bindings
    let function ← F.source.inContext context
    let left := mkApp function (← family.term.source.inContext context)
    let right := mkApp function (← refinement.term.source.inContext context)
    let expected ← mkEq left right
    unless ← isDefEq (← congruent.proposition.source.inContext context) expected <&&>
        isDefEq (← inferType proof) expected do
      throwError "source equality congruence discarded its actual rigid function or family terms"
    let .congruence original (.operationRefinement retained) := congruent.derivation
      | throwError "source equality congruence lost its original registered proof derivation"
    unless original.source.expression == F.source.expression &&
        retained.base.id == refinement.base.id do
      throwError "source equality congruence changed its original function or source proof role"
    checkWithKernel (← mkExpectedTypeHint proof expected)
  let other ← functions.equalityCongruence Syntax.missing G symmetric
  let rejected ← try
    discard <| functions.equalityTransitivity Syntax.missing congruent other
    pure false
  catch _ => pure true
  unless rejected do
    throwError "equality transitivity identified independently rigid intermediate functions"
