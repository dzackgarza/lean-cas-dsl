module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.PowerSets

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `h (← `(True))
  let category ← session.categoryFamily Syntax.missing "LinearOrders" [.zero]
  let routes ← SourceRoutes.forOperation category.expression "≤"
  let #[family] ← routes.operationFamilies session Syntax.missing #[] category
    | throwError "the actual first linear-order operation binding is absent"
  let some original := family.binding.refines
    | throwError "the actual source operation lost its declared restriction equality"
  let result ← session.operationRefinement Syntax.missing family
  unless result.original.binding.id == family.binding.id && result.base.id == original.base &&
      result.original.route.refs == family.route.refs &&
      result.route.refs == family.route.refs ++ original.route do
    throwError "whole-operation restriction changed an original binding or ordered source route"
  unless result.proof.source.context.entries.size == session.context.entries.size do
    throwError "whole-operation restriction discarded the complete formal source scope"
  result.proof.source.withOpen fun bindings proof => do
    let context ← ContextTelescope.capture bindings
    let left ← family.term.source.inContext context
    let right ← result.term.source.inContext context
    let expected ← mkEq left right
    unless ← isDefEq (← result.proposition.source.inContext context) expected <&&>
        isDefEq (← inferType proof) expected do
      throwError "the source restriction evidence proves a different complete family equation"
    unless proof.getUsedConstants.contains original.identification do
      throwError "the source restriction discarded its independently declared equality"
    lambdaTelescope right fun parameters body => do
      unless parameters.size == 1 && body.containsFVar parameters[0]!.fvarId! &&
          (← whnfR (← inferType body)).isAppOf ``Quiver.Hom do
        throwError "the source restriction specialized its generic object or applied operands"
    checkWithKernel (← mkExpectedTypeHint proof expected)
  let some #[initial] ← routes.finiteRoutes
    | throwError "source restriction changed the original finite first-binding reading family"
  unless initial.steps.isEmpty do
    throwError "source restriction bypassed the original first operation binding"
  let strict ← SourceRoutes.forOperation category.expression "<"
  let #[strictFamily] ← strict.operationFamilies session Syntax.missing #[] category
    | throwError "the actual strict-order source binding is absent"
  let failure : Option Exception ← try
    discard <| session.operationRefinement Syntax.missing strictFamily
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "an operation acquired an unregistered restriction equality"
  unless (← failure.toMessageData.toString).startsWith
      "the source operation has no registered restriction equality" do throw failure
