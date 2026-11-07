module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.Lists
import LeanCategories.Catalogue.Semantics.Modules.Operations
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists
meta import LeanCategories.Catalogue.Semantics.Modules.Operations

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let categoryEntry ← selectCategory (← semanticState) "Sets"
  let levels := (← checkedDeclaration categoryEntry.declaration).levelParams.map Level.param
  let sets ← empty.namedCategory Syntax.missing "Sets" levels #[]
  let objectType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← sets.value.source.inContext context]
  let session ← empty.assume `h (← `(True))
  let cases := #[
    (NaturalTransformationId.listUnit, false),
    (NaturalTransformationId.listJoin, false),
    (NaturalTransformationId.listReverse, false),
    (NaturalTransformationId.listReverse, true)]
  for (id, inverse) in cases do
    let cell ← session.cell Syntax.missing id #[] sets inverse
    unless cell.transformation.source.context.entries.size == session.context.entries.size do
      throwError "whole source cell formation changed its complete formal scope"
    let objects ← session.assumeTerm `X objectType
    let object ← objects.term (← `(term| $(mkIdent `X):ident))
    let selected ← objects.cellComponent Syntax.missing cell object
    unless selected.cell.entry.id == id && selected.cell.inverse == inverse &&
        selected.value.source.context.entries.size == objects.context.entries.size do
      throwError "source cell formation changed its role, direction or complete scope"
    selected.value.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let transformation ← selected.cell.transformation.source.inContext context
      let left ← selected.cell.left.source.inContext context
      let right ← selected.cell.right.source.inContext context
      let expected ← mkAppM ``CategoryTheory.NatTrans #[left, right]
      unless ← isDefEq (← inferType transformation) expected do
        throwError "the retained transformation has different complete native endpoints"
      let actualObject ← selected.object.source.inContext context
      let component ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, actualObject]
      unless ← isDefEq value component do
        throwError "source component formation replaced its actual directed action"
      let declaration := Lean.mkConst selected.cell.entry.declaration levels
      let original ← if selected.cell.entry.invertible then
          mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom)
            #[declaration]
        else pure declaration
      let originalComponent ← mkAppM ``CategoryTheory.NatTrans.app #[original, actualObject]
      unless ← isDefEq value originalComponent do
        throwError "source component formation changed the independently declared component"
      unless value.getUsedConstants.contains selected.cell.entry.declaration &&
          value.containsFVar bindings[1]!.expression.fvarId! do
        throwError "source component formation discarded its declaration or generic object"
      checkWithKernel value
  let rejected ← try
    discard <| session.cell Syntax.missing NaturalTransformationId.listUnit #[] sets true
    pure false
  catch _ => pure true
  unless rejected do throwError "a noninvertible source cell acquired an inverse"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.namedCategory Syntax.missing "Rings" [.param `u] #[]
  let ringType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← rings.value.source.inContext context]
  let parameters ← empty.assumeTerm `R ringType
  let ring ← parameters.term (← `(term| $(mkIdent `R):ident))
  let modules ← parameters.namedCategory Syntax.missing "Modules" [.param `u, .param `u] #[ring]
  let arrows ← parameters.unaryCategory Syntax.missing ConstructorId.arrow modules
  let arrowType ← parameters.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← arrows.value.source.inContext context]
  for inverse in #[false, true] do
    let cell ← parameters.cell Syntax.missing ⟨"cell.modules.coimage_image"⟩ #[ring] arrows inverse
    let shadowed ← parameters.assumeTerm `R ringType
    let objects ← shadowed.assumeTerm `f arrowType
    let object ← objects.term (← `(term| $(mkIdent `f):ident))
    let selected ← objects.cellComponent Syntax.missing cell object
    selected.value.source.withOpen fun bindings value => do
      let context ← ContextTelescope.capture bindings
      let scalar := bindings[0]!.expression
      let object := bindings[2]!.expression
      let iso ← mkAppM ``CasCatalogue.Modules.Operations.coimageImageIso #[scalar]
      let transformation ← mkAppM
        (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[iso]
      let expected ← mkAppM ``CategoryTheory.NatTrans.app #[transformation, object]
      unless ← isDefEq value expected do
        throwError "the module comparison replaced its original scalar or directed component"
      unless value.containsFVar scalar.fvarId! && value.containsFVar object.fvarId! &&
          !value.containsFVar bindings[1]!.expression.fvarId! do
        throwError "the module comparison rebound an original source parameter after shadowing"
      let target ← selected.cell.target.value.source.inContext context
      let (_, actualTarget) ← functorCategoryBundles
        (← selected.cell.left.source.inContext context)
      unless ← isDefEq target actualTarget do
        throwError "the module comparison discarded its complete native target category"
      checkWithKernel value
    let otherRing ← objects.term (← `(term| $(mkIdent `R):ident))
    let otherModules ← objects.namedCategory Syntax.missing "Modules"
      [.param `u, .param `u] #[otherRing]
    let otherArrows ← objects.unaryCategory Syntax.missing ConstructorId.arrow otherModules
    let otherType ← objects.elaborate Syntax.missing fun context => do
      mkAppM ``CategoryTheory.Bundled.α #[← otherArrows.value.source.inContext context]
    let otherObjects ← objects.assumeTerm `g otherType
    let otherObject ← otherObjects.term (← `(term| $(mkIdent `g):ident))
    let rejected ← try
      discard <| otherObjects.cellComponent Syntax.missing cell otherObject
      pure false
    catch _ => pure true
    unless rejected do throwError "a source comparison changed its independently chosen scalar"
