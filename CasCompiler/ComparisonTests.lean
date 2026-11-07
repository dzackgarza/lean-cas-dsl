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
    let .registered entry arguments direction := selected.cell.derivation
      | throwError "the original source cell lost its registered derivation"
    unless entry.id == id && direction == inverse && arguments.isEmpty &&
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
      let declaration := Lean.mkConst entry.declaration levels
      let original ← if entry.invertible then
          mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom)
            #[declaration]
        else pure declaration
      let originalComponent ← mkAppM ``CategoryTheory.NatTrans.app #[original, actualObject]
      unless ← isDefEq value originalComponent do
        throwError "source component formation changed the independently declared component"
      unless value.getUsedConstants.contains entry.declaration &&
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

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let entry ← selectCategory (← semanticState) "Sets"
  let levels := (← checkedDeclaration entry.declaration).levelParams.map Level.param
  let sets ← empty.namedCategory Syntax.missing "Sets" levels #[]
  let objectType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← sets.value.source.inContext context]
  let join ← empty.cell Syntax.missing NaturalTransformationId.listJoin #[] sets
  let reverse ← empty.cell Syntax.missing NaturalTransformationId.listReverse #[] sets
  let composite ← empty.composeCells Syntax.missing join reverse
  let .vertical (.registered first _ _) (.registered second _ _) := composite.derivation
    | throwError "vertical composition lost its original directed derivations"
  unless first.id == NaturalTransformationId.listJoin &&
      second.id == NaturalTransformationId.listReverse do
    throwError "vertical composition reordered its original source cells"
  let reversed ← reverse.inverse
  let invertible ← empty.composeCells Syntax.missing reverse reversed
  let inverted ← invertible.inverse
  let objects ← empty.assumeTerm `X objectType
  let object ← objects.term (← `(term| $(mkIdent `X):ident))
  for (cell, invert) in #[(composite, false), (inverted, true)] do
    let component ← objects.cellComponent Syntax.missing cell object
    component.value.source.withOpen fun bindings value => do
      let join := Lean.mkConst ``CasCatalogue.Foundation.Lists.listJoinCell levels
      let reverse := Lean.mkConst ``CasCatalogue.Foundation.Lists.listReverseCell levels
      let hom ← mkAppM ``CategoryTheory.Iso.hom #[reverse]
      let inv ← mkAppM ``CategoryTheory.Iso.inv #[reverse]
      let expected ← if invert then
          mkAppM ``CategoryTheory.CategoryStruct.comp #[hom, inv]
        else mkAppM ``CategoryTheory.CategoryStruct.comp #[join, hom]
      let expected ← mkAppM ``CategoryTheory.NatTrans.app #[expected, bindings[0]!.expression]
      unless ← isDefEq value expected do
        throwError "cell composition changed its actual source action or inverse order"
      checkWithKernel value
  let invalidOrder ← try
    discard <| empty.composeCells Syntax.missing reverse join
    pure false
  catch _ => pure true
  unless invalidOrder do throwError "cell composition ignored its complete middle functor"
  let invalidInverse ← try
    discard <| composite.inverse
    pure false
  catch _ => pure true
  unless invalidInverse do throwError "a composite acquired an inverse of a noninvertible source cell"
