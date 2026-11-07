module

import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.Lists
public meta import Lean.Elab.Command
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.Lists

open Lean Meta Elab Term CasCompiler CasCatalogue

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let entry ← selectCategory (← semanticState) "Sets"
  let levels := (← checkedDeclaration entry.declaration).levelParams.map Level.param
  let sets ← empty.namedCategory Syntax.missing "Sets" levels #[]
  let objectType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← sets.value.source.inContext context]
  let session ← empty.assume `h (← `(True))
  let named ← session.namedFunctor Syntax.missing FunctorId.setsList #[] sets
  let .registered original arguments := named.derivation
    | throwError "explicit functor formation lost its actual registered source"
  unless original.id == FunctorId.setsList && !original.structural && arguments.isEmpty do
    throwError "explicit functor formation changed its source role or structural status"
  let routes ← SourceRoutes.forOwner sets.expression sets.expression
  let route ← routes.prepareFunctor session Syntax.missing #[] sets
  let structural := route.asFunctor
  for functor in #[named, structural] do
    for (id, invertible) in #[(NaturalTransformationId.listJoin, false),
        (NaturalTransformationId.listReverse, true)] do
      let cell ← session.cell Syntax.missing id #[] sets
      for side in #[WhiskerSide.left, WhiskerSide.right] do
        let whiskered ← session.whiskerCell Syntax.missing side functor cell
        unless whiskered.transformation.source.context.entries.size ==
            session.context.entries.size && whiskered.isomorphism.isSome == invertible do
          throwError "whiskering changed complete source scope or invertibility authority"
        let objects ← session.assumeTerm `X objectType
        let object ← objects.term (← `(term| $(mkIdent `X):ident))
        let component ← objects.cellComponent Syntax.missing whiskered object
        component.value.source.withOpen fun bindings value => do
          let context ← ContextTelescope.capture bindings
          let F ← match functor.derivation with
            | .registered entry _ => pure (Lean.mkConst entry.declaration levels)
            | .structural _ =>
              let carrier ← mkAppM ``CategoryTheory.Bundled.α
                #[← sets.value.source.inContext context]
              let category ← mkAppM ``CategoryTheory.Bundled.str
                #[← sets.value.source.inContext context]
              mkAppOptM ``CategoryTheory.Functor.id #[some carrier, some category]
          unless ← isDefEq F (← functor.functor.source.inContext context) do
            throwError "the retained functor differs from its original source declaration"
          let .registered entry _ _ := cell.derivation
            | throwError "the actual whiskering cell lost its original source row"
          let declaration := Lean.mkConst entry.declaration levels
          let transformation ← if invertible then
              mkAppM ``CategoryTheory.Iso.hom #[declaration]
            else pure declaration
          let expected ← match side with
            | .left => mkAppM ``CategoryTheory.Functor.whiskerLeft #[F, transformation]
            | .right => mkAppM ``CategoryTheory.Functor.whiskerRight #[transformation, F]
          let expected ← mkAppM ``CategoryTheory.NatTrans.app #[expected, bindings[1]!.expression]
          unless ← isDefEq value expected do
            throwError "whiskering changed its original source functor or directed cell action"
          checkWithKernel value
        if invertible then
          let inverse ← objects.inverseCell Syntax.missing whiskered
          let component ← objects.cellComponent Syntax.missing inverse object
          component.value.source.withOpen fun bindings value => do
            let context ← ContextTelescope.capture bindings
            let some iso := whiskered.isomorphism
              | throwError "invertible whiskering lost its native isomorphism"
            let iso ← iso.source.inContext context
            let expected ← mkAppM ``CategoryTheory.Iso.inv #[iso]
            let expected ← mkAppM ``CategoryTheory.NatTrans.app #[expected, bindings[1]!.expression]
            unless ← isDefEq value expected do
              throwError "inverse whiskering discarded its actual source inverse action"
            checkWithKernel iso
            checkWithKernel value
  let otherSets ← session.namedCategory Syntax.missing "Sets"
    (levels.map fun _ => .param `otherUniverse) #[]
  let otherCell ← session.cell Syntax.missing NaturalTransformationId.listReverse #[] otherSets
  for side in #[WhiskerSide.left, WhiskerSide.right] do
    let rejected ← try
      discard <| session.whiskerCell Syntax.missing side named otherCell
      pure false
    catch _ => pure true
    unless rejected do throwError "whiskering specialized incompatible rigid category universes"
