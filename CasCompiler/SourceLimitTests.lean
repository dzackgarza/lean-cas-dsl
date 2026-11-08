module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

open Lean Meta Elab Term CasCompiler CasCatalogue

private def nativeTerm (text : String) : TermElabM Term := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `term text
    | throwError "the native limit parameter did not parse"
  return ⟨parsed⟩

private def sourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the source limit did not parse"
  return ⟨parsed⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Type")
  let session ← session.assume `Y (← nativeTerm "Type")
  for (text, declaration, colimit) in #[
      ("X × Y", ``CasCatalogue.Limits.Registration.setsProduct, false),
      ("X ⊔ Y", ``CasCatalogue.Limits.Registration.setsCoproduct, true)] do
    let object ← session.read (← sourceTerm text)
    let some category := object.category
      | throwError "the source limit lost its selected category"
    unless category.expression.syntacticEq (.atom CategoryId.sets) do
      throwError "the source limit changed its complete selected category"
    object.source.withOpen fun bindings value => do
      let presentation ← mkAppM declaration #[bindings[0]!.expression, bindings[1]!.expression]
      let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
      let expected ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt) #[cone]
      unless value.containsConst (· == declaration) &&
          value.containsFVar bindings[0]!.expression.fvarId! &&
          value.containsFVar bindings[1]!.expression.fvarId! && (← isDefEq value expected) do
        throwError "the source limit replaced its declared presentation or original objects"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.namedCategory Syntax.missing "Rings" [.param `u] #[]
  let ringType ← empty.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← rings.value.source.inContext context]
  let session ← empty.assumeTerm `R ringType
  let ring ← session.term (← nativeTerm "R")
  let modules ← session.namedCategory Syntax.missing "Modules" [.param `u, .param `v] #[ring]
  let moduleType ← session.elaborate Syntax.missing fun context => do
    mkAppM ``CategoryTheory.Bundled.α #[← modules.value.source.inContext context]
  let session ← session.assumeTerm `M moduleType
  let session ← session.assumeTerm `N moduleType
  let left ← session.term (← nativeTerm "M")
  let left ← left.inCategory modules.expression modules.value
  let right ← session.term (← nativeTerm "N")
  let right ← right.inCategory modules.expression modules.value
  let session ← session.defineTerm `A left
  let session ← session.defineTerm `B right
  let product ← session.read (← sourceTerm "A × B")
  for level in #[`u, `v] do
    unless product.source.universeParams.contains level do
      throwError "the source module product specialized an independent universe"
  product.source.withOpen fun bindings value => do
    let presentation ← mkAppM ``CasCatalogue.Limits.Registration.modulesProduct
      #[bindings[0]!.expression, bindings[3]!.expression, bindings[4]!.expression]
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let expected ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    unless value.containsFVar bindings[3]!.expression.fvarId! &&
        value.containsFVar bindings[4]!.expression.fvarId! && (← isDefEq value expected) do
      throwError "the source module product changed its selected modules or scalar action"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl value) (← mkEq value expected))
  let session ← session.defineTerm `P product
  let session ← session.assume `A (← nativeTerm "Type")
  let retained ← session.read (← sourceTerm "P")
  retained.source.withOpen fun bindings value => do
    unless value == bindings[5]!.expression do
      throwError "the product was reconstructed after an original name was shadowed"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let session ← session.assume `S (← nativeTerm "RingCat.{0}")
  let left ← session.read (← sourceTerm "RegularModule(R)")
  let right ← session.read (← sourceTerm "RegularModule(S)")
  let session ← session.defineTerm `A left
  let session ← session.defineTerm `B right
  let rejected ← try
    discard <| session.read (← sourceTerm "A × B")
    pure false
  catch error =>
    let message ← error.toMessageData.toString
    if !message.startsWith "source binary construction has different complete selected categories"
      then throw error
    pure true
  unless rejected do throwError "the source product merged independently selected scalar rings"
