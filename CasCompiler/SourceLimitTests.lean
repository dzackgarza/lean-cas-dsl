module

import CasCompiler.Read
import CasCompiler.Layout
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Layout
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

/- Equal objects in distinct source bindings remain distinct occurrences in the selected
diagram. The leg at one targets the codomain of the original map after the limit is stored. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let groups ← empty.namedCategory Syntax.missing "Groups" [.zero] #[]
  let session ← empty.assume `G (← nativeTerm "GrpCat.{0}")
  let session ← session.defineTerm `H (← session.term (← nativeTerm "G"))
  let session ← session.assume `f (← nativeTerm "@Quiver.Hom GrpCat.{0} _ G H")
  let morphism ← session.term (← nativeTerm "f")
  let morphism ← morphism.inCategory groups.expression groups.value .morphism
  let session ← session.defineTerm `k morphism
  let kernel ← session.read (← sourceTerm "kernel(k)")
  let session ← session.defineTerm `K kernel
  let session ← session.defineTerm `retainedKernel (← session.read (← sourceTerm "K"))
  let session ← session.assume `G (← nativeTerm "GrpCat.{0}")
  let retained ← session.read (← sourceTerm "retainedKernel")
  let some selection := retained.category.bind (·.limit)
    | throwError "the kernel alias lost its selected constructor interface"
  for (ordinal, expectedIndex) in #[(0, 0), (1, 1)] do
    let leg ← session.read (← sourceTerm s!"retainedKernel.leg({ordinal})")
    leg.source.withOpen fun bindings value => do
      unless bindings[0]!.id != bindings[1]!.id &&
          (← isDefEq bindings[0]!.expression bindings[1]!.expression) do
        throwError "the endpoint control requires distinct bindings of equal objects"
      let type ← whnfR (← inferType value)
      unless type.isAppOfArity ``Quiver.Hom 4 do
        throwError "the selected kernel leg is not a native morphism"
      let endpoint ← declaredEndpoint type.getAppArgs[3]!
      let context ← ContextTelescope.capture bindings
      let diagram ← selection.diagram.inContext context
      let index := Lean.mkConst (if ordinal == 0 then
        ``CategoryTheory.Limits.WalkingParallelPair.zero else
        ``CategoryTheory.Limits.WalkingParallelPair.one)
      let selected ← mkAppM ``CategoryTheory.Functor.obj #[diagram, index]
      unless endpoint.consumeMData == bindings[expectedIndex]!.expression ||
          endpoint.consumeMData == selected do
        throwError "kernel leg {ordinal} replaced its selected diagram-object binding"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl endpoint)
        (← mkEq endpoint bindings[expectedIndex]!.expression))
  retained.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let interface ← selection.interface.mapM (·.inContext context)
    let some constructor := interface.dataConstructor
      | throwError "the selected kernel lost its declared data constructor"
    let diagram ← selection.diagram.inContext context
    for original in #[bindings[0]!, bindings[1]!, bindings[3]!] do
      unless diagram.containsFVar original.expression.fvarId! do
        throwError "the retained kernel replaced a source endpoint or map"
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[interface.presentation]
    let arguments ← #[``CategoryTheory.Limits.Cone.pt, ``CategoryTheory.Limits.Fork.ι,
      ``CategoryTheory.Limits.Fork.condition].mapM fun projection => mkAppM projection #[cone]
    let callable ← SourceLayout.ofTerm (← context.close constructor)
    let (_, application) ← ApplicationLayout.ofSource callable context
      (← arguments.mapM context.close)
    unless application.arguments.map (·.wireIndex) == #[some 0, some 1, none] &&
        application.arguments.map (·.precedingDependencies) == #[#[], #[0], #[0, 1]] &&
        application.arguments.map (·.binderInfo) == #[.implicit, .default, .default] do
      throwError "the selected kernel constructor changed its dependent computational ports"
    let some conditionArgument := application.arguments[2]?
      | throwError "the prepared kernel omitted its formal commutation condition"
    let condition ← conditionArgument.typeFamily.inContext context
    unless condition.containsFVar bindings[3]!.expression.fvarId! do
      throwError "the prepared kernel condition replaced the original source map"

/- The two injection ports retain their actual source objects even when those objects are equal.
This prepares the accepted constructor through the same dependent layout as runtime demands. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Type")
  let session ← session.defineTerm `Y (← session.term (← nativeTerm "X"))
  let coproduct ← session.read (← sourceTerm "X ⊔ Y")
  let session ← session.defineTerm `C coproduct
  let retained ← session.read (← sourceTerm "C")
  let some selection := retained.category.bind (·.limit)
    | throwError "the coproduct binding lost its selected constructor interface"
  retained.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let interface ← selection.interface.mapM (·.inContext context)
    let some constructor := interface.dataConstructor
      | throwError "the selected coproduct lost its declared data constructor"
    let cocone ← mkAppM ``CategoryTheory.Limits.ColimitCocone.cocone #[interface.presentation]
    let arguments ← #[``CategoryTheory.Limits.Cocone.pt,
      ``CategoryTheory.Limits.BinaryCofan.inl, ``CategoryTheory.Limits.BinaryCofan.inr].mapM
        fun projection => mkAppM projection #[cocone]
    let callable ← SourceLayout.ofTerm (← context.close constructor)
    let (_, application) ← ApplicationLayout.ofSource callable context
      (← arguments.mapM context.close)
    unless application.arguments.map (·.wireIndex) == #[some 0, some 1, some 2] &&
        application.arguments.map (·.precedingDependencies) == #[#[], #[0], #[0]] &&
        application.arguments.map (·.binderInfo) == #[.implicit, .default, .default] do
      throwError "the selected coproduct constructor changed its dependent computational ports"
    for (slot, original) in #[(1, bindings[0]!), (2, bindings[1]!)] do
      let some argument := application.arguments[slot]?
        | throwError "the prepared coproduct omitted an injection"
      let family ← argument.typeFamily.inContext context
      lambdaTelescope family fun _ type => do
        let type ← if type.consumeMData.isAppOfArity ``Quiver.Hom 4 then
            pure type.consumeMData
          else withConfig (fun config => { config with zetaDelta := false }) <|
            withReducible (whnf type)
        unless type.isAppOfArity ``Quiver.Hom 4 do
          throwError "a coproduct data port lost its native morphism type"
        let domain ← declaredEndpoint type.getAppArgs[2]!
        unless domain.consumeMData == original.expression do
          throwError "a coproduct data port replaced its selected source object"
