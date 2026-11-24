module

import CasCompiler.Read
import CasCompiler.Resolve
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
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

    let selected ← session.defineTerm `K object
    let selected ← selected.defineTerm `KAgain object
    for (name, index) in #[("K", 2), ("KAgain", 3)] do
      let leg ← selected.read (← sourceTerm s!"{name}.leg(0)")
      leg.source.withOpen fun bindings value => do
        let type ← inferType value
        let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
        unless type.isAppOfArity ``Quiver.Hom 4 do
          throwError "the selected defining leg lost its native endpoints"
        let apex ← declaredEndpoint type.getAppArgs[if colimit then 3 else 2]!
        unless apex == bindings[index]!.expression do
          throwError "the defining leg replaced its selected construction occurrence"

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

/- A native cone declaration can accept all supplied maps and still require declaration
data that those maps do not determine. The helper control below preserves that distinction
without adding a downstream registry row. The public named pullback remains an independent
consumer control of the actual registered presentation. -/
open CategoryTheory CategoryTheory.Limits

def nativeTrialUnresolvedPullback {_extra : Type}
    {X Y Z : LeanCategories.Foundation.Mathlib.Sets.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    LimitCone (cospan f g) :=
  CasCatalogue.Limits.Registration.setsPullback f g

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `X (← nativeTerm "Type")
  let original ← session.read (← sourceTerm "pullback(id(X), id(X))")
  let some category := original.category
    | throwError "the named pullback lost its original selected category"
  let some limit := category.limit
    | throwError "the named pullback lost its original cone"
  unless limit.row == "lim.sets.pullback" &&
      limit.declaration == ``CasCatalogue.Limits.Registration.setsPullback &&
      !limit.colimit && limit.category.syntacticEq (.atom CategoryId.sets) do
    throwError "the named pullback changed its complete selected presentation"
  original.source.withOpen fun bindings apex => do
    let context ← ContextTelescope.capture bindings
    let cone ← limit.cone.inContext context
    unless cone.containsConst (· == ``CasCatalogue.Limits.Registration.setsPullback) &&
        cone.containsFVar bindings[0]!.expression.fvarId! do
      throwError "the named pullback replaced its original source objects or declaration"
    let expected ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    unless ← isDefEq apex expected do
      throwError "the named pullback lost its selected cone's apex"
    checkWithKernel (← mkExpectedTypeHint (← mkEqRefl apex) (← mkEq apex expected))
  let identity ← session.read (← sourceTerm "id(X)")
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let originalMap ← identity.source.inContext context
    let declaration ← mkConstWithFreshMVarLevels ``nativeTrialUnresolvedPullback
    let arguments := #[originalMap, originalMap]
    let result ← elabSourceApplicationApplicable declaration
      (Array.replicate arguments.size Syntax.missing) none fun index _ => do
        let some argument := arguments[index]?
          | throwError "the native limit control lost an original supplied map"
        return .ok argument
    let .ok (presentation, actual) := result
      | throwError "the native limit control confused undetermined data with a domain mismatch"
    let presentation ← instantiateMVars presentation
    unless actual == arguments && presentation.hasMVar &&
        presentation.getAppFn.isConstOf ``nativeTrialUnresolvedPullback do
      throwError "the native limit helper changed or silently completed the original application"

private def limitOwnerTerms (limit : NativeSourceLimitSelection) : Array Expr :=
  #[limit.cone, limit.bundle, limit.presentation, limit.diagram,
    limit.interface.presentation, limit.interface.diagram] ++
    limit.interface.standardization.toArray ++ limit.interface.dataConstructor.toArray

private def limitOwnerSyntax (original retained : NativeSourceLimitSelection) : Bool :=
  retained.row == original.row && retained.declaration == original.declaration &&
    retained.colimit == original.colimit && retained.category.syntacticEq original.category &&
    retained.interface.standardization.isSome == original.interface.standardization.isSome &&
    retained.interface.dataConstructor.isSome == original.interface.dataConstructor.isSome

private def ownerNativeTerms (category : NativeSourceCategory) : Array Expr :=
  #[category.bundle] ++
    category.carrier.toArray.flatMap (fun carrier => carrier.actions ++ carrier.comparisons) ++
    category.limit.toArray.flatMap limitOwnerTerms

/-- Freeze the completed reader judgement before encoding, as SourceSession's ordinary
instantiate-and-close boundary does. Exact comparisons below do not solve metavariables. -/
private def freezeLimitOwner (judgement : NativeSourceJudgement) : MetaM NativeSourceJudgement := do
  let resolve := fun value => do
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the original owner control has unresolved native parameters"
    return value
  let value ← resolve judgement.value
  let category ← judgement.category.mapM fun selected => do
    let bundle ← resolve selected.bundle
    let carrier ← selected.carrier.mapM fun carrier => do
      let actions ← carrier.actions.mapM resolve
      let comparisons ← carrier.comparisons.mapM resolve
      return { carrier with actions, comparisons }
    let limit ← selected.limit.mapM fun limit => do
      let cone ← resolve limit.cone
      let bundle ← resolve limit.bundle
      let presentation ← resolve limit.presentation
      let diagram ← resolve limit.diagram
      let interface ← limit.interface.mapM resolve
      return { limit with cone, bundle, presentation, diagram, interface }
    return { selected with bundle, carrier, limit }
  return ⟨value, category⟩

private def checkLimitOwner (expected actual : NativeSourceCategory) : MetaM Unit := do
  unless actual.role == expected.role &&
      actual.expression.syntacticEq expected.expression && actual.bundle.equal expected.bundle do
    throwError "the typed owner envelope changed the complete selected category"
  let some original := expected.limit
    | throwError "the original source construction lost its selected limit"
  let some retained := actual.limit
    | throwError "the typed owner envelope discarded the selected construction"
  unless limitOwnerSyntax original retained &&
      (limitOwnerTerms retained).size == (limitOwnerTerms original).size &&
      ((limitOwnerTerms retained).zip (limitOwnerTerms original)).all
        (fun (left, right) => left.equal right) do
    throwError "the typed owner envelope replaced part of the original construction"
  match expected.carrier, actual.carrier with
  | none, none => pure ()
  | some original, some retained =>
    unless toJson retained.refs == toJson original.refs &&
        retained.target.syntacticEq original.target &&
        retained.identifications == original.identifications &&
        retained.actions.size == original.actions.size &&
        retained.comparisons.size == original.comparisons.size &&
        (retained.actions.zip original.actions).all (fun (left, right) => left.equal right) &&
        (retained.comparisons.zip original.comparisons).all (fun (left, right) => left.equal right) do
      throwError "construction retention changed an original carrier selection"
  | _, _ => throwError "construction retention added or discarded a carrier selection"

/- A construction passed as a native object or carrier parameter retains its actual cone,
category, row and original source bindings. Native closure transport uses the same fields;
it must not reconstruct a construction from its definitionally equal apex. -/
private def checkLimitEnvelope (session : SourceSession) (text : String) : TermElabM Unit := do
  let source ← sourceTerm text
  let #[retained] ← session.elaborateJudgements source fun context => do
    -- These parameters are authored native types/rings. Their source categories are
    -- supplied by the same public construction reader as the original positive cases.
    let original ← withSynthesize <| readExpression (fun _ => pure none) source none
    let original ← freezeLimitOwner original
    let some category := original.category
      | throwError "the original construction has no selected category"
    let some limit := category.limit
      | throwError "the original construction has no selected cone"
    unless limit.interface.standardization.isSome && limit.interface.dataConstructor.isSome do
      throwError "the independent binary limit row lost its declared computational interface"
    let encoded ← annotateSourceObject category original.value
    let some (decoded, object) ← sourceObjectOrigin? encoded
      | throwError "the selected construction lost its object annotation"
    checkLimitOwner category decoded
    unless object.equal original.value do
      throwError "the owner envelope replaced the original construction occurrence"
    withLetDecl `sameSpelling (← inferType encoded) encoded fun boundOwner => do
      let some (decoded, object) ← sourceObjectOrigin? boundOwner
        | throwError "a native alias lost the selected construction's owner"
      checkLimitOwner category decoded
      unless object.equal original.value do
        throwError "a native alias reconstructed the selected source object"
    let carrier ← freezeLimitOwner (← sourceCarrier original)
    let encodedType ← annotateSourceType category original.value carrier.value
    let some decoded ← sourceTypeOrigin? encodedType
      | throwError "the construction's carrier lost its original selected owner"
    checkLimitOwner category decoded.category
    unless decoded.object.equal original.value && decoded.type.equal carrier.value do
      throwError "the typed carrier envelope changed its original object or carrier"
    let closed ← context.close encodedType
    let originalObject ← context.close original.value
    let originalTerms : Array ClosedTerm ← (ownerNativeTerms category).mapM fun value => do
      return ← context.close value
    closed.withOpen fun bindings expression => do
      let reopened ← ContextTelescope.capture bindings
      let some decoded ← sourceTypeOrigin? expression
        | throwError "native context reopening discarded the original selected construction"
      let some reopenedLimit := decoded.category.limit
        | throwError "native context reopening discarded the selected cone"
      unless decoded.object.equal (← originalObject.inContext reopened) &&
          limitOwnerSyntax limit reopenedLimit &&
          (ownerNativeTerms decoded.category).size == originalTerms.size do
        throwError "native context transport substituted another construction occurrence"
      for actual in ownerNativeTerms decoded.category, original in originalTerms do
        unless actual.equal (← original.inContext reopened) do
          throwError "native context transport lost a complete construction or interface field"
    return #[original]
    | throwError "the construction envelope control changed its statement arity"
  unless retained.source.context.exactlyMatches session.context do
    throwError "construction retention shortened its original source scope"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let type ← empty.elaborate Syntax.missing fun _ =>
    pure (mkSort (.succ (.param `limitOwnerUniverse)))
  let session ← empty.assumeTerm `X type
  let session ← session.assumeTerm `Y type
  for source in #["X × Y", "X ⊔ Y"] do
    withCurrHeartbeats <| checkLimitEnvelope session source
  let rings ← empty.assume `R (← nativeTerm "RingCat.{0}")
  withCurrHeartbeats <| checkLimitEnvelope rings "RegularModule(R) × RegularModule(R)"

private def requireMalformedOwner (expression : Expr) (typeEnvelope : Bool)
    (expectedPrefix : String) : TermElabM Unit := do
  -- Metadata corruption does not make the native mathematical expression ill-typed.
  -- The negative must therefore reach the owner decoder's own integrity boundary.
  checkWithKernel expression
  let failure : Option Exception ← try
    if typeEnvelope then discard <| sourceTypeOrigin? expression
    else discard <| sourceObjectOrigin? expression
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "a partial typed owner envelope was accepted"
  unless (← failure.toMessageData.toString).startsWith expectedPrefix do throw failure

-- A real module-product structural view adds nonempty carrier actions to the original
-- selected limit. The actions are checked against the independent route declarations;
-- the original limit and the carrier comparisons remain separate typed fields.
run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let source ← sourceTerm "RegularModule(R) × RegularModule(R)"
  let #[retained] ← session.elaborateJudgements source fun context => do
    let original ← withSynthesize <| readExpression (fun _ => pure none) source none
    let original ← freezeLimitOwner original
    let some category := original.category
      | throwError "the structural-view control lost its original selected category"
    let some limit := category.limit
      | throwError "the structural-view control lost its original selected construction"
    let sets := CategoryExpr.atom CategoryId.sets
    let viewed ← freezeLimitOwner (← sourceStructuralView original sets none)
    let some origin ← sourceTypeOrigin? viewed.value
      | throwError "the actual structural view discarded its selected owner"
    let some carrier := origin.category.carrier
      | throwError "the actual structural view retained no carrier selection"
    unless !carrier.actions.isEmpty && !carrier.refs.isEmpty do
      throwError "the structural-view control did not exercise nonempty carrier data"
    let state ← semanticState
    let query ← SourceRoutes.forOwner category.expression sets
    let some routes ← query.finiteRoutes
      | throwError "the actual module carrier route has no finite independent presentation"
    let #[route] := routes.filter (·.refs == carrier.refs)
      | throwError "the structural view did not retain one actual registered route"
    let independent ← nativeRouteFunctor state route category.bundle
    unless carrier.target.syntacticEq sets &&
        carrier.identifications == (category.carrier.map (·.identifications)).getD #[] &&
        carrier.actions.size == independent.actions.size &&
        carrier.comparisons.size == ((category.carrier.map (·.comparisons)).getD #[]).size do
      throwError "the structural view changed its independently selected carrier data"
    for actual in carrier.actions, expected in independent.actions do
      unless ← withoutModifyingState <| isDefEq actual expected do
        throwError "the structural view changed an original complete native route action"
    for actual in carrier.comparisons,
        expected in (category.carrier.map (·.comparisons)).getD #[] do
      unless actual.equal expected do
        throwError "construction fields were mistaken for original carrier comparisons"
    let combined := { category with carrier := some carrier }
    checkLimitOwner combined origin.category
    unless origin.object.equal original.value do
      throwError "the structural view replaced its actual original source occurrence"

    let encodedObject ← annotateSourceObject combined original.value
    let some (decoded, _) ← sourceObjectOrigin? encodedObject
      | throwError "the combined carrier/construction owner was not decoded"
    checkLimitOwner combined decoded
    let originalTerms : Array ClosedTerm ← (ownerNativeTerms combined).mapM fun value => do
      return ← context.close value
    let originalObject ← context.close original.value
    let closed ← context.close viewed.value
    closed.withOpen fun bindings expression => do
      let reopened ← ContextTelescope.capture bindings
      let some decoded ← sourceTypeOrigin? expression
        | throwError "reopening lost a combined carrier/construction owner"
      let some reopenedLimit := decoded.category.limit
        | throwError "reopening lost the structural view's original limit"
      let some reopenedCarrier := decoded.category.carrier
        | throwError "reopening lost the structural view's original carrier"
      unless limitOwnerSyntax limit reopenedLimit && reopenedCarrier.refs == carrier.refs &&
          reopenedCarrier.identifications == carrier.identifications &&
          reopenedCarrier.target.syntacticEq carrier.target &&
          reopenedCarrier.actions.size == carrier.actions.size &&
          reopenedCarrier.comparisons.size == carrier.comparisons.size &&
          (ownerNativeTerms decoded.category).size == originalTerms.size &&
          decoded.object.equal (← originalObject.inContext reopened) do
        throwError "reopening changed complete carrier/construction source data"
      for actual in ownerNativeTerms decoded.category, expected in originalTerms do
        unless actual.equal (← expected.inContext reopened) do
          throwError "reopening substituted a carrier, comparison or limit-interface field"

    let .mdata objectData objectBody := encodedObject
      | throwError "the combined owner lost its metadata envelope"
    let partialObject := Expr.mdata
      (objectData.erase `CasCompiler.source.typeOrigin.limit.declaration) objectBody
    requireMalformedOwner partialObject false
      "the native source owner lost part of its selected construction"
    let .mdata typeData typeBody := viewed.value
      | throwError "the actual structural view lost its typed owner envelope"
    let wrongRole := Expr.mdata
      (typeData.setString `CasCompiler.source.typeOrigin.limit.colimit "false") typeBody
    requireMalformedOwner wrongRole true
      "the native source construction has a different cone role"
    let missingInterface := Expr.mdata
      (typeData.setBool `CasCompiler.source.typeOrigin.limit.dataConstructor false) typeBody
    requireMalformedOwner missingInterface true
      "the native source construction has a different typed field count"
    return #[original]
    | throwError "the structural-view control changed its source statement arity"
  unless retained.source.context.exactlyMatches session.context do
    throwError "the structural view shortened the original source scope"

-- An ordinary selected object has the exact pre-limit envelope: the original descriptor,
-- bundle/object/carrier fields, and original body. No new marker or absent field is emitted.
run_cmd Lean.Elab.Command.liftTermElabM do
  let original ← withSynthesize <| readExpression (fun _ => pure none) (← sourceTerm "Fin(3)") none
  let original ← freezeLimitOwner original
  let some category := original.category
    | throwError "the legacy owner control lost its actual selected category"
  unless category.limit.isNone do
    throwError "the legacy owner control unexpectedly selected a universal presentation"
  let encoded ← annotateSourceObject category original.value
  let .mdata data wrapped := encoded
    | throwError "the legacy owner lost its original metadata envelope"
  let descriptor : OwnerDescriptor := ⟨category.expression, category.carrier.map fun carrier =>
    ⟨carrier.refs, carrier.target, carrier.identifications.size,
      carrier.actions.size, carrier.comparisons.size⟩⟩
  unless data.getString `CasCompiler.source.objectOrigin == (toJson descriptor).compress &&
      data.size == 1 + (category.carrier.map (·.identifications.size)).getD 0 do
    throwError "an owner without a limit changed its legacy metadata format"
  let fields := #[category.bundle, original.value] ++
    category.carrier.toArray.flatMap (fun carrier => carrier.actions ++ carrier.comparisons)
  let mut body := wrapped
  for expected in fields do
    unless body.isAppOfArity ``Function.const 4 && body.getAppArgs[3]!.equal expected do
      throwError "an owner without a limit changed its legacy typed-field order"
    body := body.getAppArgs[2]!
  unless body.equal original.value do
    throwError "an owner without a limit gained a new payload delimiter"
  let some (decoded, object) ← sourceObjectOrigin? encoded
    | throwError "the legacy owner no longer decodes"
  unless decoded.limit.isNone && decoded.role == category.role &&
      decoded.expression.syntacticEq category.expression &&
      object.equal original.value &&
      (ownerNativeTerms decoded).size == (ownerNativeTerms category).size &&
      ((ownerNativeTerms decoded).zip (ownerNativeTerms category)).all
        (fun (left, right) => left.equal right) do
    throwError "legacy decoding changed the complete original owner"
