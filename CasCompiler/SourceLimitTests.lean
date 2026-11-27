module

import CasCompiler.Read
import CasCompiler.Resolve
import CasCompiler.SourceTestSupport
import LeanCategories.Catalogue.Semantics.Foundation.Objects
import LeanCategories.Catalogue.Semantics.Limits.Registration
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.Resolve
meta import CasCompiler.SourceTestSupport
meta import LeanCategories.Catalogue.Semantics.Foundation.Objects
meta import LeanCategories.Catalogue.Semantics.Limits.Registration

open Lean Meta Elab Term CasCompiler CasCatalogue
open CasCompiler.SourceTest

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
    checkSelected object fun value => do
      let scope ← get
      let bindings := scope.context.bindings
      let presentation ← mkAppM declaration #[bindings[0]!.expression, bindings[1]!.expression]
      let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
      let expected ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
        else ``CategoryTheory.Limits.Cone.pt) #[cone]
      let some retained ← SourceReadM.selection? value
        | throwError "the source limit lost its exact selected native binder"
      let some original := retained.originalApplication
        | throwError "the source limit lost its original positional application"
      unless original.getAppFn.isConstOf declaration do
        throwError "the source limit replaced its declared presentation"
      for input in #[bindings[0]!.expression, bindings[1]!.expression] do
        unless ← original.getAppArgs.anyM fun actual =>
            originatesAt scope.context scope.selections actual input false do
          throwError "the source limit replaced an original input object"
      checkOriginal #[value, expected] fun native => do
        unless ← isDefEq native[0]! native[1]! do
          throwError "the source limit changed its declared apex"
        checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
          (← mkEq native[0]! native[1]!))

    let selected ← session.defineTerm `K object
    let selected ← selected.defineTerm `KAgain object
    for name in #[`K, `KAgain] do
      let leg ← selected.read (← sourceTerm s!"{name}.leg(0)")
      checkSelected leg fun value => do
        let scope ← get
        let some authored := selected.context.entries.find? (·.userName == name)
          | throwError "the selected defining leg lost its original authored receiver"
        let some receiver := scope.context.bindings.find? (·.id == authored.id)
          | throwError "the selected defining leg lost its original native receiver"
        let type ← inferType value
        let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
        unless type.isAppOfArity ``Quiver.Hom 4 do
          throwError "the selected defining leg lost its native endpoints"
        let apex := type.getAppArgs[if colimit then 3 else 2]!
        let apex := (selectedEndpoint? scope.context scope.selections apex).getD apex
        unless ← originatesAt scope.context scope.selections apex receiver.expression false do
          throwError "the defining leg replaced its selected construction occurrence"

run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let rings ← empty.namedCategory Syntax.missing "Rings" [.param `u] #[]
  let ringType ← empty.elaborateScoped Syntax.missing do
    mkAppM ``CategoryTheory.Bundled.α #[← empty.readTerm rings.value]
  let session ← empty.assumeTerm `R ringType
  let ring ← session.term (← nativeTerm "R")
  let modules ← session.namedCategory Syntax.missing "Modules" [.param `u, .param `v] #[ring]
  let moduleType ← session.elaborateScoped Syntax.missing do
    mkAppM ``CategoryTheory.Bundled.α #[← session.readTerm modules.value]
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
  checkSelected product fun value => do
    let scope ← get
    let bindings ← #[`R, `A, `B].mapM fun name => do
      let some entry := session.context.entries.find? (·.userName == name)
        | throwError "the source module product lost an original authored input"
      let some binding := scope.context.bindings.find? (·.id == entry.id)
        | throwError "the source module product lost an original input binding"
      return binding
    let presentation ← mkAppM ``CasCatalogue.Limits.Registration.modulesProduct
      #[bindings[0]!.expression, bindings[1]!.expression, bindings[2]!.expression]
    let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let expected ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    let some retained ← SourceReadM.selection? value
      | throwError "the module product lost its original typed selection"
    let some application := retained.originalApplication
      | throwError "the module product lost its complete positional application"
    for input in bindings do
      unless ← application.getAppArgs.anyM fun actual =>
          originatesAt scope.context scope.selections actual input.expression false do
        throwError "the source module product changed its selected modules or scalar action"
    checkOriginal #[value, expected] fun native => do
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
  let session ← session.defineTerm `P product
  let session ← session.assume `A (← nativeTerm "Type")
  let retained ← session.read (← sourceTerm "P")
  checkSelected retained fun value => do
    let scope ← get
    let some original := session.context.entries.find? (·.userName == `P)
      | throwError "the product lost its authored original binding"
    let some binding := scope.context.bindings.find? (·.id == original.id)
      | throwError "the product lost its native original binding"
    unless value.equal binding.expression do
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
  checkSelected original fun apex => do
    let scope ← get
    let cone ← limit.cone.inContext scope.context
    unless cone.containsConst (· == ``CasCatalogue.Limits.Registration.setsPullback) &&
        (← visitNativeData (fun term => originatesAt scope.context scope.selections term
          scope.context.bindings[0]!.expression false) cone false) > 0 do
      throwError "the named pullback replaced its original source objects or declaration"
    let expected ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
    checkOriginal #[apex, expected] fun native => do
      unless ← isDefEq native[0]! native[1]! do
        throwError "the named pullback lost its selected cone's apex"
      checkWithKernel (← mkExpectedTypeHint (← mkEqRefl native[0]!)
        (← mkEq native[0]! native[1]!))
  let identity ← session.read (← sourceTerm "id(X)")
  discard <| session.elaborateScoped Syntax.missing do
    let originalMap ← session.readTerm identity
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
    return originalMap

private def limitOwnerTerms (limit : NativeSourceLimitSelection) : Array Expr :=
  #[limit.cone, limit.bundle, limit.presentation, limit.diagram,
    limit.interface.presentation, limit.interface.diagram] ++
    limit.interface.standardization.toArray ++ limit.interface.dataConstructor.toArray ++
    limit.ownerFamily.toArray

private def limitOwnerSyntax (original retained : NativeSourceLimitSelection) : Bool :=
  retained.row == original.row && retained.declaration == original.declaration &&
    retained.construction == original.construction &&
    retained.colimit == original.colimit && retained.category.syntacticEq original.category &&
    retained.interface.standardization.isSome == original.interface.standardization.isSome &&
    retained.interface.dataConstructor.isSome == original.interface.dataConstructor.isSome &&
    retained.ownerFamily.isSome == original.ownerFamily.isSome

private def ownerNativeTerms (category : NativeSourceCategory) : Array Expr :=
  #[category.bundle] ++
    category.carrier.toArray.flatMap (fun carrier => carrier.actions ++ carrier.comparisons) ++
    category.limit.toArray.flatMap limitOwnerTerms



private def freezeLimitOwner (judgement : NativeSourceJudgement) : MetaM NativeSourceJudgement := do
  let resolve := fun value => do
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the original owner control has unresolved native parameters"
    return value
  let value ← resolve judgement.value
  let category ← judgement.category.mapM fun selected => selected.mapM resolve
  return ⟨value, category⟩

private def checkLimitOwner (expected actual : NativeSourceCategory) : MetaM Unit := do
  unless ({ value := actual.bundle, category := some actual } : SourceSelection Expr).exactlyMatches
      Expr.equal { value := expected.bundle, category := some expected } do
    throwError "the typed owner changed a complete original category or construction field"
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




private def checkLimitEnvelope (session : SourceSession) (text : String) : TermElabM Unit := do
  let source ← sourceTerm text
  let #[retained] ← session.elaborateJudgementsScoped source do
    let original ← readExpression (fun _ => pure none) source none
    let original ← freezeLimitOwner original
    let some category := original.category
      | throwError "the original construction has no selected category"
    let some limit := category.limit
      | throwError "the original construction has no selected cone"
    unless limit.interface.standardization.isSome && limit.interface.dataConstructor.isSome do
      throwError "the independent binary limit row lost its declared computational interface"
    let some ownerFamily := limit.ownerFamily
      | throwError "the original construction lost its full formal owner family"
    let scope ← get
    let owner ← SelectedLimitOwner.ofBinding scope.context scope.selections ownerFamily
    forallTelescope (← inferType owner.selection.receiver) fun formals _ => do
      let formal ← owner.specialize formals
      let parameters := formal.source.interface.presentation.getAppArgs
      unless formal.source.construction == limit.construction &&
          formal.source.ownerFamily.isNone && formals.size == parameters.size &&
          (formals.zip parameters).all (fun (formal, actual) => formal.equal actual) do
        throwError "the owner family replaced or merged complete formal M argument positions"
    let applied ← owner.specialize limit.interface.presentation.getAppArgs
    unless applied.source.construction == limit.construction &&
        applied.source.interface.presentation.equal limit.interface.presentation &&
        applied.source.interface.dataConstructor == limit.interface.dataConstructor do
      throwError "source formation re-prepared its original interface after actual substitution"
    let encoded ← annotateSourceObject category original.value
    let some (decoded, object) ← sourceObjectOrigin? encoded
      | throwError "the selected construction lost its object annotation"
    checkLimitOwner category decoded
    let scope ← get
    unless object.equal encoded &&
        (← originatesAt scope.context scope.selections object original.value) do
      throwError "the owner binding replaced the original construction occurrence"
    discard <| SourceReadM.withLet `sameSpelling (← inferType encoded) encoded fun boundOwner => do
      let some (decoded, object) ← sourceObjectOrigin? boundOwner
        | throwError "an explicitly bound native alias lost the selected construction's owner"
      checkLimitOwner category decoded
      let scope ← get
      unless object.equal boundOwner &&
          (← originatesAt scope.context scope.selections object original.value) do
        throwError "a native alias reconstructed the selected source object"
      return boundOwner
    let carrier ← freezeLimitOwner (← sourceCarrier original)
    let encodedType ← annotateSourceType category original.value carrier.value
    let some decoded ← sourceTypeOrigin? encodedType
      | throwError "the construction's carrier lost its original selected owner"
    checkLimitOwner category decoded.category
    unless decoded.object.equal original.value && decoded.type.equal carrier.value do
      throwError "the typed carrier changed its original object or carrier"
    let scope ← get
    let closed ← scope.context.close encodedType
    let originalObject ← scope.context.close original.value
    let originalCategory ← category.mapM scope.context.close
    let selections ← scope.selections.close scope.context
    liftM (m := TermElabM) <| closed.withOpen fun bindings expression => do
      let reopened ← ContextTelescope.capture bindings
      let selections ← selections.inContext reopened
      let assertions : SourceReadM Unit := do
        let some decoded ← sourceTypeOrigin? expression
          | throwError "native context reopening discarded the original selected construction"
        let some reopenedLimit := decoded.category.limit
          | throwError "native context reopening discarded the selected cone"
        checkLimitOwner (← originalCategory.mapM (fun term => term.inContext reopened))
          decoded.category
        unless decoded.object.equal (← originalObject.inContext reopened) &&
            limitOwnerSyntax limit reopenedLimit do
          throwError "native context transport substituted another construction occurrence"
      assertions.runK { identities := scope.identities, context := reopened, selections }
        fun _ _ => pure ()
    return #[original]
    | throwError "the construction owner control changed its statement arity"
  session.withTerm retained fun _ _ _ => pure ()
  let originalEntries ← authoredEntries session.context session.selections
  let actualEntries ← authoredEntries retained.source.context retained.selections
  unless actualEntries.map (·.id) == originalEntries.map (·.id) do
    throwError "construction retention changed its original authored source scope"

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

private def requireMalformedOwner (expression : Expr) (category : NativeSourceCategory)
    (typeOwner : Bool) : SourceReadM Unit := do
  let scope ← get
  let some binding := scope.context.bindings.find? (·.expression.equal expression)
    | throwError "the malformed owner control lost its exact binding"
  let some original ← SourceReadM.selection? expression
    | throwError "the malformed owner control lost its original complete typed record"
  let (owner, body, changed) ← if typeOwner then do
      let some origin := original.typeOrigin
        | throwError "the malformed type owner control lost its complete original fields"
      pure (origin.object, origin.type, { original with
        typeOrigin := some { origin with category } })
    else pure (expression, expression, { original with category := some category })
  checkWithKernel body
  let failure : Option Exception ← try
    if typeOwner then discard <| annotateSourceType category owner body
    else discard <| annotateSourceObject category owner
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "an inconsistent complete typed owner was accepted at a fresh binder"
  unless (← failure.toMessageData.toString).startsWith
      "a source owner changed its original selected construction" do throw failure
  let failure : Option Exception ← try
    discard <| SourceSelectionScope.merge scope.selections
      (({} : SourceSelectionScope Expr).insert binding.id changed)
    pure none
  catch error => pure (some error)
  let some failure := failure
    | throwError "one original source binding accepted a different complete owner record"
  unless (← failure.toMessageData.toString).startsWith
      "one source binding has incompatible retained selections" do throw failure




run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let session ← empty.assume `R (← nativeTerm "RingCat.{0}")
  let source ← sourceTerm "RegularModule(R) × RegularModule(R)"
  let #[retained] ← session.elaborateJudgementsScoped source do
    let original ← readExpression (fun _ => pure none) source none
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
      checkOriginal #[actual, expected] fun native => do
        unless ← withoutModifyingState <| isDefEq native[0]! native[1]! do
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
    let scope ← get
    let originalCategory ← combined.mapM scope.context.close
    let originalObject ← scope.context.close original.value
    let closed ← scope.context.close viewed.value
    let selections ← scope.selections.close scope.context
    liftM (m := TermElabM) <| closed.withOpen fun bindings expression => do
      let reopened ← ContextTelescope.capture bindings
      let selections ← selections.inContext reopened
      let assertions : SourceReadM Unit := do
        let some decoded ← sourceTypeOrigin? expression
          | throwError "reopening lost a combined carrier/construction owner"
        let some reopenedLimit := decoded.category.limit
          | throwError "reopening lost the structural view's original limit"
        let some reopenedCarrier := decoded.category.carrier
          | throwError "reopening lost the structural view's original carrier"
        checkLimitOwner (← originalCategory.mapM (fun term => term.inContext reopened))
          decoded.category
        unless limitOwnerSyntax limit reopenedLimit && reopenedCarrier.refs == carrier.refs &&
            reopenedCarrier.identifications == carrier.identifications &&
            reopenedCarrier.target.syntacticEq carrier.target &&
            reopenedCarrier.actions.size == carrier.actions.size &&
            reopenedCarrier.comparisons.size == carrier.comparisons.size &&
            decoded.object.equal (← originalObject.inContext reopened) do
          throwError "reopening changed complete carrier/construction source data"
      assertions.runK { identities := scope.identities, context := reopened, selections }
        fun _ _ => pure ()

    requireMalformedOwner encodedObject
      { combined with limit := some { limit with declaration := .anonymous } } false
    requireMalformedOwner viewed.value
      { combined with limit := some { limit with colimit := !limit.colimit } } true
    requireMalformedOwner viewed.value
      { combined with limit := some { limit with
        interface := { limit.interface with dataConstructor := none } } } true
    return #[original]
    | throwError "the structural-view control changed its source statement arity"
  session.withTerm retained fun _ _ _ => pure ()
  let originalEntries ← authoredEntries session.context session.selections
  let actualEntries ← authoredEntries retained.source.context retained.selections
  unless actualEntries.map (·.id) == originalEntries.map (·.id) do
    throwError "the structural view changed the original authored source scope"



run_cmd Lean.Elab.Command.liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  discard <| empty.elaborateScoped Syntax.missing do
    let original ← readExpression (fun _ => pure none) (← sourceTerm "Fin(3)") none
    let original ← freezeLimitOwner original
    let some category := original.category
      | throwError "the ordinary owner control lost its actual selected category"
    unless category.limit.isNone do
      throwError "the ordinary owner control unexpectedly selected a universal presentation"
    let encoded ← annotateSourceObject category original.value
    let some selected ← SourceReadM.selection? encoded
      | throwError "the ordinary owner lost its exact original typed binding"
    unless encoded.isFVar && selected.value.equal original.value && selected.limit.isNone do
      throwError "an owner without a limit changed its original native body or gained a limit"
    let some (decoded, object) ← sourceObjectOrigin? encoded
      | throwError "the ordinary owner no longer retains its complete category"
    unless ({ value := category.bundle, category := some category } : SourceSelection Expr).exactlyMatches
        Expr.equal { value := decoded.bundle, category := some decoded } &&
        object.equal encoded && decoded.limit.isNone &&
        (ownerNativeTerms decoded).size == (ownerNativeTerms category).size &&
        ((ownerNativeTerms decoded).zip (ownerNativeTerms category)).all
          (fun (left, right) => left.equal right) do
      throwError "ordinary owner retention changed complete original data"
    return encoded
