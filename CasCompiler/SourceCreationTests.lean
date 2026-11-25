module

import CasCompiler.Read
import CasCompiler.CreationFamily
import CasCompiler.PreparedCreationFamily
import CasCompiler.SourceLimit
import CasCompiler.CategoricalPointFamily
import LeanCategories.Catalogue
public meta import Lean.Elab.Command
meta import CasCompiler.Read
meta import CasCompiler.CreationFamily
meta import CasCompiler.PreparedCreationFamily
meta import CasCompiler.SourceLimit
meta import CasCompiler.CategoricalPointFamily
meta import LeanCategories.Catalogue

open Lean Meta Elab Term CasCompiler CasCatalogue

private def creationSourceTerm (text : String) : TermElabM (TSyntax `cas_term) := do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term text
    | throwError "the original creation source did not parse"
  return ⟨parsed⟩

/-- The original SourceNamedLimitTests finite-set pullback inputs, unchanged. -/
private def creationSourceSession : TermElabM SourceSession := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  let empty ← SourceSession.empty identities
  let f ← empty.read (← creationSourceTerm
    "{0 ↦ 0, 1 ↦ 1, 2 ↦ 1} : (Fin(3) in FiniteSets) → (Fin(2) in FiniteSets)")
  let session ← empty.defineTerm `f' f
  let g ← session.read (← creationSourceTerm
    "{0 ↦ 1, 1 ↦ 0} : (Fin(2) in FiniteSets) → (Fin(2) in FiniteSets)")
  session.defineTerm `g' g

private def creationField (source : SourceLayout) (projection : Name) : MetaM SourceLayout := do
  let some field := source.fields.find? (·.projection == projection)
    | throwError "the complete creation interface lost native field {projection}"
  field.toLayout

/- Read the complete existing native data family, including data-bearing subsingletons.
No new mathematical definition or target answer is introduced by this source-layout control. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let state ← semanticState
  let #[entry] := state.lifts.filter (·.id == LiftId.finiteSetsPullbacks)
    | throwError "the original finite-set creation lift is absent or ambiguous"
  let family ← CreationFamily.forLift entry
  unless family.evidenceFamily.getAppFn.isConstOf entry.evidence &&
      !family.family.hasMVar && !family.family.hasLevelMVar do
    throwError "creation preparation changed its complete rigid evidence family"
  lambdaTelescope family.family fun parameters result => do
    unless parameters.size == family.parameterCount + 3 do
      throwError "the creation family lost an original evidence/diagram/cone/universal slot"
    let cone := parameters[family.parameterCount + 1]!
    let universal := parameters[family.parameterCount + 2]!
    let expected ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
    unless (← isDefEq (← inferType universal) expected) && !(← isProp expected) do
      throwError "the original target universal data was erased or retargeted"
    let nativeType ← whnfR (← inferType result)
    unless nativeType.isAppOf ``CategoryTheory.LiftsToLimit do
      throwError "creation preparation discarded the complete LiftsToLimit result"
    let declarations := (← getLCtx).foldl (fun values declaration => values.push declaration) #[]
    let bindings := declarations.mapIdx fun index declaration =>
      { id := ⟨"creation-family-layout", index⟩, role := .parameter,
        expression := mkFVar declaration.fvarId : LocalBinding }
    let context ← ContextTelescope.capture bindings
    let layout ← SourceLayout.ofTerm (← context.close result)
    let liftable ← creationField layout ``CategoryTheory.LiftsToLimit.toLiftableCone
    let cone ← creationField liftable ``CategoryTheory.LiftableCone.liftedCone
    let comparison ← creationField liftable ``CategoryTheory.LiftableCone.validLift
    let hom ← creationField comparison ``CategoryTheory.Iso.hom
    let inv ← creationField comparison ``CategoryTheory.Iso.inv
    let universal ← creationField layout ``CategoryTheory.LiftsToLimit.makesLimit
    let mediator ← creationField universal ``CategoryTheory.Limits.IsLimit.lift
    unless cone.kind == .record && comparison.kind == .record &&
        hom.kind != .proof && inv.kind != .proof && mediator.kind == .function do
      throwError "the complete creation interface erased a cone, comparison or mediator"
    let some law := universal.fields.find? (·.projection == ``CategoryTheory.Limits.IsLimit.fac)
      | throwError "the creation mediator lost its original native law"
    unless law.kind == .proof && law.wireIndex.isNone do
      throwError "the creation interface changed its proof/data boundary"
  let template ← family.standardizedTemplate
  lambdaTelescope template fun parameters result => do
    unless parameters.size == family.parameterCount + 5 &&
        (← whnfR (← inferType result)).isAppOf ``CategoryTheory.LiftsToLimit do
      throwError "the published creation template erased its complete comparison/data context"
    let comparison := parameters[family.parameterCount + 2]!
    let cone := parameters[family.parameterCount + 3]!
    let universal := parameters[family.parameterCount + 4]!
    unless (← whnfR (← inferType comparison)).isAppOf ``CategoryTheory.Iso &&
        (← isDefEq (← inferType universal)
          (← mkAppM ``CategoryTheory.Limits.IsLimit #[cone])) do
      throwError "the published creation template changed its selected comparison or c/t relation"

/- Source formation retains the exact selected lift, target presentation, comparison and full
request. The request consumes raw target c/t; standardization stays inside its fixed source. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← creationSourceSession
  let result ← session.read (← creationSourceTerm "pullback(f', g')")
  let some selected := result.category.bind (·.limit)
    | throwError "the original created pullback lost its selected construction"
  let some creation := selected.creation
    | throwError "the created pullback did not retain its complete creation interface"
  unless creation.lift == LiftId.finiteSetsPullbacks &&
      creation.declaration == ``CasCatalogue.Limits.Lifts.finiteSetsCreatePullbacks &&
      creation.edge == .classifierForget ClassifierId.setsFinite &&
      selected.row == "lim.sets.pullback" && !selected.colimit do
    throwError "the created pullback changed its accepted lift/target pair"
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let native ← creation.mapM (·.inContext context)
    let presentation ← selected.interface.presentation.inContext context
    let targetCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
    let targetUniversal ← mkAppM ``CategoryTheory.Limits.LimitCone.isLimit #[presentation]
    unless native.targetCone.equal targetCone && native.targetUniversal.equal targetUniversal do
      throwError "creation replaced one original target projection"
    let request ← instantiateMVars native.requestFamily
    lambdaTelescope request fun actual body => do
      let #[cone, universal] := actual
        | throwError "the selected creation request changed its two original data inputs"
      let coneType ← mkAppM ``CategoryTheory.Limits.Cone
        #[← selected.interface.diagram.inContext context]
      let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
      unless (← isDefEq (← inferType cone) coneType) &&
          (← isDefEq (← inferType universal) universalType) &&
          body.containsFVar cone.fvarId! && body.containsFVar universal.fvarId! do
        throwError "creation requested computed standardized inputs instead of original target data"
      unless body.containsConst (· == ``CategoryTheory.liftsToLimitOfCreates) &&
          body.containsConst (· == ``CategoryTheory.Limits.IsLimit.postcomposeInvEquiv) do
        throwError "the fixed request discarded its accepted creation or diagram transport"
      check body
    let actual := mkAppN request #[targetCone, targetUniversal]
    unless actual.equal native.result do
      throwError "creation result no longer belongs to its exact prepared request"
    let source ← result.source.inContext context
    unless source.containsConst (· == ``CategoryTheory.liftLimit) &&
        source.containsConst (· == ``CasCatalogue.Limits.Registration.setsPullback) do
      throwError "creation changed the original source presentation"
  let retained ← session.defineTerm `Created result
  let sourceAlias ← retained.read (← creationSourceTerm "Created")
  let leg ← retained.read (← creationSourceTerm "Created.leg(0)")
  let secondLeg ← retained.read (← creationSourceTerm "Created.leg(1)")
  let thirdLeg ← retained.read (← creationSourceTerm "Created.leg(2)")
  let some aliasSelection := sourceAlias.category.bind (·.limit)
    | throwError "the source alias dropped the original selected construction"
  let some aliasCreation := aliasSelection.creation
    | throwError "the source alias dropped the complete creation interface"
  unless aliasSelection.construction == selected.construction &&
      aliasCreation.lift == creation.lift && aliasCreation.edge == creation.edge &&
      aliasSelection.creationInputs == selected.creationInputs &&
      aliasSelection.creationFamily.isSome do
    throwError "the source alias changed the original creation selection"
  retained.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let original ← creation.mapM (·.inContext context)
    let reopened ← aliasCreation.mapM (·.inContext context)
    unless (original.terms.zip reopened.terms).all (fun (left, right) => left.equal right) do
      throwError "closing and reopening changed an original creation field"
    let source ← leg.source.inContext context
    let some decoded ← NativeLimitLegSelection.ofExpr? source
      | throwError "the alias leg lost its original typed construction envelope"
    let some decodedCreation := decoded.construction.source.creation
      | throwError "the typed owner envelope omitted the selected creation"
    unless (decodedCreation.terms.zip original.terms).all
        (fun (left, right) => left.equal right) do
      throwError "the typed construction envelope changed its complete creation field table"
    let shape := Lean.mkConst ``CategoryTheory.Limits.WalkingPair
    let expected := #[
      ← mkAppOptM ``Option.none #[some shape],
      ← mkAppOptM ``Option.some #[some shape, some (Lean.mkConst ``CategoryTheory.Limits.WalkingPair.left)],
      ← mkAppOptM ``Option.some #[some shape, some (Lean.mkConst ``CategoryTheory.Limits.WalkingPair.right)]]
    for leg in #[leg, secondLeg, thirdLeg], index in expected do
      let some selected ← NativeLimitLegSelection.ofExpr? (← leg.source.inContext context)
        | throwError "a created leg lost its original typed native index"
      unless selected.index.equal index &&
          selected.construction.source.construction == decoded.construction.source.construction do
        throwError "the created leg changed its native constructor-order index or original owner"
  let outside ← try
      discard <| retained.read (← creationSourceTerm "Created.leg(3)")
      pure none
    catch error => pure (some error)
  let some outside := outside
    | throwError "the original created cone admitted an ordinal outside its native shape"
  unless CasCatalogue.Exception.stratum? outside == some .invalid do throw outside

/- The prepared contextual marker retains actual separately supplied c/t expressions while
leaving every original selected interface field intact. A universal record for another actual
cone fails its native dependent input check before any provider is selected. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← creationSourceSession
  let result ← session.read (← creationSourceTerm "pullback(f', g')")
  session.context.withOpen fun originalBindings => do
    let original ← ContextTelescope.capture originalBindings
    let owner ← result.source.inContext original
    let some prepared ← PreparedCreationFamily.ofSelection original owner
      | throwError "the selected creation did not prepare a complete contextual request"
    unless prepared.operation == LiftId.finiteSetsPullbacks.raw &&
        prepared.input == "lift.finite_sets.pullbacks#input" &&
        prepared.inputs.evidence.arguments.isEmpty &&
        prepared.inputs.diagramTag == "cospan" && prepared.inputs.diagramPorts.size == 2 do
      throwError "the prepared creation changed an original public/native input position"
    let explicit := (prepared.inputs.evidence.arguments ++
      prepared.inputs.standardization.arguments ++ prepared.inputs.target.arguments).filter
      (fun argument => argument.wireIndex.isSome && argument.binderInfo.isExplicit)
    unless prepared.captureSources.size > explicit.size do
      throwError "the creation capture plan erased its actual implicit computational parameters"
    let originalInputs ← prepared.sourceArguments.mapM (·.inContext original)
    let markedInputs := originalInputs.mapIdx fun index value =>
      Expr.mdata (KVMap.empty.setNat `test.creation.sourceInput index) value
    let rebound ← prepared.rebindSource original markedInputs
    let reboundSelection ← rebound.selection original
    for marked in markedInputs, index in prepared.sourcePositions do
      let some actual := reboundSelection.source.diagram.getAppArgs[index]?
        | throwError "the source owner lost an original full diagram argument"
      unless actual.equal marked do
        throwError "the source owner reconstructed or merged an original positional input"
    let some reboundCreation := reboundSelection.source.creation
      | throwError "positional source binding lost the selected creation"
    let presentation := reboundSelection.source.interface.presentation
    let information ← getFunInfoNArgs presentation.getAppFn presentation.getAppNumArgs
    let mut targetInputs := #[]
    for input in presentation.getAppArgs, index in [:presentation.getAppNumArgs] do
      if (information.paramInfo[index]?.map (·.isExplicit)).getD false && !(← isProof input) then
        targetInputs := targetInputs.push input
    unless targetInputs.size == rebound.inputs.diagramPorts.size do
      throwError "the target presentation changed its original mapped source-port order"
    let maps ← CategoricalPointFamily.forOwner (.action reboundCreation.edge)
    let objects ← SourceActionFamily.forEdge reboundCreation.edge
    let family ← if (← maps.carrierFamily?).isSome then maps.asReference else maps.asWhole
    for targetInput in targetInputs, sourcePort in rebound.inputs.diagramPorts do
      let sourceInput ← sourcePort.source.source.inContext original
      unless targetInput.isAppOfArity ``id 2 do
        throwError "the target map lost its complete original endpoint hint"
      let hom := targetInput.getAppArgs[0]!
      unless hom.isAppOfArity ``Quiver.Hom 4 do
        throwError "the target map lost its complete native Hom schema"
      let .mdata data body := targetInput.getAppArgs[1]!
        | throwError "the target map lost its selected generic action family"
      unless data.getName `CasCompiler.source.kind == ``CategoricalPointFamily &&
          data.getString `CasCompiler.source.id == maps.operation &&
          data.getName `CasCompiler.source.declaration == maps.declaration do
        throwError "the target map changed its complete original action owner"
      let (levels, arguments) ← family.application body
      let parameters := arguments.extract 0 maps.parameterCount
      let #[source, target, input] := parameters.extract maps.declarationParameterCount parameters.size
        | throwError "the target map lost its original endpoint/arrow input positions"
      unless input.equal sourceInput do
        throwError "the target map recomputed or replaced its exact original source input"
      let sourceType ← instantiateMVars (← inferType sourceInput)
      let sourceType ← if sourceType.isAppOfArity ``Quiver.Hom 4 then pure sourceType
        else whnfR sourceType
      let endpoints ← if sourceType.isAppOfArity ``Quiver.Hom 4 then
          pure (sourceType.getAppArgs.extract 2 4)
        else if sourceType.isAppOfArity ``TypeCat.Hom 2 then pure sourceType.getAppArgs
        else throwError "the original test arrow lost its stated native endpoint slots"
      unless endpoints == #[source, target] do
        dbg_trace "[creation.endpoint] original positions={reprStr prepared.sourcePositions}; source arguments={reprStr markedInputs}"
        dbg_trace "[creation.endpoint] actual source input={reprStr sourceInput}; original native type={reprStr sourceType}"
        dbg_trace "[creation.endpoint] stated endpoints={reprStr endpoints}; selected action endpoints={reprStr #[source, target]}"
        dbg_trace "[creation.endpoint] retained target application={reprStr targetInput}"
        throwError "the target map replaced an original stated source endpoint"
      let (native, _) ← maps.arrowAt levels parameters
      unless native.isAppOfArity ``CategoryTheory.Functor.map 8 &&
          native.getAppArgs[7]!.equal sourceInput do
        throwError "the selected target family changed its original native map"
      let nativeType ← inferType native
      unless nativeType.isAppOfArity ``Quiver.Hom 4 &&
          hom.getAppFn == nativeType.getAppFn &&
          hom.getAppArgs.extract 0 2 == nativeType.getAppArgs.extract 0 2 do
        throwError "the target endpoint hint changed its original universe or category dictionary"
      for image in hom.getAppArgs.extract 2 4, receiver in #[source, target] do
        let .mdata data body := image
          | throwError "an implicit target object lost its selected object action"
        unless data.getName `CasCompiler.source.kind == ``SourceActionFamily &&
            data.getString `CasCompiler.source.id == objects.operation do
          throwError "an implicit target object changed its original action"
        let (objectLevels, objectInputs) ← objects.application body
        unless objectLevels == levels &&
            objectInputs.extract 0 objects.parameterCount ==
              parameters.extract 0 maps.declarationParameterCount &&
            objectInputs[objects.parameterCount]!.equal receiver do
          throwError "an implicit target object lost an original declaration argument or receiver"
    let firstType := targetInputs[0]!.getAppArgs[0]!
    let secondType := targetInputs[1]!.getAppArgs[0]!
    unless presentation.getAppNumArgs == 5 &&
        presentation.getAppArgs[0]!.equal firstType.getAppArgs[2]! &&
        presentation.getAppArgs[1]!.equal secondType.getAppArgs[2]! &&
        presentation.getAppArgs[2]!.equal firstType.getAppArgs[3]! &&
        presentation.getAppArgs[2]!.equal secondType.getAppArgs[3]! do
      throwError "the target presentation lost the action markers at its original implicit object slots"
    unless reboundCreation.requestFamily.containsConst
        (· == ``CategoryTheory.Limits.IsLimit.postcomposeInvEquiv) do
      throwError "the same source inputs no longer determine the fixed creation request"
    let coneType ← inferType (← prepared.interface.targetCone.inContext original)
    withLocalDeclD `actualTargetCone coneType fun cone => do
      let universalType ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
      withLocalDeclD `actualTargetUniversal universalType fun universal => do
        withLocalDeclD `otherTargetCone coneType fun other => do
          let otherType ← mkAppM ``CategoryTheory.Limits.IsLimit #[other]
          withLocalDeclD `otherTargetUniversal otherType fun otherUniversal => do
            let actualBindings := #[cone, universal, other, otherUniversal].mapIdx fun index value =>
              (⟨⟨"creation-actual-input", index⟩, .parameter, value⟩ : LocalBinding)
            let context ← ContextTelescope.capture (originalBindings ++ actualBindings)
            let cone := Expr.mdata (KVMap.empty.setNat `test.creation.input 0) cone
            let universal := Expr.mdata (KVMap.empty.setNat `test.creation.input 1) universal
            let actual ← prepared.withArguments context cone universal
            let marked ← actual.mark context
            let temporary ← prepared.markArguments original
              (← prepared.owner.inContext original) cone universal
            unless temporary.equal marked do
              throwError "the temporary creation inputs changed before their complete scope was closed"
            let .mdata data body := marked
              | throwError "the fixed creation request lost its selected marker"
            let decoded ← PreparedCreationFamily.fromMark context data body
            let #[retainedCone, retainedUniversal] ← decoded.arguments.mapM (·.inContext context)
              | throwError "the fixed creation request changed its exact input arity"
            unless retainedCone.equal cone && retainedUniversal.equal universal do
              throwError "the fixed creation marker regenerated an actual c/t input"
            let before ← prepared.interface.mapM (·.inContext context)
            let after ← decoded.interface.mapM (·.inContext context)
            unless (before.terms.zip after.terms).all
                (fun (left, right) => left.equal right) do
              throwError "actual input retention changed the immutable original creation interface"
            let wrong ← try
                discard <| prepared.withArguments context cone otherUniversal
                pure false
              catch _ => pure true
            unless wrong do
              throwError "creation accepted universal data for another original cone"
            let replaced ← try
                discard <| PreparedCreationFamily.fromMark context
                  (data.setName `CasCompiler.source.creation.construction `differentConstruction) body
                pure false
              catch _ => pure true
            unless replaced do
              throwError "the fixed creation marker accepted a different construction occurrence"

/- Candidate order cannot choose among two applicable accepted native interfaces. The test
duplicates only publication metadata for the same existing mathematics; no new math is added. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← creationSourceSession
  let first ← session.read (← creationSourceTerm "f'")
  let second ← session.read (← creationSourceTerm "g'")
  let state ← semanticState
  let #[lift] := state.lifts.filter (·.id == LiftId.finiteSetsPullbacks)
    | throwError "the original creation lift is absent or ambiguous"
  let #[row] := state.limits.filter (·.id.raw == "lim.sets.pullback")
    | throwError "the original target presentation is absent or ambiguous"
  let otherLift := { lift with id := ⟨"test.creation.same_native_lift"⟩ }
  let otherRow := { row with id := ⟨"test.creation.same_native_presentation"⟩ }
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let firstValue ← first.source.inContext context
    let secondValue ← second.source.inContext context
    let .fvar firstId := firstValue.consumeMData
      | throwError "the first original map lost its source binding"
    let .fvar secondId := secondValue.consumeMData
      | throwError "the second original map lost its source binding"
    let some selected ← session.openCategory context firstId
      | throwError "the first original map lost its complete source category"
    let some secondSelected ← session.openCategory context secondId
      | throwError "the second original map lost its complete source category"
    let maps : Array NativeSourceJudgement := #[
      ⟨firstValue, some selected⟩, ⟨secondValue, some secondSelected⟩]
    for inventory in #[
        { state with lifts := #[lift, otherLift] },
        { state with lifts := #[otherLift, lift] },
        { state with limits := #[row, otherRow] },
        { state with limits := #[otherRow, row] }] do
      let failure ← try
          discard <| sourceCreatedLimit? inventory "pullback" selected maps
          pure none
        catch error => pure (some error)
      let some failure := failure
        | throwError "creation silently selected the first applicable lift/presentation pair"
      unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
    let absent ← sourceCreatedLimit? { state with lifts := #[] } "pullback" selected maps
    unless absent.isNone do
      throwError "creation inferred an unregistered source lift"
