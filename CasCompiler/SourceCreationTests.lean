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


private def withCreationTerms (session : SourceSession) (terms : Array SourceTerm)
    (action : OpenContext → SourceSelectionScope Expr → Array Expr → TermElabM α) :
    TermElabM α := do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  session.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let initial : SourceReadScope := {
      identities := identities, context,
      selections := ← session.selections.inContext context }
    let read : SourceReadM (Array Expr) := terms.mapM session.readTerm
    read.runK initial fun values scope => action scope.context scope.selections values


private def creationApplication (context : OpenContext) (selections : SourceSelectionScope Expr)
    (value : Expr) : MetaM (SelectedSourceApplication Expr) := do
  let rec visit (fuel : Nat) (value : Expr) : MetaM (SelectedSourceApplication Expr) := do
    match fuel with
    | 0 => throwError "the creation action has cyclic endpoint provenance"
    | fuel + 1 =>
      let some template := selections.findAt? context value.getAppFn
        | throwError "the creation lost an exact selected action binder"
      let selected ← template.specialize value.getAppArgs
      if let some application := selected.application then return application
      if let some endpoint := selected.endpoint then return ← visit fuel endpoint.value
      throwError "the creation lost its complete original action family"
  visit (context.bindings.size + 1) value



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
  withCreationTerms session #[result] fun context _ values => do
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
    context.withOriginalSources #[values[0]!] fun sources => do
      let letIds := (← getLCtx).foldl (fun ids declaration =>
        if declaration.isLet then ids.push declaration.fvarId else ids) #[]
      let source ← zetaDeltaFVars sources[0]! letIds
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
  withCreationTerms retained #[sourceAlias, leg, secondLeg, thirdLeg] fun context selections _ => do
    let original ← creation.mapM (·.inContext context)
    let reopened ← aliasCreation.mapM (·.inContext context)
    unless (original.terms.zip reopened.terms).all (fun (left, right) => left.equal right) do
      throwError "closing and reopening changed an original creation field"
    let source ← leg.source.inContext context
    let some decoded ← NativeLimitLegSelection.ofExpr? context selections source
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
      let some selected ← NativeLimitLegSelection.ofExpr? context selections (← leg.source.inContext context)
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




run_cmd Lean.Elab.Command.liftTermElabM do
  let session ← creationSourceSession
  let result ← session.read (← creationSourceTerm "pullback(f', g')")
  withCreationTerms session #[result] fun original selections values => do
    let owner := values[0]!
    let some sourceSelection := selections.findAt? original owner
      | throwError "the selected creation lost its complete typed source record"
    let some selected := sourceSelection.limit
      | throwError "the selected creation lost its original native interface"
    let some (creationFamily, targetFamily) := sourceSelection.creationOwner
      | throwError "the selected creation lost its complete accepted family pair"
    let some prepared ← PreparedCreationFamily.ofSelection original owner selected
      creationFamily targetFamily selections
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
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let originalInputs ← prepared.sourceArguments.mapM (·.inContext original)
    let reading : SourceReadM (Array Expr) :=
      originalInputs.mapM fun value => SourceReadM.select { value }
    reading.runK { identities := identities, context := original, selections }
        fun markedInputs scope =>
      prepared.rebindSource identities scope.context scope.selections markedInputs
          fun original selections rebound => do
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
          let hom ← inferType targetInput
          unless hom.isAppOfArity ``Quiver.Hom 4 do
            throwError "the target map lost its complete native Hom schema"
          let targetMap := if targetInput.isAppOfArity ``id 2 then
            targetInput.getAppArgs[1]! else targetInput
          let application ← creationApplication original selections targetMap
          let .point retainedFamily := application.family
            | throwError "the target map lost its selected generic action family"
          unless (SelectedApplicationFamily.point retainedFamily).exactlyMatches (.point family) do
            throwError "the target map changed its complete original action owner"
          let levels := application.universes
          let parameters := application.parameters
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
            let application ← creationApplication original selections image
            let .objectAction retainedFamily := application.family
              | throwError "an implicit target object lost its selected object action"
            unless (SelectedApplicationFamily.objectAction retainedFamily).exactlyMatches
                (.objectAction objects) do
              throwError "an implicit target object changed its original action"
            unless application.universes == levels &&
                application.parameters == parameters.extract 0 maps.declarationParameterCount &&
                application.arguments == #[receiver] do
              throwError "an implicit target object lost an original declaration argument or receiver"
        let firstType ← inferType targetInputs[0]!
        let secondType ← inferType targetInputs[1]!
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
                let context ← ContextTelescope.capture (original.bindings ++ actualBindings)
                let decoded ← prepared.withArguments context cone universal
                let selectedRequest ← prepared.selectedArguments context
                  (← prepared.owner.inContext context) cone universal
                let some application := selectedRequest.application
                  | throwError "the fixed creation request lost its complete selected application"
                unless selectedRequest.value.equal
                    (mkAppN (← decoded.familyIn context) #[cone, universal]) &&
                    application.arguments == #[cone, universal] do
                  throwError "the temporary creation inputs changed before their complete scope was closed"
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
                    let originalSelection ← prepared.selection context
                    let changed ← NativeLimitSelection.ofSource
                      { originalSelection.source with construction := `differentConstruction }
                      originalSelection.receiver
                    discard <| PreparedCreationFamily.ofSelection context
                      (← prepared.owner.inContext context) changed prepared.family prepared.target selections
                    pure false
                  catch _ => pure true
                unless replaced do
                  throwError "the fixed creation marker accepted a different construction occurrence"



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
  withCreationTerms session #[first, second] fun context selections values => do
    let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
    let initial : SourceReadScope := { identities, context, selections }
    let firstValue := values[0]!
    let secondValue := values[1]!
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
          (sourceCreatedLimit? inventory "pullback" selected maps).runK initial
            (fun _ _ => pure ())
          pure none
        catch error => pure (some error)
      let some failure := failure
        | throwError "creation silently selected the first applicable lift/presentation pair"
      unless CasCatalogue.Exception.isSemanticAmbiguity failure do throw failure
    (sourceCreatedLimit? { state with lifts := #[] } "pullback" selected maps).runK initial
        fun absent _ => do
      unless absent.isNone do
        throwError "creation inferred an unregistered source lift"
