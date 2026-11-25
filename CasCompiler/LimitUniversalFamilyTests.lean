module

import CasCompiler.LimitUniversalFamily
import CasCompiler.PublishedPorts
import LeanCategories.Catalogue
meta import CasCompiler.LimitUniversalFamily
meta import CasCompiler.PublishedPorts
meta import LeanCategories.Catalogue
public meta import Lean.Elab.Command

open Lean Meta Elab Command CasCatalogue CasCompiler

-- Every source binder, including original proof positions and rigid universe parameters,
-- survives selecting the universal record from the complete native presentation. The
-- existing nullary terminal presentation must remain a record with an empty input frame.
run_cmd liftTermElabM do
  let identifiers := #["lim.sets.product", "lim.sets.pullback", "colim.sets.coproduct",
    "lim.sets.diagram", "lim.sets.terminal"]
  for identifier in identifiers do
    let family ← LimitUniversalFamily.forId ⟨identifier⟩
    let information ← getConstInfo family.presentation.entry.declaration
    unless family.universeParams == information.levelParams &&
        family.operation == identifier ++ "#" ++ family.projection.getString! &&
        family.input == family.operation ++ "#input" && family.path == #[family.projection] do
      throwError "the universal family changed its independently selected native owner"
    checkWithKernel family.family
    for levels in #[family.universeParams.map (fun _ => Level.zero),
        family.universeParams.map Level.param] do
      let declaration := mkConst information.name levels
      forallTelescopeReducing (← inferType declaration) fun parameters _ => do
        unless parameters.size == family.parameterCount do
          throwError "the universal family added or removed an original declaration parameter"
        let bindings := parameters.mapIdx fun index expression =>
          { id := { session := "universal-original-telescope", serial := index },
            role := BindingRole.parameter, expression : LocalBinding }
        let context ← ContextTelescope.capture bindings
        let closed ← (parameters.mapM context.close : MetaM (Array ClosedTerm))
        let original ← SourceLayout.ofTerm (← context.close declaration)
        let (_, application) ← ApplicationLayout.ofSource original context closed
        let selected ← application.forProjection family.projection
        unless selected.arguments.size == parameters.size &&
            selected.result.address == application.result.address ++ family.path do
          throwError "native universal selection changed its original telescope or full path"
        for parameter in parameters, argument in selected.arguments, index in [:parameters.size] do
          unless argument.sourceIndex == index &&
              argument.wireIndex.isNone == (← isProof parameter) &&
              argument.binderInfo == (← parameter.fvarId!.getDecl).binderInfo do
            throwError "native universal selection changed an original proof or binder position"
        let presentation := mkAppN declaration parameters
        let expected ← mkAppM family.projection #[presentation]
        let actual := (mkAppN
          (family.family.instantiateLevelParams family.universeParams levels) parameters).headBeta
        unless ← isDefEq actual expected do
          throwError "the universal family changed the original selected native projection"
        if ← isProof actual then
          throwError "the data-bearing universal interface was discarded as a proof"
        let actualResult ← selected.result.source.inContext context
        unless ← isDefEq actualResult expected do
          throwError "the application selected another original native result"
        let typeFamily := (mkAppN
          (← selected.resultTypeFamily.inContext context) parameters).headBeta
        unless ← isDefEq typeFamily (← inferType expected) do
          throwError "the projected dependency family changed the complete native result type"
        let dependencies ← application.dependenciesAt family.path
        unless selected.resultDependencies == dependencies.arguments &&
            selected.resultContextDependencies == dependencies.context do
          throwError "the universal projection lost its original dependency positions"
        if identifier == "lim.sets.product" then
          unless selected.resultDependencies.contains 0 && selected.resultDependencies.contains 1 do
            throwError "the universal product interface lost an original endpoint parameter"
        if identifier == "lim.sets.terminal" then
          unless parameters.isEmpty && selected.arguments.isEmpty &&
              selected.resultDependencies.isEmpty && selected.result.kind == .record do
            throwError "the nullary universal presentation lost its empty original record frame"
        let #[nativeUniversal] := application.result.fields.filter
            (·.projection == family.projection)
          | throwError "the complete presentation lost its original universal field"
        let earlier ← application.result.actionInputs context presentation #[nativeUniversal]
        unless earlier.any (·.projection == family.presentation.coneProjection) do
          throwError "the universal interface lost its actual earlier cone input"
        for predecessor in earlier do
          unless predecessor.sourceIndex < nativeUniversal.sourceIndex do
            throwError "the universal interface changed its original source order"
        let liftProjection := if family.presentation.entry.colimit then
          ``CategoryTheory.Limits.IsColimit.desc else ``CategoryTheory.Limits.IsLimit.lift
        let #[nativeLift] := selected.result.fields.filter (·.projection == liftProjection)
          | throwError "the native universal continuation is absent"
        unless nativeLift.wireIndex == some 0 do
          throwError "the universal continuation lost its actual data position"
        checkWithKernel (← mkLambdaFVars parameters expected
          (usedOnly := false) (usedLetOnly := false))
        checkWithKernel (← mkLambdaFVars parameters actualResult
          (usedOnly := false) (usedLetOnly := false))
    let ports ← PublishedPorts.forLimitUniversal family.presentation.entry.id
    unless ports.any (fun port => port.operation == family.operation &&
        port.path == family.path) do
      throwError "publication lost the whole native universal record"
    unless ports.any (fun port => port.operation == family.operation &&
        port.path.size > family.path.size) do
      throwError "publication lost the native universal continuation"
    if ports.any (·.operation == identifier) then
      throwError "a universal native field reused the distinct raw cone address"
    for suffix in #["#leg", "#apex", "#map", "#input"] do
      if (← PublishedPorts.limitUniversal? (← semanticState) (identifier ++ suffix)).isSome then
        throwError "a limit prefix authorized an undeclared universal address"

-- Source formation retains the original construction and every actual parameter position.
-- The default cone is a published whole request; explicit completed-cone marks survive exactly.
run_cmd liftTermElabM do
  for identifier in #["lim.sets.product", "colim.sets.coproduct", "lim.sets.pullback"] do
    let family ← LimitUniversalFamily.forId ⟨identifier⟩
    let levels := family.universeParams.map Level.param
    let declaration := family.presentation.presentationFamily.instantiateLevelParams
      family.universeParams levels
    forallTelescopeReducing (← inferType declaration) fun parameters _ => do
      let construction ← mkFreshUserName `originalUniversalConstruction
      let ownerFamily ← family.presentation.prepareOwner levels construction
      let source ← family.markSelected ownerFamily levels parameters
      checkWithKernel (← mkLambdaFVars parameters source
        (usedOnly := false) (usedLetOnly := false))
      let .mdata metadata body := source
        | throwError "the universal source lost its exact owner marker"
      let restored ← LimitUniversalFamily.fromMark metadata
      let (actualLevels, actual, owner, selected, cone) ← restored.application body
      unless actualLevels == levels && actual == parameters &&
          selected.source.construction == construction do
        throwError "the universal source changed its original selected parameter table"
      let .mdata coneData coneBody := cone
        | throwError "the universal source lost its published whole-cone request"
      let raw ← LimitFamily.fromMark coneData
      let (_, rawArguments, rawOwner, rawSelected) ← raw.application coneBody
      unless rawArguments == parameters && rawOwner == owner &&
          rawSelected.source.construction == construction do
        throwError "the default universal cone changed its original raw source occurrence"
      for key in #[41, 42] do
        let actualCone := Expr.mdata (KVMap.empty.setNat `CasCompiler.lower.value key) cone
        let marked ← family.markAtOwner owner levels parameters (some actualCone)
        let .mdata _ body := marked
          | throwError "the explicit completed cone lost its universal envelope"
        let (_, _, _, original, retained) ← family.application body
        unless retained == actualCone && original.source.construction == construction do
          throwError "the universal envelope replaced an actual completed-cone occurrence"
      let wrongCone ← try
          discard <| family.markAtOwner owner levels parameters (some (mkNatLit 1))
          pure false
        catch _ => pure true
      unless wrongCone do throwError "the universal source admitted another native cone interface"
      let wrongProjection ← try
          discard <| LimitUniversalFamily.fromMark
            (metadata.setName `CasCompiler.source.limit.universal family.presentation.coneProjection)
          pure false
        catch _ => pure true
      unless wrongProjection do throwError "the universal source admitted another native projection"


-- The root creation port publishes the complete fixed-context template, including
-- target diagram and accepted comparison. Its two actual data inputs remain the
-- original target cone and universal record, not standardized runtime substitutes.
run_cmd liftTermElabM do
  let family ← CreationFamily.forId ⟨"lift.finite_sets.pullbacks"⟩
  let template ← family.standardizedTemplate
  let signature ← inferType template
  let #[port] ← PublishedPorts.forCreation family.entry.id
    | throwError "creation publication changed its single complete-result operation"
  unless port.operation == family.entry.id.raw && port.path.isEmpty &&
      (← isDefEq port.type signature) do
    throwError "the creation port omitted its full original comparison context"
  for levels in #[family.universeParams.map (fun _ => Level.zero),
      family.universeParams.map Level.param] do
    let native := template.instantiateLevelParams family.universeParams levels
    let type ← inferType native
    unless !native.hasMVar && !native.hasLevelMVar && !native.hasFVar do
      throwError "the creation publication failed to close its rigid native telescope"
    checkWithKernel native
    checkWithKernel type
    forallTelescopeReducing type fun parameters result => do
      unless parameters.size == family.parameterCount + 5 do
        throwError "the creation signature lost an evidence, diagram or comparison position"
      let some targetDiagram := parameters[family.parameterCount + 1]?
        | throwError "the creation signature lost its original target diagram"
      let some comparison := parameters[family.parameterCount + 2]?
        | throwError "the creation signature lost its accepted comparison"
      let some cone := parameters[family.parameterCount + 3]?
        | throwError "the creation signature lost its actual target cone"
      let some universal := parameters[family.parameterCount + 4]?
        | throwError "the creation signature lost its actual target universal data"
      unless (← whnfR (← inferType comparison)).isAppOf ``CategoryTheory.Iso &&
          (← isDefEq (← inferType cone)
            (← mkAppM ``CategoryTheory.Limits.Cone #[targetDiagram])) &&
          (← isDefEq (← inferType universal)
            (← mkAppM ``CategoryTheory.Limits.IsLimit #[cone])) &&
          !(← isProof universal) &&
          (← whnfR result).isAppOf ``CategoryTheory.LiftsToLimit do
        throwError "the creation signature changed its original inputs or complete native result"
