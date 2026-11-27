module

import CasCompiler.LimitUniversalFamily
import CasCompiler.PublishedPorts
import LeanCategories.Catalogue
meta import CasCompiler.LimitUniversalFamily
meta import CasCompiler.PublishedPorts
meta import LeanCategories.Catalogue
public meta import Lean.Elab.Command

open Lean Meta Elab Command CasCatalogue CasCompiler




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



run_cmd liftTermElabM do
  let identities ← liftM (m := IO) CasRuntime.IdentitySupply.new
  for identifier in #["lim.sets.product", "colim.sets.coproduct", "lim.sets.pullback"] do
    let family ← LimitUniversalFamily.forId ⟨identifier⟩
    let levels := family.universeParams.map Level.param
    let declaration := family.presentation.presentationFamily.instantiateLevelParams
      family.universeParams levels
    forallTelescopeReducing (← inferType declaration) fun parameters _ => do
      let construction ← mkFreshUserName `originalUniversalConstruction
      let owner ← family.presentation.prepareOwner identities levels construction
      let bindings ← parameters.mapM fun expression => do
        let allocated ← liftM (m := BaseIO) <| identities.fresh .sourceBinding
        return ({ id := ⟨allocated.worker, allocated.serial⟩,
          role := .parameter, expression } : LocalBinding)
      let context ← ContextTelescope.capture bindings
      let initial : SourceReadScope := { identities, context, selections := {} }
      let read : SourceReadM (SourceSelection Expr) :=
        family.selectedAtOwner owner levels parameters
          (fun selected expected => SourceReadM.select selected expected)
      read.runK initial fun source scope => do
        checkWithKernel (← mkLambdaFVars parameters source.value
          (usedOnly := false) (usedLetOnly := false))
        let some application := source.application
          | throwError "the universal source lost its complete selected application"
        let .limitUniversal restored := application.family
          | throwError "the universal source lost its exact complete native family"
        let some selected := source.limit
          | throwError "the universal source lost its original construction"
        let some originalOwner := application.ownerSelection
          | throwError "the universal source lost its complete typed owner template"
        unless (SelectedApplicationFamily.limitUniversal restored).exactlyMatches
              (.limitUniversal family) &&
            application.universes == levels && application.parameters == parameters &&
            selected.source.construction == construction do
          throwError "the universal source changed its original selected parameter table"
        let #[cone] := application.arguments
          | throwError "the universal source lost its single original cone argument"
        let some rawSource := scope.selections.findAt? scope.context cone
          | throwError "the universal source lost its published whole-cone request"
        let some rawApplication := rawSource.application
          | throwError "the default universal cone lost its complete native parameter table"
        let .limit raw := rawApplication.family
          | throwError "the default universal cone changed its original raw family"
        let some rawOwner := rawApplication.ownerSelection
          | throwError "the default universal cone lost its typed owner"
        let some rawSelected := rawSource.limit
          | throwError "the default universal cone lost its original construction"
        let sameOwner := SourceSelection.exactlyMatches Expr.equal
          ({ value := originalOwner.selection.receiver, limit := some originalOwner.selection,
            formalBindings := originalOwner.formalBindings } : SourceSelection Expr)
          ({ value := rawOwner.selection.receiver, limit := some rawOwner.selection,
            formalBindings := rawOwner.formalBindings } : SourceSelection Expr)
        unless (SelectedApplicationFamily.limit raw).exactlyMatches (.limit family.presentation) &&
            rawApplication.parameters == parameters && rawApplication.owner == application.owner &&
            sameOwner && rawSelected.source.construction == construction do
          throwError "the default universal cone changed its original raw source occurrence"
        for _ in #[41, 42] do
          SourceSelectionScope.withBinding identities scope.selections scope.context rawSource
              fun _ _ actualCone => do
            let explicit ← family.selectedAtOwner originalOwner levels parameters
              (fun _ _ => throwError "the explicitly supplied cone cannot be replaced")
              (some actualCone)
            let some explicitApplication := explicit.application
              | throwError "the explicit completed cone lost its universal application"
            let some original := explicit.limit
              | throwError "the explicit completed cone lost its original construction"
            unless explicitApplication.arguments == #[actualCone] &&
                original.source.construction == construction do
              throwError "the universal source replaced an actual completed-cone occurrence"
        let wrongCone ← try
            discard <| family.selectedAtOwner originalOwner levels parameters
              (fun _ _ => throwError "the explicitly supplied cone cannot be replaced")
              (some (mkNatLit 1))
            pure false
          catch _ => pure true
        unless wrongCone do throwError "the universal source admitted another native cone interface"
        let presentation := mkAppN declaration parameters
        let wrongValue ← mkAppM family.presentation.coneProjection #[presentation]
        let expected ← inferType source.value
        let wrongProjection ← try
            SourceSelectionScope.withBinding identities scope.selections scope.context
              { source with value := wrongValue } (fun _ _ _ => pure ())
              (declaredType := some expected)
            pure false
          catch _ => pure true
        unless wrongProjection do throwError "the universal source admitted another native projection"




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
