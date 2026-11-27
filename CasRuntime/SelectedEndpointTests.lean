module

import all CasRuntime.Session
import CasCompiler.Parse
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
import LeanCategories.Catalogue.Semantics.Algebra.SuccessorSeries
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
meta import LeanCategories.Catalogue.Semantics.Algebra.SuccessorSeries

namespace CasRuntime.SelectedEndpointTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue




set_option maxHeartbeats 2000000 in
run_cmd liftTermElabM do
  let original ← getEnv
  try
    let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/rx08-ordinary-kernel.cas"
    let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
    let root ← liftM (m := IO) IO.currentDir
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let manifest := root / ".tmp" / "selected-endpoint-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile manifest
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let mut session ← KernelSession.start (some manifest) (computationOnly := true)
    try
      let mut selectedNames : Array Name := #[]
      for item in file.items do
        let `(cas_item| $statement:cas_stmt) := item | continue
        let `(cas_stmt| let $name:ident := $_:cas_term) := statement | continue
        unless #[`Q, `row, `projection].contains name.getId do continue
        let run ← withoutErrToSorry <| file.withContext (session.run statement)
        unless run.outcome.kind == "holds" do
          throwError "the original endpoint declaration {name.getId} is {run.outcome.kind}: {run.outcome.detail}"
        session := run.session
        selectedNames := selectedNames.push name.getId
      unless selectedNames == #[`Q, `row, `projection] do
        throwError "the endpoint control lost the original RX08 source declarations"
      for text in #["let Qagain := ℚ in CommutativeRings",
          "let rowAgain := [1, 0] in RectangularMatrices(1, 2, Q)",
          "let projectionAgain := row_linear_map(2, Q, rowAgain)"] do
        let statement ← match Parser.runParserCategory (← getEnv) `cas_stmt text with
          | .ok statement => pure statement
          | .error error => throwError "the equal endpoint declaration did not parse: {error}"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" do
          throwError "the equal endpoint declaration is {run.outcome.kind}: {run.outcome.detail}"
        session := run.session
      session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let selections ← session.source.selections.inContext context
        let mut bound : Std.HashMap BindingId ValueBinding := {}
        for binding in bindings do
          if let some value := session.value? binding.id then
            bound := bound.insert binding.id value
        let originalBinding (name : Name) : MetaM (LocalBinding × ValueBinding) := do
          let some entry := session.source.context.entries.find? (·.userName == name)
            | throwError "the endpoint control lost its original source binding {name}"
          let some binding := bindings.find? (·.id == entry.id)
            | throwError "the endpoint control lost its reopened source binding {name}"
          let some value := session.value? entry.id
            | throwError "the endpoint control lost its actual input {name}"
          return (binding, value)
        let (scalarBinding, scalarValue) ← originalBinding `Q
        let (otherScalarBinding, otherScalarValue) ← originalBinding `Qagain
        unless scalarValue.value != otherScalarValue.value &&
            (← context.withOriginalSources #[scalarBinding.expression, otherScalarBinding.expression]
              (fun values => isDefEq values[0]! values[1]!)) do
          throwError "the endpoint control did not retain distinct equal original scalar inputs"
        let same := fun (left right : ValueBinding) =>
          left.value == right.value && left.associationIds == right.associationIds
        let transaction ← CellTransaction.begin session.kernel.ledger
        try
          let inspected ← (show MetaM (Array (Expr × ValueBinding × ValueBinding × Array ValueBinding)) from do
            let mut inspected : Array (Expr × ValueBinding × ValueBinding × Array ValueBinding) := #[]
            for (mapName, rowName) in #[(`projection, `row), (`projectionAgain, `rowAgain)] do
              let (mapBinding, mapValue) ← originalBinding mapName
              let (_, rowValue) ← originalBinding rowName
              let type ← instantiateMVars (← inferType mapBinding.expression)
              let type := type.consumeMData
              let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
              unless type.isAppOfArity ``Quiver.Hom 4 do
                throwError "the original row map lost its native endpoint interface"
              let endpointSource := type.getAppArgs[2]!
              let some _ := selectedEndpoint? context selections endpointSource
                | throwError "the original row map lost its explicitly selected source endpoint"
              let endpoint ← session.kernel.run transaction context bound endpointSource (selections := selections)
              let graph ← transaction.view
              let some expectedSelection := selections.findAt? context endpointSource
                | throwError "the original row map lost its complete endpoint selection"
              withBindingContext graph context bound endpoint fun context _ => do
                let some retained ← endpoint.role.selected? context
                  | throwError "endpoint formation replaced its original selected source role"
                unless retained.exactlyMatches Expr.equal expectedSelection do
                  throwError "endpoint formation replaced its original selected source role"
              let some node := graph.find endpoint.value
                | throwError "the selected endpoint is outside its original graph"
              let .container descriptor := node.payload.data
                | throwError "the selected endpoint lost its map descriptor"
              let expectedPacket := Json.mkObj [("ctor", "morphismEndpoint"),
                ("args", .arr #[.null, "source"])]
              unless descriptor.template == expectedPacket do
                throwError "native endpoint fields changed the original descriptor packet"
              let #[slot] := descriptor.slots
                | throwError "the selected endpoint lost its sole original map slot"
              unless slot.path == #[.field "args", .index 0] && slot.fieldIndex.isNone &&
                  same slot.binding mapValue do
                throwError "the selected endpoint changed its original map occurrence"
              let some named ← InputDescriptorView.namedMorphism? graph
                  (← session.kernel.codes.get) slot.binding
                | throwError "the endpoint lost its actual named morphism producer"
              let some request := named.family
                | throwError "the endpoint lost its sealed original request"
              unless request.reference == some (.morphism ⟨"mor.modules.row_linear_map"⟩) do
                throwError "the endpoint changed its original released map family"
              let some application := request.origin.application
                | throwError "the endpoint lost its original complete argument table"
              let #[some dimension, some actualScalar, some actualRow] := application.arguments
                | throwError "the original row map changed its complete parameter positions"
              unless same actualScalar scalarValue && same actualRow rowValue do
                throwError "the endpoint substituted an equal original scalar or row"
              request.environment.withContext context bound fun context _ => do
                let dimensionSource ← dimension.role.source.inContext context
                unless ← context.withOriginalSources #[dimensionSource, mkNatLit 2]
                    (fun source => isDefEq source[0]! source[1]!) do
                  throwError "the original dimension input changed its source value"
              let some fields := descriptor.fields
                | throwError "the source-defined endpoint discarded its declared native field code"
              let some carrier := endpoint.role.fields.find? (·.projection == ``ModuleCat.carrier)
                | throwError "the selected module endpoint lost its native carrier field"
              let some carrierIndex := carrier.wireIndex
                | throwError "the native endpoint carrier became a proof field"
              let some carrierCode := fields[carrierIndex]?
                | throwError "the endpoint carrier has no retained native field closure"
              let some carrierNode := graph.find carrierCode.value
                | throwError "the endpoint field code is outside its original graph"
              let .closure code captures := carrierNode.payload.data
                | throwError "endpoint formation evaluated its native field eagerly"
              let some (.term _ _) := (← session.kernel.codes.get)[code]?
                | throwError "the endpoint field is not its retained original source code"
              inspected := inspected.push (endpointSource, endpoint, dimension, captures)
            return inspected)
          let #[(endpointSource, endpoint, dimension, captures),
              (otherSource, otherEndpoint, otherDimension, otherCaptures)] := inspected
            | throwError "the endpoint control did not inspect both original maps"
          unless endpoint.value != otherEndpoint.value && dimension.value != otherDimension.value &&
              (← context.withOriginalSources #[endpointSource, otherSource]
                (fun values => isDefEq values[0]! values[1]!)) do
            throwError "the endpoint control merged its distinct equal source occurrences"
          for (actualDimension, otherDimension, fieldCaptures) in
              #[(dimension, otherDimension, captures), (otherDimension, dimension, otherCaptures)] do
            unless fieldCaptures.any (same actualDimension) && fieldCaptures.any (same scalarValue) &&
                !(fieldCaptures.any (fun value => value.value == otherDimension.value ||
                  value.value == otherScalarValue.value)) do
              throwError "native endpoint field code replaced an original dimension or scalar input"
          withBindingContext (← transaction.view) context bound endpoint fun context bound => do
            let selections ← SourceSelectionScope.merge selections (← endpoint.role.selections.inContext context)
            withBoundValue session.kernel.ledger.owners.identities context bound
                (← endpoint.selectedSource context) endpoint fun context bound markedEndpoint => do
              let graph ← transaction.view
              let environment ← RuntimeEnvironment.captureBound
                session.kernel.ledger.owners.worker context bound graph (selections := selections)
              let source ← context.close markedEndpoint
              let .ok actual := RuntimeArgument.ofValue graph 0 endpoint
                | throwError "the original endpoint input is outside its graph"
              let admitted ← environment.checkArgument source actual
              unless same admitted endpoint do
                throwError "endpoint argument admission changed the actual selected reference"
              let .ok other := RuntimeArgument.ofValue graph 0 otherEndpoint
                | throwError "the distinct equal endpoint input is outside its graph"
              let failure : Option Exception ← try
                discard <| environment.checkArgument source other
                pure none
              catch error => pure (some error)
              let some failure := failure
                | throwError "the native view accepted a different equal endpoint occurrence"
              unless failure.toMessageData.hasTag
                  (· == `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch) do throw failure
              let some declaredEndpointSource := selectedEndpoint? context selections endpointSource
                | throwError "the original map lost its declared endpoint argument"
              unless declaredEndpointSource.getAppFn.isConstOf
                  ``CasCatalogue.Algebra.LinearAlgebra.vectorModule do
                throwError "the original RX08 map changed its declared source formation"
              let #[nativeScalar, _] := declaredEndpointSource.getAppArgs
                | throwError "the original module endpoint changed its native parameter positions"
              let inclusionInfo ← getConstInfo
                ``CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
              let inclusion := mkApp
                (Lean.mkConst inclusionInfo.name (inclusionInfo.levelParams.map fun _ => Level.zero))
                nativeScalar
              let inclusionPrefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[inclusion]
              let totalTerm ← mkAppM ``Prefunctor.obj #[inclusionPrefunctor, markedEndpoint]
              let totalValue ← session.kernel.run transaction context bound totalTerm (selections := selections)
              withBindingContext (← transaction.view) context bound totalValue fun context bound => do
                let selections ← SourceSelectionScope.merge selections
                  (← totalValue.role.selections.inContext context)
                withBoundValue session.kernel.ledger.owners.identities context bound
                    (← totalValue.selectedSource context) totalValue fun context bound totalSource => do
                  let some fibreField := totalValue.role.fields.find?
                      (·.projection == ``CategoryTheory.Pseudofunctor.CoGrothendieck.fiber)
                    | throwError "the native total module lost its original fibre field"
                  let some fibreIndex := fibreField.wireIndex
                    | throwError "the original selected endpoint became a proof field"
                  let fibreValue ← IO.ofExcept <|
                    ((← transaction.view).project totalValue fibreIndex).mapError IO.userError
                  unless fibreValue.value == endpoint.value &&
                      endpoint.associationIds.toList.isPrefixOf fibreValue.associationIds.toList do
                    throwError "the native fibre inclusion replaced the actual selected endpoint"
                  let actionInfo ← getConstInfo
                    ``CasCatalogue.Modules.CatalogueRegistration.modulesAdditiveGroupDeclaration
                  let action := Lean.mkConst actionInfo.name (actionInfo.levelParams.map fun _ => Level.zero)
                  let actionPrefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[action]
                  let objectAction ← mkAppM ``Prefunctor.obj #[actionPrefunctor]


                  let outputTerm := mkApp objectAction totalSource
                  let output ← session.kernel.run transaction context bound outputTerm (selections := selections)
                  withBindingContext (← transaction.view) context bound output fun context bound => do
                    let selections ← SourceSelectionScope.merge selections
                      (← output.role.selections.inContext context)
                    withBoundValue session.kernel.ledger.owners.identities context bound
                        (← output.selectedSource context) output fun context bound markedOutput => do
                      let originalPaths : Array (Name × Array Name) := #[
                        (``AddGrpCat.carrier,
                          #[``CategoryTheory.Pseudofunctor.CoGrothendieck.fiber, ``ModuleCat.carrier]),
                        (``AddGrpCat.str,
                          #[``CategoryTheory.Pseudofunctor.CoGrothendieck.fiber,
                            ``ModuleCat.isAddCommGroup, ``AddCommGroup.toAddGroup])]
                      for (projection, originalPath) in originalPaths do
                        let some field := output.role.fields.find? (·.projection == projection)
                          | throwError "the additive view lost its original output field"
                        let selected ← session.kernel.run transaction context bound
                          (← projectTerm markedOutput field) (selections := selections)
                        let graph ← transaction.view
                        let some baseline ← IO.ofExcept <|
                            (graph.projected? totalValue originalPath).mapError IO.userError
                          | throwError "the additive view did not publish its original native input path"
                        let some retained ← IO.ofExcept <|
                            (graph.projectionBasis selected totalValue originalPath).mapError IO.userError
                          | throwError "the additive view lost its exact original endpoint projection"
                        unless selected.value == baseline.value &&
                            baseline.associationIds.toList.isPrefixOf selected.associationIds.toList &&
                            same retained baseline do
                          throwError "the additive view replaced an original selected endpoint field"
                      unless (← session.kernel.dispatches.get).isEmpty do
                        throwError "the native selected endpoint view dispatched a mathematical provider"
        finally discard <| transaction.abort
    finally liftM (m := IO) session.close
  finally setEnv original





run_cmd liftTermElabM do
  let extendedEnvironment ← getEnv
  try
    let extensionModule := `LeanCategories.Catalogue.Semantics.Algebra.SuccessorSeries
    unless extendedEnvironment.imports.any (·.module == extensionModule) do
      throwError "the registry stability control lost its declared module dependency"
    let baseImports := extendedEnvironment.imports.filter (·.module != extensionModule)
    let baseline ← liftM (m := IO) <| Lean.importModules baseImports (← getOptions)
      (leakEnv := true) (loadExts := true)
    setEnv baseline
    let before ← RegistrySnapshot.snapshot
    let addedId := "mor.sets.successor_power_series_terms"
    if before.hasEntry addedId then
      throwError "the unrelated released row was already present before endpoint selection"
    let identities ← liftM (m := IO) IdentitySupply.new
    let mut source ← SourceSession.empty identities
    let path := "tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/rx08-ordinary-kernel.cas"
    let file ← SourceFile.parse path (← liftM (m := IO) (IO.FS.readFile path))
    let mut selectedNames : Array Name := #[]
    for item in file.items do
      let `(cas_item| $statement:cas_stmt) := item | continue
      let `(cas_stmt| let $name:ident := $_:cas_term) := statement | continue
      unless #[`Q, `row, `projection].contains name.getId do continue
      let .definition next _ ← withoutErrToSorry <|
          file.withContext (source.readStatement statement)
        | throwError "the endpoint registry control changed an original public definition"
      source := next
      selectedNames := selectedNames.push name.getId
    unless selectedNames == #[`Q, `row, `projection] do
      throwError "the endpoint registry control lost the original RX08 source statements"
    let some mapEntry := source.context.entries.back?
      | throwError "the original endpoint source lost its public map binding"
    unless mapEntry.userName == `projection do
      throwError "the original endpoint source changed its final authored binding"
    let some originalMap := source.selections[mapEntry.id]?
      | throwError "the original public map lost its complete selected row"
    let (endpointId, endpointSource, originalEndpoint, originalArrow) ←
        source.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      let selections ← source.selections.inContext context
      let some binding := bindings.find? (·.id == mapEntry.id)
        | throwError "the original map is outside its complete source context"
      let type ← instantiateMVars (← inferType binding.expression)
      let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
      unless type.isAppOfArity ``Quiver.Hom 4 do
        throwError "the original map lost its complete native endpoint interface"
      let endpoint := type.getAppArgs[2]!
      let some _ := selectedEndpoint? context selections endpoint
        | throwError "the original map has no explicitly selected source endpoint"
      let some binding := context.bindings.find? (·.expression.equal endpoint)
        | throwError "the original selected endpoint lost its exact native binding"
      let some selected := selections[binding.id]?
        | throwError "the original selected endpoint lost its complete typed data"
      let some endpointData := selected.endpoint
        | throwError "the original endpoint lost its exact selected map projection"
      let some arrow := selections.findAt? context endpointData.arrow
        | throwError "the original endpoint lost its complete selected map"
      return (binding.id, ← context.close endpoint,
        ← selected.mapM (fun term => context.close term),
        ← arrow.mapM (fun term => context.close term))
    let endpointTerm ← source.elaborate Syntax.missing fun context =>
      endpointSource.inContext context
    source ← source.defineTerm `originalEndpoint endpointTerm


    setEnv extendedEnvironment
    source.ensureDeclarations
    let after ← RegistrySnapshot.snapshot
    let added := after.entries.filter fun entry => !before.hasEntry entry.stableId
    unless added.map (·.stableId) == #[addedId] do
      throwError "the independent module did not make its exact unrelated registry addition"
    for entry in before.entries do
      let some retained := after.findEntry? entry.stableId
        | throwError "the independent module removed an original registered row"
      unless toJson retained == toJson entry do
        throwError "the independent module changed an original complete registered row"
    let root ← liftM (m := IO) IO.currentDir
    liftM (m := IO) <| IO.FS.createDirAll (root / ".tmp")
    let manifest := root / ".tmp/selected-endpoint-registry-empty-leaves.json"
    liftM (m := IO) <| IO.FS.writeFile manifest
      (Json.mkObj [("backends", .arr #[]), ("registrations", .arr #[])]).compress
    let initial ← KernelSession.start (some manifest) (computationOnly := true)
    try
      let mut session := { initial with source }
      let mut endpoints : Array ValueBinding := #[]
      for (name, text) in #[
          (`retainedEndpoint, "let retainedEndpoint := originalEndpoint"),
          (`endpointAlias, "let endpointAlias := retainedEndpoint")] do
        let .ok statement := Parser.runParserCategory (← getEnv) `cas_stmt text
          | throwError "the retained endpoint's public continuation did not parse"
        let run ← withoutErrToSorry <| session.run ⟨statement⟩
        unless run.outcome.kind == "holds" && run.attempted && run.published do
          throwError "the retained endpoint's public continuation failed: {run.outcome.detail}"
        session := run.session
        let some entry := session.source.context.entries.back?
          | throwError "the retained endpoint continuation lost its authored result"
        unless entry.userName == name do
          throwError "the retained endpoint continuation changed its original result binding"
        let some value := session.value? entry.id
          | throwError "the retained endpoint continuation lost its actual occurrence"
        endpoints := endpoints.push value
      let #[endpointValue, endpointAlias] := endpoints
        | throwError "the endpoint registry control lost its original and later public results"
      unless retainsReference endpointValue endpointAlias do
        throwError "the later public alias replaced its original endpoint occurrence"
      let graph := (← SessionSnapshot.current).graph
      session.source.context.withOpen fun bindings => do
        let context ← ContextTelescope.capture bindings
        let selections ← session.source.selections.inContext context
        let expectedMap ← originalMap.mapM (fun term => term.inContext context)
        let expectedEndpoint ← originalEndpoint.mapM (fun term => term.inContext context)
        let expectedArrow ← originalArrow.mapM (fun term => term.inContext context)
        let endpoint ← endpointSource.inContext context
        let some endpointBinding := context.bindings.find? (·.id == endpointId)
          | throwError "the registry addition replaced the original endpoint binding identity"
        unless endpointBinding.expression.equal endpoint do
          throwError "the registry addition changed the original endpoint source reference"
        let some retainedEndpoint := selections[endpointId]?
          | throwError "the registry addition removed the original typed endpoint"
        let some retainedMap := selections[mapEntry.id]?
          | throwError "the registry addition removed the original selected map row"
        let some endpointData := retainedEndpoint.endpoint
          | throwError "the registry addition removed the original map projection"
        let some retainedArrow := selections.findAt? context endpointData.arrow
          | throwError "the registry addition removed the original selected arrow"
        unless expectedEndpoint.exactlyMatches Expr.equal retainedEndpoint &&
            expectedMap.exactlyMatches Expr.equal retainedMap &&
            expectedArrow.exactlyMatches Expr.equal retainedArrow do
          throwError "the unrelated registry addition changed a complete selected endpoint or map"
        let some mapBinding := context.bindings.find? (·.id == mapEntry.id)
          | throwError "the original map is outside its complete source context"
        let type ← instantiateMVars (← inferType mapBinding.expression)
        let type ← if type.isAppOfArity ``Quiver.Hom 4 then pure type else whnfR type
        unless type.isAppOfArity ``Quiver.Hom 4 &&
            type.getAppArgs[2]!.equal endpoint do
          throwError "the registry addition substituted a different selected source endpoint"
        let mut bound : Std.HashMap BindingId ValueBinding := {}
        for binding in bindings do
          if let some value := session.value? binding.id then
            bound := bound.insert binding.id value
        withBindingContext graph context bound endpointValue fun context bound => do
          let some selected ← endpointValue.role.selected? context
            | throwError "the runtime endpoint lost its complete original source selection"
          let expected ← originalEndpoint.mapM (fun term => term.inContext context)
          unless selected.exactlyMatches Expr.equal expected do
            throwError "the runtime endpoint changed its complete selected meaning"
          let some endpointData := selected.endpoint
            | throwError "the runtime endpoint lost its original selected map projection"
          let retainedScope ← endpointValue.role.selections.inContext context
          let some actualArrow := retainedScope.findAt? context endpointData.arrow
            | throwError "the runtime endpoint lost its complete original selected map"
          let expectedArrow ← originalArrow.mapM (fun term => term.inContext context)
          unless actualArrow.exactlyMatches Expr.equal expectedArrow do
            throwError "the runtime endpoint changed its original selected map data"
          let some (arrowId, suffix) ← boundProjection? context bound endpointData.arrow
            | throwError "the runtime endpoint lost its actual original map binding"
          let some actualParent := bound[arrowId]?
            | throwError "the runtime endpoint's map is outside its actual bound context"
          unless suffix.isEmpty do
            throwError "the runtime endpoint changed its original map operand position"
          let some node := graph.find endpointValue.value
            | throwError "the selected endpoint is outside its actual runtime graph"
          let .container descriptor := node.payload.data
            | throwError "the selected endpoint lost its actual map descriptor"
          let #[slot] := descriptor.slots
            | throwError "the selected endpoint lost its original map position"
          unless descriptor.template == Json.mkObj [("ctor", "morphismEndpoint"),
              ("args", .arr #[.null, "source"])] &&
              slot.path == #[.field "args", .index 0] && slot.fieldIndex.isNone &&
              retainsReference actualParent slot.binding do
            throwError "the unrelated registry addition replaced the endpoint's actual map"
          let some named ← InputDescriptorView.namedMorphism? graph
              (← session.kernel.codes.get) slot.binding
            | throwError "the endpoint slot lost its original named morphism producer"
          let some request := named.family
            | throwError "the endpoint slot lost its original prepared family"
          let .primitive (.registered family) _ := request.action
            | throwError "the endpoint slot changed its original family boundary"
          let some reference := actualArrow.reference
            | throwError "the endpoint slot lost its complete original registered row"
          unless family.selectedReference.exactlyMatches reference do
            throwError "the endpoint slot substituted a different complete registered row"
      unless (← session.kernel.dispatches.get).isEmpty do
        throwError "the registry stability control dispatched an unrequested implementation"
    finally initial.close
  finally setEnv extendedEnvironment

end CasRuntime.SelectedEndpointTests
