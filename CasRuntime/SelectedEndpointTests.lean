module

import CasRuntime.Session
import CasCompiler.Parse
import LeanCategories.Catalogue
import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra
public meta import Lean.Elab.Command
meta import CasRuntime.Session
meta import CasCompiler.Parse
meta import LeanCategories.Catalogue
meta import LeanCategories.Catalogue.Semantics.Algebra.RectangularLinearAlgebra

namespace CasRuntime.SelectedEndpointTests

open Lean Meta Elab Command Term CasCompiler CasCatalogue

-- The source endpoint of the original RX08 row map has native field code declared by
-- that map's source family. It stays the selected endpoint of that same actual map;
-- the control supplies no expected module/group fields or mathematical map answer.
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
            (← isDefEq scalarBinding.expression otherScalarBinding.expression) do
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
              let some _ := selectedEndpoint? endpointSource
                | throwError "the original row map lost its explicitly selected source endpoint"
              let endpoint ← session.kernel.run transaction context bound endpointSource
              unless (← endpoint.role.source.inContext context) == endpointSource do
                throwError "endpoint formation replaced its original selected source role"
              let graph ← transaction.view
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
              let dimensionSource ← dimension.role.source.inContext context
              unless ← isDefEq dimensionSource (mkNatLit 2) do
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
              let some (.term _) := (← session.kernel.codes.get)[code]?
                | throwError "the endpoint field is not its retained original source code"
              inspected := inspected.push (endpointSource, endpoint, dimension, captures)
            return inspected)
          let #[(endpointSource, endpoint, dimension, captures),
              (otherSource, otherEndpoint, otherDimension, otherCaptures)] := inspected
            | throwError "the endpoint control did not inspect both original maps"
          unless endpoint.value != otherEndpoint.value && dimension.value != otherDimension.value &&
              (← isDefEq endpointSource otherSource) do
            throwError "the endpoint control merged its distinct equal source occurrences"
          for (actualDimension, otherDimension, fieldCaptures) in
              #[(dimension, otherDimension, captures), (otherDimension, dimension, otherCaptures)] do
            unless fieldCaptures.any (same actualDimension) && fieldCaptures.any (same scalarValue) &&
                !(fieldCaptures.any (fun value => value.value == otherDimension.value ||
                  value.value == otherScalarValue.value)) do
              throwError "native endpoint field code replaced an original dimension or scalar input"
          let markedEndpoint ← markValue session.kernel.marks endpoint endpointSource
          let graph ← transaction.view
          let mut parameters : Array RuntimeParameter := #[]
          for binding in bindings do
            if let some value := session.value? binding.id then
              let .ok parameter := RuntimeParameter.ofValue graph binding.id value
                | throwError "the original endpoint context is outside its graph"
              parameters := parameters.push parameter
          let environment ← RuntimeEnvironment.capture session.kernel.ledger.owners.worker context parameters
          let source ← context.close markedEndpoint
          let .ok actual := RuntimeArgument.ofValue graph 0 endpoint (← session.kernel.marks.get)
            | throwError "the original endpoint input is outside its graph"
          let admitted ← environment.checkArgument source actual
          unless same admitted endpoint do
            throwError "endpoint argument admission changed the actual selected reference"
          let .ok other := RuntimeArgument.ofValue graph 0 otherEndpoint (← session.kernel.marks.get)
            | throwError "the distinct equal endpoint input is outside its graph"
          let failure : Option Exception ← try
            discard <| environment.checkArgument source other
            pure none
          catch error => pure (some error)
          let some failure := failure
            | throwError "the native view accepted a different equal endpoint occurrence"
          unless (← failure.toMessageData.toString).startsWith
              "the runtime argument does not retain its specified source value" do throw failure
          let some declaredEndpointSource := selectedEndpoint? endpointSource
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
          let totalValue ← session.kernel.run transaction context bound totalTerm
          let totalSource ← markValue session.kernel.marks totalValue totalTerm
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
          -- The actual native action must supply its own selected input projections.
          -- None of these expected fields is evaluated or staged before that action.
          let outputTerm := mkApp objectAction totalSource
          let output ← session.kernel.run transaction context bound outputTerm
          let markedOutput ← markValue session.kernel.marks output outputTerm
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
              (← projectTerm markedOutput field)
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

end CasRuntime.SelectedEndpointTests
