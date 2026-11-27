module

import CasRuntime.FixedInput
public meta import Lean.Elab.Command
meta import CasRuntime.FixedInput

open Lean Meta CasCompiler CasRuntime




run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, left) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, right) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless left.value != right.value do
    throwError "the route control merged equal-valued input occurrences"
  let stage (graph : ValueGraph) (context : OpenContext)
      (parameters : Array (Option ValueBinding)) (term : Expr) (payload : ValuePayload) :
      MetaM (ValueGraph × ValueBinding) := do
    let role ← SourceLayout.ofTerm (← context.close term)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role, parameters } payload
  let prepare (graph : ValueGraph) (context : OpenContext) (callable : ValueBinding)
      (arguments : Array Expr) (values : Array (Option ValueBinding))
      (parameters : Array RuntimeParameter) : MetaM PreparedRequest := do
    unless arguments.size == values.size do
      throwError "the route control omitted a formal argument slot"
    let mut actual : Array RuntimeArgument := #[]
    for value in values, index in [:values.size] do
      if let some value := value then
        let .ok argument := RuntimeArgument.ofValue graph index value
          | throwError "the route control argument is outside its actual graph"
        actual := actual.push argument
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let request ← PreparedRequest.forApplication owners.identities program occurrence context
      callable (← arguments.mapM context.close) actual parameters (some graph)
    discard <| request.admitInputs graph
    return request
  let checkFixed (label : String) (request : PreparedRequest) (graph : ValueGraph)
      (expected : ValueBinding) : MetaM Unit := do
    let some fixed ← request.fixedInputFor graph request.source
      | throwError m!"{label}: the fixed input route is absent"
    unless fixed.parent.value == expected.value && fixed.path.isEmpty do
      throwError m!"{label}: the route selected a different actual input"
    let some stored ← fixed.storedValue? graph
      | throwError m!"{label}: an existing fixed input was treated as a lazy demand"
    let required ← fixed.storedValue graph
    unless stored.value == expected.value && required.value == expected.value do
      throwError m!"{label}: stored traversal changed the selected input occurrence"
  withLocalDeclD `n (mkConst ``Nat) fun original => do
    let originalBinding : LocalBinding := {
      id := ⟨"fixed-input-route", 0⟩, role := .parameter, expression := original }
    let context ← ContextTelescope.capture #[originalBinding]
    let .ok originalParameter := RuntimeParameter.ofValue graph originalBinding.id left
      | throwError "the original route context value is absent"
    let parameters := #[originalParameter]
    let values := #[some left]


    let constant ← Elab.Term.elabTermAndSynthesize
      (← `(fun (x _y : Nat) => x)) none
    let (graph, constant) ← stage graph context values constant (.closure program #[])
    let first ← prepare graph context constant #[mkNatLit 7] #[some left] parameters
    let (graph, residual) ← liftM (m := IO) <| graph.stage owners.identities first.origin
      (.closure program #[])
    let some originalApplication := first.origin.application
      | throwError "the first partial application lost its original source table"

    let supplied : Std.HashMap BindingId ValueBinding := {}
    withBindingContext graph context (supplied.insert originalBinding.id left) residual
        fun context bound => do
      let values := context.telescope.entries.map fun entry => bound[entry.id]?
      let parameters ← (context.bindings.filterMap fun binding =>
        (bound[binding.id]?).map fun value => (binding.id, value)).mapM fun (id, value) =>
          IO.ofExcept <| (RuntimeParameter.ofValue graph id value).mapError IO.userError


      let partialTerm ← residual.role.source.inContext context
      let callableType ← inferType partialTerm
      let (graph, typeValue) ← stage graph context values callableType (.portable "null".toUTF8)
      let identityLevel ← getLevel callableType
      let (graph, identity) ← stage graph context values (mkConst ``id [identityLevel])
        (.closure program #[])
      let forwarded ← prepare graph context identity #[callableType, partialTerm]
        #[some typeValue, some residual] parameters
      checkFixed "identity forwarding" forwarded graph residual
      let (graph, wrapped) ← liftM (m := IO) <|
        graph.bindApplication owners.identities forwarded.origin residual #[]
      unless wrapped.value == residual.value &&
          wrapped.applications.size == residual.applications.size + 1 do
        throwError "identity forwarding replaced the node or lost its new consuming association"
      unless wrapped.role.kind == .data && wrapped.nativeRole.kind == .function &&
          wrapped.admittedInterface?.isSome &&
          wrapped.nativeInterface.exactlyMatches residual &&
          wrapped.role.source.context.exactlyMatches forwarded.source.source.context do
        throwError "identity forwarding lost its consuming role or complete admitted callable"
      let .ok relabeled := residual.withRole forwarded.source #[]
          (some forwarded.environment.values)
        | throwError "the role-only interface control lost its complete original source table"
      unless relabeled.admittedInterface?.isNone && relabeled.nativeRole.kind == .data do
        throwError "an unchecked consuming role manufactured a native callable interface"
      let .ok unchanged := wrapped.withRole wrapped.role #[] wrapped.sourceParameters?
        | throwError "an unchanged native interface view lost its complete source table"
      unless unchanged.admittedInterface?.isSome &&
          unchanged.nativeInterface.exactlyMatches wrapped.nativeInterface do
        throwError "an unchanged native interface view lost its admitted relation"
      let .ok unrelated := wrapped.withRole wrapped.role #[right] wrapped.sourceParameters?
        | throwError "the changed dependency control lost its complete source table"
      unless unrelated.admittedInterface?.isNone do
        throwError "an unchecked dependency addition retained an exact native interface view"
      let (otherGraph, otherResidual) ← liftM (m := IO) <| graph.stage owners.identities
        first.origin (.closure program #[])
      let wrongForwarded ← liftM (m := IO) <| try
          discard <| otherGraph.bindApplication owners.identities forwarded.origin otherResidual #[]
          pure true
        catch error =>
          if error.toString == "the application result changed its exact admitted interface input" then
            pure false
          else throw error
      if wrongForwarded then
        throwError "the admitted callable interface accepted another equal-source occurrence"


      let threeStage ← Elab.Term.elabTermAndSynthesize
        (← `(fun (_h : True) (x : Nat) (_k : True) (_y _z : Nat) => x)) none
      let (graph, threeStage) ← stage graph context values threeStage (.closure program #[])
      let proofFirst ← prepare graph context threeStage #[mkConst ``True.intro, mkNatLit 7]
        #[none, some left] parameters
      let (graph, proofPartial) ← liftM (m := IO) <| graph.stage owners.identities proofFirst.origin
        (.closure program #[])
      let proofSecond ← prepare graph context proofPartial #[mkConst ``True.intro, mkNatLit 7]
        #[none, some right] parameters
      let (graph, proofResidual) ← liftM (m := IO) <| graph.stage owners.identities proofSecond.origin
        (.closure program #[])
      for request in #[proofFirst, proofSecond] do
        let some application := request.origin.application
          | throwError "a proof-bearing route stage lost its original argument table"
        unless application.arguments.size == 2 &&
            (application.arguments[0]?.bind id).isNone &&
            application.layout.arguments.map (·.wireIndex) == #[none, some 0] do
          throwError "proof erasure displaced a route's original formal positions"


      let paired ← Elab.Term.elabTermAndSynthesize
        (← `(fun (x : Nat) => ((fun (_y : Nat) => x), (0 : Nat)))) none
      let (graph, paired) ← stage graph context values paired (.closure program #[])
      let pairRequest ← prepare graph context paired #[mkNatLit 7] #[some left] parameters
      let some record := pairRequest.record
        | throwError "the native callable pair has no prepared record"
      let #[functionField, scalarField] := record.fields
        | throwError "the native callable pair changed its source fields"
      let functionOrigin ← pairRequest.originFor functionField.layout
      let scalarOrigin ← pairRequest.originFor scalarField.layout
      let (graph, functionValue) ← liftM (m := IO) <| graph.stage owners.identities
        functionOrigin (.closure program #[])
      let (graph, scalarValue) ← liftM (m := IO) <| graph.stage owners.identities
        scalarOrigin (.portable "0".toUTF8)
      let (graph, pairValue) ← liftM (m := IO) <| graph.stage owners.identities pairRequest.origin
        (.product #[functionValue, scalarValue])


      withBindingContext graph context bound pairValue fun recordContext recordBound => do
        let recordValues := recordContext.telescope.entries.map fun entry => recordBound[entry.id]?
        let recordParameters ← (recordContext.bindings.filterMap fun binding =>
          (recordBound[binding.id]?).map fun value => (binding.id, value)).mapM fun (id, value) =>
            IO.ofExcept <| (RuntimeParameter.ofValue graph id value).mapError IO.userError
        let pairTerm ← pairValue.role.source.inContext recordContext
        let pairType ← inferType pairTerm
        let (recordGraph, pairTypeValue) ← stage graph recordContext recordValues pairType
          (.portable "null".toUTF8)
        let (recordGraph, recordIdentity) ← stage recordGraph recordContext recordValues
          (mkConst ``id [← getLevel pairType]) (.closure program #[])
        let recordForward ← prepare recordGraph recordContext recordIdentity #[pairType, pairTerm]
          #[some pairTypeValue, some pairValue] recordParameters
        checkFixed "identity record forwarding" recordForward recordGraph pairValue
        let (recordGraph, wrappedRecord) ← liftM (m := IO) <|
          recordGraph.bindApplication owners.identities recordForward.origin pairValue #[]
        unless wrappedRecord.role.kind == .data && wrappedRecord.nativeRole.kind == .record &&
            wrappedRecord.nativeInterface.exactlyMatches pairValue &&
            wrappedRecord.role.source.context.exactlyMatches recordForward.source.source.context &&
            wrappedRecord.applications.size == pairValue.applications.size + 1 do
          throwError "identity forwarding erased the native record or its full consuming view"
        let projectedOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
        let fieldRequest ← PreparedRequest.forProjection owners.identities program projectedOccurrence
          recordContext recordGraph wrappedRecord 0 recordParameters
        let .ok originalField := recordGraph.project wrappedRecord 0
          | throwError "the forwarded native record lost its exact stored callable field"
        unless retainsReference functionValue originalField do
          throwError "the forwarded native record selected another actual field"
        let (recordGraph, forwardedField) ← recordGraph.bindProjection owners.identities
          fieldRequest.origin originalField #[]
        let later ← prepare recordGraph recordContext forwardedField #[mkNatLit 7]
          #[some right] recordParameters
        checkFixed "identity record field continuation" later recordGraph left


      withLocalDeclD `n (mkConst ``Nat) fun shadow => do
        let shadowBinding : LocalBinding := {
          id := ⟨"fixed-input-route", 1⟩, role := .parameter, expression := shadow }
        let current ← ContextTelescope.capture (context.bindings.push shadowBinding)
        let .ok shadowParameter := RuntimeParameter.ofValue graph shadowBinding.id right
          | throwError "the later route context value is absent"
        let currentParameters := parameters.push shadowParameter
        let direct ← prepare graph current residual #[mkNatLit 7] #[some right] currentParameters
        checkFixed "two partial applications" direct graph left
        let wrappedRequest ← try
            prepare graph current wrapped #[mkNatLit 7] #[some right] currentParameters
          catch failure => throwError
            "identity-wrapped partial callable preparation: {failure.toMessageData}"
        checkFixed "identity-wrapped partial callable" wrappedRequest graph left
        let finalRequest ← prepare graph current proofResidual #[mkNatLit 7] #[some right]
          currentParameters
        checkFixed "three stages with proof slots" finalRequest graph left
        let projectionOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
        let projection ← PreparedRequest.forProjection owners.identities program projectionOccurrence
          current graph pairValue 0 currentParameters
        let refreshedOrigin ← projection.originFor projection.source (some graph)
        let some preparedProjection := projection.origin.application
          | throwError "the projected callable lost its original application"
        let some refreshedProjection := refreshedOrigin.application
          | throwError "refreshing the projected callable lost its original application"
        let some producingApplication := pairRequest.origin.application
          | throwError "the native callable pair lost its original application"
        unless refreshedProjection.path == #[``Prod.fst] &&
            refreshedProjection.path == preparedProjection.path &&
            refreshedProjection.dependencies == preparedProjection.dependencies &&
            refreshedProjection.contextDependencies == preparedProjection.contextDependencies &&
            refreshedOrigin.accessPath == projection.origin.accessPath do
          throwError "refreshing the projected callable changed its original dependency paths"
        let producingSource := producingApplication.layout.result.source
        let refreshedSource := refreshedProjection.layout.result.source
        unless projection.source.kind == .function &&
            refreshedProjection.layout.result.kind == .record &&
            refreshedSource.context.exactlyMatches producingSource.context &&
            refreshedSource.expression.equal producingSource.expression &&
            refreshedSource.type.equal producingSource.type &&
            refreshedSource.universeParams == producingSource.universeParams &&
            refreshedSource.nativeDeclarations.exactlyMatches producingSource.nativeDeclarations do
          throwError "refreshing the projected callable replaced its complete original root"
        for (retainedInputs, originalInputs) in #[
            (refreshedProjection.parameters, producingApplication.parameters),
            (refreshedProjection.arguments, producingApplication.arguments),
            (refreshedOrigin.parameters, projection.origin.parameters)] do
          unless retainedInputs.size == originalInputs.size &&
              (retainedInputs.zip originalInputs).all (fun (retained, original) =>
                match retained, original with
                | none, none => true
                | some retained, some original => retained.exactlyMatches original
                | _, _ => false) do
            throwError "refreshing the projected callable changed an original input table"
        let .ok stored := graph.project pairValue 0
          | throwError "the native callable pair lost its stored function"
        let (graph, projected) ←
          graph.bindProjection owners.identities projection.origin stored #[]
        let .ok (some projectedOrigin) := graph.applicationOrigin projected
          | throwError "the native projected callable lost its application origin"
        unless projectedOrigin.path == #[``Prod.fst] do
          throwError "the native projected callable lost its exact source path"
        let projectedRequest ← prepare graph current projected #[mkNatLit 7] #[some right]
          currentParameters
        checkFixed "native projected partial callable" projectedRequest graph left
        let (graph, refreshed) ←
          graph.bindProjection owners.identities refreshedOrigin stored #[]
        let refreshedRequest ← prepare graph current refreshed #[mkNatLit 7] #[some right]
          currentParameters
        checkFixed "refreshed native projected partial callable" refreshedRequest graph left
        let some currentApplication := direct.origin.application
          | throwError "the final application lost its current source table"
        let originalContext := originalApplication.layout.result.source.context.entries
        let currentContext := currentApplication.layout.result.source.context.entries
        let originalAuthored := originalContext.filter (·.role == .parameter)
        let currentAuthored := currentContext.filter (·.role == .parameter)
        let originalInputs := originalContext.filter (·.role == .result)
        let currentInputs := currentContext.filter (·.role == .result)
        unless originalApplication.parameters.size == originalContext.size &&
            currentApplication.parameters.size == currentContext.size &&
            originalAuthored.map (·.id) == #[originalBinding.id] &&
            currentAuthored.map (·.id) == #[originalBinding.id, shadowBinding.id] &&
            originalInputs.size == 1 && currentInputs.size == 2 &&
            originalContext.size == originalAuthored.size + originalInputs.size &&
            currentContext.size == currentAuthored.size + currentInputs.size &&
            (originalInputs ++ currentInputs).all
              (fun entry => entry.value.isNone && entry.originalSource.isSome) &&
            originalApplication.arguments.size == 1 && currentApplication.arguments.size == 1 &&
            (originalApplication.arguments[0]?.bind id).map (·.value) == some left.value &&
            (currentApplication.arguments[0]?.bind id).map (·.value) == some right.value do
          throwError "fixed-route composition changed an original context or argument plane"
        for original in originalContext do
          let some before := originalContext.findIdx? (·.id == original.id)
            | throwError "the original route lost its native parameter position"
          let some after := currentContext.findIdx? (·.id == original.id)
            | throwError "the later route dropped an original source binding"
          let some previous := originalApplication.parameters[before]?.bind id
            | throwError "the original route lost an actual parameter"
          let some retained := currentApplication.parameters[after]?.bind id
            | throwError "the later route lost an imported actual parameter"
          unless retainsReference previous retained && previous.value == left.value do
            throwError "the later route replaced an original equal-valued occurrence"
        for added in currentContext.filter
            (fun entry => !(originalContext.any (·.id == entry.id))) do
          let some index := currentContext.findIdx? (·.id == added.id)
            | throwError "the later route lost its own original binder"
          let some actual := currentApplication.parameters[index]?.bind id
            | throwError "the later route omitted its own actual parameter"
          unless retainsReference right actual do
            throwError "the later route reused the earlier equal-valued occurrence"
        for application in #[originalApplication, currentApplication] do
          application.layout.result.source.withOpen fun bindings _ => do
            let opened ← ContextTelescope.capture bindings
            let #[argument] := application.layout.arguments
              | throwError "the route changed its complete original formal argument table"
            let input ← argument.source.source.inContext opened
            let some binding := bindings.find? (·.expression.equal input)
              | throwError "the route's actual input lost its opaque source binder"
            let some originalSource := binding.originalSource
              | throwError "the route's actual input lost its native source"
            unless binding.role == .result && originalSource.equal (mkNatLit 7) &&
                (← inferType input).equal (mkConst ``Nat) do
              throwError "the route's original formal argument changed its typed source"


run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, left) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, right) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let source ← Elab.Term.elabTermAndSynthesize (← `(fun (x _y : Nat) => x)) none
  withLetDecl `pick (← inferType source) source fun pick => do
    let binding : LocalBinding := {
      id := ⟨"fixed-input-let", 0⟩, role := .definition, expression := pick }
    let context ← ContextTelescope.capture #[binding]
    let role ← SourceLayout.ofTerm (← context.close pick)
    let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role, parameters := #[none] } (.closure program #[])
    let .ok none := graph.applicationOrigin callable
      | throwError "the native let control already has an application origin"
    let .ok parameter := RuntimeParameter.ofValue graph binding.id callable
      | throwError "the native let callable is outside its graph"
    let .ok firstArgument := RuntimeArgument.ofValue graph 0 left
      | throwError "the native let's first actual argument is absent"
    let firstOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let first ← PreparedRequest.forApplication owners.identities program firstOccurrence context
      callable #[← context.close (mkNatLit 7)] #[firstArgument] #[parameter] (some graph)
    discard <| first.admitInputs graph
    let (graph, residual) ← liftM (m := IO) <| graph.stage owners.identities first.origin
      (.closure program #[])
    let .ok secondArgument := RuntimeArgument.ofValue graph 0 right
      | throwError "the native let's second actual argument is absent"
    let secondOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let second ← PreparedRequest.forApplication owners.identities program secondOccurrence context
      residual #[← context.close (mkNatLit 7)] #[secondArgument] #[parameter] (some graph)
    discard <| second.admitInputs graph
    let some fixed ← second.fixedInputFor graph second.source
      | throwError "the native let-bound callable lost its fixed input route"
    let selected ← fixed.storedValue graph
    unless fixed.parent.value == left.value && fixed.path.isEmpty &&
        selected.value == left.value && selected.value != right.value do
      throwError "the native let-bound callable selected a different equal-valued input"


run_cmd Lean.Elab.Command.liftTermElabM do
  let context ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← context.close (mkNatLit 7))
  let innerTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
  let outerTerm ← mkAppM ``Prod.mk #[innerTerm, mkNatLit 7]
  let innerRole ← SourceLayout.ofTerm (← context.close innerTerm)
  let outerRole ← SourceLayout.ofTerm (← context.close outerTerm)
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, other) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, selected) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, inner) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := innerRole, parameters := #[] } (.product #[other, selected])
  let (graph, original) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := outerRole, parameters := #[] } (.product #[inner, other])
  let firstOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let first ← PreparedRequest.forProjection owners.identities program firstOccurrence
    context graph original 0 #[]
  let .ok firstStored := graph.project original 0
    | throwError "the nested projection control lost its stored inner pair"
  let (graph, firstView) ←
    graph.bindProjection owners.identities first.origin firstStored #[other, selected]
  let secondOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let second ← PreparedRequest.forProjection owners.identities program secondOccurrence
    context graph firstView 1 #[]
  let .ok secondStored := graph.project firstView 1
    | throwError "the nested projection control lost its selected scalar"
  let (graph, secondView) ←
    graph.bindProjection owners.identities second.origin secondStored #[]
  let .ok (some basis) := graph.projectionBasis secondView original #[``Prod.fst, ``Prod.snd]
    | throwError "nested stored projections lost their original composed-path baseline"
  unless basis.value == selected.value && basis.associationIds == selected.associationIds &&
      basis.value != other.value do
    throwError "the composed projection baseline replaced its original selected scalar"
  let .ok none := graph.projectionBasis secondView original #[``Prod.fst, ``Prod.fst]
    | throwError "the composed projection baseline accepted a different native path"



run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, left) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, right) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless left.value != right.value do
    throwError "the captured input control merged equal-valued occurrences"
  let checkCaptured (label : String) (original : LocalBinding) : MetaM Unit := do
    let context ← ContextTelescope.capture #[original]
    let source ← withLocalDeclD `_y (mkConst ``Nat) fun ignored =>
      mkLambdaFVars #[ignored] original.expression
    let role ← SourceLayout.ofTerm (← context.close source)
    let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role, parameters := #[some left] } (.closure program #[left])
    let .ok none := graph.applicationOrigin callable
      | throwError m!"{label}: the captured callable already has an application history"
    let .ok originalParameter := RuntimeParameter.ofValue graph original.id left
      | throwError m!"{label}: the original captured parameter is absent"
    withLocalDeclD `x (mkConst ``Nat) fun shadow => do
      withLocalDeclD `f (← inferType source) fun retained => do
        let shadowBinding : LocalBinding := {
          id := ⟨original.id.session, 1⟩, role := .parameter, expression := shadow }
        let callableBinding : LocalBinding := {
          id := ⟨original.id.session, 2⟩, role := .parameter, expression := retained }
        let current ← ContextTelescope.capture #[original, shadowBinding, callableBinding]
        let .ok shadowParameter := RuntimeParameter.ofValue graph shadowBinding.id right
          | throwError m!"{label}: the shadowing parameter is absent"
        let .ok callableParameter := RuntimeParameter.ofValue graph callableBinding.id callable
          | throwError m!"{label}: the retained callable parameter is absent"
        let parameters := #[originalParameter, shadowParameter, callableParameter]
        let environment ← RuntimeEnvironment.capture program.worker current parameters (some graph)
        let .ok (some supplied) := environment.lookup callableBinding.id
          | throwError m!"{label}: the callable lost its current source binding"
        let .ok argument := RuntimeArgument.ofValue graph 0 right
          | throwError m!"{label}: the later formal argument is absent"
        let callOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
        let request ← PreparedRequest.forApplication owners.identities program callOccurrence
          current supplied #[← current.close (mkNatLit 7)] #[argument] parameters (some graph)
        discard <| request.admitInputs graph
        let some fixed ← request.fixedInputFor graph request.source
            (some fun _ => throwError m!"{label}: route discovery invoked a resolver")
          | throwError m!"{label}: the original captured input route is absent"
        let selected ← fixed.storedValue graph
        unless fixed.parent.value == left.value && fixed.path.isEmpty &&
            selected.value == left.value && selected.value != right.value &&
            selected.associationIds == left.associationIds do
          throwError m!"{label}: a later equal-valued occurrence replaced the captured input"
        unless fixed.source.context.entries.map (·.id) == #[original.id] &&
            fixed.parameters.map (fun value => value.map (·.value)) == #[some left.value] do
          throwError m!"{label}: the selected source escaped its original parameter plane"
        fixed.source.withOpen fun bindings expression => do
          let #[binding] := bindings
            | throwError m!"{label}: the captured source acquired later context entries"
          unless binding.id == original.id && expression == binding.expression do
            throwError m!"{label}: the retained source variable was unfolded or replaced"
  withLocalDeclD `x (mkConst ``Nat) fun original =>
    checkCaptured "captured parameter" {
      id := ⟨"fixed-input-captured", 0⟩, role := .parameter, expression := original }
  withLetDecl `x (mkConst ``Nat) (mkNatLit 7) fun original =>
    checkCaptured "retained let value" {
      id := ⟨"fixed-input-retained-let", 0⟩, role := .definition, expression := original }



run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, left) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, right) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless left.value != right.value do
    throwError "the lazy callable control merged equal-valued occurrences"
  let stage (graph : ValueGraph) (context : OpenContext)
      (parameters : Array (Option ValueBinding)) (term : Expr) :
      MetaM (ValueGraph × ValueBinding) := do
    let role ← SourceLayout.ofTerm (← context.close term)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role, parameters } (.closure program (parameters.filterMap id))
  let prepare (graph : ValueGraph) (context : OpenContext) (callable : ValueBinding)
      (arguments : Array Expr) (values : Array ValueBinding)
      (parameters : Array RuntimeParameter) : MetaM PreparedRequest := do
    unless arguments.size == values.size do
      throwError "the lazy callable control omitted an actual argument"
    let mut actual : Array RuntimeArgument := #[]
    for value in values, index in [:values.size] do
      let .ok argument := RuntimeArgument.ofValue graph index value
        | throwError "the lazy callable control argument is outside its graph"
      actual := actual.push argument
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let request ← PreparedRequest.forApplication owners.identities program occurrence context
      callable (← arguments.mapM context.close) actual parameters (some graph)
    discard <| request.admitInputs graph
    return request
  let selectField ← Elab.Term.elabTermAndSynthesize
    (← `(fun (p : (Nat → Nat) × Nat) => p.1)) none
  let (graph, selectField) ← stage graph empty #[] selectField
  withLocalDeclD `x (mkConst ``Nat) fun original => do
    let originalBinding : LocalBinding := {
      id := ⟨"fixed-input-lazy-callable", 0⟩, role := .parameter, expression := original }
    let context ← ContextTelescope.capture #[originalBinding]
    let .ok originalParameter := RuntimeParameter.ofValue graph originalBinding.id left
      | throwError "the lazy callable's original parameter is absent"
    let captured ← withLocalDeclD `_y (mkConst ``Nat) fun ignored =>
      mkLambdaFVars #[ignored] original
    let pairTerm ← mkAppM ``Prod.mk #[captured, mkNatLit 0]
    let (graph, plainPair) ← stage graph context #[some left] pairTerm
    let .ok none := graph.applicationOrigin plainPair
      | throwError "the lazy source pair already has an application origin"
    let producer ← Elab.Term.elabTermAndSynthesize
      (← `(fun (x : Nat) => ((fun (_y : Nat) => x), (0 : Nat)))) none
    let (graph, producer) ← stage graph context #[some left] producer
    let first ← prepare graph context producer #[mkNatLit 7] #[left] #[originalParameter]
    let (graph, producedPair) ← liftM (m := IO) <| graph.stage owners.identities first.origin
      (.closure program #[left])
    let .ok (some history) := graph.applicationOrigin producedPair
      | throwError "the lazy application pair lost its original producer"
    unless history.arguments.size == 1 &&
        (history.arguments[0]?.bind id).map (·.value) == some left.value do
      throwError "the lazy pair producer lost its original actual argument"
    for pair in #[plainPair, producedPair] do
      let .error _ := graph.project pair 0
        | throwError "the lazy callable control already has a stored field"
    let originalSource ← context.close original
    let some originalArgument := history.layout.arguments[0]?
      | throwError "the lazy pair producer lost its original source argument"
    for (label, pair, expectedSource, expectedParameters) in #[
        ("lazy original source", plainPair, originalSource, #[some left]),
        ("lazy application history", producedPair, originalArgument.source.source, history.parameters)] do
      let supplied : Std.HashMap BindingId ValueBinding := {}
      withBindingContext graph context (supplied.insert originalBinding.id left) pair
          fun context bound => do
        let parameters ← (context.bindings.filterMap fun binding =>
          (bound[binding.id]?).map fun value => (binding.id, value)).mapM fun (id, value) =>
            IO.ofExcept <| (RuntimeParameter.ofValue graph id value).mapError IO.userError
        let pairSource ← pair.role.source.inContext context
        let selection ← prepare graph context selectField #[pairSource] #[pair] parameters
        let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities selection.origin
          (.closure program #[pair])
        withBindingContext graph context bound callable fun context bound => do
          let parameters ← (context.bindings.filterMap fun binding =>
            (bound[binding.id]?).map fun value => (binding.id, value)).mapM fun (id, value) =>
              IO.ofExcept <| (RuntimeParameter.ofValue graph id value).mapError IO.userError
          let callableType ← inferType (← callable.role.source.inContext context)
          withLocalDeclD `x (mkConst ``Nat) fun shadow => do
            withLocalDeclD `f callableType fun retained => do
              let shadowBinding : LocalBinding := {
                id := ⟨"fixed-input-lazy-callable", 1⟩, role := .parameter, expression := shadow }
              let callableBinding : LocalBinding := {
                id := ⟨"fixed-input-lazy-callable", 2⟩, role := .parameter, expression := retained }
              let current ← ContextTelescope.capture (context.bindings ++ #[shadowBinding, callableBinding])
              let .ok shadowParameter := RuntimeParameter.ofValue graph shadowBinding.id right
                | throwError "the lazy callable's later shadowing parameter is absent"
              let .ok callableParameter := RuntimeParameter.ofValue graph callableBinding.id callable
                | throwError "the lazy callable's retained continuation is absent"
              let parameters := parameters ++ #[shadowParameter, callableParameter]
              let environment ← RuntimeEnvironment.capture program.worker current parameters (some graph)
              let .ok (some supplied) := environment.lookup callableBinding.id
                | throwError "the lazy callable lost its current source binding"
              let request ← prepare graph current supplied #[mkNatLit 7] #[right] parameters
              let some fixed ← request.fixedInputFor graph request.source
                  (some fun _ => throwError m!"{label}: route discovery invoked the lazy resolver")
                | throwError m!"{label}: the retained callable's fixed input route is absent"
              let selected ← fixed.storedValue graph
              unless fixed.parent.value == left.value && fixed.path.isEmpty &&
                  selected.value == left.value && selected.value != right.value &&
                  selected.associationIds == left.associationIds do
                throwError m!"{label}: the callable selected a different equal-valued input"
              unless fixed.source.context.exactlyMatches expectedSource.context &&
                  fixed.parameters.map (fun value => value.map (fun value =>
                    (value.value, value.associationIds))) ==
                  expectedParameters.map (fun value => value.map (fun value =>
                    (value.value, value.associationIds))) do
                throwError m!"{label}: the lazy callable lost its original source context"
              fixed.source.withOpen fun bindings expression => do
                let opened ← ContextTelescope.capture bindings
                unless expression.equal (← expectedSource.inContext opened) do
                  throwError m!"{label}: the lazy callable changed its exact original source argument"




run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, left) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, right) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless left.value != right.value do
    throwError "the source-body route control merged equal-valued occurrences"
  let stage (graph : ValueGraph) (context : OpenContext)
      (parameters : Array (Option ValueBinding)) (term : Expr) :
      MetaM (ValueGraph × ValueBinding) := do
    let role ← SourceLayout.ofTerm (← context.close term)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role, parameters } (.closure program (parameters.filterMap id))
  let prepare (graph : ValueGraph) (context : OpenContext) (callable : ValueBinding)
      (values : Array ValueBinding) (parameters : Array RuntimeParameter) :
      MetaM PreparedRequest := do
    let mut actual : Array RuntimeArgument := #[]
    for value in values, index in [:values.size] do
      let .ok argument := RuntimeArgument.ofValue graph index value
        | throwError "a source-body route argument is outside its graph"
      actual := actual.push argument
    let arguments ← values.mapM fun value => do
      context.close (← value.role.source.inContext context)
    let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
    let request ← PreparedRequest.forApplication owners.identities program occurrence context
      callable arguments actual parameters (some graph)
    discard <| request.admitInputs graph
    return request
  let checkFixed (label : String) (request : PreparedRequest) (graph : ValueGraph)
      (expected : ValueBinding) : MetaM Unit := do
    let some fixed ← request.fixedInputFor graph request.source
        (some fun _ => throwError m!"{label}: source-body routing invoked a resolver")
      | throwError m!"{label}: the saturated source-body input route is absent"
    let selected ← fixed.storedValue graph
    unless fixed.parent.value == expected.value && fixed.path.isEmpty &&
        selected.value == expected.value && selected.associationIds == expected.associationIds do
      throwError m!"{label}: the source-body route changed its exact selected input"
  let identityTerm ← Elab.Term.elabTermAndSynthesize (← `(fun (x : Nat) => x)) none
  let (graph, identity) ← stage graph empty #[] identityTerm
  let keep ← Elab.Term.elabTermAndSynthesize (← `(fun (_unknown keep : Nat) => keep)) none
  let (graph, keep) ← stage graph empty #[] keep
  let invoke ← Elab.Term.elabTermAndSynthesize
    (← `(fun (p : (Nat → Nat) × Nat) (y : Nat) => p.1 y)) none
  let (graph, invoke) ← stage graph empty #[] invoke
  let pairTerm ← mkAppM ``Prod.mk #[identityTerm, mkNatLit 0]
  let (graph, pair) ← stage graph empty #[] pairTerm
  let .error _ := graph.project pair 0
    | throwError "the saturated source-body control already has a stored callable field"
  let compose ← Elab.Term.elabTermAndSynthesize
    (← `(fun (f g : Nat → Nat) (x : Nat) => f (g x))) none
  let (graph, compose) ← stage graph empty #[] compose
  let ignore ← Elab.Term.elabTermAndSynthesize
    (← `(fun (f : Nat → Nat → Nat) (g : Nat → Nat) (x keep : Nat) => f (g x) keep)) none
  let (graph, ignore) ← stage graph empty #[] ignore
  let wrap ← Elab.Term.elabTermAndSynthesize
    (← `(fun (f : Nat → Nat) (x keep : Nat) => (f x, keep))) none
  let (graph, wrap) ← stage graph empty #[] wrap
  let pairIdentity ← Elab.Term.elabTermAndSynthesize
    (← `(fun (p : Nat × Nat) => p)) none
  let (graph, pairIdentity) ← stage graph empty #[] pairIdentity
  let projectCall ← Elab.Term.elabTermAndSynthesize
    (← `(fun (f : (Nat × Nat) → Nat × Nat) (p : Nat × Nat) => (f p).1)) none
  let (graph, projectCall) ← stage graph empty #[] projectCall
  let nativeProjection ← Elab.Term.elabTermAndSynthesize (← `(@Prod.fst Nat Nat)) none
  let (graph, nativeProjection) ← stage graph empty #[] nativeProjection
  let applyField ← Elab.Term.elabTermAndSynthesize
    (← `(fun (f : (Nat × Nat) → Nat) (p : Nat × Nat) => f p)) none
  let (graph, applyField) ← stage graph empty #[] applyField
  let dataPairTerm ← mkAppM ``Prod.mk #[mkNatLit 7, mkNatLit 7]
  let dataPairRole ← SourceLayout.ofTerm (← empty.close dataPairTerm)
  let (graph, dataPair) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := dataPairRole, parameters := #[] } (.product #[left, right])
  withLocalDeclD `g (← inferType identityTerm) fun unknown => do
    let binding : LocalBinding := {
      id := ⟨"fixed-input-source-body", 0⟩, role := .parameter, expression := unknown }
    let context ← ContextTelescope.capture #[binding]
    let (graph, unknown) ← stage graph context #[none] unknown
    let .ok parameter := RuntimeParameter.ofValue graph binding.id unknown
      | throwError "the abstract source-body callable is outside its graph"
    let parameters := #[parameter]
    let unresolved ← prepare graph context compose #[identity, unknown, left] parameters
    let .none ← unresolved.fixedInputFor graph unresolved.source
        (some fun _ => throwError "an unresolved symbolic argument invoked a resolver")
      | throwError "a selected unknown source-body computation acquired a fabricated input"
    let saturated ← prepare graph context invoke #[pair, right] parameters
    checkFixed "saturated lazy record call" saturated graph right
    let nested ← prepare graph context compose #[identity, identity, left] parameters
    checkFixed "nested f (g x)" nested graph left
    let ignored ← prepare graph context ignore #[keep, unknown, left, right] parameters
    checkFixed "ignored unknown source-body argument" ignored graph right

    let wrapped ← prepare graph context wrap #[identity, left, right] parameters
    let some record := wrapped.record
      | throwError "the source-body constructor lost its native record layout"
    let #[firstField, _] := record.fields
      | throwError "the source-body constructor changed its ordered fields"
    let some before ← wrapped.fixedInputFor graph firstField.layout
        (some fun _ => throwError "a constructor field route invoked a resolver")
      | throwError "the constructor field lost its pending source-body call"
    let beforeValue ← before.storedValue graph
    unless before.parent.value == left.value && before.path.isEmpty &&
        beforeValue.value == left.value && beforeValue.associationIds == left.associationIds do
      throwError "a consumed constructor path was repeated after the source-body call"

    let projected ← prepare graph context projectCall #[pairIdentity, dataPair] parameters
    let some after ← projected.fixedInputFor graph projected.source
        (some fun _ => throwError "a post-call field route invoked a resolver")
      | throwError "the source-body call lost its following native field selection"
    let afterValue ← after.storedValue graph
    unless after.parent.value == dataPair.value && after.path == #[``Prod.fst] &&
        afterValue.value == left.value && afterValue.associationIds == left.associationIds do
      throwError "the source-body route dropped or repeated its post-call field selection"
    let native ← prepare graph context applyField #[nativeProjection, dataPair] parameters
    let some fixed ← native.fixedInputFor graph native.source
        (some fun _ => throwError "a native projection callable invoked a resolver")
      | throwError "the source-body call lost its retained native projection function"
    let selected ← fixed.storedValue graph
    unless fixed.parent.value == dataPair.value && fixed.path == #[``Prod.fst] &&
        selected.value == left.value && selected.associationIds == left.associationIds do
      throwError "the native projection callable changed its exact parent or field"



run_cmd Lean.Elab.Command.liftTermElabM do
  let empty ← ContextTelescope.capture #[]
  let scalar ← SourceLayout.ofTerm (← empty.close (mkNatLit 7))
  let owners ← liftM (m := IO) OwnerRegistry.new
  let program ← liftM (m := BaseIO) (owners.identities.fresh .program)
  let occurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
  let (graph, left) ← liftM (m := IO) <|
    (ValueGraph.empty owners.identities).stage owners.identities
      { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  let (graph, right) ← liftM (m := IO) <| graph.stage owners.identities
    { program, occurrence, role := scalar, parameters := #[] } (.portable "7".toUTF8)
  unless left.value != right.value do
    throwError "the native captured-frame control merged equal-valued occurrences"
  withLocalDeclD `x (mkConst ``Nat) fun original => do
    let originalBinding : LocalBinding := {
      id := ⟨"fixed-input-native-frame", 0⟩, role := .parameter, expression := original }
    let context ← ContextTelescope.capture #[originalBinding]
    let source ← withLocalDeclD `_y (mkConst ``Nat) fun ignored =>
      mkLambdaFVars #[ignored] original
    let role ← SourceLayout.ofTerm (← context.close source)
    let (graph, callable) ← liftM (m := IO) <| graph.stage owners.identities
      { program, occurrence, role, parameters := #[some left] } (.closure program #[left])
    let .ok originalParameter := RuntimeParameter.ofValue graph originalBinding.id left
      | throwError "the native callable's original captured parameter is absent"
    withLocalDeclD `x (mkConst ``Nat) fun shadow => do
      let shadowBinding : LocalBinding := {
        id := ⟨"fixed-input-native-frame", 1⟩, role := .parameter, expression := shadow }
      let current ← ContextTelescope.capture #[originalBinding, shadowBinding]
      let .ok shadowParameter := RuntimeParameter.ofValue graph shadowBinding.id right
        | throwError "the native callable's later shadowing parameter is absent"
      let .ok argument := RuntimeArgument.ofValue graph 0 right
        | throwError "the native callable's later formal argument is absent"
      let callOccurrence ← liftM (m := BaseIO) (owners.identities.fresh .occurrence)
      let request ← PreparedRequest.forApplication owners.identities program callOccurrence
        current callable #[← current.close (mkNatLit 7)] #[argument]
        #[originalParameter, shadowParameter] (some graph)
      discard <| request.admitInputs graph
      let some fixed ← request.fixedInputFor graph request.source
          (some fun _ => throwError "native captured-frame discovery invoked a resolver")
        | throwError "the native callable lost its original captured input route"
      let selected ← fixed.storedValue graph
      unless fixed.parent.value == left.value && fixed.path.isEmpty &&
          selected.value == left.value && selected.associationIds == left.associationIds do
        throwError "the native callable changed its exact captured input"
      unless fixed.source.context.entries.map (·.id) == #[originalBinding.id] &&
          fixed.parameters.map (fun value => value.map (·.value)) == #[some left.value] do
        throwError "the native callable selected through the later consuming source frame"
