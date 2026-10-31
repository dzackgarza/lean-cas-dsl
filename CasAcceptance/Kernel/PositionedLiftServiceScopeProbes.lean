/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Newly reconstructed engineering controls. These are not recovered historical
3032352 source or a claim that its old differential counts have been rerun.
The reference functions below are the published-87 pure implementations.
No mathematical assertion, registry entry, backend, or external process is added. -/

open Lean Meta Elab Term
open CasCatalogue CasCatalogue.Realize

meta section

private def referenceValidate (scope : ComputationalData.InterfaceScope)
    (data : Json) : Except String Unit := do
  unless scope.data.json == data do
    throw "a positioned computational interface changed its complete packet"
  scope.data.validate
  let mut paths : Array DataOwnership.Path := #[]
  for binding in scope.bindings do
    if paths.contains binding.path then
      throw "one computational position has two independently selected interfaces"
    paths := paths.push binding.path
    let actual ← scope.data.project binding.path
    unless actual == binding.fragment do
      throw "a positioned computational interface changed its packet or exact suppliers"

private def referenceAssemble (data : DataOwnership.Data)
    (children : Array (DataOwnership.Path × ComputationalData.InterfaceScope)) :
    Except String ComputationalData.InterfaceScope := do
  for (path, child) in children do
    referenceValidate child child.data.json
    let selected ← data.project path
    unless selected == child.data do
      throw "a positioned child scope changed its complete packet or exact suppliers"
  let bindings := children.foldl (fun bindings (path, child) =>
    bindings ++ child.bindings.map (fun binding => { binding with path := path ++ binding.path })) #[]
  let scope := { data, bindings : ComputationalData.InterfaceScope }
  referenceValidate scope data.json
  return scope

private def sameResult (left right : Except String Unit) : Bool :=
  match left, right with
  | .ok (), .ok () => true
  | .error left, .error right => left == right
  | _, _ => false

private def sameRole (left right : ComputationalData.InterfaceRole) : Bool :=
  match left, right with
  | .value, .value => true
  | .object left, .object right | .map left, .map right =>
    left.expression.syntacticEq right.expression && left.bundle == right.bundle
  | _, _ => false

private def sameScope (left right : ComputationalData.InterfaceScope) : Bool :=
  left.data == right.data && left.bindings.size == right.bindings.size &&
    (left.bindings.zip right.bindings).all (fun (left, right) =>
      left.path == right.path && left.fragment == right.fragment && left.formal == right.formal &&
        left.expectedType == right.expectedType && sameRole left.role right.role &&
        left.representation == right.representation)

private def sameAssembly (left right : Except String ComputationalData.InterfaceScope) : Bool :=
  match left, right with
  | .ok left, .ok right => sameScope left right
  | .error left, .error right => left == right
  | _, _ => false

private def envelope (tag : String) (args : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]

run_elab do
  let scalar : DataOwnership.Data := { json := toJson (6 : Nat) }
  let other : DataOwnership.Data := { json := toJson (7 : Nat) }
  let opaquePacket := envelope "opaqueData" #[toJson "one spelling"]
  let first := DataOwnership.Data.capture opaquePacket ("first fixture", 1)
  let second := DataOwnership.Data.capture opaquePacket ("second fixture", 2)
  let absent : DataOwnership.Data := { json := opaquePacket }
  let duplicate := { first with ownership := first.ownership ++ first.ownership }
  let array := DataOwnership.Data.array #[scalar, first]
  let fragments := #[scalar, other, first, second, absent, duplicate, array,
    DataOwnership.Data.array #[second, other]]
  let formal := mkNatLit 6
  let type := Lean.mkConst ``Nat
  let mut scopes : Array ComputationalData.InterfaceScope := #[]
  for data in fragments do
    let binding : ComputationalData.InterfaceBinding := {
      path := #[], fragment := data, formal, expectedType := type, role := .value }
    scopes := scopes ++ #[{ data }, { data, bindings := #[binding] },
      { data, bindings := #[binding, binding] },
      { data, bindings := #[{ binding with fragment := scalar }] },
      { data, bindings := #[{ binding with path := #[.index 0], fragment := scalar }] },
      { data, bindings := #[{ binding with path := #[.field "missing"], fragment := scalar }] }]
  let mut validationCount : Nat := 0
  for scope in scopes do
    for data in fragments do
      unless sameResult (referenceValidate scope data.json) (scope.validate data.json) do
        throwError "the fused validator changed acceptance or its first error"
      validationCount := validationCount + 1
  let paths : Array DataOwnership.Path := #[#[], #[.index 0], #[.index 1],
    #[.field "args"], #[.field "missing"], #[.index 0, .field "args"]]
  let children := (#[0, 1, 2, 5, 12, 13, 14, 18, 19, 24, 30, 36] : Array Nat).map
    fun index => scopes[index]?.getD { data := scalar }
  let mut assemblyCount : Nat := 0
  for data in fragments do
    unless sameAssembly (referenceAssemble data #[])
        (ComputationalData.InterfaceScope.assemble data #[]) do
      throwError "empty scope assembly changed acceptance or its first error"
    assemblyCount := assemblyCount + 1
    for (firstChild, firstIndex) in children.zipIdx do
      for (secondChild, secondIndex) in children.zipIdx do
        let selected := #[(paths[firstIndex % paths.size]!, firstChild),
          (paths[secondIndex % paths.size]!, secondChild)]
        unless sameAssembly (referenceAssemble data selected)
            (ComputationalData.InterfaceScope.assemble data selected) do
          throwError "fused scope assembly changed a binding, supplier, acceptance or first error"
        assemblyCount := assemblyCount + 1
  logInfo m!"PASS: new pure differential matrix ({validationCount} validation, {assemblyCount} assembly cases)"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted Sets category is absent"
  let source ← elabTermAndSynthesize (← `(Fin 2)) none
  let context ← CategoryContext.ofNamed sets source
  let identity ← identityAtContext context source
  let type ← CategoryContext.hom context source source
  let descriptor : DataOwnership.Data := { json := envelope "obj.sets.fin" #[toJson (2 : Nat)] }
  let body : DataOwnership.Data := { json := envelope "identity" #[descriptor.json, descriptor.json] }
  let scalar : DataOwnership.Data := { json := toJson (6 : Nat) }
  let valueBinding : ComputationalData.InterfaceBinding := {
    path := #[], fragment := body, formal := identity, expectedType := type, role := .value }
  let valueScope : ComputationalData.InterfaceScope := { data := body, bindings := #[valueBinding] }
  let .ok () ← LiftedSubobjectData.checkReplyScopeContext context true body.json (some valueScope)
    | throwError "a value declared at the complete Hom was rejected as a callable input"
  let scalarScope ← bindValidationScope { data := scalar } (mkNatLit 6) .value
  let .error _ ← LiftedSubobjectData.checkReplyScopeContext context true scalar.json (some scalarScope)
    | throwError "an unrelated scalar acquired a callable role"
  let objectScope ← bindValidationScope { data := descriptor } source (.object context)
  let .error _ ← LiftedSubobjectData.checkReplyScopeContext context true descriptor.json (some objectScope)
    | throwError "an object reference acquired a whole-map role"
  let parent : ComputationalData.InterfaceBinding := {
    valueBinding with role := .map context }
  let .ok () ← ComputationalData.checkScopedCategorySlots (some parent)
      #[(true, body.json, some valueScope)]
    | throwError "the ordinary callable-field validator rejected a declared Hom value"
  let moved := { context with
    expression := .construct ⟨"scope-control-moved-context"⟩ #[.category context.expression] }
  let movedScope : ComputationalData.InterfaceScope := {
    data := body, bindings := #[{ valueBinding with role := .map moved }] }
  let .error _ ← LiftedSubobjectData.checkReplyScopeContext context true body.json (some movedScope)
    | throwError "an equal-Hom reference changed its complete selected category expression"
  logInfo "PASS: declared Hom values, scalar/object rejection and complete category identity"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted Sets category is absent"
  let formal ← elabTermAndSynthesize (← `(Fin 2)) none
  let context ← CategoryContext.ofNamed sets formal
  let data : DataOwnership.Data := { json := envelope "obj.sets.fin" #[toJson (2 : Nat)] }
  let wire : Wire := {
    form := .diagrams sets, payload := (← scopedPayload formal data), categoryContext := some context }
  let harness ← Harness.empty
  let trace ← Trace.new
  let scope : ServiceScope := {
    harness, trace, references := #[wire], known := #[], operands := (← IO.mkRef #[]), backend := "fixture" }
  let template ← serviceResultTemplate scope (Json.arr #[Backend.resultRef 0, Backend.resultRef 0])
  let selected ← templateValidationScope template (mapView := .logical)
  unless selected.data == DataOwnership.Data.array #[data, data] && selected.bindings.size == 2 do
    throwError "repeated exact references lost their separate declared positions"
  let .array #[.logical (.retained (.wire .parameter first)),
      .logical (.retained (.wire .parameter second))] := template
    | throwError "service assembly discarded the original typed reference children"
  unless sameCompleteWireContext first wire && sameCompleteWireContext second wire do
    throwError "service assembly replaced an original reference occurrence"
  let fresh ← serviceResultTemplate scope data.json
  let freshScope ← templateValidationScope fresh
  unless freshScope.bindings.isEmpty do
    throwError "fresh untrusted reply bytes acquired a requested result binding"
  let request : ComputationalData.InterfaceScope := {
    data := { json := envelope "monoLiftInput" #[toJson "fixture", Json.null,
      data.json, data.json, Json.arr #[]] } }
  let .ok appended := LiftedSubobjectData.appendSelectionReplyScope request freshScope
    | throwError "a neutral reply could not fill its next declared output position"
  unless appended.bindings.isEmpty do
    throwError "appending a fresh reply installed an unvalidated result root"
  logInfo "PASS: exact service reference templates and neutral fresh reply roots"

run_elab do
  let source ← elabTermAndSynthesize (← `(Fin 2)) none
  let other ← elabTermAndSynthesize (← `(Fin 3)) none
  let first := Node.object ⟨"obj.sets.fin"⟩ #[mkNatLit 2]
  let second := Node.object ⟨"obj.sets.fin"⟩ #[mkNatLit 3]
  let original ← Trace.new
  let selected ← Trace.new
  Trace.record (some original) source first
  Trace.record (some selected) source first
  Trace.record (some selected) other second
  let originalBefore := (← original.get).toArray
  let selectedBefore := (← selected.get).toArray
  let merged ← Trace.merge original selected
  unless (← merged.get).size == 2 && (← original.get).toArray == originalBefore &&
      (← selected.get).toArray == selectedBefore do
    throwError "local service trace union changed an original trace or omitted an exact entry"
  let conflicting ← Trace.new
  Trace.record (some conflicting) source second
  let rejected ← try
    discard <| Trace.merge original conflicting
    pure false
  catch _ => pure true
  unless rejected && (← original.get).toArray == originalBefore do
    throwError "local trace union overwrote a conflicting exact producer key"
  logInfo "PASS: conflict-checked local trace union preserves both original traces"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted Sets category is absent"
  let source ← elabTermAndSynthesize (← `(Fin 2)) none
  let context ← CategoryContext.ofNamed sets source
  let formal ← identityAtContext context source
  let type ← CategoryContext.hom context source source
  let oldData : DataOwnership.Data := { json := envelope "obj.sets.fin" #[toJson (2 : Nat)] }
  let newData ← scopedNode "finiteData" #[oldData,
    { json := Json.arr #[toJson (0 : Nat), toJson (1 : Nat)] }]
  let endpoint := fun (data : DataOwnership.Data) => do
    return ({
      form := Form.diagrams sets, payload := (← scopedPayload source data),
      categoryContext := some context } : Wire)
  let oldEndpoint ← endpoint oldData
  let newEndpoint ← endpoint newData
  let oldBody ← scopedNode "identity" #[oldData, oldData]
  let newBody ← scopedNode "identity" #[newData, newData]
  let oldPacket ← scopedNode "typedMap" #[oldData, oldData, oldBody]
  let newPacket ← scopedNode "typedMap" #[newData, newData, newBody]
  let declared := fun (data : DataOwnership.Data) => do
    let wire : Wire := {
      form := .canonicalMorphism sets,
      payload := (← recipePayload formal data) }
    retainIntrinsicResultAssembly wire (.value type) (.literal data)
  let original ← declared oldPacket
  let actual ← declared newPacket
  let read := fun (wire : Wire) (_ : CategoryContext) => do
    if sameCompleteWireContext wire original then return (oldEndpoint, oldEndpoint)
    if sameCompleteWireContext wire actual then return (newEndpoint, newEndpoint)
    throwError "the declared Hom adapter requested an unrelated endpoint producer"
  let framed ← captureCompleteCallableWith read original context
  let adapter := framed.morphismFraming.map (·.input) |>.getD framed
  let some assembly ← currentIntrinsicAssembly? adapter
    | throwError "the declared Hom adapter lost its intrinsic owner"
  let .ctor "valueData" #[.wire .parameter child] := assembly.template
    | throwError "the declared Hom adapter changed its original value-child boundary"
  unless sameCompleteWireContext child original do
    throwError "the declared Hom adapter replaced its original typed value"
  let observed ← IO.mkRef (0 : Nat)
  let observe := fun (role : ActionDataRole) (wire : Wire) => do
    unless role == .parameter && sameCompleteWireContext wire original do
      throwError "the adapter independently advanced an old endpoint instead of its original value"
    observed.modify (· + 1)
    return actual
  let harness ← Harness.empty
  let result ← observeCurrentIntrinsicAssemblyWith observe read harness adapter
  let some (domain, target) ← retainedCallableEndpoints? result context
    | throwError "the observed value adapter lost its complete callable endpoint receipt"
  unless (← observed.get) == 1 && sameCompleteWireContext domain newEndpoint &&
      sameCompleteWireContext target newEndpoint do
    throwError "the declared Hom adapter did not follow its exact observed value's typedMap fields"
  let scope ← wireValidationScope .map result (some context) (mapView := .logical)
  let .ok () ← ComputationalData.validateEndpointPort formal newData.json newData.json
      result.json (scope := some scope)
    | throwError "the original declared Hom value was rejected inside its refreshed complete map envelope"
  logInfo "PASS: declared Hom adapter refreshes from its original value child's complete map"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted Sets category is absent"
  let domain ← ServiceRequest.closedElementDomain
  let natPoint ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun (_ : Fin 1) => (6 : Nat)))) none
  let intPoint ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun (_ : Fin 1) => (6 : Int)))) none
  let context ← CategoryContext.ofNamed sets domain
  let data : DataOwnership.Data := { json := toJson (6 : Nat) }
  let domainData : DataOwnership.Data := { json := envelope "obj.sets.fin" #[toJson (1 : Nat)] }
  let targetData : DataOwnership.Data := { json := toJson "retained Nat endpoint fixture" }
  let wire : Wire := {
    form := .canonicalMorphism sets, payload := (← scopedPayload natPoint data),
    categoryContext := some context
    pointDataInterface := some {
      domain, target := mkConst ``Nat, domainData, targetData } }
  let scope : ServiceScope := {
    harness := (← Harness.empty), trace := (← Trace.new), references := #[wire], known := #[],
    operands := (← IO.mkRef #[]), backend := "fixture" }
  let prepared : ServiceRequest.Prepared := {
    requestValue := natPoint, request := data.json, result := natPoint,
    resultForm := .canonicalMorphism sets, dependencies := #[],
    resultContext := some context, callableResult := true, pointResult := true,
    complete := fun _ => pure (.ok none) }
  validateServiceResultTemplate scope prepared (Backend.resultRef 0)
  let rejected ← try
    validateServiceResultTemplate scope { prepared with result := intPoint } (Backend.resultRef 0)
    pure false
  catch error => pure (Exception.stratum? error == some .malformed)
  unless rejected do
    throwError "a native Nat point reference became an Int point after equal scalar bytes were substituted"
  logInfo "PASS: native point references retain their original complete Hom before substitution"

run_elab do
  let state ← registryState
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the accepted Sets category is absent"
  let source ← elabTermAndSynthesize (← `(Fin 2)) none
  let other ← elabTermAndSynthesize (← `(Fin 3)) none
  let context ← CategoryContext.ofNamed sets source
  let formal ← identityAtContext context source
  let wrong ← identityAtContext context other
  let type ← CategoryContext.hom context source source
  let wrongType ← CategoryContext.hom context other other
  let graph : DataOwnership.Data := {
    json := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (0 : Nat)],
      Json.arr #[toJson (1 : Nat), toJson (1 : Nat)]] }
  let port : StructuredResult.DataPort := {
    index := 0, constructorBinder := 1, formalField := formal, expectedType := type,
    dependencies := #[0], domainBinder := some 0, codomainBinder := some 0 }
  -- This private control selects only the data-port dependency role. It is not
  -- a registered construction or a witness of a universal property.
  let plan : StructuredResult.DataPlan := {
    colimit := false, constructor := Name.anonymous,
    binders := #[{ index := 0, formalValue := some source, port := none }], ports := #[port] }
  let scope : ComputationalData.InterfaceScope := {
    data := graph, bindings := #[{
      path := #[], fragment := graph, formal := wrong, expectedType := wrongType,
      role := .map context }] }
  let descriptor := envelope "obj.sets.fin" #[toJson (2 : Nat)]
  let .error _ ← ComputationalData.validatePlannedPort plan port #[] graph.json
      (fun _ => some descriptor) ComputationalData.endpointKeys (scope := some scope)
    | throwError "a raw graph reference changed its complete Hom while fitting the new inventory"
  logInfo "PASS: raw construction graphs retain their positioned full Hom before inventory checks"
