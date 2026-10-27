/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics

/-! Engineering controls for the existing named-refinement and method interfaces.
They use accepted catalogue rows, fixed interpretation and inert data suppliers.
No mathematical row, numerical answer, backend process or protected assertion
is added. The first control reaches the captured ordinary-method lifecycle;
the second changes a positioned parameter occurrence before representation use.
-/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Realize

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private def unavailable (action : TermElabM Unit) : TermElabM Bool := do
  try
    action
    return false
  catch error =>
    if Exception.stratum? error == some .unavailable then return true
    throw error

run_elab do
  let .ok parsed := Parser.runParserCategory (← getEnv) `cas_stmt
      "assert |Sym(3) in Groups| = 6"
    | throwError "the existing inherited-method control did not parse"
  let question ← interpret {} parsed
  let trace ← IO.mkRef question.trace
  let state ← registryState
  let empty ← Harness.empty
  let mut checked := false
  for (formal, operation) in question.trace.toArray do
    let .method id route receiver _ application := operation | continue
    let original ← realizeUnobserved empty trace "the original named method source" receiver
    let .object entry := original.form
      | throwError "the inherited-method control lost its named source"
    let (base, remaining) := state.transport entry route
    unless base.id != entry.id && remaining.size < route.size do
      throwError "the existing method no longer exercises a named refinement prefix"
    let harness ← Harness.ofManifest "." {
      backends := #[{ name := "named-refinement-engineering", command := "unused" }]
      registrations := #[{ operation := id.raw, input := base.id.raw,
        backend := "named-refinement-engineering" }] }
    unless harness.rejected.isEmpty && harness.admitted.size == 1 do
      throwError "the existing canonical-base registration was not admitted"
    let pending ← realizeUnobserved harness trace "the captured inherited method" formal
    let some captured ← retainedCapturedInvocation? pending
      | throwError "the ordinary method did not retain its pending invocation"
    let .routed selected := captured.interface
      | throwError "the ordinary method changed its retained invocation family"
    unless selected.canonical.prefixActions == route.zip application.routeApplications &&
        sameCompleteWireContext selected.original original do
      throwError "capturing the base boundary replaced the original selected route or receiver"
    let some presented := selected.presented
      | throwError "the captured method omitted its admitted canonical-base boundary"
    checkRoutedBoundaryPositions selected presented
    unless presented.routeOffset == route.size - remaining.size &&
        presented.prefixActions.map (·.1) == remaining &&
        presented.receiver.form.id == base.id.raw && !presented.materializeRoute do
      throwError "the canonical-base boundary lost its exact original action offset"
    let some origin ← currentNamedRefinementOrigin? presented.receiver
      | throwError "the canonical base has no retained representation producer"
    let some context := presented.receiver.categoryContext
      | throwError "the canonical base lost its complete target category"
    let some comparison := presented.receiver.endpointPresentation
      | throwError "the canonical base lost its accepted comparison"
    let (forward, backward) ← endpointPresentationMaps presented.receiver context comparison
    let some (image, actual) ← retainedCallableEndpoints? forward context
      | throwError "the comparison lost its original image and base occurrences"
    let some (reverseActual, reverseImage) ← retainedCallableEndpoints? backward context
      | throwError "the inverse comparison lost its endpoint occurrences"
    unless sameCompleteWireContext image reverseImage &&
        sameCompleteWireContext actual reverseActual &&
        actual.fragment == presented.receiver.fragment &&
        !forward.callableObserved && !backward.callableObserved &&
        !presented.receiver.objectObserved && !presented.receiver.actualData do
      throwError "forming a named representation replaced an endpoint or claimed execution"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq image.value presented.receiver.value) do
      throwError "the named representation replaced its interpreted structural image"
    for selector in #["refinement", "inverseRefinement"] do
      let arrow ← ObjectPresentation.field entry selector origin.parameters (some trace)
      let wire ← realizeUnobserved harness trace "the public refinement direction" arrow
      let .ok decoded := Backend.ObjectField.decode wire.json
        | throwError "the released object-field decoder rejected a refinement direction"
      unless decoded.object == entry.id.raw && decoded.field == selector do
        throwError "the public refinement selector changed its accepted owner or direction"
      if let .error message ← ComputationalData.validatePort arrow (← inferType arrow) wire.json then
        throwError "the public refinement field rejected its complete endpoints: {message}"
    let (chosen, registration) ← routedInvocationRegistrations harness trace pending selected
    let some registration := registration
      | throwError "the ordinary captured method could not reach its existing base registration"
    unless registration.input == base.id.raw && chosen.routeOffset == presented.routeOffset &&
        chosen.receiver.form.id == base.id.raw do
      throwError "method selection replaced its admitted canonical-base boundary"
    discard <| routedInvocationResultPlan selected chosen
    unless (← harness.actions.get).isEmpty && (← harness.connections.get).isEmpty &&
        (← harness.replies.get).isEmpty do
      throwError "prospective canonical-base selection executed an action or method"
    let alias ← mkAppM ``id #[presented.receiver.value]
    let changed := { presented.receiver with
      payload := forwardPayload presented.receiver alias presented.receiver.json }
    unless ← unavailable (do
        discard <| materializeNamedRefinementWith (fun _ wire => pure wire) trace changed origin) do
      throwError "a historical producer authorized another definitionally equal occurrence"
    let changedData := { presented.receiver with
      payload := forwardPayload presented.receiver presented.receiver.value
        (node base.id.raw #[toJson (4 : Nat)]) }
    unless ← unavailable (do
        discard <| materializeNamedRefinementWith (fun _ wire => pure wire) trace changedData origin) do
      throwError "a historical producer authorized a different representation packet"
    let forwarded ← forwardRetainedValue presented.receiver alias
    let some forwardedOrigin ← currentNamedRefinementOrigin? forwarded
      | throwError "a checked transparent alias lost its named producer"
    let refreshed ← materializeNamedRefinementWith (fun _ wire => pure wire)
      trace forwarded forwardedOrigin
    unless sameCompleteWireContext refreshed forwarded do
      throwError "an unchanged checked alias replaced its original comparison occurrences"
    checked := true
  unless checked do throwError "the control did not reach the ordinary inherited method"

run_elab do
  let state ← registryState
  let some entry := state.objects.find? (·.id.raw == "obj.groups.symmetric")
    | throwError "the existing parameterized named source is absent"
  let some refinement := entry.refines
    | throwError "the existing named source has no accepted refinement"
  let trace ← Trace.new
  let harness ← Harness.empty
  let parameter := mkNatLit 3
  let formal ← objectAt trace entry #[parameter]
  let original ← realizeUnobserved harness trace "the original named constructor" formal
  let some context := original.categoryContext
    | throwError "the original constructor lost its complete category"
  let makeParameter := fun (token : String) => do
    let wire : Wire := {
      form := original.form,
      payload := .computed parameter (.owned "named-parameter-engineering" 19
        (node "opaqueData" #[toJson token])) }
    retainIntrinsicResultAssembly wire (.value (← inferType parameter)) (.literal wire.fragment)
  let first ← makeParameter "first positioned parameter data"
  let second ← makeParameter "materialized positioned parameter data"
  let makeSource := fun (parameter : Wire) => do
    let template := ActionDataTemplate.ctor entry.id.raw #[.wire .parameter parameter]
    let (fragment, inputs) ← renderCapturedActionData template
    let wire := { original with
      payload := (← combinedRecipePayload formal fragment inputs), intrinsicAssembly := none }
    retainIntrinsicAssembly wire .object context template
  let source ← makeSource first
  let actualSource ← makeSource second
  unless source.owner? == first.owner? && !source.actualData do
    throwError "the pending constructor lost its independent actual parameter supplier"
  let applications ← refinement.route.mapM (Semantic.edgeFunctor state)
  let presented ← transport trace source refinement.route
    (applications := some applications)
  let some origin ← currentNamedRefinementOrigin? presented
    | throwError "parameter ownership wrongly suppressed the accepted named presentation"
  unless sameCompleteWireContext origin.source source &&
      origin.applications == applications && origin.descriptors.size == refinement.route.size do
    throwError "the named producer changed its complete original input positions"
  let observe := fun (role : ActionDataRole) (wire : Wire) => do
    if role == .object && sameCompleteWireContext wire source then return actualSource
    if role == .parameter && sameCompleteWireContext wire first then return second
    throwError "the named presentation consulted an uncaptured data occurrence"
  let refreshed ← materializeNamedRefinementWith observe trace presented origin
  let some refreshedOrigin ← currentNamedRefinementOrigin? refreshed
    | throwError "the materialized presentation lost its current producer"
  unless refreshed.value == presented.value && refreshed.owner? == second.owner? &&
      sameCompleteWireContext refreshedOrigin.source actualSource &&
      refreshed.json != presented.json do
    throwError "parameter refresh changed the interpreted object or retained stale data"
  let some targetContext := refreshed.categoryContext
    | throwError "the materialized presentation lost its complete target category"
  let some comparison := refreshed.endpointPresentation
    | throwError "the materialized presentation lost its accepted comparison"
  let (forward, backward) ← endpointPresentationMaps refreshed targetContext comparison
  for wire in #[forward, backward] do
    let .ok field := Backend.ObjectField.decode wire.json
      | throwError "refresh changed the public comparison descriptor family"
    unless field.parameters == #[second.json] && wire.owner? == second.owner? do
      throwError "a comparison direction retained an earlier parameter packet or supplier"
  unless (← harness.actions.get).isEmpty && (← harness.connections.get).isEmpty do
    throwError "refreshing constructor parameters executed a structural image action"
