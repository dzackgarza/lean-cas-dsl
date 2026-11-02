/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Actual-process controls for complete callable requests. Both directions of
the existing nonidentity F9 presentation and an Arrow-induced comparison retain
their full original domains. The process supplies only arbitrary opaque data;
hostile endpoint replies must fail before reuse. No mathematical result is asserted. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private partial def containsData (data expected : Json) : Bool :=
  data == expected || match data with
    | .arr values => values.any (containsData · expected)
    | .obj fields => fields.any fun _ value => containsData value expected
    | _ => false

private def exercise (trace : Trace) (formal : Expr) (context : CategoryContext)
    (address inputAddress : String) (inverse : Option Bool := none)
    (constructors : Array ConstructorId := #[])
    (endpointRoutes : Array (Array EdgeRef) := #[]) : TermElabM Unit := do
  let some (source, target) := homEnds? (← inferType formal)
    | throwError "the complete fixture lost its original full Hom"
  CategoryContext.checkMorphism context formal source target
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let prerequisites := endpointRoutes.flatten.foldl (fun selected edge =>
    if selected.contains edge then selected else selected.push edge) (#[] : Array EdgeRef)
  let expectedOperations := endpointRoutes.flatten.map edgeActionAddress |>.push address
  let cases := (if prerequisites.isEmpty then #[] else #[(false, false)]) ++
    #[(true, false), (true, true)]
  for (available, hostile) in cases do
    let installed := if available then prerequisites else #[]
    let manifest : Manifest := {
      backends := #[{
        name := "complete-callable-probe", command := "python3"
        args := #["probe_complete_callable.py", address] ++ installed.map edgeActionAddress ++
          (if hostile then #["--wrong-endpoints"] else #[]) }]
      registrations := #[{
        operation := address, input := inputAddress, backend := "complete-callable-probe" }] ++
        installed.map (fun edge => {
          operation := edgeActionAddress edge, input := edgeActionInputAddress edge,
          backend := "complete-callable-probe" }) }
    let calls ← IO.mkRef #[]
    let harness ← Harness.ofManifest root manifest
    let harness := { harness with dispatches := some calls }
    unless harness.rejected.isEmpty && harness.admitted.size == 1 + installed.size do
      throwError "the complete callable's published input registration was rejected"
    try
      let descriptor ← realize harness trace "the complete callable's original descriptor" formal
      if !available then
        let missing ← try
          discard <| realizeArrowObservation harness trace descriptor
          pure false
        catch error => pure (Exception.stratum? error == some .noImplementation)
        unless missing && (← calls.get).isEmpty do
          throwError "a complete component hid its absent endpoint action registration"
      else if hostile then
        let malformed ← try
          discard <| realizeArrowObservation harness trace descriptor
          pure false
        catch error => pure (Exception.stratum? error == some .malformed)
        unless malformed do throwError "a complete callable accepted different full endpoints"
        unless (← calls.get).map (fun event =>
            (event.getObjValAs? String "operation").toOption) == expectedOperations.map some do
          throwError "the hostile callable did not observe its original prerequisite actions"
      else
        let actual ← realizeArrowObservation harness trace descriptor
        unless actual.value == formal && actual.owner?.isSome do
          throwError "the observed complete callable lost its formal type or actual owner"
        let events ← calls.get
        unless events.map (fun event => (event.getObjValAs? String "operation").toOption) ==
            expectedOperations.map some do
          throwError "whole-callable observation changed its original ordered prerequisite actions"
        let #[sent] := events.filter (fun event =>
          (event.getObjValAs? String "operation").toOption == some address)
          | throwError "whole-callable observation did not dispatch its own operation once"
        let .ok request := sent.getObjVal? "request" | throwError "the request was not retained"
        let sourceWire ← realizeCallableEndpoint harness trace descriptor source true (some context)
        let targetWire ← realizeCallableEndpoint harness trace descriptor target false (some context)
        let sourceWire ← realizeObjectObservation harness trace sourceWire
        let targetWire ← realizeObjectObservation harness trace targetWire
        if let some inverse := inverse then
          let .ok invocation := Backend.PresentationInvocation.decode request
            | throwError "a presentation direction lost its complete comparison invocation"
          unless invocation.inverse == inverse && invocation.source == sourceWire.json &&
              invocation.target == targetWire.json do
            throwError "the complete presentation changed its direction or full endpoints"
        else
          let .ok invocation := Backend.PointInvocation.decode request
            | throwError "the constructed component lost its complete point invocation"
          unless invocation.operation == address && invocation.domain == sourceWire.json &&
              invocation.source == sourceWire.json && invocation.target == targetWire.json do
            throwError "the component changed its actual full generalized domain"
          unless invocation.parameters.size == 3 && invocation.parameters[2]! == toJson false do
            throwError "the component omitted its selected parameters or direction"
          let .ok ("constructedCellComponent", #[path, _]) :=
              ComputationalData.envelope invocation.arrow
            | throwError "the component lost its accepted constructor path"
          unless path == toJson (constructors.map (·.raw)) do
            throwError "the component changed its exact ordered constructor path"
        let retained ← realizeArrowObservation harness trace actual
        unless retained.json == actual.json && retained.owner? == actual.owner? &&
            (← calls.get).size == expectedOperations.size do
          throwError "a returned complete callable replayed its descriptor"
        let arrow ← mkAppOptM ``CategoryTheory.Arrow.mk
          #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
            some source, some target, some formal]
        Trace.record (some trace) arrow (.contextualArrow context formal source target)
        let wrapper ← realize harness trace "the returned callable in its complete Arrow" arrow
        let wrapper ← realizeObjectObservation harness trace wrapper
        unless wrapper.owner? == actual.owner? && containsData wrapper.json actual.json &&
            (← calls.get).size == expectedOperations.size do
          throwError "the complete Arrow detached the actual returned callable or owner"
    finally harness.stop

run_elab do
  let state ← registryState
  let some row := state.presentations.find? (·.id.raw == "cmp.f9.translation")
    | throwError "the independently registered nonidentity F9 comparison is absent"
  let some sourceRow := state.objects.find? (·.id == row.source)
    | throwError "the full comparison source is absent"
  let some category := state.categories.find? (·.id == sourceRow.category)
    | throwError "the full comparison category is absent"
  let iso ← ObjectPresentation.applyParameters row.declaration #[]
  for inverse in #[false, true] do
    let trace ← Trace.new
    let formal ← Semantic.presentationArrow row iso inverse (some trace)
    let some (source, target) := homEnds? (← inferType formal)
      | throwError "the selected comparison has no full endpoints"
    if ← withTransparency .all <| isDefEq source target then
      throwError "the nonidentity presentation control lost its distinct selected presentations"
    let context ← CategoryContext.ofNamed category source
    exercise trace formal context row.id.raw row.id.raw (some inverse)

run_elab do
  let state ← registryState
  let some cell := state.cells.find? (·.id.raw == "cmp.rings.carrier")
    | throwError "the accepted constructor comparison is absent"
  let .ok receiverSyntax := Parser.runParserCategory (← getEnv) `cas_term "id(ℤ in Rings)"
    | throwError "the selected comparison source map did not parse"
  let trace ← Trace.new
  let constructors := #[ConstructorId.arrow]
  let selected ← (Language.selectedCell {} cell.id.raw #[] receiverSyntax constructors false).run
    { trace := some trace }
  let (formal, _, _, context, _, _) ← (morphismContext selected).run {}
  let some (.cellComponent id parameters retainedConstructors inverse receiver) ← trace.node? formal
    | throwError "the selected comparison lost its complete producer record"
  unless id == cell.id && parameters.isEmpty && retainedConstructors == constructors && !inverse do
    throwError "the selected comparison changed its original parameters or direction"
  let action ← CellAction.select cell #[] constructors false receiver
  let address := cell.componentAddress constructors
  let some form := state.componentForm? address
    | throwError "the constructed component has no published complete request form"
  let some category := state.categories.find? (·.id == form.category)
    | throwError "the constructed component's full category is not registered"
  exercise trace formal context address category.id.raw none constructors
    #[action.leftRoute, action.rightRoute]

end
