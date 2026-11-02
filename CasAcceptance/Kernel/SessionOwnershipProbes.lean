/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Actual connection-lifecycle checks for a complete registered callable.
The protocol-only process returns arbitrary data witnesses, never mathematical
answers. These checks observe host ownership, actual consumption, wrappers, foreign
sessions, stop/reconnect and fresh realization. They do not establish the separate
fixed RX10 equality or its required reindexed callable observation. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private partial def containsData (data expected : Json) : Bool :=
  data == expected || match data with
    | .arr children => children.any (containsData · expected)
    | .obj fields => fields.any fun _ child => containsData child expected
    | _ => false

private def unavailable (action : TermElabM α) : TermElabM Bool := do
  try
    discard action
    return false
  catch error => return Exception.stratum? error == some .unavailable

run_elab do
  let state ← registryState
  let some row := state.morphisms.find? (·.id.raw == "mor.sets.fin_rev")
    | throwError "the published complete callable fixture is absent"
  let formal ← elabTermAndSynthesize (← `($(mkCIdent row.declaration) 4)) none
  let some (source, target) := homEnds? (← inferType formal)
    | throwError "the complete callable lost its original endpoints"
  let some sets := state.categories.find? (·.id == row.category)
    | throwError "the complete callable lost its accepted category"
  let trace ← Trace.new
  Semantic.namedMorphism row formal (some trace)
  discard <| Semantic.recordNamedObject source (some trace)
  discard <| Semantic.recordNamedObject target (some trace)
  let mut applications : Array Expr := #[]
  let mut points : Array Expr := #[]
  for numeral in #[0, 1] do
    let .ok parsed := Parser.runParserCategory (← getEnv) `cas_term s!"{numeral} in Fin(4)"
      | throwError "the independent point input did not parse"
    let .element point _ ← (eval {} parsed).run { trace := some trace }
      | throwError "the declared input did not remain a complete point"
    let some (domain, middle) := homEnds? (← inferType point)
      | throwError "the original point lost its endpoints"
    unless ← isDefEq middle source do throwError "the point belongs to a different actual source"
    let application ← mkAppM ``CategoryTheory.CategoryStruct.comp #[point, formal]
    Trace.record (some trace) application
      (.morphismComposition sets.id point formal domain source target)
    applications := applications.push application
    points := points.push point
  let manifest : Manifest := {
    backends := #[{
      name := "session-probe"
      command := "python3"
      args := #["probe_owned_callable.py", "--materialize-invocation", row.id.raw] }]
    registrations := #[{ operation := row.id.raw, input := row.id.raw, backend := "session-probe" }] }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let observations ← IO.mkRef #[]
  let harness ← Harness.ofManifest root manifest
  let harness := { harness with dispatches := some observations }
  let foreignObservations ← IO.mkRef #[]
  let foreign ← Harness.ofManifest root manifest
  let foreign := { foreign with dispatches := some foreignObservations }
  unless harness.rejected.isEmpty && harness.admitted.size == 1 do
    throwError "the existing complete callable registration was not admitted"
  try
    let descriptor ← realize harness trace "the original complete callable" formal
    unless descriptor.owner?.isNone do throwError "a formal descriptor invented a session owner"
    let actual ← realizeArrowObservation harness trace descriptor
    let some owner := actual.owner?
      | throwError "the actual process reply did not retain its host connection identity"
    unless actual.value == formal && (← observations.get).size == 1 do
      throwError "whole-callable materialization changed its formal value or dispatch count"
    -- Later computations select the returned occurrence explicitly. Replaying
    -- the bare mathematical expression would ask for a new callable, not reuse
    -- this result. The same original point applications still fix their types.
    let callablePath : DataOwnership.Path := #[.field "args", .index 2]
    let argumentPath : DataOwnership.Path := #[.field "args", .index 6]
    let callableRef := Backend.inputRef (publicServiceInputPath callablePath)
    let argumentRef := Backend.inputRef (publicServiceInputPath argumentPath)
    let scopeFor (active : Harness) (callable : Wire) (argument : Wire) :
        TermElabM ServiceScope := do
      return {
        harness := active, trace, references := #[], known := #[]
        inputReferences := #[(callablePath, callable), (argumentPath, argument)]
        positionedInputs := true, operands := (← IO.mkRef #[]), backend := "session-probe" }
    let consume (active : Harness) (callable : Wire) (point application : Expr) :
        TermElabM Unit := do
      let argument ← realize active trace "the original independent point input" point
      let scope ← scopeFor active callable argument
      let invocation : Backend.PointInvocation := {
        operation := row.id.raw, parameters := #[toJson (4 : Nat)]
        arrow := callableRef
        domain := node "morphismEndpoint" #[argumentRef, toJson "source"]
        source := node "morphismEndpoint" #[callableRef, toJson "source"]
        target := node "morphismEndpoint" #[callableRef, toJson "target"]
        argument := argumentRef }
      let prepared ← prepareServiceRequest scope row.id.raw descriptor.form invocation.encode
      unless ← isDefEq prepared.result application do
        throwError "retained-callable consumption changed its original complete point application"
      discard <| executeServiceRequest scope row.id.raw descriptor.form prepared
    for (point, application) in points.zip applications do
      consume harness actual point application
    let calls ← observations.get
    unless calls.size == 3 do
      throwError "subsequent distinct point computations did not each use the returned callable"
    for call in calls.extract 1 calls.size do
      let .ok request := call.getObjVal? "request" | throwError "a dispatch lost its request"
      let .ok invocation := Backend.PointInvocation.decode request
        | throwError "a subsequent computation lost its complete point-invocation interface"
      unless containsData invocation.arrow actual.json &&
          (call.getObjVal? "inputOwner").toOption == some (toJson (some owner)) do
        throwError "a subsequent computation replayed a descriptor or detached its actual owner"
    let context ← CategoryContext.ofNamed sets source
    let structured ← mkAppM ``CategoryTheory.Arrow.mk #[formal]
    Trace.record (some trace) structured (.contextualArrow context formal source target)
    let scope ← scopeFor harness actual
      (← realize harness trace "the original independent point input" points[0]!)
    let sourceRef := node "morphismEndpoint" #[callableRef, toJson "source"]
    let targetRef := node "morphismEndpoint" #[callableRef, toJson "target"]
    let structuredWire ← serviceWire scope
      (← serviceObject scope (node "arrow" #[sourceRef, targetRef, callableRef]))
    unless ← isDefEq structuredWire.value structured do
      throwError "the retained callable's wrapper changed its original complete Arrow"
    let composition ← mkAppM ``CategoryTheory.CategoryStruct.comp #[formal, formal]
    Trace.record (some trace) composition
      (.morphismComposition sets.id formal formal source target target)
    let composedWire ← serviceWire scope
      (← serviceArrow scope (node "compose" #[callableRef, callableRef]))
    unless ← isDefEq composedWire.value composition do
      throwError "the retained callable's composition changed its original complete Hom"
    for wrapper in #[structuredWire, composedWire] do
      unless wrapper.owner? == actual.owner? && containsData wrapper.json actual.json do
        throwError "a complete wrapper lost the actual returned callable or changed its owner"
    unless (← observations.get).size == 3 do
      throwError "structural reuse unexpectedly requested a replacement callable"
    let .ok other ← foreign.connection "session-probe"
      | throwError "the independent foreign session did not start"
    unless other.identity != owner.2 do throwError "independent live sessions share an identity"
    unless ← unavailable (consume foreign actual points[0]! applications[0]!) do
      throwError "a foreign session consumed another connection's actual callable"
    unless (← foreignObservations.get).isEmpty do
      throwError "foreign data crossed the host boundary before rejection"
    harness.stop
    let .ok reconnected ← harness.connection "session-probe"
      | throwError "the new owning-session connection did not start"
    unless reconnected.identity != owner.2 do throwError "reconnection revived the old identity"
    unless ← unavailable (consume harness actual points[0]! applications[0]!) do
      throwError "reconnection revived old owned computational data"
    unless (← observations.get).size == 3 do
      throwError "expired data were dispatched before rejection"
    harness.results.set {}
    let fresh ← realizeArrowObservation harness trace
      (← realize harness trace "the same full mathematical callable in a new session" formal)
    unless fresh.owner? == some ("session-probe", reconnected.identity) &&
        fresh.json != actual.json && fresh.value == formal do
      throwError "fresh realization reused the old token, identity or a different formal arrow"
    consume harness fresh points[0]! applications[0]!
    unless (← observations.get).size == 5 do
      throwError "fresh realization and consumption did not both reach the new actual process"
  finally
    foreign.stop
    harness.stop
