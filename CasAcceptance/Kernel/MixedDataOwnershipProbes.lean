/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Protocol bookkeeping controls for independently supplied opaque occurrences.
The two actual processes may return identical token bytes. Their arbitrary data
assert no mathematical answers; these controls check only retained positions,
suppliers, session liveness, and the boundary before another dispatch. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def requireData (result : Except String α) : TermElabM α :=
  match result with
  | .ok data => pure data
  | .error message => throwError "ownership control could not construct its packet: {message}"

private def rejects (expected : Stratum) (work : TermElabM α) : TermElabM Unit := do
  let actual ← try
    discard <| work
    pure (none, "unexpected success")
  catch error => pure (Exception.stratum? error, ← error.toMessageData.toString)
  unless actual.1 == some expected do
    throwError "ownership control expected {reprStr expected}, received {reprStr actual}"

private def dispatchCount (harness : Harness) : TermElabM Nat := do
  let some calls := harness.dispatches | throwError "the dispatch observation is absent"
  return (← calls.get).size

private def wireRecord (wire : Wire) : TermElabM Json := do
  return Json.mkObj [
    ("formal", toJson (reprStr wire.value)), ("type", toJson (reprStr (← inferType wire.value))),
    ("data", wire.json), ("ownership", toJson wire.ownership),
    ("owners", toJson (DataOwnership.owners wire.ownership))]

private def record (label : String) (harness : Harness) (wires : Array Wire)
    (checks : Array String) : TermElabM Unit := do
  if let some path ← IO.getEnv "CAS_DEFERRED_SERVICE_REPORT" then
    let replies ← (← harness.replies.get).mapM fun reply => do
      return Json.mkObj [("operation", toJson reply.operation), ("backend", toJson reply.backend),
        ("session", toJson reply.session), ("original", reply.original),
        ("completed", toJson reply.completed), ("ownership", toJson reply.completedOwnership)]
    let some calls := harness.dispatches | throwError "the dispatch observation is absent"
    let report := Json.mkObj [("case", toJson label), ("checks", toJson checks),
      ("wires", Json.arr (← wires.mapM wireRecord)), ("replies", Json.arr replies),
      ("dispatches", Json.arr (← calls.get))]
    IO.FS.withFile path .append fun output => output.putStrLn report.compress

private def fixture (mode : String) : TermElabM (Trace × Harness × FunctorEntry × Expr × Wire) := do
  let trace ← Trace.new
  let state ← registryState
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the existing outer action is absent"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the independently selected endpoint family is absent"
  let source ← Semantic.object finite #[← `(2)] (some trace)
  let empty ← Harness.empty
  let original ← realize empty trace "the independent ownership-control source" source
  let action ← Semantic.edgeFunctor state (.functor entry.id)
  discard <| Semantic.objOf action source
  let action ← instantiateMVars action
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := #[
      { name := "outer-service", command := "python3", args := #["probe_deferred_service.py", "outer", mode] },
      { name := "child-service", command := "python3", args := #["probe_deferred_service.py", "child", mode] },
      { name := "target-service", command := "python3", args := #["probe_deferred_service.py", "target", mode] }]
    registrations := #[
      { operation := "fun.sets.list", input := "fun.sets.list#input", backend := "outer-service" },
      { operation := "fun.sets.identity", input := "fun.sets.identity#input", backend := "child-service" },
      { operation := "meth.cardinality", input := "cat.sets", backend := "target-service" }] }
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty && harness.admitted.size == 3 do
    throwError "the independent ownership protocol registrations did not admit"
  let calls ← IO.mkRef #[]
  let harness := enableService { harness with dispatches := some calls } trace
  return (trace, harness, entry, action, original)

run_elab do
  for mode in #["mixed-owners", "mixed-owners-equal", "mixed-owners-equal-repeated"] do
    logInfo m!"checking mixed ownership protocol: {mode}"
    let (trace, harness, entry, action, original) ← fixture mode
    try
      let result ← executeObjectEdge harness trace (.functor entry.id) action original
      unless ← isDefEq result.value (← Semantic.objOf action original.value) do
        throwError "mixed assembly replaced the enclosing independently fixed formal value"
      checkServiceOwner harness result
      let owners := DataOwnership.owners result.ownership
      let some childOwner := owners.find? (·.1 == "child-service")
        | throwError "mixed assembly lost the actual child supplier"
      let some outerOwner := owners.find? (·.1 == "outer-service")
        | throwError "mixed assembly lost the actual outer supplier"
      unless owners.size == 2 && childOwner.2 != outerOwner.2 && result.owner?.isNone do
        throwError "mixed assembly collapsed two live supplying sessions"
      let #[service] ← harness.services.get | throwError "the completed service scope is absent"
      let #[child] := service.nodes | throwError "the retained child occurrence is absent"
      unless service.completed && child.result.owner? == some childOwner do
        throwError "mixed assembly did not complete with its original child occurrence"
      unless (← dispatchCount harness) == 2 && (← harness.replies.get).size == 2 do
        throwError "mixed assembly did not retain exactly the two actual process replies"

      let repeated := mode == "mixed-owners-equal-repeated"
      let firstPath : DataOwnership.Path := if repeated then
        #[.field "args", .index 0, .field "args", .index 0]
        else #[.field "args", .index 0]
      let secondPath : DataOwnership.Path := if repeated then
        #[.field "args", .index 0, .field "args", .index 1]
        else #[.field "args", .index 1]
      let first ← requireData (result.fragment.project firstPath)
      let second ← requireData (result.fragment.project secondPath)
      unless first == child.result.fragment && DataOwnership.owners first.ownership == #[childOwner] &&
          DataOwnership.owners second.ownership == #[outerOwner] do
        throwError "exact completed positions selected a different actual supplier"
      if mode != "mixed-owners" then
        unless first.json == second.json && first.ownership != second.ownership do
          throwError "the independent processes did not retain different owners of identical token bytes"
      if repeated then
        let again ← requireData (result.fragment.project
          #[.field "args", .index 1, .field "args", .index 0])
        let portable ← requireData (result.fragment.project
          #[.field "args", .index 1, .field "args", .index 1])
        unless again == first && result.ownership.size == 3 && portable.ownership.isEmpty do
          throwError "repeated result references lost positions or assigned a supplier to their portable sibling"
        let node := fun tag args => Json.mkObj [("ctor", toJson (tag : String)),
          ("args", Json.arr args)]
        let malformed := #[
          node "objectProduct" #[node "objectProduct" #[first.json], second.json],
          node "objectProduct" #[node "objectProduct" #[first.json, toJson "not an object"], second.json]]
        for data in malformed do
          if (← ComputationalData.validatePort result.value (← inferType result.value) data).isOk then
            throwError "nested product validation accepted a missing or ill-typed factor"
      else
        unless result.ownership.size == 2 do
          throwError "the two-field result has missing or extra occurrence bindings"

      let state ← registryState
      let some finite := state.objects.find? (·.id.raw == "obj.sets.fin") | unreachable!
      let some sets := state.categories.find? (·.id == CategoryId.sets) | unreachable!
      let target ← Semantic.object finite #[← `(3)] (some trace)
      let empty ← Harness.empty
      let portableTarget ← realize empty trace "the independent portable endpoint" target
      let formalMap ← instantiateMVars (← elabTermAndSynthesize
        (← `(TypeCat.ofHom (fun (_ : $(← exprToSyntax original.value)) =>
          (0 : $(← exprToSyntax target))))) none)
      -- This portable table is an arbitrary protocol field. No control evaluates
      -- it or compares a computed mathematical answer with it.
      let callable ← requireData (DataOwnership.Data.portable
        (toJson (#[#[(0 : Nat), 0], #[1, 0]])))
      let mapData ← requireData (DataOwnership.Data.ctor "typedMap" #[first, second, callable])
      let mapWire : Wire := {
        form := .canonicalMorphism sets
        payload := (← scopedPayload formalMap mapData)
        categoryContext := some (← CategoryContext.ofNamed sets original.value)
        callableObserved := true }
      let scope : ServiceScope := {
        harness, trace, references := #[mapWire], known := #[]
        operands := (← IO.mkRef #[]), backend := "outer-service" }
      let retained ← serviceRegister scope mapWire
      let sourceEndpoint ← serviceEndpoint scope retained true
      let targetEndpoint ← serviceEndpoint scope retained false
      let sourceWire ← serviceWire scope sourceEndpoint
      let targetWire ← serviceWire scope targetEndpoint
      unless (← isDefEq sourceEndpoint.value original.value) &&
          (← isDefEq targetEndpoint.value target) && sourceEndpoint.fragment == first &&
          targetEndpoint.fragment == second && sourceEndpoint.handle != targetEndpoint.handle &&
          sourceWire.owner? == some childOwner && targetWire.owner? == some outerOwner do
        throwError "typed-map endpoint projection confused a formal side, data position, or supplier"

      let portableMap ← requireData
        (DataOwnership.Data.ctor "typedMap" #[first, portableTarget.fragment, callable])
      let portableMapWire := { mapWire with payload := (← scopedPayload formalMap portableMap) }
      let portableHandle ← serviceRegister scope portableMapWire
      let portableEndpoint ← serviceEndpoint scope portableHandle false
      let portableWire ← serviceWire scope portableEndpoint
      unless portableEndpoint.fragment == portableTarget.fragment && portableWire.owner?.isNone do
        throwError "a portable endpoint inherited an opaque sibling's supplier"
      if mode != "mixed-owners" then
        let sameFirst : Wire := { original with payload := (← scopedPayload original.value first) }
        let sameSecond : Wire := { original with payload := (← scopedPayload original.value second) }
        unless sameFirst.value == sameSecond.value && sameFirst.json == sameSecond.json &&
            sameActionOperand sameFirst sameFirst && !sameActionOperand sameFirst sameSecond do
          throwError "action reuse identified equal bytes from independent supplying sessions"
        let cache ← harness.results.get
        try
          harness.results.modify (·.insert original.value sameSecond)
          let request := { sameFirst with
            serviceHandles := (← retainServiceOperands harness #[sameFirst]) }
          let known ← serviceKnownInputs harness request
          unless known.size == 2 && known.all (sameServiceSelection · sameFirst) do
            throwError "equal bytes in a global cache invented a parent request occurrence"
        finally harness.results.set cache

      -- All assembly and projections above succeed. A registration on another
      -- process cannot consume either opaque session without a compatible bridge.
      let before ← dispatchCount harness
      let repliesBefore := (← harness.replies.get).size
      rejects .noImplementation (sendData harness "meth.cardinality" result)
      rejects .noImplementation (send harness "meth.cardinality" result)
      unless (← dispatchCount harness) == before && (← harness.replies.get).size == repliesBefore &&
          ((← harness.connections.get)["target-service"]?).isNone do
        throwError "incompatible consumption dispatched or started an unrelated process"

      let dropped := { mapData with ownership := mapData.ownership.extract 0 1 }
      let stale := { mapData with ownership := mapData.ownership.push {
        path := #[.field "absent"], owner := childOwner } }
      let conflicting := { mapData with ownership := mapData.ownership.push {
        path := #[.field "args", .index 0], owner := outerOwner } }
      for invalid in #[dropped, stale, conflicting] do
        rejects .unavailable (scopedPayload formalMap invalid)
        let invalidWire := { mapWire with payload := .computed formalMap (.scoped invalid) }
        rejects .unavailable (checkServiceOwner harness invalidWire)
        rejects .unavailable (serviceRegister scope invalidWire)

      let connections ← harness.connections.get
      let some (.ok childSession) := connections[childOwner.1]?
        | throwError "the actual child session is absent"
      harness.connections.modify (·.insert childOwner.1
        (.ok { childSession with identity := childSession.identity + 1 }))
      try
        rejects .unavailable (checkServiceOwner harness result)
        rejects .unavailable (checkServiceOwner harness sourceWire)
        rejects .unavailable (sendData harness "meth.cardinality" result)
        checkServiceOwner harness targetWire
        checkServiceOwner harness portableWire
      finally harness.connections.set connections
      checkServiceOwner harness result
      unless (← dispatchCount harness) == before do
        throwError "invalid occurrence metadata crossed the dispatch boundary"
      record mode harness #[result, mapWire, sourceWire, targetWire, portableMapWire, portableWire]
        (#["two retained live suppliers", "exact asymmetric typed-map endpoints",
          "portable sibling has no supplier", "no bridge: noImplementation only at consumption",
          "no extra dispatch or consumer process", "dropped/stale/conflicting tables rejected",
          "changed child session expires without expiring outer or portable data"] ++
          (if mode == "mixed-owners" then #[] else
            #["identical bytes retain independent suppliers", "action reuse keeps suppliers distinct",
              "global equal-byte caches do not supply request occurrences"]) ++
          (if repeated then #["repeated references retain distinct occurrence paths",
            "missing and ill-typed nested product factors rejected"] else #[]))
    finally harness.stop
