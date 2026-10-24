/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

/- A named full-object presentation supplies mathematical identity only. It must
not replace the actual previously computed packet of a distinct retained child. -/
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.rings.integers")
    | throwError "the accepted full-object control is absent"
  let some category := state.categories.find? (·.id == row.category)
    | throwError "the selected full-object category is absent"
  let trace ← Trace.new
  let named ← Semantic.object row #[] (some trace)
  let actual ← mkAppM ``id #[named]
  let wrapper ← mkAppM ``id #[actual]
  unless actual != named && wrapper != actual do
    throwError "the actual result and its presentation lost their distinct trace identities"
  let actualValue : Value := .object actual category none none none
  let namedValue : Value := .object named category (some (row, #[])) none none
  let expected ← inferType actual
  let evidence ← (coalesceSelectedParameterViews expected wrapper
    #[actualValue, namedValue]).run { trace := some trace }
  let (_, _, _, alternatives, _) := evidence
  unless !alternatives.isEmpty do throwError "the accepted full-object identity is absent"
  Trace.record (some trace) wrapper (.parameterEquivalence expected actual alternatives)
  let packet := Json.mkObj [("ctor", toJson "opaqueData"),
    ("args", Json.arr #[toJson "retained previously computed object"])]
  let context ← CategoryContext.ofNamed category actual
  let original : Wire := {
    form := .object row
    payload := .computed actual (.owned "original-owner" 731 packet)
    categoryContext := some context }
  let harness ← Harness.ofManifest "." { backends := #[], registrations := #[] }
  harness.results.modify (·.insert actual original)
  let result ← realize harness trace "the actual object under a checked presentation" wrapper
  unless result.value == wrapper && result.json == packet &&
      result.owner? == original.owner? && result.categoryContext.isSome do
    throwError "the named presentation replaced the actual full object or its owning session"
  let reused ← realize harness trace "the reused full object presentation" wrapper
  unless reused.json == packet && reused.owner? == original.owner? do
    throwError "a subsequent use rebuilt the named presentation instead of the actual result"
  let (parameters, dependencies) ← realizedParameters harness trace #[wrapper]
  unless parameters == #[packet] && dependencies.any (·.owner? == original.owner?) do
    throwError "a subsequent complete parameter request lost the actual packet or owning session"
