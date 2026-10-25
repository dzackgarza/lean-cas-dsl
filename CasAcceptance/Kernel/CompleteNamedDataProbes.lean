/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering checks of complete selected object recovery. These inspect public
data and owner retention; they do not assert a backend's mathematical answers. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

run_elab do
  let inputs ← pure #[
    ("obj.sets.naturals", ← `(Nat)),
    ("obj.sets.integers", ← `(Int)),
    ("obj.rings.rationals", ← `(RingCat.of CasCatalogue.Algebra.NamedRings.rationals))]
  for (id, input) in inputs do
    let value ← instantiateMVars (← elabTermAndSynthesize input none)
    let trace ← Trace.new
    let harness ← Harness.empty
    let wire ← realizeEndpoint harness trace "the complete selected object" value
    unless wire.value == value && wire.json == node id #[] && wire.owner?.isNone do
      throwError "complete named recovery changed the selected value or descriptor"
    unless (← parameterData trace value) == wire.json do
      throwError "parameter and endpoint recovery disagree on the complete selected object"

-- Exact actual returned data precede recovery. An equal object under another
-- expression key cannot supply the requested object's packet or session.
run_elab do
  let state ← registryState
  let some row := state.objects.find? (·.id.raw == "obj.rings.rationals")
    | throwError "the complete rational ring fixture is absent"
  let trace ← Trace.new
  let named ← objectAt trace row #[]
  let selected ← instantiateMVars (← elabTermAndSynthesize
    (← `(RingCat.of CasCatalogue.Algebra.NamedRings.rationals)) none)
  unless named != selected && (← withTransparency .all <| isDefEq named selected) do
    throwError "the exact selected expression fixture lost its distinct key"
  let foreign : Wire := {
    form := .object row
    payload := .computed named (.owned "unrelated-complete-object" 410
      (node "opaqueData" #[toJson "foreign actual object"])) }
  let harness ← Harness.empty
  harness.results.modify (·.insert named foreign)
  let ordinary ← realizeEndpoint harness trace "the original selected object" selected
  unless ordinary.value == selected && ordinary.owner?.isNone &&
      ordinary.json == node row.id.raw #[] do
    throwError "named recovery substituted an unrelated equal cached object"
  let actual := { foreign with
    payload := .computed selected (.owned "actual-selected-object" 411
      (node "opaqueData" #[toJson "original actual object"])) }
  harness.results.modify (·.insert selected actual)
  let reused ← realizeEndpoint harness trace "the actual selected object" selected
  unless reused.value == selected && reused.json == actual.json &&
      reused.owner? == actual.owner? do
    throwError "named recovery replaced the original returned object or its owner"

-- A named object's literal parameters retain the actual packets and their owner.
run_elab do
  let state ← registryState
  let some sourceRow := state.objects.find? (·.id.raw == "obj.sets.naturals")
    | throwError "the parameter fixture is absent"
  let some mapsRow := state.objects.find? (·.id.raw == "obj.sets.maps")
    | throwError "the accepted complete map-object fixture is absent"
  let trace ← Trace.new
  let source := Lean.mkConst ``Nat
  let sourceWire : Wire := {
    form := .object sourceRow
    payload := .computed source (.owned "actual-parameter-object" 412
      (node "opaqueData" #[toJson "retained parameter packet"])) }
  let selected ← mkAppM mapsRow.declaration #[source, source]
  let harness ← Harness.empty
  harness.results.modify (·.insert source sourceWire)
  let actual ← realize harness trace "the named object with actual parameters" selected
  unless actual.value == selected && actual.owner? == sourceWire.owner? &&
      actual.json == node mapsRow.id.raw #[sourceWire.json, sourceWire.json] do
    throwError "named recovery erased an actual parameter packet or its owner"

-- A symbolic numeral keeps its original full ring owner when its independently
-- selected coordinate is the integer set. Different callables agree on that
-- complete coordinate without replacing either callable's actual data.
run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the declared point category is absent"
  let trace ← Trace.new
  let harness ← Harness.empty
  let source ← closedElementDomain state
  let target := Lean.mkConst ``Int
  let formal ← elabTermAndSynthesize
    (← `(TypeCat.ofHom (fun (_ : $(← exprToSyntax source)) => (29 : Int)))) none
  let scalarOwner := node "obj.rings.integers" #[]
  let original := node "element" #[scalarOwner, node "numeral" #[toJson (29 : Nat)]]
  let point : Wire := {
    form := .canonicalMorphism category
    payload := .ordinary formal original }
  let (framed, _) ← frameMorphismData harness trace source target point
  let .ok framedData := Backend.TypedMap.decode framed
    | throwError "the symbolic selected-coordinate point lost its typed frame"
  unless framedData.target == node "obj.sets.integers" #[] && framedData.callable == original do
    throwError "coordinate recovery changed the original element or its scalar owner"
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[target]
  let callable : Wire := {
    form := .canonicalMorphism category
    payload := .ordinary identity (node "identity" #[node "obj.sets.integers" #[]]) }
  let endpoint ← realizeCallableEndpoint harness trace callable target true
  unless endpoint.value == target && endpoint.json == framedData.target do
    throwError "complete endpoint recovery depends on the enclosing callable"

-- An actual callable keeps its anonymous computational endpoint even when its
-- formal carrier has a unique definitionally equal named presentation.
run_elab do
  let state ← registryState
  let some category := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the complete callable category is absent"
  let target := Lean.mkConst ``Int
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[target]
  let portable := node "identity"
    #[node "obj.sets.integers" #[], node "obj.sets.integers" #[]]
  let token := node "opaqueData" #[toJson "actual anonymous callable"]
  for payload in #[WirePayload.computed identity (.inline portable),
      WirePayload.computed identity (.owned "anonymous-callable-owner" 413 token)] do
    let actual : Wire := { form := .canonicalMorphism category, payload }
    let trace ← Trace.new
    let endpoint ← realizeCallableEndpoint (← Harness.empty) trace actual target false
    unless endpoint.value == target && endpoint.owner? == actual.owner? &&
        endpoint.json == Backend.MorphismEndpoint.encode
          { callable := actual.json, source := false } do
      throwError "complete named fallback replaced an actual anonymous endpoint"

end
