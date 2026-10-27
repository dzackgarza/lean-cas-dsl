/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for the private ownership projection used by target
operation admission. Existing accepted list actions supply actual owned data;
the ordinary typed product producer fixes the nested slots. No returned value
is a mathematical oracle, and no source declaration or leaf is introduced. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Realize

namespace CasCatalogue.NestedOwnerAdmissionProbes
meta section

private def privateHarness (h : Harness) : TermElabM Harness := do
  let inspect ← Harness.empty
  inspect.connections.set (← h.connections.get)
  inspect.serviceOperands.set (← h.serviceOperands.get)
  inspect.results.set (← h.results.get)
  return inspect

private def capture (h : Harness) (trace : Trace) (entry : FunctorEntry)
    (action : Expr) (source : Wire) : TermElabM Wire := do
  let h := { h with demandObjectActions := false }
  let edge := EdgeRef.functor entry.id
  let descriptor ← capturedEdgeData h trace edge action
  let encoder : ScopedActionEncoder := fun selected application => do
    unless selected == edge && application == action do
      throwError "the nested ownership control changed its accepted action"
    renderCapturedActionData descriptor
  let (template, _, _) ← objectActionTemplate h trace edge action source (some encoder)
  retainActionInput false edge action source template descriptor

private def sameResults (before after : Std.HashMap Expr Wire) : Bool :=
  before.size == after.size && before.toArray.all fun (formal, original) =>
    (after[formal]?).any fun actual => sameCompleteWireContext original actual &&
      original.serviceHandles == actual.serviceHandles

run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some entry := state.functors.find? (·.id.raw == "fun.sets.list")
    | throwError "the existing nested ownership action is absent"
  let some finite := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the existing product component is absent"
  let action ← instantiateMVars (← Semantic.asFunctor
    (← Semantic.edgeFunctor state (.functor entry.id)))
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let manifest : Manifest := {
    backends := (#["nested-source", "nested-foreign"].map fun name => {
      name, command := "python3", args := #["probe_functor_execution.py", "action",
        entry.id.raw, "--opaque-objects"] }) ++
      (#["nested-target", "nested-peer"].map fun name => {
        name, command := "python3", args := #["probe_functor_execution.py", "target", "meth.cardinality"] })
    registrations := (#["nested-source", "nested-foreign"].map fun backend => {
      operation := entry.id.raw, input := entry.inputAddress, backend }) ++
      (#["nested-target", "nested-peer"].map fun backend => {
        operation := "meth.cardinality", input := "cat.sets", backend }) }
  let base ← Harness.ofManifest root manifest
  let calls ← IO.mkRef #[]
  let base := { base with dispatches := some calls, demandObjectActions := true }
  try
    unless base.rejected.isEmpty && base.admitted.size == 4 do
      throwError "the existing nested ownership ports were not admitted"
    let scope := fun backend => { base with
      admitted := base.admitted.filter (fun row => row.registration.backend == backend) }
    let prepare ← Harness.empty
    let first ← Semantic.object finite #[← `(2)] (some trace)
    let second ← Semantic.object finite #[← `(3)] (some trace)
    let first ← realize prepare trace "the first independently fixed source" first
    let second ← realize prepare trace "the second independently fixed source" second
    let source ← executeObjectEdge (scope "nested-source") trace (.functor entry.id) action first
    let foreign ← executeObjectEdge (scope "nested-foreign") trace (.functor entry.id) action second
    unless source.owner?.map Prod.fst == some "nested-source" &&
        foreign.owner?.map Prod.fst == some "nested-foreign" && (← calls.get).size == 2 do
      throwError "the nested ownership control lacks two actual independent suppliers"
    let pending ← capture base trace entry action source
    unless pending.actionRecipe.isSome && !pending.actualData && (← calls.get).size == 2 do
      throwError "capturing the nested owner executed its pending action"
    let target := { base with admitted := base.admitted.filter fun row =>
      #["nested-target", "nested-peer"].contains row.registration.backend }
    for condition in #["portable-sibling", "foreign-sibling", "repeated-action", "known-output"] do
      let sibling := if condition == "foreign-sibling" then foreign
        else if condition == "repeated-action" then pending else second
      if condition == "known-output" then
        discard <| executeObjectEdge (scope "nested-source") trace (.functor entry.id) action source
      base.results.modify (·.insert pending.value pending |>.insert sibling.value sibling)
      let formal ← instantiateMVars (← mkAppM ``Prod #[pending.value, sibling.value])
      let product ← realizeEndpoint { base with demandObjectActions := false }
        trace "the original complete nested product" formal
      unless product.intrinsicAssembly.isSome && product.productComponents.size == 2 do
        throwError "the ordinary product producer did not retain its typed children"
      let beforeCalls ← calls.get
      let beforeActions ← base.actions.get
      let beforeResults ← base.results.get
      let beforeOperands ← base.serviceOperands.get
      let beforeReplies ← base.replies.get
      let inspect ← privateHarness base
      let privateTrace ← IO.mkRef (← trace.get)
      let (prospective, objects) ← prospectiveOwnerData base inspect privateTrace product
      unless (← calls.get).size == beforeCalls.size &&
          (← base.actions.get).size == beforeActions.size &&
          (← base.replies.get).size == beforeReplies.size &&
          sameResults beforeResults (← base.results.get) &&
          sameProductComponents beforeOperands (← base.serviceOperands.get) do
        throwError "prospective nested admission modified a live execution or operand table"
      let .ok ("objectProduct", #[_, _]) := ComputationalData.envelope prospective.json
        | throwError "prospective ownership replaced the complete intrinsic product"
      let right ← checkedFragment (prospective.fragment.project #[.field "args", .index 1])
      let candidates ← admittedRegistrations target "meth.cardinality" prospective
      if condition == "foreign-sibling" then
        unless right == foreign.fragment &&
            DataOwnership.owners prospective.ownership == DataOwnership.owners foreign.ownership &&
            candidates.isEmpty && objects.size == 1 do
          throwError "prospective nested admission erased an unrelated actual sibling supplier"
      else if condition == "known-output" then
        let #[_, _, completed] := beforeActions
          | throwError "the completed nested action lost its actual execution receipt"
        let left ← checkedFragment (prospective.fragment.project #[.field "args", .index 0])
        unless left == completed.result.fragment && right == second.fragment &&
            candidates.isEmpty && objects.isEmpty do
          throwError "prospective nested admission forgot an already determined output supplier"
      else
        unless prospective.ownership.isEmpty && candidates.size == 2 && objects.size == 1 do
          throwError "a pending nested output hid a prospective target peer before execution"
        if condition == "repeated-action" then
          let left ← checkedFragment (prospective.fragment.project #[.field "args", .index 0])
          unless left == right do
            throwError "one retained pending action acquired two unrelated future occurrences"
        else unless right == second.fragment do
          throwError "prospective nested admission replaced an actual portable sibling"
    -- A future whole-map body does not make its already known image endpoints
    -- portable. The ordinary Arrow producer retains both fields and the map.
    let #[_, _, image] ← base.actions.get
      | throwError "the endpoint ownership control lost its actual image receipt"
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | throwError "the endpoint ownership control lost its complete category"
    let context ← CategoryContext.ofNamed sets source.value
    let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[source.value]
    Trace.record (some trace) identity (.contextualIdentity context source.value)
    let identity ← realizeUnobserved base trace "the original identity occurrence" identity
    let mapped ← captureMapRoute { base with demandObjectActions := false } trace identity
      #[.functor entry.id] #[action]
    base.results.modify (·.insert mapped.value mapped)
    let arrow ← instantiateMVars (← mkAppOptM ``CategoryTheory.Arrow.mk
      #[some (← CategoryContext.carrier context), some (← CategoryContext.dictionary context),
        some image.result.value, some image.result.value, some mapped.value])
    Trace.record (some trace) arrow
      (.contextualArrow context mapped.value image.result.value image.result.value)
    let arrow ← realizeUnobserved base trace "the original Arrow input" arrow
    let inspect ← privateHarness base
    let privateTrace ← IO.mkRef (← trace.get)
    let (prospective, objects) ← prospectiveOwnerData base inspect privateTrace arrow
    let .ok ("arrow", #[left, right, callable]) := ComputationalData.envelope prospective.json
      | throwError "prospective ownership lost the ordinary Arrow field roles"
    let .ok framed := Backend.TypedMap.decode callable
      | throwError "the future whole callable omitted its complete fixed endpoints"
    unless left == image.result.json && right == image.result.json &&
        framed.source == image.result.json && framed.target == image.result.json &&
        DataOwnership.owners prospective.ownership == DataOwnership.owners image.result.ownership &&
        objects.size == 1 && (← calls.get).size == 3 && (← base.actions.get).size == 3 do
      throwError "a prospective whole-map body erased its actual endpoint suppliers"
  finally base.stop

end
end CasCatalogue.NestedOwnerAdmissionProbes
