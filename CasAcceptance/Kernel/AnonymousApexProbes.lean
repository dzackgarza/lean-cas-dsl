/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import CasAcceptance.Kernel.ProtocolFixtureData
import LeanCategories.Catalogue.Semantics.Limits.Registration
import LeanCategories.Catalogue.Semantics.Limits.Lifts
meta import CasCatalogue.Realize
meta import CasAcceptance.Kernel.ProtocolFixtureData
meta import LeanCategories.Catalogue.Semantics.Limits.Registration
meta import LeanCategories.Catalogue.Semantics.Limits.Lifts

open Lean Meta Elab Term CasCatalogue

/-! Framing controls, not mathematical assertions: an anonymous six-point
computational apex accompanies an independently fixed two-point formal product. -/

run_elab do
  let state ← registryState
  let trace ← Trace.new
  let some row := state.limits.find? (·.id.raw == "lim.sets.product")
    | throwError "the accepted product schema is unavailable"
  let first ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 1)) none
  let second ← elabTermAndSynthesize (← `(CasCatalogue.Foundation.Objects.fin 2)) none
  let diagram ← mkAppM ``CategoryTheory.Limits.pair #[first, second]
  let presentation ← Semantic.limitPresentation row diagram
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let node := fun tag args => Json.mkObj [("ctor", toJson (tag : String)), ("args", Json.arr args)]
  let fin := fun size => node "obj.sets.fin" #[toJson (size : Nat)]
  let actualApex := node "objectProduct" #[fin 2, fin 3]
  let keys := (Array.range 2).flatMap fun i =>
    (Array.range 3).map fun j => Json.arr #[toJson i, toJson j]
  let left := Json.arr (keys.map fun key => Json.arr #[key, toJson (0 : Nat)])
  let right := Json.arr (keys.mapIdx fun index key => Json.arr #[key, toJson (index % 2)])
  let answer := node "cone" #[actualApex, left, right]
  let .ok plan ← StructuredResult.dataPlan row diagram presentation
    | throwError "the accepted construction has no complete data plan"
  let objects := #[fin 1, fin 2]
  let external := fun binder => do
    let binding ← plan.binders[binder]?
    let .argument position ← binding.inputRoles[0]? | none
    objects[position]?
  if let .error message ← StructuredResult.validatePlannedData plan answer
      (fun port seen data => ComputationalData.validatePlannedPort plan port seen data
        external ComputationalData.endpointKeys) then
    throwError "the anonymous complete computational apex was rejected: {message}"
  let full := node "constructionApex" #[toJson row.id.raw, node "pair" objects, answer]
  let check := fun (formal : Expr) (form : Form) (full expectedApex : Json)
      (owner expectedOwner : Option (String × Nat)) => do
    let payload := match owner with
      | none => Realize.WirePayload.computed formal (.inline full)
      | some (backend, session) => .computed formal (.owned backend session full)
    let input : Realize.Wire := { form, payload }
    let actual ← Realize.computationalApexReceiver trace input
    unless actual.form.id == row.category.raw && actual.json == expectedApex &&
        actual.value == input.value && actual.owner? == expectedOwner do
      throwError "anonymous apex dispatch changed its complete data, formal request or ownership"
    unless actual.payload matches .computed .. do
      throwError "a portable computed apex became ordinary formal input"
  let owner := some ("anonymous-apex-fixture", 27)
  -- An enclosing session does not make a fully portable selected object opaque.
  for parentOwner in #[none, owner] do
    check apex (.limitApex row) full actualApex parentOwner none
  -- Actual opaque apex data, in contrast, must retain their original owner.
  let opaqueDatum := fun token => node "opaqueData" #[toJson (token : String)]
  let ownedApex := opaqueDatum "actual returned apex"
  let typedMap := fun source target callable => node "typedMap" #[source, target, callable]
  let ownedAnswer := node "cone" #[ownedApex,
    typedMap ownedApex (fin 1) (opaqueDatum "actual first leg"),
    typedMap ownedApex (fin 2) (opaqueDatum "actual second leg")]
  if let .error message ← StructuredResult.validatePlannedData plan ownedAnswer
      (fun port seen data => ComputationalData.validatePlannedPort plan port seen data
        external ComputationalData.endpointKeys) then
    throwError "the complete opaque computational apex was rejected: {message}"
  let ownedFull := node "constructionApex" #[toJson row.id.raw, node "pair" objects, ownedAnswer]
  check apex (.limitApex row) ownedFull ownedApex owner owner
  -- The accepted creation lift retains a formal object in its source category
  -- while the actual complete packet remains framed in the base category.
  let some finite := state.objects.find? (·.id.raw == "obj.finite_sets.fin")
    | throwError "the accepted structured finite-object family is unavailable"
  let sourceObject ← Realize.objectAt trace finite #[mkNatLit 2]
  let identity ← mkAppM ``CategoryTheory.CategoryStruct.id #[sourceObject]
  let sourceDiagram ← mkAppM ``CategoryTheory.Limits.cospan #[identity, identity]
  let created ← Semantic.limit false "pullback" sourceDiagram finite.category.raw (some trace)
  let sourceCone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[created]
  let sourceApex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[sourceCone]
  let some pullback := state.limits.find? (·.id.raw == "lim.sets.pullback")
    | throwError "the accepted base construction is unavailable"
  let finiteData := node finite.id.raw #[toJson (2 : Nat)]
  let identityData := Json.arr #[Json.arr #[toJson (0 : Nat), toJson (0 : Nat)],
    Json.arr #[toJson (1 : Nat), toJson (1 : Nat)]]
  let sourceArrow := node "arrow" #[finiteData, finiteData, identityData]
  let sourceData := node "cospan" #[sourceArrow, sourceArrow]
  let packet := node "createdCone" #[toJson LiftId.finiteSetsPullbacks.raw, sourceData, answer]
  let complete := node "constructionApex" #[toJson pullback.id.raw, sourceData, packet]
  let some creation := state.lifts.find? (·.id == LiftId.finiteSetsPullbacks)
    | throwError "the original creating action is unavailable"
  let action ← Semantic.asFunctor (← Semantic.edgeFunctor state creation.edge)
  let expectedImage ← Semantic.objOf action sourceApex
  let action ← instantiateMVars action
  let some targetCategory := state.categories.find? (·.id == pullback.category)
    | throwError "the original creating action lost its target category"
  let expectedContext ← CategoryContext.ofNamed targetCategory expectedImage
  let operation := match creation.edge with
    | .functor id => id.raw
    | edge => edgeActionAddress edge
  let inputAddress ← match creation.edge with
    | .functor id =>
      let some entry := state.functor? id
        | throwError "the original creating functor is unavailable"
      pure entry.inputAddress
    | edge => pure (edgeActionInputAddress edge)
  CasAcceptance.Kernel.ProtocolFixtureData.withData "anonymous-image-fixture" operation actualApex
    (fun harness returned _ => do
      unless harness.rejected.isEmpty && harness.admitted.size == 1 do
        throwError "the original creating action's complete request was not admitted"
      for parentOwner in #[none, owner] do
        let payload := match parentOwner with
          | none => Realize.WirePayload.computed sourceApex (.inline complete)
          | some (backend, session) => .computed sourceApex (.owned backend session complete)
        let input : Realize.Wire := { form := .createdApex pullback finite.category, payload }
        let retained ← Realize.computationalApexReceiver trace input
        unless retained.value == input.value && retained.fragment == input.fragment &&
            retained.form.id == input.form.id && retained.form.category == input.form.category &&
            retained.owner? == input.owner? do
          throwError "created apex receiver changed its original complete source occurrence"
        unless retained.payload matches .computed .. do
          throwError "a portable computed apex became ordinary formal input"
        let actual ← Realize.executeObjectEdge harness trace creation.edge action retained
        let some actualContext := actual.categoryContext
          | throwError "the created apex image lost its complete target category"
        unless actual.value == expectedImage && actual.json == actualApex &&
            actual.fragment == returned && actual.owner?.isNone &&
            actual.form.category == pullback.category &&
            actualContext.expression.syntacticEq expectedContext.expression &&
            (← withTransparency .all <| isDefEq actualContext.bundle expectedContext.bundle) do
          throwError "anonymous apex dispatch changed its complete data, formal request or ownership"
        let receipts := (← harness.actions.get).filter fun receipt =>
          receipt.operation == operation && receipt.action == action &&
            receipt.input.value == input.value && receipt.input.fragment == input.fragment
        let #[receipt] := receipts
          | throwError "the creating action lost its exact original source packet"
        unless receipt.input.form.id == input.form.id &&
            receipt.input.form.category == input.form.category &&
            receipt.input.owner? == input.owner? && receipt.result.fragment == returned do
          throwError "the creating action replaced its source occurrence or a supplier"
        unless actual.payload matches .computed .. do
          throwError "a portable computed apex became ordinary formal input")
    #[{ operation, input := inputAddress, backend := "anonymous-image-fixture" }]
