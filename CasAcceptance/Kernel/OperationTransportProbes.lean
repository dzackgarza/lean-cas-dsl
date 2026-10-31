/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
meta import CasCatalogue.Realize

/-! Engineering controls for accepted presentation prefixes followed by complete
residual object actions. Opaque packets test data flow and ownership only; no
mathematical result or extra registration is supplied. No process is started. -/

open Lean Meta Elab Term CategoryTheory
open CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private def node (tag : String) (arguments : Array Json) : Json :=
  Json.mkObj [("ctor", toJson tag), ("args", Json.arr arguments)]

private partial def containsData (actual expected : Json) : Bool :=
  actual == expected || match actual with
    | .arr values => values.any (containsData · expected)
    | .obj fields => fields.any fun _ value => containsData value expected
    | _ => false

private def registered (addresses : Array String) : TermElabM Harness := do
  return ← Harness.ofManifest "." {
    backends := #[{ name := "transport-probe", command := "unused" }]
    registrations := addresses.map fun address => {
      operation := "meth.cardinality", input := address, backend := "transport-probe" } }

-- A complete named prefix retains its accepted comparison and target context;
-- the remaining actions are then applied exactly once. Old exact-base and new
-- category registrations remain peers when both are present.
run_elab do
  let state ← registryState
  let some entry := state.objects.find? (·.id.raw == "obj.groups.symmetric")
    | throwError "the accepted named-prefix fixture is absent"
  let some refinement := entry.refines | throwError "the accepted prefix is absent"
  let some sourceCategory := state.categories.find? (·.id == entry.category)
    | throwError "the selected source category is absent"
  let some base := state.objects.find? (·.id == refinement.base)
    | throwError "the accepted prefix base is absent"
  let trace ← Trace.new
  let formal ← objectAt trace entry #[mkNatLit 5]
  let empty ← Harness.empty
  let original ← realize empty trace "the complete named source" formal
  let residual : Array EdgeRef := #[.functor FunctorId.setsWholeSubset, .functor FunctorId.subobjectsSetsDomain]
  let route := refinement.route ++ residual
  let context ← CategoryContext.ofNamed sourceCategory formal
  for retainContext in #[false, true] do
    let original := { original with categoryContext := if retainContext then some context else none }
    let (prepared, remaining) ← canonicalOperationInput trace original route
    unless prepared.form.id == base.id.raw && remaining == residual &&
        prepared.presentationIsos.size == 1 do
      throwError "the accepted named prefix or its exact residual was discarded"
    if let some context := prepared.categoryContext then
      let some expression := state.formExpression? prepared.form
        | throwError "the normalized named base lost its accepted category"
      unless context.expression.syntacticEq expression do
        throwError "the normalized named prefix retained its old category context"
      CategoryContext.checkObject context prepared.value
    let generic ← registered #[CategoryId.sets.raw]
    let selected ← computationalOperationReceiver generic trace "meth.cardinality"
      original route prepared
    unless containsData selected.json prepared.json do
      throwError "the residual route replaced the accepted prefix's computational input"
    let mut nested := selected.json
    for _ in [:residual.size] do
      let .ok ("functorAction", #[_, previous]) := ComputationalData.envelope nested
        | throwError "the residual route omitted or duplicated an accepted action"
      nested := previous
    unless nested == prepared.json do
      throwError "the residual actions were not based on the normalized named input"
    let legacy ← registered #[base.id.raw]
    let old ← computationalOperationReceiver legacy trace "meth.cardinality" original route prepared
    unless old.json == prepared.json && old.form.id == base.id.raw do
      throwError "an existing exact-base implementation no longer receives its accepted input"
    let overlapping ← registered #[base.id.raw, CategoryId.sets.raw]
    let ambiguous ← try
      discard <| computationalOperationReceiver overlapping trace "meth.cardinality"
        original route prepared
      pure false
    catch error => pure (Exception.stratum? error == some .ambiguousRealization)
    unless ambiguous do
      throwError "the accepted prefix gave one competing registration an implicit priority"

-- A proof-only prefix restores the complete actual source snapshot before any
-- residual action. Missing snapshots remain errors rather than formal fallback.
run_elab do
  let state ← registryState
  let some entry := state.objects.find? (·.id.raw == "obj.sets.fin")
    | throwError "the complete proof-prefix source is absent"
  let some host := state.categories.find? (·.id == entry.category)
    | throwError "the proof-prefix host is absent"
  let some target := state.categories.find? (·.id == CategoryId.finiteSets)
    | throwError "the complete proof-prefix total is absent"
  let classifier := ClassifierId.setsFinite
  let trace ← Trace.new
  let source ← objectAt trace entry #[mkNatLit 5]
  let context ← CategoryContext.ofNamed host source
  let original : Wire := {
    form := .diagrams host
    payload := .computed source (.owned "transport-probe" 23
      (node "opaqueData" #[toJson ("actual proof-prefix source" : String)]))
    categoryContext := some context }
  let completed ← ProofRefinement.construct state classifier target source
  Trace.record (some trace) completed.value
    (.proofRefinement classifier host.id target.id source completed.action completed.identity)
  let harness ← registered #[CategoryId.sets.raw]
  harness.results.modify (·.insert source original)
  let refined ← realize harness trace "the complete proof refinement" completed.value
  let residual : Array EdgeRef :=
    #[.functor FunctorId.setsWholeSubset, .functor FunctorId.subobjectsSetsDomain]
  let route := #[.classifierForget classifier] ++ residual
  let (prepared, remaining) ← canonicalOperationInput trace refined route
  unless prepared.value == original.value && prepared.json == original.json &&
      prepared.owner? == original.owner? && prepared.form.id == original.form.id &&
      prepared.proofSources.isEmpty && remaining == residual do
    throwError "the proof-only prefix did not restore its exact owned source snapshot"
  let selected ← computationalOperationReceiver harness trace "meth.cardinality"
    refined route prepared
  unless selected.owner? == original.owner? && containsData selected.json original.json do
    throwError "the residual action dropped the proof refinement's actual source or owner"
  let expected ← Semantic.objOf (← Semantic.routeFunctor state route) refined.value
  unless ← withTransparency .all <| isDefEq selected.value expected do
    throwError "the proof prefix and residual route changed the complete formal receiver"
  let rejected ← try
    discard <| canonicalOperationInput trace { refined with proofSources := [] } route
    pure false
  catch _ => pure true
  unless rejected do throwError "a proof refinement invented its missing source snapshot"

-- The selected action parameter can be the only live computational dependency.
-- Its actual packet and owner must survive operation dispatch just as they do
-- ordinary contextual object and morphism actions.
run_elab do
  let state ← registryState
  let trace ← Trace.new
  let ring ← elabTermAndSynthesize (← `(RingCat.of (ZMod 4))) none
  let source ← elabTermAndSynthesize
    (← `(ModuleCat.of (RingCat.of (ZMod 4)) (ZMod 4))) none
  let some ringCategory := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the action parameter category is absent"
  let some sourceCategory := state.categories.find? (·.id == CategoryId.modulesR)
    | throwError "the complete parameterized source category is absent"
  let parameter : Wire := {
    form := .diagrams ringCategory
    payload := .computed ring (.owned "transport-probe" 31
      (node "opaqueData" #[toJson ("actual selected ring" : String)])) }
  let original : Wire := {
    form := .diagrams sourceCategory
    payload := .ordinary source
      (node "obj.modules.regular" #[node "obj.rings.integers_mod" #[toJson (4 : Nat)]])
    categoryContext := some (← CategoryContext.ofNamed sourceCategory source) }
  let route : Array EdgeRef := #[.functor FunctorId.modulesFibreInclusion,
    .functor FunctorId.modulesAdditiveGroup, .functor FunctorId.additiveGroupsToGroups,
    .functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
    .classifierForget ClassifierId.magmasAssociative,
    .classifierForget ClassifierId.setsBinaryOperation]
  let harness ← registered #[CategoryId.sets.raw]
  harness.results.modify (·.insert ring parameter)
  let prepared ← canonicalOperationReceiver trace original route
  let selected ← computationalOperationReceiver harness trace "meth.cardinality"
    original route prepared
  unless selected.owner? == parameter.owner? && containsData selected.json parameter.json do
    throwError "the residual parameterized action lost its actual parameter data or sole owner"
  let relabeledPortable := { original with
    payload := .computed source (.owned "foreign-transport" 32 original.json) }
  unless relabeledPortable.ownership.isEmpty do
    throwError "a portable original module acquired a supplier from its wrapper label"
  let retained ← computationalOperationReceiver harness trace "meth.cardinality"
    relabeledPortable route relabeledPortable
  unless retained.fragment == selected.fragment && retained.owner? == parameter.owner? do
    throwError "a portable source label changed the selected action's actual parameter dependency"
  unless ← withTransparency .all <| isDefEq retained.value selected.value do
    throwError "portable source relabelling changed the independently fixed transported receiver"

end
