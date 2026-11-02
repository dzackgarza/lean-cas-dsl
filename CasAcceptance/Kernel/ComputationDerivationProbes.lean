/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.Realize
import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations
meta import CasCatalogue.Realize
meta import LeanCategories.Catalogue.Semantics.Algebra.ComputationDerivations

/-! Engineering controls for the generic consumer of upstream whole-family
derivations. Existing protocol fixtures supply arbitrary data and fault injection;
they provide no mathematical implementation or independent acceptance evidence. -/

open Lean Meta Elab Term CasCatalogue CasCatalogue.Language CasCatalogue.Realize

meta section

private structure Fixture where
  trace : Trace
  harness : Harness
  request : OperationObservation
  expected : Expr
  category : NamedCategoryEntry
  events : IO.Ref (Array Json)

private def fixture (kind : String := "primitive") (fault : Option String := none)
    (modulus : Nat := 5) : TermElabM Fixture := do
  let trace ← Trace.new
  let state ← registryState
  let some object := state.objects.find? (·.id.raw == "obj.rings.integers_mod")
    | throwError "the public ring object is absent"
  let some rings := state.categories.find? (·.id == CategoryId.rings)
    | throwError "the public ring category is absent"
  let some sets := state.categories.find? (·.id == CategoryId.sets)
    | throwError "the public data category is absent"
  let ring ← Semantic.object object #[← exprToSyntax (toExpr modulus)] (some trace)
  let selected := Value.object ring rings (some (object, #[.nat modulus])) none none
  let application ← mkAppM ``Algebra.NamedRings.mul #[ring]
  let .element formal target ← (applyFamily ``Algebra.NamedRings.mul sets #[.nat 2, .nat 3]
      (parameters := #[selected]) (application := some application)
      (operationId := some ⟨"op.rings.mul"⟩)).run { trace := some trace }
    | throwError "the fixed complete operation was not read"
  let .element expected _ ← (toElement (.nat 1) target).run { trace := some trace }
    | throwError "the fixed independent numeral was not read"
  let empty ← Harness.empty
  let original ← realize empty trace "the fixed original operation" formal
  let operations := if kind == "alternative" then
      #["fun.rings.semiring", "fun.rings.multiplicative_monoid", "op.semirings.mul"]
    else #["fun.rings.semiring", "fun.semirings.monoid", "op.monoids.mul"]
  let registrations := operations.map fun operation => {
    operation := operation
    input := if operation == "op.monoids.mul" then "cat.monoids"
      else if operation == "op.semirings.mul" then "cat.semirings"
      else if operation == "fun.rings.multiplicative_monoid" then "obj.rings.rationals"
      else operation ++ "#input"
    backend := "derivation-probe" : Registration }
  let registrations := if kind == "missing" then
      registrations.filter (·.operation != "fun.rings.semiring")
    else if kind == "reversed" then registrations.reverse else registrations
  let arguments := match fault with
    | some fault => #["probe_reply_conditions.py", s!"derivation_{fault}.json"]
    | none => #["probe_owned_callable.py", "--require-argument-owner"] ++ operations
  let manifest : Manifest := {
    backends := #[{ name := "derivation-probe", command := "python3", args := arguments }]
    registrations }
  let root : System.FilePath := (← IO.getEnv "CAS_OWNERSHIP_PROTOCOL_DIR").getD
    ("CasAcceptance" / "Strata" : System.FilePath).toString
  let harness ← Harness.ofManifest root manifest
  unless harness.rejected.isEmpty do
    throwError "the complete public primitive registrations did not admit: {harness.rejected}"
  let events ← IO.mkRef #[]
  let harness := enableService { harness with dispatches := some events } trace
  let request ← prepareOperationObservation harness trace original ⟨"op.rings.mul"⟩ #[ring]
  return { trace, harness, request, expected, category := sets, events }

private def operations (events : Array Json) : Array String := events.map fun event =>
  (event.getObjValAs? String "operation").toOption.getD ""

run_elab do
  let some checked := (← checkedComputationDerivations (.operation ⟨"op.rings.mul"⟩))[0]?
    | throwError "the checked complete family is absent"
  let first ← elabTermAndSynthesize (← `(Algebra.NamedRings.ringIntegersMod 5)) none
  let second ← elabTermAndSynthesize (← `(Algebra.NamedRings.ringIntegersMod 7)) none
  let original ← mkAppM ``Algebra.NamedRings.mul #[first]
  let changed ← mkAppM ``Algebra.NamedRings.mul #[second]
  let wrongFamily ← mkAppM ``Algebra.NamedRings.add #[first]
  let accepted ← ComputationDerivation.instantiate checked original original
  unless ← Decide.kernelAccepts (← mkEq accepted.expanded accepted.original) accepted.identity do
    throwError "the exact complete family specialization lost its upstream identity"
  for (application, context, reason) in #[
      (wrongFamily, wrongFamily, "changed its original published family"),
      (original.getAppFn, original, "complete dependent telescope"),
      (changed, original, "does not retain its selected family application")] do
    let rejected ← try
      discard <| ComputationDerivation.instantiate checked application context
      pure false
    catch error => pure (((← error.toMessageData.toString).splitOn reason).length > 1)
    unless rejected do throwError "the derivation changed its full original binding: {reason}"

run_elab do
  -- A self cycle and a changed-argument mutual cycle have no grounded leaves.
  -- These are graph-only metadata controls; they are never published or executed
  -- as mathematical derivations. Production plans are validated upstream.
  let entries ← computationDerivations
  let some exemplar := entries[0]? | throwError "the public plans are absent"
  let first := ComputationRef.operation ⟨"op.graph.first"⟩
  let second := ComputationRef.operation ⟨"op.graph.second"⟩
  let leaf := ComputationRef.operation ⟨"op.graph.leaf"⟩
  let self := { exemplar with target := first, prerequisites := #[first] }
  let forward := { exemplar with target := first, prerequisites := #[second] }
  let backward := { exemplar with target := second, prerequisites := #[first] }
  let exit := { exemplar with target := second, prerequisites := #[leaf] }
  unless (ComputationDerivation.grounded #[self, forward, backward] (fun _ => false)).isEmpty do
    throwError "a cyclic family graph manufactured computational support"
  let supported := ComputationDerivation.grounded #[self, forward, backward, exit] (· == leaf)
  unless supported.contains first && supported.contains second do
    throwError "a grounded alternative was discarded because another rule was cyclic"
  let blocked := ComputationDerivation.grounded #[forward, backward, exit] (· == leaf) #[second]
  if blocked.contains first || blocked.contains second then
    throwError "a blocked recursive expansion manufactured support"

run_elab do
  for kind in #["primitive", "reversed"] do
    let fixed ← fixture kind
    let h := fixed.harness
    try
      -- Ordinary observation, not a private derivation evaluator, owns execution.
      let actual ← realize h fixed.trace "the primitive-only fixed operation" fixed.request.original.value
      unless actual.value == fixed.request.original.value && actual.callableObserved &&
          actual.owner?.isSome do
        throwError "the derived result changed the original formal value or lost its actual owner"
      unless operations (← fixed.events.get) ==
          #["fun.rings.semiring", "fun.semirings.monoid", "op.monoids.mul"] do
        throwError "primitive-only derivation called a target implementation or changed its plan with registration order"
      let records ← h.derivations.get
      unless records.size == 2 && records.all (·.result.isSome) do
        throwError "the nested proved expansion lost its complete receipts"
      for record in records do
        unless record.steps.any (·.owner?.isSome) do
          throwError "the derivation discarded actual owned prerequisite Wires"
        unless ← Decide.kernelAccepts (← inferType record.identity) record.identity do
          throwError "a computational reply replaced the upstream family identity"
      let again ← realize h fixed.trace "the same retained result" fixed.request.original.value
      unless again.json == actual.json && again.owner? == actual.owner? &&
          (← fixed.events.get).size == 3 do
        throwError "reusing the actual derived result replayed its formal recipe"
    finally h.stop

run_elab do
  let fixed ← fixture "alternative"
  let h := fixed.harness
  try
    let actual ← executeOperationObservation h fixed.request
    unless actual.value == fixed.request.original.value && actual.owner?.isSome do
      throwError "the alternative changed the fixed original operation"
    unless operations (← fixed.events.get) == #["fun.rings.semiring", "op.semirings.mul"] do
      throwError "the inapplicable monoid-port plan hid the available proved alternative"
    unless (← h.derivations.get).any (fun record =>
        record.derivation.raw == "derive.rings.mul.semiring" && record.result.isSome) do
      throwError "the successful alternative lost its exact proof-bearing address"
  finally h.stop

run_elab do
  let fixed ← fixture "missing"
  let h := fixed.harness
  try
    let rejected ← try
      discard <| executeOperationObservation h fixed.request
      pure false
    catch error => pure (Exception.stratum? error == some .noImplementation)
    unless rejected && (← fixed.events.get).isEmpty do
      throwError "a missing prerequisite did not produce a gap before dispatch"
    -- Different complete parameters still revisit the same mathematical family.
    -- A value-key-only recursion guard would not cover both requests.
    for modulus in #[5, 7] do
      let changed ← fixture "missing" none modulus
      try
        let rejected ← try
          discard <| executeDerivedRequest changed.harness changed.trace
            #[.operation ⟨"op.rings.mul"⟩] "op.rings.mul" changed.request.input true
          pure false
        catch error => pure (Exception.stratum? error == some .noImplementation &&
          ((← error.toMessageData.toString).splitOn "cyclic computational derivation").length > 1)
        unless rejected && (← changed.events.get).isEmpty do
          throwError "changed recursive arguments bypassed the finite family cycle guard"
      finally changed.harness.stop
  finally h.stop

run_elab do
  let fixed ← fixture "primitive" (some "wrong")
  let h := fixed.harness
  try
    let claim := Claim.homs fixed.request.original.value fixed.expected fixed.category
      (← mkEq fixed.request.original.value fixed.expected) "the fixed operation" "the fixed numeral"
    let .wrong _ ← realizeClaim h fixed.trace claim
      | throwError "a well-framed wrong primitive reply was replaced by the proved formal plan"
    let records ← h.derivations.get
    unless records.any (fun record => record.result.any (·.json == toJson (0 : Nat))) do
      throwError "the wrong actual portable packet disappeared from derivation provenance"
    unless operations (← fixed.events.get) ==
        #["fun.rings.semiring", "fun.semirings.monoid", "op.monoids.mul"] do
      throwError "a wrong answer caused selection of a different proved plan"
  finally h.stop

run_elab do
  for (fault, expected) in #[("malformed", Stratum.malformed), ("unsupported", Stratum.noImplementation)] do
    let fixed ← fixture "primitive" (some fault)
    let h := fixed.harness
    try
      let rejected ← try
        discard <| executeOperationObservation h fixed.request
        pure false
      catch error => pure (Exception.stratum? error == some expected)
      unless rejected && operations (← fixed.events.get) ==
          #["fun.rings.semiring", "fun.semirings.monoid", "op.monoids.mul"] do
        throwError "a primitive failure changed its stratum or tried another proved plan"
      unless (← h.derivations.get).all (fun record =>
          record.derivation.raw != "derive.rings.mul.semiring") do
        throwError "a dispatched failure selected an alternative plan"
    finally h.stop

end
