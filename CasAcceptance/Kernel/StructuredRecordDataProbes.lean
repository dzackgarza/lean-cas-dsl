/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData

/-! Engineering checks of the published record interface. These arbitrary
tokens supply no values, algebraic laws, mathematical answers, or live owners.
Only field framing is checked here; runtime consumers retain session ownership. -/

open Lean Meta Elab Term CasCatalogue

run_elab do
  let opaqueField := fun (token : String) => Json.mkObj
    [("ctor", toJson "opaqueData"), ("args", Json.arr #[toJson token])]
  let additive := Json.arr #[opaqueField "add", opaqueField "zero", opaqueField "nsmul"]
  let multiplicative := Json.arr #[opaqueField "mul", opaqueField "one", opaqueField "npow"]
  let semiring := Json.arr #[additive, multiplicative, opaqueField "natCast"]
  let packet := Json.arr #[opaqueField "carrier", semiring]
  let formal ← elabTermAndSynthesize (← `(SemiRingCat.of ℕ)) none
  let type ← inferType formal
  let check := fun data expected => do
    let result ← ComputationalData.validatePort formal type data
    unless result.isOk == expected do
      throwError "structural record interface control failed: {reprStr result}"
  check packet true
  check (Json.mkObj [("ctor", toJson "valueData"), ("args", Json.arr #[packet])]) true
  check (opaqueField "complete opaque record") true
  -- The outer carrier and every nested operation remain separate data slots.
  check (Json.arr #[semiring]) false
  check (Json.arr #[opaqueField "carrier", semiring, toJson true]) false
  check (Json.arr #[opaqueField "carrier", Json.arr #[additive, multiplicative]]) false
  check (Json.arr #[opaqueField "carrier", Json.arr #[additive, multiplicative, opaqueField ""]]) false
  check (Json.arr #[toJson "private carrier", semiring]) false
  -- Ring's published parent record is still complete, with its five data fields.
  let ring ← elabTermAndSynthesize (← `(RingCat.of ℤ)) none
  let ringData := Json.arr #[opaqueField "ring carrier", Json.arr
    #[semiring, opaqueField "neg", opaqueField "sub", opaqueField "zsmul", opaqueField "intCast"]]
  unless (← ComputationalData.validatePort ring (← inferType ring) ringData).isOk do
    throwError "a complete released ring record was rejected"
  let wrong := Json.arr #[opaqueField "ring carrier", semiring]
  if (← ComputationalData.validatePort ring (← inferType ring) wrong).isOk then
    throwError "a semiring record silently supplied the additional ring data"
  logInfo "published structural record framing and malformed controls checked"

-- Equal bytes and equal actual formal fields do not identify their occurrences.
-- The selected action is inspected only on a fresh symbolic receiver.
run_elab do
  let type ← elabTermAndSynthesize (← `(Nat × (Nat × Nat))) none
  let plan ← withLocalDeclD `receiver type fun receiver => do
    let left ← mkProjection receiver `fst
    let right ← mkProjection receiver `snd
    let last ← mkProjection right `snd
    let target ← mkAppM ``Prod.mk #[last, left]
    let some plan ← ComputationalData.recordProjectionPlan? receiver target
      | throwError "a structural record action lost its selected projection plan"
    if (← ComputationalData.recordProjectionPlan? receiver (mkNatLit 7)).isSome then
      throwError "a fixed actual value was treated as a symbolic record projection"
    return plan
  let bytes := Json.mkObj [("ctor", toJson "opaqueData"), ("args", Json.arr #[toJson "same"])]
  let first := DataOwnership.Data.capture bytes ("first-supplier", 31)
  let middle := DataOwnership.Data.capture bytes ("middle-supplier", 32)
  let last := DataOwnership.Data.capture bytes ("last-supplier", 33)
  let actual := DataOwnership.Data.array #[first, DataOwnership.Data.array #[middle, last]]
  let some result := plan.apply? actual
    | throwError "a complete nested record could not supply its declared fields"
  unless result == DataOwnership.Data.array #[last, first] && result.validate.isOk do
    throwError "structural record projection changed an occurrence or its original supplier"
  let wrapped : DataOwnership.Data := {
    json := Json.mkObj [("ctor", toJson "valueData"), ("args", Json.arr #[actual.json])]
    ownership := DataOwnership.prefix #[.field "args", .index 0] actual.ownership }
  unless plan.apply? wrapped == some result do
    throwError "the public inline envelope changed structural projection ownership"
  if (plan.apply? first).isSome ||
      (plan.apply? (DataOwnership.Data.array #[first, middle, last])).isSome then
    throwError "unexposed or malformed fields supplied a structural projection"
  let wrapperType ← elabTermAndSynthesize (← `(ULift Nat)) none
  let oneField ← withLocalDeclD `receiver wrapperType fun receiver => do
    ComputationalData.recordProjectionPlan? receiver (← mkProjection receiver `down)
  let some oneField := oneField | throwError "the declared single field was not read"
  if (oneField.apply? first).isSome then
    throwError "a whole opaque record was opened through single-field elision"
  unless (oneField.apply? { json := toJson (11 : Nat) }).map (·.json) == some (toJson (11 : Nat)) do
    throwError "a transparent single-field record lost its published elision"
  logInfo "symbolic record action and exact occurrence projection controls checked"
