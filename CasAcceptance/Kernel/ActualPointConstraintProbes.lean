module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData

open Lean Meta Elab Term Command
open CasCatalogue

/-! Engineering controls for the boundary between actual point data and the
canonical reference's proof-bearing refinement. No mathematical answer is
obtained from the deliberately different supplied data. -/

run_cmd liftTermElabM do
  let rational (numerator : Int) (denominator : Nat) :=
    Json.arr #[toJson numerator, toJson denominator]
  let refined ← elabTermAndSynthesize (← `({q : Rat // q = 0})) none
  let nested ← elabTermAndSynthesize (← `(List (ULift.{0, 0} {q : Rat // q = 0}))) none
  let paired ← elabTermAndSynthesize (← `({q : Rat // q = 0} × Int)) none
  let cases := #[
    ("actual refined rational", refined, rational 3 7, true),
    ("actual refined zero denominator", refined, rational 1 0, false),
    ("actual refined unreduced rational", refined, rational 2 4, false),
    ("nested actual refined rational", nested, Json.arr #[rational 3 7], true),
    ("nested actual zero denominator", nested, Json.arr #[rational 1 0], false),
    ("nested actual unreduced rational", nested, Json.arr #[rational 2 4], false),
    ("paired actual refined rational", paired,
      Json.arr #[rational 3 7, toJson (9 : Int)], true),
    ("paired actual unreduced rational", paired,
      Json.arr #[rational 2 4, toJson (9 : Int)], false)]
  for (label, type, data, accepted) in cases do
    let some schema ← ComputationalData.pointSchema type (actualPoints := true)
      | throwError "{label}: the fixed point-data schema was lost"
    let result ← ComputationalData.validatePoint schema data
    unless result.isOk == accepted do
      throwError "{label}: accepted={result.isOk}, required={accepted}"
  -- Ordinary literals still require their complete closed representation.
  let some literalSchema ← ComputationalData.pointSchema refined
    | throwError "the ordinary refined literal has no schema"
  if (← ComputationalData.validatePoint literalSchema (rational 3 7)).isOk then
    throwError "an ordinary literal bypassed its closed constructor condition"
  if !(← ComputationalData.validatePoint literalSchema (rational 0 1)).isOk then
    throwError "an ordinary valid refined literal was rejected"

run_cmd liftTermElabM do
  let scalar ← elabTermAndSynthesize (← `(Rat)) none
  for actualPoints in #[false, true] do
    let predicate ← mkFreshExprMVar (← mkArrow scalar (mkSort .zero))
    let subtype ← mkAppM ``Subtype #[predicate]
    let some schema ← ComputationalData.pointSchema subtype (actualPoints := actualPoints)
      | throwError "an unresolved predicate hid the fixed rational data field"
    if !(← ComputationalData.validatePoint schema
        (Json.arr #[toJson (3 : Int), toJson (7 : Nat)])).isOk then
      throwError "a fixed rational data field was rejected"
    if (← ComputationalData.validatePoint schema
        (Json.arr #[toJson (2 : Int), toJson (4 : Nat)])).isOk then
      throwError "an unresolved predicate erased rational representation constraints"
    unless (← instantiateMVars predicate) == predicate do
      throwError "point data assigned the unresolved predicate"

run_cmd liftTermElabM do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let graph (data : Json) := node "finiteGraph" #[Json.arr #[toJson (0 : Nat)],
    Json.arr #[Json.arr #[toJson (0 : Nat), data]]]
  let formal ← elabTermAndSynthesize (← `(fun (_ : Fin 1) => (∅ : Finset Int))) none
  let expected ← inferType formal
  if !(← ComputationalData.validatePort formal expected
      (graph (Json.arr #[toJson (1 : Int), toJson (2 : Int)]))).isOk then
    throwError "an ordinary finite-set graph rejected distinct literal elements"
  if (← ComputationalData.validatePort formal expected
      (graph (Json.arr #[toJson (1 : Int), toJson (1 : Int)]))).isOk then
    throwError "an ordinary finite-set graph bypassed its no-duplicates condition"
