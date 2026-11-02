module

import CasCatalogue.ComputationalData
meta import CasCatalogue.ComputationalData

open Lean Meta Elab Term Command
open CasCatalogue

run_cmd liftTermElabM do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let rational (numerator : Int) (denominator : Nat) :=
    Json.arr #[toJson numerator, toJson denominator]
  let singleton (value : Json) := node "finiteGraph" #[
    Json.arr #[toJson (0 : Nat)], Json.arr #[Json.arr #[toJson (0 : Nat), value]]]
  let ownedValue :=  node "opaqueData" #[toJson "original-owned-numerator"]
  let partlyOpaque := Json.arr #[ownedValue, toJson (7 : Nat)]
  let formal ← elabTermAndSynthesize (← `(fun (_ : Fin 1) => (0 : Rat))) none
  let nested ← elabTermAndSynthesize (← `(fun (_ : Fin 1) (_ : Fin 1) => (0 : Rat))) none
  let listFormal ← elabTermAndSynthesize (← `(fun (_ : Fin 1) => ([] : List Rat))) none
  let cases := #[
    ("reduced rational graph", formal, singleton (rational (-3) 7), true),
    ("zero denominator graph", formal, singleton (rational 1 0), false),
    ("unreduced rational graph", formal, singleton (rational 2 4), false),
    ("wrapped invalid rational graph", formal,
      singleton (node "valueData" #[rational 1 0]), false),
    ("partly opaque rational graph", formal, singleton partlyOpaque, true),
    ("whole opaque rational graph", formal, singleton ownedValue, true),
    ("reduced nested rational graph", nested, singleton (singleton (rational 3 7)), true),
    ("zero denominator nested graph", nested, singleton (singleton (rational 1 0)), false),
    ("unreduced nested graph", nested, singleton (singleton (rational 2 4)), false),
    ("partly opaque nested graph", nested, singleton (singleton partlyOpaque), true),
    ("reduced rational list graph", listFormal, singleton (Json.arr #[rational 3 7]), true),
    ("unreduced rational list graph", listFormal, singleton (Json.arr #[rational 2 4]), false),
    ("partly opaque rational list graph", listFormal, singleton (Json.arr #[partlyOpaque]), true)]
  let mut failures : Nat := 0
  for (name, value, data, expected) in cases do
    let result ← ComputationalData.validatePort value (← inferType value) data
    logInfo m!"{name}: accepted={result.isOk}, required={expected}"
    if result.isOk != expected then failures := failures + 1
  unless failures == 0 do
    throwError "{failures} nested scalar representation constraints were not enforced"
