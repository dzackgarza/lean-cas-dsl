module

import CasCatalogue.ElementData
meta import CasCatalogue.ElementData

open Lean Meta Elab Command Term
open CasCatalogue CasCatalogue.Language

/- Engineering checks only: decode typed data and reject malformed envelopes. No mathematical
acceptance answer is inferred from these implementation checks. -/
run_cmd liftTermElabM do
  let state ← registryState
  let selected ← (object state "ZMod" #[.nat 5] none).run {}
  let .object _ _ (some (entry, _)) _ _ := selected
    | throwError "probe selected object lost its registered identity"
  let descriptor := Json.mkObj [("ctor", toJson entry.id.raw),
    ("args", Json.arr #[toJson (5 : Nat)])]
  let type ← (semanticObject selected).run {}
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let envelope (object data : Json) := node "element" #[object, data]
  let numeral := node "numeral" #[toJson (2 : Nat)]
  let arithmetic := node "add" #[numeral, node "neg" #[node "mul" #[numeral, numeral]]]
  for data in #[numeral, arithmetic] do
    let some (.ok point) ← ElementData.decode selected descriptor type (envelope descriptor data)
      | throwError "generic closed element arithmetic failed to decode"
    unless ← isTypeCorrect point do throwError "decoded element is not type correct"
  let wrongParameter := Json.mkObj [("ctor", toJson entry.id.raw),
    ("args", Json.arr #[toJson (7 : Nat)])]
  let wrongObject := Json.mkObj [("ctor", toJson "other-object"),
    ("args", Json.arr #[toJson (5 : Nat)])]
  for json in #[envelope wrongParameter numeral, envelope wrongObject numeral,
      envelope descriptor (node "numeral" #[toJson (-1 : Int)]),
      envelope descriptor (node "add" #[numeral]),
      envelope descriptor (node "arbitrary-declaration" #[]), node "element" #[]] do
    let some (.error _) ← ElementData.decode selected descriptor type json
      | throwError "malformed or incorrectly selected element data was accepted"
  let .none ← ElementData.decode selected descriptor type numeral
    | throwError "an unrecognized envelope was captured by element decoding"
  let polynomial ← (eval {} (← `(cas_term| ℤ[x]))).run {}
  let .element generator _ ← (ElementData.read polynomial (node "generator" #[])).run {}
    | throwError "registered generator data did not produce an element"
  unless ← isTypeCorrect generator do throwError "registered generator data is not typed"
