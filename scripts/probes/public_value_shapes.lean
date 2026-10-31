/- Engineering checks of published literal/callable representations, without backend answers. -/
module
import CasCatalogue.ComputationalData
import LeanCategories.Catalogue.Semantics
meta import CasCatalogue.ComputationalData
meta import LeanCategories.Catalogue.Semantics

open Lean Meta Elab Term CasCatalogue

run_elab do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let rational ← elabTermAndSynthesize (← `((0 : ℚ))) none
  for (data, accepted) in #[(Json.arr #[toJson (-3 : Int), toJson (7 : Nat)], true),
      (Json.arr #[toJson (1 : Int), toJson (0 : Nat)], false),
      (Json.arr #[toJson (2 : Int), toJson (4 : Nat)], false)] do
    let outcome ← ComputationalData.validatePort rational (← inferType rational) data
    unless outcome.isOk == accepted do throwError "rational representation framing: {repr outcome}"
  let degree ← elabTermAndSynthesize (← `((⊥ : WithBot ℕ))) none
  for (data, accepted) in #[(node "none" #[], true),
      (node "some" #[toJson (8 : Nat)], true),
      (node "some" #[], false), (node "none" #[toJson (0 : Nat)], false)] do
    let outcome ← ComputationalData.validatePort degree (← inferType degree) data
    unless outcome.isOk == accepted do throwError "bottom/natural framing: {repr outcome}"
  logInfo "PASS: reduced rational and WithBot Nat representations, including malformed records"

run_elab do
  let matrix ← elabTermAndSynthesize (← `(fun (_ : Fin 2) (_ : Fin 2) => (0 : ℚ))) none
  let rational := Json.arr #[toJson (1 : Int), toJson (2 : Nat)]
  let row := Json.arr #[Json.arr #[toJson (0 : Nat), rational],
    Json.arr #[toJson (1 : Nat), rational]]
  let valid := Json.arr #[Json.arr #[toJson (0 : Nat), row],
    Json.arr #[toJson (1 : Nat), row]]
  let incomplete := Json.arr #[Json.arr #[toJson (0 : Nat), Json.arr #[]],
    Json.arr #[toJson (1 : Nat), row]]
  for (data, accepted) in #[(valid, true), (incomplete, false)] do
    let outcome ← ComputationalData.validatePort matrix (← inferType matrix) data
    unless outcome.isOk == accepted do throwError "nested finite matrix framing: {repr outcome}"
  logInfo "PASS: nested finite callable matrix representation and missing-column rejection"

run_elab do
  let node (tag : String) (args : Array Json) :=
    Json.mkObj [("ctor", toJson tag), ("args", Json.arr args)]
  let real := node "obj.sets.reals" #[]
  let realPoint := node "element" #[real, node "numeral" #[toJson (2 : Nat)]]
  let squareRoot := node "point" #[node "compose"
    #[realPoint, node "mor.sets.real_sqrt" #[]]]
  let pi := node "point" #[node "mor.sets.real_pi" #[]]
  let imaginaryUnit := node "point" #[node "mor.sets.complex_i" #[]]
  let complexPoint := node "point" #[node "compose" #[node "element" #[real, pi],
    node "incl.sets.reals_complexes" #[]]]
  let rationalRing := node "obj.commutative_rings.rationals" #[]
  let polynomial := node "obj.sets.polynomials" #[rationalRing]
  let coordinate := node "element" #[polynomial, node "generator" #[]]
  let differential := node "point" #[node "compose" #[coordinate,
    node "mor.sets.kaehler_from_coordinate" #[rationalRing]]]
  let naturals := node "obj.sets.naturals" #[]
  let identity := node "identity" #[naturals, naturals]
  let imagePoint := node "point" #[node "powerObjectMap"
    #[toJson "pow.sets", toJson "image", Json.arr #[naturals, naturals, identity]]]
  for expression in #[squareRoot, pi, imaginaryUnit, complexPoint, differential, imagePoint] do
    if let .error message ← ComputationalData.validateElementExpression expression then
      throwError "a documented point representation failed framing: {message}"
  let divisionAsOperation := node "operationExpression"
    #[toJson "mor.sets.divide", Json.arr #[], Json.arr #[]]
  if (← ComputationalData.validateElementExpression divisionAsOperation).isOk then
    throwError "a morphism address was accepted as an element-operation address"
  for callable in #[node "compose" #[realPoint, node "mor.sets.real_sqrt" #[]],
      node "mediator" #[realPoint, realPoint], node "opaqueData" #[toJson "native infinite callable"]] do
    if let .error message ← ComputationalData.validateCallableData callable then
      throwError "a complete callable representation failed framing: {message}"
  logInfo "PASS: irrational/complex, differential and infinite-image point framing; closed-point compositions and mediators"
