/-
Wire codec: `Value` / `Domain` ↔ backend JSON (DESIGN.md §The port).

Integers and rational components travel as decimal STRINGS — a backend
factorization of a 200-digit integer must survive the wire, and JSON numbers
are not a bignum transport. Structural counts (a modulus, a matrix size, a
multiplicity) are JSON numbers: they index the presentation, they are not
computed magnitudes.

Decoding never falls back to a default value. A frame that does not carry the
value the caller was promised is a protocol failure with a precise message; a
"reasonable guess" here would launder a backend bug into a wrong CAS answer.
-/
import Lean
import CasDsl.Value

namespace CasDsl.Codec

open Lean (Json toJson)

/-! ## Encoding -/

partial def domainToJson : Domain → Json
  | .nat => Json.mkObj [("d", "nat")]
  | .int => Json.mkObj [("d", "int")]
  | .rat => Json.mkObj [("d", "rat")]
  | .mod n => Json.mkObj [("d", "mod"), ("n", toJson n)]
  | .poly c => Json.mkObj [("d", "poly"), ("coeff", domainToJson c)]
  | .matrix n e =>
      Json.mkObj [("d", "matrix"), ("n", toJson n), ("entry", domainToJson e)]

private def cardinalToJson : Cardinality → Json
  | .finite n => Json.mkObj [("t", "cardinal"), ("v", "finite"), ("n", toJson n)]
  | .countablyInfinite => Json.mkObj [("t", "cardinal"), ("v", "countably_infinite")]

partial def valueToJson : Value → Json
  | .int z => Json.mkObj [("t", "int"), ("v", toString z)]
  | .rat q =>
      Json.mkObj [("t", "rat"), ("num", toString q.num), ("den", toString q.den)]
  | .mod n v => Json.mkObj [("t", "mod"), ("n", toJson n), ("v", toJson v)]
  | .poly c coeffs =>
      Json.mkObj
        [("t", "poly"), ("coeff", domainToJson c),
         ("coeffs", Json.arr (coeffs.map valueToJson))]
  | .mat n e rows =>
      Json.mkObj
        [("t", "mat"), ("n", toJson n), ("entry", domainToJson e),
         ("rows", Json.arr (rows.map fun r => Json.arr (r.map valueToJson)))]
  | .factorization unit factors dom =>
      Json.mkObj
        [("t", "factorization"), ("unit", valueToJson unit),
         ("factors",
           Json.arr (factors.map fun (f, m) => Json.arr #[valueToJson f, toJson m])),
         ("dom", domainToJson dom)]
  | .idealV gens ring =>
      Json.mkObj
        [("t", "ideal"), ("gens", Json.arr (gens.map valueToJson)),
         ("ring", domainToJson ring)]
  | .cardinal c => cardinalToJson c
  | .bool b => Json.mkObj [("t", "bool"), ("v", Json.bool b)]

/-! ## Decoding -/

private def field (j : Json) (k : String) : Except String Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{k}' in {j.compress}"

private def strField (j : Json) (k : String) : Except String String := do
  match (← field j k).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{k}' must be a string in {j.compress}"

private def natField (j : Json) (k : String) : Except String Nat := do
  match (← field j k).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{k}' must be a natural number in {j.compress}"

private def arrField (j : Json) (k : String) : Except String (Array Json) := do
  match (← field j k).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field '{k}' must be an array in {j.compress}"

private def intField (j : Json) (k : String) : Except String Int := do
  let s ← strField j k
  match s.toInt? with
  | some z => .ok z
  | none => .error s!"field '{k}' is not a decimal integer: {repr s}"

partial def domainFromJson (j : Json) : Except String Domain := do
  match ← strField j "d" with
  | "nat" => return .nat
  | "int" => return .int
  | "rat" => return .rat
  | "mod" => return .mod (← natField j "n")
  | "poly" => return .poly (← domainFromJson (← field j "coeff"))
  | "matrix" => return .matrix (← natField j "n") (← domainFromJson (← field j "entry"))
  | other => .error s!"unknown domain tag {repr other} in {j.compress}"

private def cardinalFromJson (j : Json) : Except String Cardinality := do
  match ← strField j "v" with
  | "finite" => return .finite (← natField j "n")
  | "countably_infinite" => return .countablyInfinite
  | other => .error s!"unknown cardinality tag {repr other} in {j.compress}"

partial def valueFromJson (j : Json) : Except String Value := do
  match ← strField j "t" with
  | "int" => return .int (← intField j "v")
  | "rat" =>
      let num ← intField j "num"
      let den ← intField j "den"
      if den ≤ 0 then
        .error s!"rational denominator must be positive in {j.compress}"
      else
        return .rat (mkRat num den.toNat)
  | "mod" => return .mod (← natField j "n") (← natField j "v")
  | "poly" =>
      let coeff ← domainFromJson (← field j "coeff")
      let coeffs ← (← arrField j "coeffs").mapM valueFromJson
      return .poly coeff coeffs
  | "mat" =>
      let n ← natField j "n"
      let entry ← domainFromJson (← field j "entry")
      let rows ← (← arrField j "rows").mapM fun row =>
        match row.getArr? with
        | .ok cells => cells.mapM valueFromJson
        | .error _ => .error s!"matrix row must be an array in {j.compress}"
      if rows.size != n || rows.any (·.size != n) then
        .error s!"matrix is not {n}×{n} in {j.compress}"
      else
        return .mat n entry rows
  | "factorization" =>
      let unit ← valueFromJson (← field j "unit")
      let dom ← domainFromJson (← field j "dom")
      let factors ← (← arrField j "factors").mapM fun pair =>
        match pair.getArr? with
        | .ok #[f, m] => do
            let base ← valueFromJson f
            match m.getNat? with
            | .ok mult => return (base, mult)
            | .error _ => .error s!"factor multiplicity must be a natural number in {j.compress}"
        | _ => .error s!"factor must be a [value, multiplicity] pair in {j.compress}"
      return .factorization unit factors dom
  | "ideal" =>
      let gens ← (← arrField j "gens").mapM valueFromJson
      return .idealV gens (← domainFromJson (← field j "ring"))
  | "cardinal" => return .cardinal (← cardinalFromJson j)
  | "bool" =>
      match (← field j "v").getBool? with
      | .ok b => return .bool b
      | .error _ => .error s!"field 'v' must be a boolean in {j.compress}"
  | other => .error s!"unknown value tag {repr other} in {j.compress}"

end CasDsl.Codec
