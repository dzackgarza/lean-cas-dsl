/-
Round-trip proof for the wire codec.

The property that matters is not "decoding usually works": it is that a frame
which does not carry the promised value produces an error instead of a
plausible-looking value. A codec that repairs frames turns a backend defect
into a wrong CAS answer, which nothing downstream can detect.
-/
import CasDsl.Codec

namespace CasDslTests.Codec

open Lean (Json)
open CasDsl

private def roundTrips (v : Value) : Bool :=
  match CasDsl.Codec.valueFromJson (CasDsl.Codec.valueToJson v) with
  | .ok v' => v' == v
  | .error _ => false

private def domainRoundTrips (d : Domain) : Bool :=
  match CasDsl.Codec.domainFromJson (CasDsl.Codec.domainToJson d) with
  | .ok d' => d' == d
  | .error _ => false

private def rejects (j : Json) : Bool :=
  match CasDsl.Codec.valueFromJson j with
  | .ok _ => false
  | .error _ => true

/-- One of every `Value` constructor, including an integer far past 64 bits
(the reason magnitudes travel as decimal strings). -/
private def samples : Array Value := #[
  .int 0,
  .int (-123456789012345678901234567890),
  .rat (mkRat 3 4),
  .rat (mkRat (-7) 2),
  .mod 6 4,
  .poly .rat #[.rat (mkRat 1 2), .int 0, .rat 3],
  .mat 2 .rat #[#[.rat 1, .rat 2], #[.rat (mkRat 3 2), .rat (mkRat (-1) 2)]],
  .factorization (.int (-1)) #[(.int 2, 2), (.int 3, 1)] .int,
  .idealV #[.int 6] .int,
  .cardinal (.finite 5),
  .cardinal .countablyInfinite,
  .bool true,
  .func .real .real `t (.poly .int #[.int 1, .int 0, .int 1])]

private def domains : Array Domain :=
  #[.nat, .int, .rat, .real, .mod 7, .poly .rat, .matrix 3 (.poly .int),
    .funcs .real .real]

#guard samples.all roundTrips
#guard domains.all domainRoundTrips

-- Malformed frames: a non-decimal magnitude, a zero denominator, a matrix
-- whose declared size contradicts its rows, and unknown/ill-typed tags.
#guard rejects (Json.mkObj [("t", "int"), ("v", "twelve")])
#guard rejects (Json.mkObj [("t", "rat"), ("num", "1"), ("den", "0")])
#guard rejects (Json.mkObj
  [("t", "mat"), ("n", (2 : Nat)), ("entry", Json.mkObj [("d", "rat")]),
   ("rows", Json.arr #[Json.arr #[Json.mkObj [("t", "int"), ("v", "1")]]])])
#guard rejects (Json.mkObj [("t", "quaternion"), ("v", "1")])
#guard rejects (Json.str "not an object")
-- a function whose binder is empty is not a function: `Name.mkSimple ""` would
-- decode to the anonymous name and render as `↦ …`
#guard rejects (Json.mkObj
  [("t", "func"), ("src", Json.mkObj [("d", "real")]),
   ("tgt", Json.mkObj [("d", "real")]), ("binder", ""),
   ("body", Json.mkObj [("t", "int"), ("v", "1")])])

end CasDslTests.Codec
