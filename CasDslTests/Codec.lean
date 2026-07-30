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
(the reason magnitudes travel as decimal strings) and BOTH signs of radicand
(a sign flip in either direction of the alg codec is a different number). -/
private def samples : Array Value := #[
  .alg 0 1 2,
  .alg (mkRat (-1) 2) (mkRat 1 2) 5,
  .alg 2 (-2) (-1),
  .int 0,
  .int (-123456789012345678901234567890),
  .rat (mkRat 3 4),
  .rat (mkRat (-7) 2),
  .mod 6 4,
  .poly .rat #[.rat (mkRat 1 2), .int 0, .rat 3],
  .mat 2 .rat #[#[.rat 1, .rat 2], #[.rat (mkRat 3 2), .rat (mkRat (-1) 2)]],
  .vec 2 .rat #[.rat 1, .rat 2],
  .vec 3 .int #[.int 1, .int 0, .int 1],
  .factorization (.int (-1)) #[(.int 2, 2), (.int 3, 1)] .int,
  .idealV #[.int 6] .int,
  .setV #[.int 1] .int,
  .setV #[] .rat,
  .progV .nat (.int 0) (.int 2) none,
  .progV .int (.int 1) (.int (-3)) (some (.int (-8))),
  .cardinal (.finite 5),
  .cardinal .countablyInfinite,
  .bool true,
  .func .real .real `t (.poly .int #[.int 1, .int 0, .int 1]),
  -- SPEC.md §Elementary calculus' three symbolic bodies, and the two points
  -- its limits and integrals are taken between. Every node kind appears: a
  -- named function, a named constant, a rational leaf, and each of the five
  -- operations plus unary minus
  .func .real .real `t (.sym (.pow (.const `e) (.var `t))),
  .func .real .real `t (.sym (.app `sin (.var `t))),
  .func .real .real `t (.sym (.div (.num 1) (.var `t))),
  .sym (.const `pi),
  .sym (.const `infinity),
  .sym (.neg (.add (.sub (.mul (.num (mkRat 1 2)) (.var `t))
    (.app `exp (.var `t))) (.num (-3)))),
  -- SPEC.md's own approximation, and one of a rational: the decimal is a
  -- string on the wire like every other magnitude, and both tolerances ride
  -- in the ordinary rational form
  .approx (.alg 0 1 2) "1.4142135623" (mkRat 1 (10 ^ 10)) (mkRat 1 (10 ^ 10)),
  .approx (.rat (mkRat 1 3)) "0.333" (mkRat 1 100) (mkRat 1 1000)]

private def domains : Array Domain :=
  #[.nat, .int, .rat, .real, .complex, .mod 7, .poly .rat,
    .matrix 3 (.poly .int), .funcs .real .real, .poly .complex,
    .vector 2 .rat, .vector 3 .rat, .matrix 2 (.vector 2 .rat)]

#guard samples.all roundTrips
#guard domains.all domainRoundTrips

-- An alg frame is NORMALIZED on the way in: a backend that sends `√8` gets
-- the `2√2` it denotes, so a decoded surd obeys the same invariant a computed
-- one does and compares equal to it
#guard (CasDsl.Codec.valueFromJson (Json.mkObj
  [("t", "alg"), ("a", CasDsl.Codec.valueToJson (.rat 0)),
   ("b", CasDsl.Codec.valueToJson (.rat 1)), ("d", "8")])).toOption
  == some (Value.alg 0 2 2)
-- …and a frame whose radical vanishes is the RATIONAL it denotes
#guard (CasDsl.Codec.valueFromJson (Json.mkObj
  [("t", "alg"), ("a", CasDsl.Codec.valueToJson (.rat 3)),
   ("b", CasDsl.Codec.valueToJson (.rat 0)), ("d", "5")])).toOption
  == some (Value.int 3)

/-! ### The symbolic vocabulary is CLOSED at the wire too

A name is checked on the way IN as well as on the way out. Without that, a
frame naming `arctan` would become a symbolic body this surface never agreed
to present — and the whole point of a typed expression tree rather than a
source string is that neither end gets to widen the language unilaterally. -/

private def symFrame (node : Json) : Json := Json.mkObj [("t", "sym"), ("e", node)]

#guard rejects (symFrame (Json.mkObj [("s", "app"), ("f", "arctan"),
  ("a", Json.mkObj [("s", "var"), ("n", "t")])]))
#guard rejects (symFrame (Json.mkObj [("s", "const"), ("n", "gamma")]))
-- …and the vocabulary's own names decode
#guard (CasDsl.Codec.valueFromJson (symFrame (Json.mkObj
  [("s", "app"), ("f", "sin"), ("a", Json.mkObj [("s", "var"), ("n", "t")])]))).toOption
  == some (Value.sym (.app `sin (.var `t)))

/-! ### An approximation frame is CHECKED on the way in

The decode goes through `Value.mkApprox`, so the certificate is verified at the
boundary: a backend that returns a wrong digit, a bound it did not achieve, or
a bound that does not meet what was asked cannot get a value into the session.
This is the one place a lying backend is caught, so each way of lying gets its
own frame. -/

private def approxFrame (exact : Value) (decimal : String) (eps achieved : Rat) : Json :=
  Json.mkObj
    [("t", "approx"), ("exact", CasDsl.Codec.valueToJson exact),
     ("decimal", Json.str decimal),
     ("eps", CasDsl.Codec.valueToJson (.rat eps)),
     ("achieved", CasDsl.Codec.valueToJson (.rat achieved))]

private def accepts (j : Json) : Bool := !rejects j

-- the honest frame: √2 to ten digits, within the tenth power of ten
#guard accepts (approxFrame (.alg 0 1 2) "1.4142135623" (mkRat 1 (10 ^ 10)) (mkRat 1 (10 ^ 10)))
-- what is checked is the BOUND, not a spelling: the rounded tenth digit meets
-- it too (√2 = 1.41421356237…), so the backend's choice between truncating
-- and rounding is its own — the certificate is what it must satisfy
#guard accepts (approxFrame (.alg 0 1 2) "1.4142135624" (mkRat 1 (10 ^ 10)) (mkRat 1 (10 ^ 10)))
-- …and a digit that is WRONG at that bound is refused: 1.4142145623 misses √2
-- by about 10^-6, and a digit dropped from the end misses it by 4·10^-10
#guard rejects (approxFrame (.alg 0 1 2) "1.4142145623" (mkRat 1 (10 ^ 10)) (mkRat 1 (10 ^ 10)))
#guard rejects (approxFrame (.alg 0 1 2) "1.414213562" (mkRat 1 (10 ^ 10)) (mkRat 1 (10 ^ 10)))
-- a bound the backend did not achieve (the decimal is only good to 10^-3)
#guard rejects (approxFrame (.alg 0 1 2) "1.414" (mkRat 1 100) (mkRat 1 (10 ^ 10)))
-- …and a bound that does not meet what was REQUESTED, however true it is
#guard rejects (approxFrame (.alg 0 1 2) "1.414" (mkRat 1 (10 ^ 10)) (mkRat 1 1000))
-- a non-positive bound is not a certificate
#guard rejects (approxFrame (.rat (mkRat 1 2)) "0.5" (mkRat 1 10) 0)
-- a value with an imaginary part has no decimal presentation here
#guard rejects (approxFrame (.alg 2 2 (-1)) "2.828" (mkRat 1 100) (mkRat 1 100))
-- and the decimal must BE a decimal
#guard rejects (approxFrame (.rat (mkRat 1 2)) "0.5.0" (mkRat 1 10) (mkRat 1 10))
#guard rejects (approxFrame (.rat (mkRat 1 2)) "1/2" (mkRat 1 10) (mkRat 1 10))
#guard rejects (approxFrame (.rat (mkRat 1 2)) "" (mkRat 1 10) (mkRat 1 10))

-- Malformed frames: a non-decimal magnitude, a zero denominator, a matrix
-- whose declared size contradicts its rows, and unknown/ill-typed tags.
#guard rejects (Json.mkObj [("t", "int"), ("v", "twelve")])
#guard rejects (Json.mkObj [("t", "rat"), ("num", "1"), ("den", "0")])
#guard rejects (Json.mkObj
  [("t", "mat"), ("n", (2 : Nat)), ("entry", Json.mkObj [("d", "rat")]),
   ("rows", Json.arr #[Json.arr #[Json.mkObj [("t", "int"), ("v", "1")]]])])
-- …and a vector whose declared LENGTH contradicts its components: the length
-- is the whole shape, and matrix application is checked against exactly it
#guard rejects (Json.mkObj
  [("t", "vec"), ("n", (3 : Nat)), ("entry", Json.mkObj [("d", "rat")]),
   ("comps", Json.arr #[Json.mkObj [("t", "int"), ("v", "1")]])])
#guard rejects (Json.mkObj [("t", "quaternion"), ("v", "1")])
#guard rejects (Json.str "not an object")
-- a function whose binder is empty is not a function: `Name.mkSimple ""` would
-- decode to the anonymous name and render as `↦ …`
#guard rejects (Json.mkObj
  [("t", "func"), ("src", Json.mkObj [("d", "real")]),
   ("tgt", Json.mkObj [("d", "real")]), ("binder", ""),
   ("body", Json.mkObj [("t", "int"), ("v", "1")])])

end CasDslTests.Codec
