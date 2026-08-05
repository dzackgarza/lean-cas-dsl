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
  | .real => Json.mkObj [("d", "real")]
  | .complex => Json.mkObj [("d", "complex")]
  | .mod n => Json.mkObj [("d", "mod"), ("n", toJson n)]
  | .poly c => Json.mkObj [("d", "poly"), ("coeff", domainToJson c)]
  | .series c => Json.mkObj [("d", "series"), ("coeff", domainToJson c)]
  | .matrix n e =>
      Json.mkObj [("d", "matrix"), ("n", toJson n), ("entry", domainToJson e)]
  | .vector n e =>
      Json.mkObj [("d", "vector"), ("n", toJson n), ("entry", domainToJson e)]
  | .funcs s t =>
      Json.mkObj [("d", "funcs"), ("src", domainToJson s), ("tgt", domainToJson t)]

private def cardinalToJson : Cardinality → Json
  | .finite n => Json.mkObj [("t", "cardinal"), ("v", "finite"), ("n", toJson n)]
  | .countablyInfinite => Json.mkObj [("t", "cardinal"), ("v", "countably_infinite")]

/-- The rational form, named because two encoders write it: a `Value.rat` and
a symbolic expression's numeric leaf. -/
def ratToJson (q : Rat) : Json :=
  Json.mkObj [("t", "rat"), ("num", toString q.num), ("den", toString q.den)]

/-- A symbolic expression on the wire. It is a TYPED TREE, not a source
string: the adapter builds a Sage symbolic expression from these nodes and
never parses anything this side wrote (DESIGN.md decision 2 — the adapter
never receives generated Sage source). Names are checked against the fixed
vocabulary at BOTH ENDS — here on decode and in the adapter's own `dec_sym`
— so neither end can widen the language unilaterally. (The ENCODER writes
only names the surface already accepted, so it needs no check of its own.) -/
partial def symToJson : SymExpr → Json
  | .var n => Json.mkObj [("s", "var"), ("n", Json.str n.toString)]
  | .num q => Json.mkObj [("s", "num"), ("q", ratToJson q)]
  | .const n => Json.mkObj [("s", "const"), ("n", Json.str n.toString)]
  | .app f a =>
      Json.mkObj [("s", "app"), ("f", Json.str f.toString), ("a", symToJson a)]
  | .neg a => Json.mkObj [("s", "neg"), ("a", symToJson a)]
  | .add a b => Json.mkObj [("s", "add"), ("a", symToJson a), ("b", symToJson b)]
  | .sub a b => Json.mkObj [("s", "sub"), ("a", symToJson a), ("b", symToJson b)]
  | .mul a b => Json.mkObj [("s", "mul"), ("a", symToJson a), ("b", symToJson b)]
  | .div a b => Json.mkObj [("s", "div"), ("a", symToJson a), ("b", symToJson b)]
  | .pow a b => Json.mkObj [("s", "pow"), ("a", symToJson a), ("b", symToJson b)]

partial def valueToJson : Value → Json
  | .int z => Json.mkObj [("t", "int"), ("v", toString z)]
  | .rat q => ratToJson q
  | .mod n v => Json.mkObj [("t", "mod"), ("n", toJson n), ("v", toJson v)]
  -- `a + b√d`, with the radicand a decimal string like every other magnitude
  -- on this wire (`a` and `b` ride in the ordinary rational form)
  | .alg a b d =>
      Json.mkObj
        [("t", "alg"), ("a", valueToJson (.rat a)), ("b", valueToJson (.rat b)),
         ("d", Json.str (toString d))]
  -- an approximation: the exact value it is OF, the decimal presenting it, the
  -- REQUESTED tolerance and the bound the backend certified. The decimal is a
  -- string like every other magnitude here, and the two tolerances ride in the
  -- ordinary rational form
  | .approx exact decimal eps achieved =>
      Json.mkObj
        [("t", "approx"), ("exact", valueToJson exact), ("decimal", Json.str decimal),
         ("eps", valueToJson (.rat eps)), ("achieved", valueToJson (.rat achieved))]
  | .poly c coeffs =>
      Json.mkObj
        [("t", "poly"), ("coeff", domainToJson c),
         ("coeffs", Json.arr (coeffs.map valueToJson))]
  | .mat n e rows =>
      Json.mkObj
        [("t", "mat"), ("n", toJson n), ("entry", domainToJson e),
         ("rows", Json.arr (rows.map fun r => Json.arr (r.map valueToJson)))]
  | .vec n e comps =>
      Json.mkObj
        [("t", "vec"), ("n", toJson n), ("entry", domainToJson e),
         ("comps", Json.arr (comps.map valueToJson))]
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
  | .setV elems dom =>
      Json.mkObj
        [("t", "set"), ("elems", Json.arr (elems.map valueToJson)),
         ("dom", domainToJson dom)]
  | .spanV n basis =>
      Json.mkObj
        [("t", "span"), ("n", toJson n), ("basis", Json.arr (basis.map valueToJson))]
  | .progV dom first step last? =>
      Json.mkObj
        [("t", "progression"), ("dom", domainToJson dom),
         ("first", valueToJson first), ("step", valueToJson step),
         ("last", match last? with | some l => valueToJson l | none => Json.null)]
  | .cardinal c => cardinalToJson c
  | .bool b => Json.mkObj [("t", "bool"), ("v", Json.bool b)]
  | .sym e => Json.mkObj [("t", "sym"), ("e", symToJson e)]
  -- a differential 1-form is its coefficient plus the free generator `dx`,
  -- so the frame carries exactly that: no `dx` field, because the generator
  -- is what the TAG means
  | .diff1 c p =>
      Json.mkObj [("t", "diff1"), ("coeff", domainToJson c), ("p", valueToJson p)]
  | .derivation asForm =>
      Json.mkObj [("t", "derivation"), ("as_form", Json.bool asForm)]
  | .cosetV offset kernel =>
      Json.mkObj
        [("t", "coset"), ("offset", valueToJson offset), ("kernel", domainToJson kernel)]
  -- a series carries WHICH reading it is, because that is the claim: a rule
  -- knows every coefficient, terms know exactly the ones they carry
  | .seriesV c (.rule inN) =>
      Json.mkObj
        [("t", "series"), ("coeff", domainToJson c), ("gen", "rule"),
         ("cs", Json.arr (inN.map ratToJson))]
  | .seriesV c (.terms cs) =>
      Json.mkObj
        [("t", "series"), ("coeff", domainToJson c), ("gen", "terms"),
         ("cs", Json.arr (cs.map ratToJson))]
  | .func s t binder body =>
      Json.mkObj
        [("t", "func"), ("src", domainToJson s), ("tgt", domainToJson t),
         ("binder", Json.str binder.toString), ("body", valueToJson body)]
  -- a hom carries the map as written (binders and coefficient rows); the
  -- rows are the DERIVED standard-frame matrix, riding in the ordinary
  -- rational form
  | .hom s t binders rows =>
      Json.mkObj
        [("t", "hom"), ("src", domainToJson s), ("tgt", domainToJson t),
         ("binders", Json.arr (binders.map fun b => Json.str b.toString)),
         ("rows", Json.arr (rows.map fun r => Json.arr (r.map ratToJson)))]

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
  | "real" => return .real
  | "complex" => return .complex
  | "mod" => return .mod (← natField j "n")
  | "poly" => return .poly (← domainFromJson (← field j "coeff"))
  | "series" => return .series (← domainFromJson (← field j "coeff"))
  | "matrix" => return .matrix (← natField j "n") (← domainFromJson (← field j "entry"))
  | "vector" => return .vector (← natField j "n") (← domainFromJson (← field j "entry"))
  | "funcs" =>
      return .funcs (← domainFromJson (← field j "src")) (← domainFromJson (← field j "tgt"))
  | other => .error s!"unknown domain tag {repr other} in {j.compress}"

/-- A name that is IN the fixed vocabulary, or a protocol failure listing it.
This is the DECODE side; the adapter checks the same list on its own decode,
which is what "both ends" means. A frame naming `arctan` would otherwise
become a symbolic body this surface never agreed to present, and the refusal
is what keeps the vocabulary a closed list rather than whatever the two ends
happen to agree on. -/
private def vocabName (j : Json) (k what : String) (allowed : List Lean.Name)
    : Except String Lean.Name := do
  let s ← strField j k
  let n := Lean.Name.mkSimple s
  if allowed.contains n then return n
  else
    .error s!"{repr s} is not one of the {what} CasDsl presents \
({", ".intercalate (allowed.map toString)}) in {j.compress}"

partial def symFromJson (j : Json) : Except String SymExpr := do
  let bin (f : SymExpr → SymExpr → SymExpr) : Except String SymExpr := do
    return f (← symFromJson (← field j "a")) (← symFromJson (← field j "b"))
  match ← strField j "s" with
  | "var" =>
      let s ← strField j "n"
      if s.isEmpty then .error s!"a symbolic variable must be a name in {j.compress}"
      else return .var (Lean.Name.mkSimple s)
  | "num" =>
      let q ← field j "q"
      let num ← intField q "num"
      let den ← intField q "den"
      if den ≤ 0 then
        .error s!"rational denominator must be positive in {j.compress}"
      else return .num (mkRat num den.toNat)
  | "const" => return .const (← vocabName j "n" "named constants" SymExpr.constants)
  | "app" =>
      return .app (← vocabName j "f" "named functions" SymExpr.functions)
        (← symFromJson (← field j "a"))
  | "neg" => return .neg (← symFromJson (← field j "a"))
  | "add" => bin .add
  | "sub" => bin .sub
  | "mul" => bin .mul
  | "div" => bin .div
  | "pow" => bin .pow
  | other => .error s!"unknown symbolic node tag {repr other} in {j.compress}"

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
  | "alg" =>
      -- decoded THROUGH the normalizing constructor: a frame carrying `√8` or
      -- a zero coefficient becomes the value it denotes, so a decoded surd
      -- obeys the same invariant a computed one does
      match ← valueFromJson (← field j "a"), ← valueFromJson (← field j "b") with
      | .rat a, .rat b => Value.mkAlg a b (← intField j "d")
      | a, b => .error s!"an algebraic value needs rational parts, got \
{a.render} and {b.render} in {j.compress}"
  | "approx" =>
      -- decoded THROUGH the checking constructor, exactly as `alg` is decoded
      -- through `mkAlg`: the certificate is verified HERE, at the boundary, so
      -- a decimal that does not present the value it claims to — a backend
      -- returning a wrong digit — cannot enter the session at all
      let exact ← valueFromJson (← field j "exact")
      let decimal ← strField j "decimal"
      match ← valueFromJson (← field j "eps"), ← valueFromJson (← field j "achieved") with
      | .rat eps, .rat achieved => Value.mkApprox exact decimal eps achieved
      | e, a => .error s!"the tolerances of an approximation are rationals, got \
{e.render} and {a.render} in {j.compress}"
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
  | "vec" =>
      let n ← natField j "n"
      let entry ← domainFromJson (← field j "entry")
      let comps ← (← arrField j "comps").mapM valueFromJson
      -- the length is the whole shape of a vector, so a frame whose component
      -- count disagrees with it is a protocol failure rather than a value to
      -- read leniently — matrix application is checked against exactly this
      if comps.size != n then
        .error s!"a vector of length {n} carries {comps.size} components in {j.compress}"
      else
        return .vec n entry comps
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
  | "set" =>
      let elems ← (← arrField j "elems").mapM valueFromJson
      return .setV elems (← domainFromJson (← field j "dom"))
  | "span" =>
      -- decoded THROUGH the normalizing constructor, exactly as `alg` is
      -- decoded through `mkAlg`: a frame carrying a dependent or unreduced
      -- generating set becomes the REDUCED basis it denotes, so a decoded span
      -- compares equal to the same subspace built any other way
      Value.mkSpan (← natField j "n") (← (← arrField j "basis").mapM valueFromJson)
  | "progression" =>
      let lastJ ← field j "last"
      let last? : Option Value ←
        if lastJ.isNull then pure none else Option.some <$> valueFromJson lastJ
      return .progV (← domainFromJson (← field j "dom"))
        (← valueFromJson (← field j "first")) (← valueFromJson (← field j "step")) last?
  | "cardinal" => return .cardinal (← cardinalFromJson j)
  | "func" =>
      let src ← domainFromJson (← field j "src")
      let tgt ← domainFromJson (← field j "tgt")
      let binder ← strField j "binder"
      if binder.isEmpty then
        .error s!"a function's binder must be a name in {j.compress}"
      else
        return .func src tgt (Lean.Name.mkSimple binder) (← valueFromJson (← field j "body"))
  | "hom" =>
      let src ← domainFromJson (← field j "src")
      let tgt ← domainFromJson (← field j "tgt")
      let binders ← (← arrField j "binders").mapM fun b =>
        match b.getStr? with
        | .ok s =>
            if s.isEmpty then .error s!"a hom's binder must be a name in {j.compress}"
            else .ok (Lean.Name.mkSimple s)
        | .error _ => .error s!"a hom's binders must be strings in {j.compress}"
      let rows ← (← arrField j "rows").mapM fun r =>
        match r.getArr? with
        | .ok es => es.mapM fun q => do
            let num ← intField q "num"
            let den ← intField q "den"
            if den ≤ 0 then .error s!"rational denominator must be positive in {j.compress}"
            else return mkRat num den.toNat
        | .error _ => .error s!"a hom's rows must be arrays in {j.compress}"
      return .hom src tgt binders rows
  | "bool" =>
      match (← field j "v").getBool? with
      | .ok b => return .bool b
      | .error _ => .error s!"field 'v' must be a boolean in {j.compress}"
  | "sym" => return .sym (← symFromJson (← field j "e"))
  | "diff1" =>
      return .diff1 (← domainFromJson (← field j "coeff")) (← valueFromJson (← field j "p"))
  | "derivation" =>
      match (← field j "as_form").getBool? with
      | .ok b => return .derivation b
      | .error _ => .error s!"field 'as_form' must be a boolean in {j.compress}"
  | "series" =>
      let c ← domainFromJson (← field j "coeff")
      let cs ← (← arrField j "cs").mapM fun q => do
        let num ← intField q "num"
        let den ← intField q "den"
        if den ≤ 0 then .error s!"rational denominator must be positive in {j.compress}"
        else return mkRat num den.toNat
      match ← strField j "gen" with
      | "rule" => return .seriesV c (.rule cs)
      | "terms" => return .seriesV c (.terms cs)
      | other => .error s!"unknown series generator {repr other} in {j.compress}"
  | "coset" =>
      -- decoded THROUGH the canonicalizing constructor, exactly as `alg` is
      -- decoded through `mkAlg` and `span` through `mkSpan`: a frame carrying
      -- any representative of the coset becomes the one with constant term
      -- zero, so a decoded coset compares equal to the same coset computed here
      let (offset, kernel) ← Value.mkCoset (← valueFromJson (← field j "offset"))
        (← domainFromJson (← field j "kernel"))
      return .cosetV offset kernel
  | other => .error s!"unknown value tag {repr other} in {j.compress}"

end CasDsl.Codec
