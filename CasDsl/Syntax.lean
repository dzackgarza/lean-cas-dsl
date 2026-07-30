/-
The surface syntax: a `casTerm` category plus command elaborators. Nothing
outside Lean interprets any of this — notebook cells reach the worker
verbatim.

Parser notes (hard-won, load-bearing):
- The `let` COMMAND is declared LAST in this file. Declared earlier it
  shadows `let x := e` inside every subsequent `do` block in this module at
  parse time (the nbdsl lore); every elaborator body below the command
  block is therefore a single call into a helper defined above it.
- Commands end at newline; a `.` terminator would conflict with field
  projection.
- `n.factor` lexes as ONE hierarchical identifier — Lean's `ident` parser
  eats the dot. So `e.m(args)` is parsed as a plain call on a dotted name
  and split into receiver/method here, which is also why the receiver of a
  method call is a name rather than an arbitrary expression.
- `noWs` before `(` and `[` is what keeps a bare-expression cell from
  swallowing the next line: without it, `X.cardinality()` followed by
  `[1, 2; 3, 4]` parses as one indexing expression.
- Implicit multiplication is `numeral noWs <atom-or-power>` (`2x`, `3x²`),
  and the `noWs` is what carries the same guarantee: `assert 2 + 3 = 5`
  followed by a line starting with an identifier must not become a product.
- `...` is declared as a token; `..` already is one, and the tokenizer's
  longest match keeps them apart.
-/
import CasDsl.Eval
import CasDsl.Codec
import Worker.Output

namespace CasDsl

open Lean Elab Command
open Worker (emitOutput)

/-! ## The `casTerm` category

Precedence ladder (Lean's own conventions, restricted to what a CAS surface
needs): `+ -` at 65, `* /` at 70, unary `-` at 75, `^` at 80 (right
associative), atoms and postfix chains at max. -/

declare_syntax_cat casTerm
declare_syntax_cat casSetItem
declare_syntax_cat casRel

syntax:max (name := casNatDom) "ℕ" : casTerm
syntax:max (name := casIntDom) "ℤ" : casTerm
syntax:max (name := casRatDom) "ℚ" : casTerm
syntax:max (name := casRealDom) "ℝ" : casTerm
syntax:max (name := casComplexDom) "ℂ" : casTerm
syntax:max (name := casAleph) "ℵ₀" : casTerm
/-- SPEC.md's `lim_{t → ∞}`. A TOKEN rather than a name, because `∞` is not
an identifier character — `π` and `e` are, so those two are the ordinary
constants `Eval.constantValue?` carries. All three denote the same kind of
thing: a symbolic constant, with no arithmetic and no domain. -/
syntax:max (name := casInfinity) "∞" : casTerm
/-- Implicit multiplication — SPEC.md's `2x`, `2n`, `3x²`, `2√2`.

The right operand is an ATOM POSSIBLY RAISED TO A POWER (`casTerm:76`), and
that precedence is the whole content of the fix for #26: 76 admits the two
power productions (80) and every atom, so the exponent binds TIGHTER than
the juxtaposition — `3x²` is `3·(x²)` and `2x^2` is `2·(x²)`, which is the
universal convention. It was `numeral noWs ident` at `max` before, which put
the whole product inside the superscript's base: `3x²` parsed as `(3x)² =
9x²`, and SPEC.md §Differentials' own `f := x ↦ 3x² + x + 1` therefore bound
a polynomial nobody wrote — a silent wrong answer, which is the one outcome
this system forbids.

76 rather than 71 is also load-bearing: it EXCLUDES unary minus and `∘`
(both 75), so `3-x` is the subtraction it always was rather than `3·(-x)`.
`noWs` is unchanged, and is still what keeps a numeral ending one line from
swallowing the line below.

The BARS are the one atom this may not take, and the guard is the same kind
`notFollowedBy(&"and")` is: `|` is a DELIMITER, not an operand, so without
this `|3|` reads its opening bar as the start of a factor and runs off the
end of the cell looking for the closing one. (`2|A|` — a numeral against a
cardinality — is nothing SPEC.md writes, and the bars already name a method
rather than a value.) -/
syntax:max (name := casImplMul) num noWs notFollowedBy("|") casTerm:76 : casTerm
syntax:max (name := casNum) num : casTerm
syntax:max (name := casIdent) ident : casTerm
syntax:max (name := casParen) "(" casTerm ")" : casTerm

/-- SPEC.md's vectors — `(1, 2)`, `(1, 0, 1)`. TWO components at least, which
is what keeps it disjoint from the parenthesized term above; the `noWs` on
`casApply` is what keeps a tuple written after a name from being read as a
call's argument list. -/
syntax:max (name := casTuple) "(" casTerm ", " casTerm,+ ")" : casTerm
syntax:max (name := casSet) "{" casSetItem,* "}" : casTerm

syntax casRow := casTerm,+
syntax:max (name := casMat) "[" sepBy1(casRow, "; ") "]" : casTerm

/-! SPEC.md writes comprehensions two ways — `{x ∈ X | P(x)}` and
`{f(x) | x ∈ X, P(x)}` — and both binder spellings, `∈` and the ASCII `in`.
The two shapes are told apart by what stands before the bar; a set literal
has no bar at all, so the three productions do not overlap. -/

syntax casBinderIn := " ∈ " <|> " in "

syntax:max (name := casFilterSet)
  "{" ident casBinderIn casTerm " | " casTerm "}" : casTerm

syntax:max (name := casImageSet)
  "{" casTerm " | " ident casBinderIn casTerm ("," casTerm)? "}" : casTerm

/-- SPEC.md's `{a ∈ ℂ | r(a) = 0}` — the ROOT SET of a polynomial, and a
production of its own rather than a guarded comprehension.

`=` is the assertion relation in this surface and is deliberately not a
term-level comparison (one symbol, one meaning), so an EQUATION cannot appear
in a guard at all. It appears here, inside a production that means exactly one
thing: the set of solutions of `p(x) = q(x)` in the index domain, which is the
`roots` method the surface already has. Nothing about `=` elsewhere changes. -/
syntax:max (name := casRootSet)
  "{" ident casBinderIn casTerm " | " casTerm " = " casTerm "}" : casTerm

/-- SPEC.md's `∑_{a ∈ roots} a` and `∏_{a ∈ roots} a`. The body is an ATOM,
so `= 0` on the right of an assertion ends it exactly where the mathematician
put it; a wider body is parenthesized. -/
syntax:max (name := casBigSum)
  "∑" noWs "_" noWs "{" ident casBinderIn casTerm "}" casTerm:max : casTerm
syntax:max (name := casBigProd)
  "∏" noWs "_" noWs "{" ident casBinderIn casTerm "}" casTerm:max : casTerm

syntax (name := casEllipsis) "..." : casSetItem
syntax (name := casSetElem) casTerm : casSetItem

syntax:max (name := casIndex) casTerm:max noWs "[" casTerm "]" : casTerm
syntax:max (name := casApply) casTerm:max noWs "(" casTerm,* ")" : casTerm

/-! SPEC.md §Vectors and matrices writes the inverse `M⁻¹` and applies a
matrix to a vector by JUXTAPOSITION — `M⁻¹ b`, `M v` — alongside the explicit
`M*v`. Both are spellings of operations this surface already has: `⁻¹` is the
`inverse` METHOD, and juxtaposition is the product.

The rule these productions add, stated as what it IS rather than as where it
was first noticed: AN IDENTIFIER TOKEN FOLLOWING AN IDENTIFIER TOKEN IS AN
APPLICATION, wherever the two sit. Lines do not enter into it — a newline is
whitespace to Lean's command parser — so everything below follows from that
one rule:

- `M v` and `M⁻¹ b` are the applications SPEC.md writes;
- `and` is a NON-RESERVED keyword, hence an identifier token, so it would be
  eaten as an argument and `assert p = q and r = s` would lose its
  conjunction. The `notFollowedBy` below is what keeps SPEC.md's ⊆-chain
  working; it is the rule's ONE exception, and it belongs to the rule rather
  than to `assert` — every other non-reserved keyword this surface adds in
  argument position will need the same guard;
- a cell whose previous statement ENDS in an identifier and whose next BEGINS
  with one joins them. NEITHER STATEMENT NEED BE A BARE NAME: `k1 + 1` and
  `k1.is_prime()` end in a numeral and a `)` and do not join, while SPEC.md's
  `let W := span_QQ{…} \leq ℚ³ in QQ-Mod` ends in `Mod` and does — failing
  with the misleading "'QQ' is not bound". Parenthesize the following
  statement or reorder; documented rather than closed, and on the ledger
  (#24). -/

syntax:max (name := casInv) ident noWs "⁻¹" : casTerm
syntax:70 (name := casJuxtApp) ident notFollowedBy(&"and") ident : casTerm
syntax:70 (name := casInvJuxtApp)
  ident noWs "⁻¹" notFollowedBy(&"and") ident : casTerm

/-- `|A|`, `|z|` — SPEC.md's bars, which ARE a method: `cardinality` for a
set, `abs` for an element of ℝ or ℂ. The bars are a spelling, so a receiver
neither category covers gets the ordinary "not a method of any category this
object belongs to" error rather than a third notion of size. -/
syntax:max (name := casCard) "|" casTerm "|" : casTerm

/-- SPEC.md's exact square root — `√2`, and `2√2` as the implicit product it
writes. The product needs no production of its own: `√2` is an atom, so it
is one of the operands `casImplMul` above already takes. (It HAD one, back
when implicit multiplication was `numeral noWs ident` and a radical was not
an identifier; keeping it now would be a second parse of `2√2` of exactly
the same length as the first, which is an ambiguity rather than a spelling.) -/
syntax:max (name := casSqrt) "√" noWs casTerm:max : casTerm

/-- `𝒫(A)`. SPEC.md's other spelling, `2^A`, is the ordinary `^` production
read against a set (`Eval`). -/
syntax:max (name := casPowerset) "𝒫" noWs "(" casTerm ")" : casTerm

/-- SPEC.md's `span_QQ{u₁, u₂}` — the subspace of ℚⁿ its generators span.

The production leads with an `ident` and the NAME is checked in `toExpr`,
which is what keeps `span_QQ` an ordinary identifier: a leading
`&"span_QQ"` is not indexed by a first token, so the bare-name production
wins the longest match and the braces become a set literal on the next
statement. Any other name gets a refusal naming the one spelling there is.
CEILING: over ℚ, which is the base `span_QQ` names and the entry domain of
every matrix this slice routes. -/
syntax:max (name := casSpan) ident noWs "{" casTerm,* "}" : casTerm

/-- `ℝ/O(ε)` — the target of SPEC.md's `map √2 to ℝ/O(1/10^{10})`, and a
production of its own because it is NOT a domain term: it is a requested
tolerance, meaningful only after `map … to` (`Eval`). `O` is a non-reserved
keyword like `and`, so `O` remains an ordinary identifier everywhere else, and
this production is longer than the bare `ℝ` token wherever it is written. -/
syntax:max (name := casApproxTarget) "ℝ" "/" &"O" noWs "(" casTerm ")" : casTerm

/-- Superscript exponents (`t²`, `x³`) — SPEC.md spells powers both ways, and
`assert h = hp` is precisely the claim that the two spellings agree. CEILING:
one digit; `^` covers everything larger. -/
syntax casSup := "⁰" <|> "¹" <|> "²" <|> "³" <|> "⁴" <|> "⁵" <|> "⁶" <|> "⁷" <|> "⁸" <|> "⁹"

syntax:80 (name := casSupPow) casTerm:81 noWs casSup : casTerm
syntax:80 (name := casPow) casTerm:81 " ^ " casTerm:80 : casTerm
syntax:75 (name := casComp) casTerm:75 " ∘ " casTerm:76 : casTerm
syntax:75 (name := casNeg) "-" casTerm:75 : casTerm
syntax:70 (name := casMul) casTerm:70 " * " casTerm:71 : casTerm
/-- SPEC.md's other spelling of multiplication (`z · z.bar() = 8`). -/
syntax:70 (name := casCdot) casTerm:70 " · " casTerm:71 : casTerm
syntax:70 (name := casDiv) casTerm:70 " / " casTerm:71 : casTerm
syntax:70 (name := casInter) casTerm:70 " ∩ " casTerm:71 : casTerm
syntax:70 (name := casProd) casTerm:70 " × " casTerm:71 : casTerm
syntax:65 (name := casAdd) casTerm:65 " + " casTerm:66 : casTerm
syntax:65 (name := casSub) casTerm:65 " - " casTerm:66 : casTerm
syntax:65 (name := casUnion) casTerm:65 " ∪ " casTerm:66 : casTerm
syntax:65 (name := casSetDiff) casTerm:65 " \\ " casTerm:66 : casTerm
syntax:65 (name := casSymDiff) casTerm:65 " △ " casTerm:66 : casTerm

/-- Order comparisons, and the CHAIN `0 ≤ n < 6` SPEC.md writes in a bounded
comprehension. The chain is a separate production rather than a fold, because
`(0 ≤ n) < 6` is not what a mathematician wrote.

`\leq` is SPEC.md's own spelling of `≤` in the subobject ascription
(`span_QQ{u₁, u₂} \leq ℚ³`), and it is the SAME relation: which reading it has
is the operands' business, decided in `Eval` — between a subspace and its
ambient space it is the subobject ascription, and between two scalars it is
the order comparison it always was. -/
syntax casCmpOp := " ≤ " <|> " \\leq " <|> " < " <|> " ≥ " <|> " > "

syntax:50 (name := casCmp) casTerm:51 casCmpOp casTerm:51 : casTerm
syntax:50 (name := casCmpChain)
  casTerm:51 casCmpOp casTerm:51 casCmpOp casTerm:51 : casTerm
syntax:25 (name := casArrow) casTerm:26 (" → " <|> " -> ") casTerm:25 : casTerm
syntax:20 (name := casMap) "map " casTerm:21 " to " casTerm:21 : casTerm
syntax:10 (name := casLam) casTerm:11 " ↦ " casTerm:10 : casTerm

syntax (name := casRelEq) "=" : casRel
syntax (name := casRelNe) "≠" : casRel
syntax (name := casRelMem) "∈" : casRel
syntax (name := casRelNotMem) "∉" : casRel
syntax (name := casRelSubset) "⊆" : casRel
/-- SPEC.md's ASCII spelling of `∈` (`assert S in 𝒫(ℤ)`). It sits in relation
position, where the `in D` ambient tail cannot be: that tail follows a
complete relation. -/
syntax (name := casRelIn) "in" : casRel

/-- One assertion — `l R r`. SPEC.md chains several with `and`
(`assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ`), so the command below is a sequence of
these rather than one triple. -/
syntax casAssertion := casTerm casRel casTerm

/-! ## Syntax → `CasExpr` -/

private def subscriptDigit? (c : Char) : Option Nat :=
  if c.toNat ≥ '₀'.toNat && c.toNat ≤ '₉'.toNat then some (c.toNat - '₀'.toNat)
  else none

/-- `Mat₂` → `2`. Any size expressible in subscript digits is accepted; the
renderer in `Value.lean` produces exactly this spelling. -/
def matSize? (n : Name) : Option Nat :=
  match n with
  | .str .anonymous s =>
      if !s.startsWith "Mat" then none
      else
        let ds := s.toList.drop 3
        if ds.isEmpty then none
        else ds.foldlM (init := 0) fun acc c => (subscriptDigit? c).map (10 * acc + ·)
  | _ => none

/-- `t²` → 2. Superscript digits are not one contiguous code block — `¹ ² ³`
sit in Latin-1 and the rest in Superscripts and Subscripts — so they are
spelled out. -/
private def superscriptDigit? : Char → Option Nat
  | '⁰' => some 0 | '¹' => some 1 | '²' => some 2 | '³' => some 3 | '⁴' => some 4
  | '⁵' => some 5 | '⁶' => some 6 | '⁷' => some 7 | '⁸' => some 8 | '⁹' => some 9
  | _ => none

/-- `x^{k}` is the BRACED exponent spelling — the one this system's own LaTeX
renderer produces (`x^{3}`, DESIGN.md §LaTeX-first display) and the one SPEC.md
writes its tolerance in (`1/10^{10}`) — so a single-element brace in EXPONENT
position is that exponent rather than the one-element SET it would otherwise
be. `2^{1, 2, 3}` has a comma and is still the powerset SPEC.md spells `2^A`;
`𝒫({3})` is untouched, and remains the way to write the powerset of a
singleton. -/
private def unbrace (stx : Syntax) : Syntax :=
  if stx.getKind == ``casSet then
    match stx[1].getSepArgs with
    | #[item] => if item.getKind == ``casSetElem then item[0] else stx
    | _ => stx
  else stx

/-- Split a dotted name into receiver and final component. -/
private def splitMethod? : Name → Option (Name × Name)
  | .str p s => if p == .anonymous then none else some (p, Name.mkSimple s)
  | _ => none

private def natLit (stx : Syntax) : Except String Nat :=
  match stx.isNatLit? with
  | some n => .ok n
  | none => .error s!"expected a numeral, got {stx}"

/-- The comparison a `casCmpOp` node spells. -/
private def cmpOp (stx : Syntax) : Except String CmpOp :=
  match (stx[0].reprint.getD "").trimAscii.toString with
  | "≤" | "\\leq" => .ok .le
  | "<" => .ok .lt
  | "≥" => .ok .ge
  | ">" => .ok .gt
  | other => .error s!"{other} is not a comparison"

partial def toExpr (stx : Syntax) : Except String CasExpr := do
  match stx.getKind with
  | ``casNatDom => return .dom .nat
  | ``casIntDom => return .dom .int
  | ``casRatDom => return .dom .rat
  | ``casRealDom => return .dom .real
  | ``casComplexDom => return .dom .complex
  | ``casAleph => return .lit (.cardinal .countablyInfinite)
  | ``casInfinity => return .lit (.sym (.const `infinity))
  | ``casNum => return .num (Int.ofNat (← natLit stx[0]))
  | ``casImplMul =>
      return .bin .mul (.num (Int.ofNat (← natLit stx[0]))) (← toExpr stx[1])
  | ``casIdent => return .ref stx[0].getId
  | ``casParen => toExpr stx[1]
  | ``casTuple => do
      let rest ← stx[3].getSepArgs.mapM toExpr
      return .vecLit (#[← toExpr stx[1]] ++ rest)
  | ``casNeg => return .neg (← toExpr stx[1])
  | ``casAdd => return .bin .add (← toExpr stx[0]) (← toExpr stx[2])
  | ``casSub => return .bin .sub (← toExpr stx[0]) (← toExpr stx[2])
  | ``casMul | ``casCdot => return .bin .mul (← toExpr stx[0]) (← toExpr stx[2])
  | ``casSqrt => return .sqrt (← toExpr stx[1])
  | ``casDiv => return .bin .div (← toExpr stx[0]) (← toExpr stx[2])
  | ``casPow => return .bin .pow (← toExpr stx[0]) (← toExpr (unbrace stx[2]))
  | ``casSupPow => do
      let some k := (stx[1].reprint.getD "").trimAscii.toString.toList.head?.bind
        superscriptDigit?
        | .error s!"{stx[1]} is not a superscript digit"
      return .bin .pow (← toExpr stx[0]) (.num (Int.ofNat k))
  | ``casComp => return .comp (← toExpr stx[0]) (← toExpr stx[2])
  | ``casArrow => return .arrow (← toExpr stx[0]) (← toExpr stx[2])
  -- the set operations ARE the Sets methods, so they desugar to the calls
  -- `eval` dispatches on and `#explain_route` explains
  | ``casUnion => return .method (← toExpr stx[0]) `union #[← toExpr stx[2]]
  | ``casInter => return .method (← toExpr stx[0]) `intersect #[← toExpr stx[2]]
  | ``casSetDiff => return .method (← toExpr stx[0]) `diff #[← toExpr stx[2]]
  | ``casSymDiff => return .method (← toExpr stx[0]) `symdiff #[← toExpr stx[2]]
  | ``casCard => return .magnitude (← toExpr stx[1])
  | ``casProd => return .setProduct (← toExpr stx[0]) (← toExpr stx[2])
  | ``casPowerset => return .powersetOf (← toExpr stx[2])
  | ``casBigSum => return .aggregate `sum stx[3].getId (← toExpr stx[5]) (← toExpr stx[7])
  | ``casBigProd => return .aggregate `prod stx[3].getId (← toExpr stx[5]) (← toExpr stx[7])
  | ``casSpan =>
      let n := stx[0].getId
      if n != `span_QQ then
        .error s!"`{n}\{…}` is not a construction of this surface: the span \
SPEC.md writes is `span_QQ\{…}`, the subspace of ℚⁿ its generators span"
      else return .spanOf (← stx[2].getSepArgs.mapM toExpr)
  | ``casCmp => return .cmp (← cmpOp stx[1]) (← toExpr stx[0]) (← toExpr stx[2])
  | ``casCmpChain => do
      let mid ← toExpr stx[2]
      return .conj (.cmp (← cmpOp stx[1]) (← toExpr stx[0]) mid)
        (.cmp (← cmpOp stx[3]) mid (← toExpr stx[4]))
  | ``casLam => do
      match ← toExpr stx[0] with
      | .ref b => return .lam b (← toExpr stx[2])
      -- SPEC.md §Subspaces and spans writes `φ: ℚ³ → ℚ := (a, b, c) ↦ a+b-c`.
      -- A MULTI-BINDER lambda is a gap rather than a syntax error, and it is
      -- named as one: functions here are grounded in the UNIVARIATE polynomial
      -- engine (DESIGN.md §Functions), so a body in three variables is not
      -- expressible and is refused rather than approximated
      | .vecLit _ =>
          .error "a lambda with SEVERAL binders — SPEC.md's \
`(a, b, c) ↦ a + b - c` — is a disclosed GAP, not a syntax error: functions \
here are grounded in the univariate polynomial engine, so a body in more than \
one variable is not expressible and is refused rather than approximated. It is \
on the SPEC.md ledger (#24), and it is what `W = ker φ` waits on; the span, \
dimension and membership lines of that section need none of it"
      | _ => .error s!"the binder of a `↦` definition must be a name, got \
{(stx[0].reprint.getD "").trimAscii.toString}"
  | ``casMap => return .mapTo (← toExpr stx[1]) (← toExpr stx[3])
  | ``casApproxTarget => return .approxTarget (← toExpr stx[4])
  | ``casIndex => return .index (← toExpr stx[0]) (← toExpr stx[2])
  | ``casInv => return .method (.ref stx[0].getId) `inverse #[]
  | ``casJuxtApp => return .app (.ref stx[0].getId) #[.ref stx[1].getId]
  | ``casInvJuxtApp =>
      return .app (.method (.ref stx[0].getId) `inverse #[]) #[.ref stx[2].getId]
  | ``casApply => do
      let args ← stx[2].getSepArgs.mapM toExpr
      match ← toExpr stx[0] with
      | .ref nm =>
          match matSize? nm with
          | some k =>
              if h : args.size = 1 then return .matDom k (args[0]'(by simp [h]))
              else .error s!"Mat{k}(…) takes one entry domain, got {args.size}"
          | none =>
              match splitMethod? nm with
              | some (recv, m) => return .method (.ref recv) m args
              | none => return .app (.ref nm) args
      | f => return .app f args
  -- `{n ∈ ℤ | P}` IS `{n | n ∈ ℤ, P}`: the filtering spelling is the image
  -- of the identity, so one node reaches one evaluator
  | ``casRootSet =>
      return .rootSet stx[1].getId (← toExpr stx[3]) (← toExpr stx[5]) (← toExpr stx[7])
  | ``casFilterSet =>
      return .comprehension (.ref stx[1].getId) stx[1].getId (← toExpr stx[3])
        (some (← toExpr stx[5]))
  | ``casImageSet => do
      let guard? ← if stx[6].isNone then pure none else some <$> toExpr stx[6][1]
      return .comprehension (← toExpr stx[1]) stx[3].getId (← toExpr stx[5]) guard?
  | ``casSet => do
      let items := stx[1].getSepArgs
      let ellipses := (items.toList.zipIdx).filterMap fun (it, i) =>
        if it.getKind == ``casEllipsis then some i else none
      let elems ← items.filterMap (fun it =>
        if it.getKind == ``casEllipsis then none else some it[0]) |>.mapM toExpr
      match ellipses with
      | [] => return .finSet elems
      | [i] =>
          if i + 1 == items.size then return .progSet elems none
          else if i + 2 == items.size then
            let some last := elems.back?
              | .error "a bounded progression needs a leading element"
            return .progSet elems.pop (some last)
          else .error "`...` may only be the last or the second-to-last element \
of a set literal"
      | _ => .error "a set literal contains at most one `...`"
  | ``casMat => do
      let rows := stx[1].getSepArgs
      let cells := rows.map fun r =>
        if r.getKind == ``casRow then r[0].getSepArgs else r.getSepArgs
      let some cols := (cells[0]? : Option (Array Syntax)).map (·.size)
        | .error "a matrix literal needs at least one row"
      if cells.any (·.size != cols) then
        .error "every row of a matrix literal must have the same length"
      return .matLit cells.size cols (← cells.flatten.mapM toExpr)
  | k => .error s!"unsupported cas syntax node '{k}'"

/-! ## Rendering results -/

/-- The wire value behind a result. A set OBJECT has no `Denote.value?` — the
evaluator's value seam is deliberately element-shaped — but the two set
presentations an executor can return do have wire forms, so the payload
carries them instead of the null it used to carry for `p.roots()`. The
denoted sets (`A × B`, `𝒫(A)`, `ℤ`) have no `Value` and stay null: that is
the honest answer, not a gap. -/
private def valueJson (d : Denote) : Json :=
  match d.value?, d.asSet? with
  | some v, _ => Codec.valueToJson v
  | none, some (.finite dom elems) => Codec.valueToJson (.setV elems dom)
  | none, some (.arithProg dom first step last?) =>
      Codec.valueToJson (.progV dom first step last?)
  | none, some (.span n basis) => Codec.valueToJson (.spanV n basis)
  -- spelled out rather than a wildcard: a new set presentation must fail this
  -- build and be decided, not silently publish `null`
  | none, some (.domainSet _) | none, some (.product _ _) | none, some (.powerset _)
  | none, some (.domainDiff _ _) | none, none => Json.null

private def denoteJson (d : Denote) : Json :=
  Json.mkObj
    [("render", .str d.render),
     ("presentation", .str d.presentation),
     ("value", valueJson d)]

/-! ## Elaborator helpers

Defined ABOVE the command block so their `do`/`let` bodies parse before the
`let` command production exists. -/

private def parseCas (stx : Syntax) : CommandElabM CasExpr := do
  match toExpr stx with
  | .ok e => return e
  | .error m => throwError m

private def casCtx (ambient? : Option Domain := none) : CommandElabM EvalCtx := do
  return { env := ← getEnv, ambient? }

private def runCas (x : EvalM α) : CommandElabM α := do
  match ← x.run with
  | .ok a => return a
  | .error e => throwError e.render

/-- The source text of a syntax node, for echoing an assertion back at the
mathematician in the spelling they wrote. -/
private def src (stx : Syntax) : String :=
  (stx.reprint.getD (toString stx)).trimAscii.toString

/-- The optional `in <casTerm>` tail of a command. -/
private def optTail? (stx : Syntax) : Option Syntax :=
  if stx.isNone then none else some stx[1]

private def ambientOf (tail? : Option Syntax) : CommandElabM (Option Domain) := do
  match tail? with
  | none => return none
  | some t =>
      match ← runCas (eval (← casCtx) (← parseCas t)) with
      | .obj (.domainObj d) => return some d
      | other => throwError s!"`in {other.render}` is not a domain"

private def bindObj (n : Name) (o : Obj) : CommandElabM Unit := do
  modifyEnv fun env => addBinding env (n, o)
  logInfo s!"{n} := {o.presentation}"

def elabCasLet (idStx valStx : Syntax) (asc? : Option Syntax) : CommandElabM Unit := do
  let e ← parseCas valStx
  let a? ← asc?.mapM parseCas
  bindObj idStx.getId (← runCas (evalBinding (← casCtx) e a?))

def elabCasLetPoly (idStx xStx valStx ascStx : Syntax) : CommandElabM Unit := do
  let e ← parseCas valStx
  let a ← parseCas ascStx
  bindObj idStx.getId (← runCas (evalPolyBinding (← casCtx) xStx.getId e a))

private def relOf (relStx : Syntax) : CommandElabM AssertRel :=
  match relStx.getKind with
  | ``casRelEq => pure .eq
  | ``casRelNe => pure .ne
  | ``casRelMem | ``casRelIn => pure .mem
  | ``casRelNotMem => pure .notMem
  | ``casRelSubset => pure .subset
  | k => throwError s!"unsupported assertion relation '{k}'"

/-- `assert l R r (and l R r)* [in D]`.

`and` is the conjunction SPEC.md writes (§Exact number systems' ⊆-chain), and
it is a conjunction of ASSERTIONS rather than a term operator: each conjunct
is decided on its own, the ambient `in D` covers them all, and the FIRST one
that is not true stops the cell naming itself — a chain never reports "false"
without saying which claim was. -/
def elabCasAssert (parts : Array Syntax) (tail? : Option Syntax)
    : CommandElabM Unit := do
  let ctx ← casCtx (← ambientOf tail?)
  let mut claims : Array (AssertRel × Syntax × Syntax) := #[]
  for p in parts do
    claims := claims.push (← relOf p[1], p[0], p[2])
  let one := fun (rel, l, r) => s!"{src l} {rel.render} {src r}"
  let stated := " and ".intercalate (claims.toList.map one)
    ++ (tail?.elim "" fun t => s!" in {src t}")
  for claim in claims do
    let (rel, lhs, rhs) := claim
    -- a chain says which conjunct failed; a single assertion is worded
    -- exactly as it always was
    let which := if claims.size == 1 then stated else s!"{one claim} (of {stated})"
    match ← runCas (evalAssert ctx rel (← parseCas lhs) (← parseCas rhs)) with
    | some true => pure ()
    | some false => throwError s!"assertion is false: {which}"
    | none => throwError s!"the assertion outcome is unknown: the two sides of \
{which} are not comparable"
  logInfo s!"✓ {stated}"

/-- A bare expression cell: display the value as text and as a structured
MIME bundle. LaTeX-first (#16): a value with a natural LaTeX form carries it
as `text/latex`, wrapped in `$$…$$` so the notebook's MathJax picks it up
without a `show()`, and `text/plain` stays in the bundle as the fallback
every consumer can read. A value with no LaTeX form emits plain text alone.
DISPLAY register, like Sage's `backend_ipython` and IPython's `display.Math`:
a cell RESULT is displayed math, and inline `$…$` typesets a `pmatrix` at
text size with undersized delimiters. -/
def elabCasShow (stx : Syntax) : CommandElabM Unit := do
  let d ← runCas (eval (← casCtx) (← parseCas stx))
  logInfo d.render
  emitOutput {
    data :=
      [("text/plain", .str d.render)]
      ++ (d.latex?.toList.map fun l => ("text/latex", Json.str s!"$${l}$$"))
      ++ [("application/vnd.casdsl.value+json", denoteJson d)]
  }

/-! ## Commands

Declared last (see the header note). Every elaborator below is one call. -/

/-- `let x := e [in T]` binds `x` to the value of `e`. The ascription `T` is
a checked membership judgment, not an annotation: a domain must admit the
preferred canonical map, and a registered category must actually contain the
object. Set literals need no ascription. -/
syntax (name := casLet) "let " ident " := " casTerm (" in " casTerm)? : command

/-- `let p(x) := e in T` binds a definition with a BINDER: `x` denotes the
indeterminate inside `e`, and the ascription decides what that means — the
indeterminate of `ℤ[x]`, or the variable of a function `ℝ → ℝ`. SPEC.md
spells the definition both `:=` and `=`, so both are accepted. -/
syntax (name := casLetPoly)
  "let " ident noWs "(" ident ")" (" := " <|> " = ") casTerm " in " casTerm : command

/-- `let e: ℕ → ℕ := n ↦ 2n` — SPEC.md's leading-ascription spelling. The
type is the same ascription the trailing `in T` carries, checked identically. -/
syntax (name := casLetTyped)
  "let " ident " : " casTerm " := " casTerm : command

/-- `assert l (= | ≠ | ∈ | ∉ | ⊆) r (and …)* [in D]` — a TRUSTED COMPUTATIONAL assertion
in the ordinary CAS sense. The predicate is computed and believed; no Lean
proposition is created, no theorem is generated, and no certificate is
required. The outcome is fourfold — `true | false | unknown | error` — and
only `true` lets the cell commit, so a failed assertion rolls the cell's
registrations back with the worker's cell atomicity. `in D` sets the ambient
domain the literals and arithmetic are read in. -/
syntax (name := casAssert)
  "assert " casAssertion (&"and" casAssertion)* (" in " casTerm)? : command

/-- A bare expression cell displays its value. Low priority, so every
genuine Lean command in a cell still parses as Lean. -/
syntax (name := casShow) (priority := low) casTerm : command

@[command_elab casLet]
def elabLetCmd : CommandElab := fun stx =>
  elabCasLet stx[1] stx[3] (optTail? stx[4])

@[command_elab casLetPoly]
def elabLetPolyCmd : CommandElab := fun stx =>
  elabCasLetPoly stx[1] stx[3] stx[6] stx[8]

@[command_elab casLetTyped]
def elabLetTypedCmd : CommandElab := fun stx =>
  elabCasLet stx[1] stx[5] (some stx[3])

@[command_elab casAssert]
def elabAssertCmd : CommandElab := fun stx =>
  elabCasAssert (#[stx[1]] ++ stx[2].getArgs.map (·[1])) (optTail? stx[3])

@[command_elab casShow]
def elabShowCmd : CommandElab := fun stx => elabCasShow stx[0]

end CasDsl
