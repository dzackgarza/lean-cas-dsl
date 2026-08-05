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

/-! The BACKSLASH family (ruling 2026-07-31, #31 item 5): a unicode token's
LaTeX spelling is accepted wherever the unicode form goes — SPEC.md §Ellipses
writes `\NN` and `\in`, and `\leq` (`casCmpOp`) was already such an alias.
Coverage today: the five domain tokens here, and `\in` beside every `∈`
(relation, binder, the `let f(t) = … ∈ D` ascription). An addition follows
the same pattern, declared beside its unicode token. -/

syntax:max (name := casNatDomBS) "\\NN" : casTerm
syntax:max (name := casIntDomBS) "\\ZZ" : casTerm
syntax:max (name := casRatDomBS) "\\QQ" : casTerm
syntax:max (name := casRealDomBS) "\\RR" : casTerm
syntax:max (name := casComplexDomBS) "\\CC" : casTerm
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

/-- A PARENTHESIZED coefficient against an atom-or-power — SPEC.md's
`x³ + (1/2)x² + x`, and the spelling this system's own polynomial renderer
produces for a non-integer coefficient (`(1/2)x^2`, so that it reads as a
product rather than as one rational). Without this production the surface
could not READ BACK what it prints, which is what `assert ∫ f dx = x³ +
(1/2)x² + x + ℚ` asks it to do.

The right operand is `casTerm:76`, the same atom-or-power `casImplMul` takes,
so the two spellings of an implicit product agree about the exponent. The two
guards keep it disjoint from the productions a `)` already continues into: a
call (`(f ∘ g)(t)`) and an index. `noWs` carries the usual guarantee, and is
also what leaves `(6x + 1) dx` — with its space — to the differential form. -/
syntax:max (name := casParenMul)
  "(" casTerm ")" noWs notFollowedBy("(") notFollowedBy("[") casTerm:76 : casTerm

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

syntax casBinderIn := " ∈ " <|> " in " <|> " \\in "

syntax:max (name := casFilterSet)
  "{" ident casBinderIn casTerm " | " casTerm "}" : casTerm

syntax:max (name := casImageSet)
  "{" casTerm " | " ident casBinderIn casTerm ("," casTerm)? "}" : casTerm

/-- SPEC.md §Ellipses' `{n in ℕ | f(n) ∈ 2ℕ}` — MEMBERSHIP in guard
position, one relation admitted in one production (the discipline the root
set below sets for `=`; ruling 2026-07-31, #31 item 6). The guard desugars
to the `contains` call it means — `∈` invents nothing — so it is decided by
the same routed membership every other spelling of `∈` reaches. -/
syntax:max (name := casMemFilterSet)
  "{" ident casBinderIn casTerm " | " casTerm casBinderIn casTerm "}" : casTerm

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

/-- `D[x]` (a polynomial ring) and `e[k]` (an index). The `notFollowedBy` is
what keeps `ℤ[[t]]` — the formal power series below — from ALSO reading as
this production applied to the one-row matrix literal `[t]`, which would be a
parse of exactly the same length. An index is never written with a matrix
literal as its subscript, so nothing that parses today loses a reading. -/
syntax:max (name := casIndex)
  casTerm:max noWs "[" notFollowedBy("[") casTerm "]" : casTerm

/-- `CC[x_0, x_1, ..., x_9]` — SPEC.md §Ellipses' index-FAMILY spelling of a
multivariate polynomial algebra, and a HELD feature (#31, deferred to the
#13 demand / CategoryGraph trajectory).

The production exists so the spelling is READ and refused BY NAME. `casIndex`
above takes exactly one subscript, so without this a comma inside the
brackets reaches the tokenizer and the boundary of the spike reports itself
as `unexpected token ','` — an accident of parsing rather than a disclosure.
Items are `casSetItem` because the family is written with the same `...` the
set spellings use, and two or more of them are what tells this production
apart from the index. -/
syntax:max (name := casIndexFamily)
  casTerm:max noWs "[" notFollowedBy("[") casSetItem "," casSetItem,+ "]" : casTerm

/-- `f(args…)` — a call — and, with the optional ASCRIPTION tail, SPEC.md
§Indefinite integration's `kernel(d/dx : ℚ[x] → ℚ[x])`.

ONE production for both, and that is forced rather than tidy. A separate
`kernel(… : …)` parser has to start where a call starts, and it then OUT-RUNS
it: Lean's longest match prefers the alternative that reached the furthest
position, error or not, so a colon parser failing at the `)` of `f(2)` beats
the bare name that succeeded three tokens earlier — and every call in the
corpus stops parsing. Folding the ascription in as an optional tail keeps `:`
confined to this one spelling and leaves calls untouched; which NAME may carry
it is checked in `toExpr`, the discipline `span_QQ{…}` and `Spec` follow. -/
syntax:max (name := casApply)
  casTerm:max noWs "(" casTerm,* (" : " casTerm)? ")" : casTerm

/-- `(360).factor()` — a PARENTHESIZED receiver taking a method (ruling
2026-07-31, #31 item 1). Literal `360.factor()` is a Lean-tokenizer
casualty: the lexer eats `360.` as a decimal before any production sees it,
so SPEC L12's receiver is parenthesized — and `factor(360)` remains the
same call in the prefix spelling. A production of its own because `casApply`
reaches a method through the DOTTED NAME the `ident` lexer produces, which a
parenthesized receiver never is; the method here is resolved on the
receiver's VALUE, through the same `.method` node every other spelling
reaches. -/
syntax:max (name := casParenMethod)
  "(" casTerm ")" noWs "." noWs ident noWs "(" casTerm,* ")" : casTerm

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
  argument position will need the same guard. `dx` and `Spec` needed no such
  guard in the end: they are real TOKENS, so they are not identifiers and
  this production cannot eat them (§the differential form below says why they
  had to be tokens). `casInvJuxtApp` therefore carries the `and` guard alone,
  exactly as this one does — the two are not asymmetric;
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

/-! SPEC.md §Differentials' `(6x + 1) dx` and `f dx` — a DIFFERENTIAL 1-FORM,
its coefficient against the free generator of `Ω¹_{k[x]/k} ≅ k[x] dx`.

`dx` is a real TOKEN, and it has to be: it keys a TRAILING production, and
Lean indexes trailing parsers by the token that follows the left operand. A
non-reserved `&"dx"` is not a token, so the production would never be tried
at all — the same lore the `span_QQ{…}` note below records for the LEADING
position. The price is that `dx` is a reserved word in this surface, which is
the honest trade: it is the differential's own spelling.

CEILING: `dx`, and `dt` inside the definite integral, which spells its own
after the `∫` and therefore needs no token. This slice renders the polynomial
ring's indeterminate `x`, so `dx` is its differential and `dy` is a spelling
of nothing here. -/

syntax:max (name := casDxAtom) "dx" : casTerm
syntax:70 (name := casDiffForm) casTerm:71 "dx" : casTerm

/-- SPEC.md §Indefinite integration's `∫ f dx` — the COMPLETE set of
primitives, a coset of `ker(d/dx)`. The integrand is an ATOM (`casTerm:max`)
for the reason `∑`'s body is one: `= x³ + …` on the right of an assertion
ends it exactly where the mathematician wrote it, and a wider integrand is
parenthesized. -/
syntax:max (name := casIntegral) "∫" casTerm:max "dx" : casTerm

/-! SPEC.md's formal power series — `ℝ[[t]]`, `ℤ[[t]]`, the truncation
`map … to ℝ[[t]]/(t^6)`, the generating sum `∑_{n ∈ ℕ} n² tⁿ`, and the
coefficient extraction `[t²]f`.

The double bracket is TWO `[` tokens with no whitespace between them, not a
`[[` token of its own: a `[[` token would be produced by the tokenizer
everywhere, including inside Lean's own `#[…]` array literals in this very
file. What keeps `ℤ[[t]]` from ALSO parsing as the index `ℤ[…]` applied to
the one-row matrix `[t]` — a parse of exactly the same length, so an
ambiguity rather than a spelling — is the `notFollowedBy` on `casIndex`
above: an index is never written with a matrix literal as its subscript. -/

syntax:max (name := casSeries)
  casTerm:max noWs "[" noWs "[" ident "]" noWs "]" : casTerm

/-- `ℝ[[t]]/(t^6)` and `ℤ[[t]] / O(t^5)` — ONE truncation REQUEST with two
spellings, on the `ℝ/O(ε)` precedent: it is not a quotient domain, it is
meaningful only after `map … to`, and written anywhere else it is a loud
refusal saying so.

All three are declared with `casTerm:max` as their FIRST element rather than
through a shared named rule, and that is not a style choice: a named rule
starting with `casTerm` makes the production look like a LEADING parser to
Lean, which is left-recursive and overflows the stack while the grammar is
being built. Written out, they are trailing parsers keyed by `[[`. -/
syntax:max (name := casTruncTarget)
  casTerm:max noWs "[" noWs "[" ident "]" noWs "]" " / " "(" casTerm ")" : casTerm
syntax:max (name := casTruncTargetO)
  casTerm:max noWs "[" noWs "[" ident "]" noWs "]" " / " &"O" noWs
    "(" casTerm ")" : casTerm

/-- SPEC.md's `∑_{n ∈ ℕ} n^2 t^n` — a series given by its GENERATING RULE.

A production of its own rather than the aggregation `∑`, whose body is an
atom: the shape here is the whole content — a rule in the binder, against
`tⁿ` — and spelling it out is what lets the rule be read exactly rather than
guessed at from a product this grammar has no general form for. -/
syntax:max (name := casSeriesSum)
  "∑" noWs "_" noWs "{" ident casBinderIn casTerm "}" casTerm:76
    ident noWs "^" noWs ident : casTerm

/-- SPEC.md's `[t^2]f` — the coefficient of a power in a series, and a THIRD
reading of the brackets beside the polynomial ring and the index. It is told
apart by what follows: a matrix literal ends at its `]`, and this one has a
receiver against it with no space between. -/
syntax:max (name := casCoeffOf) "[" casTerm "]" noWs casTerm:max : casTerm

/-- SPEC.md §Differentials' `Spec ℚ[x]` — the affine scheme of a ring, and an
ASCRIPTION TAG at this stage (DESIGN.md §Differentials).

`Spec` is a real TOKEN, for the reason `dx` is one. A leading `&"Spec"` is
not indexed by a first token and would never be tried; leading with a plain
`ident` and checking the name in `toExpr` — the `span_QQ{…}` discipline —
does not work here either, because that production has no closing delimiter
to stop at, so it OUT-RUNS the bare name wherever an identifier is followed
by any atom: `|z|` reads its closing bar as the start of a factor, and Lean's
longest match prefers the alternative that got furthest even when it failed.
A token has neither problem: the production is tried only where `Spec` is
written, and nowhere else. The price is that `Spec` is a reserved word in
this surface — the same trade `dx` makes. -/
syntax:max (name := casSpec) "Spec" casTerm:max : casTerm

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

/-! SPEC.md §Elementary calculus' three analysis operations. All three are
ordinary METHODS on a FUNCTION — `limit`, `definite_integral`,
`taylor_expansion` — and these productions are spellings that build the
function by elaboration, exactly as `{a ∈ ℂ | r(a) = 0}` builds the
polynomial it hands to `roots`. `lim` is a TOKEN for the reason `dx` and
`Spec` are.

CEILING on the definite integral's bounds, and it is SPEC.md's own spelling
rather than a general one: the LOWER bound is a subscript digit and the upper
is either a superscript digit or `^` followed by an atom. `∫₀¹` and `∫₀^π`
are what SPEC.md writes; a wider bound is parenthesized after `^`. -/

syntax casSubDigit :=
  "₀" <|> "₁" <|> "₂" <|> "₃" <|> "₄" <|> "₅" <|> "₆" <|> "₇" <|> "₈" <|> "₉"

/-- The differential that closes a definite integral, and NAMES its variable:
`dt` binds `t`, `dx` binds `x`. `dt` may stay a non-reserved keyword because
it sits in the middle of a production keyed by `∫` — the position `&"O"` sits
in after `ℝ/`, where the leading-token lore does not bite. -/
syntax casIntVar := &"dt" <|> "dx"

/-- The token is `lim_`, underscore included, and that is lexical rather than
stylistic: `_` is an identifier character, so `lim_{t → 0}` lexes `lim_` as
one IDENTIFIER and a bare `lim` token is never seen. (`∑_{…}` has no such
problem — `∑` is not an identifier character, so its `_` is the ordinary
token.) -/
syntax:max (name := casLimit)
  "lim_" noWs "{" ident " → " casTerm "}" casTerm:70 : casTerm

/-- SPEC.md's `∫₀¹ t² dt` and `∫₀^π sin(t) dt`.

CEILING, and it is deliberate rather than an oversight: the INTEGRAND sits at
`casTerm:76` — an atom or a power — so `/` and `+` end it. `lim_` above takes
its body at `:70` and therefore admits `sin(t)/t`, which is the asymmetry, and
it is the SPEC lines that put it there: every limit SPEC.md writes has a
quotient body and every definite integral has an atomic one. A wider integrand
is parenthesized (`∫₀¹ (t²+1) dt`); it blocks no SPEC.md line and it fails
LOUDLY rather than binding something else. -/
syntax:max (name := casDefIntSup)
  "∫" noWs casSubDigit noWs casSup casTerm:76 casIntVar : casTerm
syntax:max (name := casDefIntCaret)
  "∫" noWs casSubDigit noWs "^" noWs casTerm:max casTerm:76 casIntVar : casTerm

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
/-- `binder ↦ body`, and its ASCII spellings `|->` and `\mapsto` (ruling
2026-07-31, the four spelling pins): `|->` is the conventional ASCII mapsto,
and `\mapsto` is its backslash-family form. `->` stays the domain arrow ONLY
— one symbol, one meaning, no shape-based disambiguation. -/
syntax:10 (name := casLam) casTerm:11 (" ↦ " <|> " |-> " <|> " \\mapsto ") casTerm:10 : casTerm

/-- The words this surface RESERVES — real tokens, so an identifier by any
of these spellings cannot be written anywhere, including as a binding name.
That is the price the productions above pay deliberately: `dx` (the
differential atom, the 1-form, `∫ f dx`), `Spec` (the scheme spelling),
`lim_` (underscore included — lexical, see `casLimit`), `map`/`to`
(the `map e to D` coercion), and `is` (the relation spelling, whose
non-reserved form the category dispatch cannot reach — see `casRelIs`).
Everything else the grammar keys on — `and`,
`O`, `dt`, `span_QQ` — is a non-reserved `&"…"` keyword and stays an
ordinary identifier everywhere else. Constants come in two kinds (ruling
2026-07-31, #31 item 3): `π` and `d` are spellings a binding always
shadows, while `e` (Euler's constant — `e^t` means exp(t)) and `i` (the
imaginary unit) are RESERVED SYMBOLS a binding may never shadow — enforced
where a name is introduced (`bindObj`, and every binder position of the
evaluator), not by the tokenizer, so identifiers merely containing them
(`is_prime`, `e1`) are untouched.

This list is DOCUMENTATION HELD TO THE GRAMMAR: the parse guard in
`CasDslTests/Core.lean` fails the build if a listed word starts parsing as
a binding name (un-reserved without being delisted) or a named non-reserved
keyword stops (reserved without being listed). One page on the whole
grammar: DESIGN.md §Surface. -/
def reservedWords : List String := ["dx", "Spec", "lim_", "map", "to", "is"]

/-- The `&"…"` keywords the grammar uses WITHOUT reserving, each pinned by
the same guard so a production rewrite cannot quietly widen the reserved
set. -/
def nonReservedKeywords : List String := ["and", "O", "dt", "span_QQ"]

syntax (name := casRelEq) "=" : casRel
syntax (name := casRelNe) "≠" : casRel
syntax (name := casRelMem) "∈" : casRel
syntax (name := casRelNotMem) "∉" : casRel
syntax (name := casRelSubset) "⊆" : casRel
/-- SPEC.md's ASCII spelling of `∈` (`assert S in 𝒫(ℤ)`). It sits in relation
position, where the `in D` ambient tail cannot be: that tail follows a
complete relation. -/
syntax (name := casRelIn) "in" : casRel
/-- `\in`, beside `∈` — the backslash family. -/
syntax (name := casRelMemBS) "\\in" : casRel
/-- SPEC.md §Ellipses' `is`, which "just means `=`" (SPEC's words). A real
TOKEN, and reluctantly so: the preferred non-reserved `&"is"` LEADS a
`casRel` category production, and a leading non-reserved keyword is not
indexed by a first token — the category dispatch never tries it (the `Spec`
lore, observed here too: the ruled-spellings guard stayed red). The price is
that `is` is a reserved word of this surface, listed in `reservedWords` and
held there by the parse guard; a segment CONTAINING it (`is_prime`) is
untouched, since tokens match whole identifier runs only. -/
syntax (name := casRelIs) "is" : casRel

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

/-- The ORDER a truncation asks for, read from `(t^6)` or `O(t^5)`, and the
POWER `[t^2]f` asks for — one reading, because they are one question about a
shape. STRUCTURAL rather than evaluated: `t` names no binding, it is the
series' own indeterminate, so the exponent is read off the shape and anything
else is a loud refusal. -/
private def seriesOrder : CasExpr → Except String Nat
  | .bin .pow (.ref `t) (.num k) =>
      if k ≥ 0 then .ok k.toNat
      else .error "a power of the series' indeterminate is nonnegative"
  | .ref `t => .ok 1
  | .num 0 => .ok 0
  | _ => .error "this asks for a power of the series' indeterminate — \
`ℝ[[t]]/(t^6)`, `ℤ[[t]] / O(t^5)`, `[t^2]f` — and is not one"

/-- The check that a series' indeterminate is the `t` this slice spells one
with. A `Domain` records no name, so one spelling per ring is the convention
(`x` for the polynomial ring), and a second one would be a display that
disagrees with its own input syntax. -/
private def seriesIndet (n : Name) : Except String Unit :=
  if n == `t then .ok ()
  else .error s!"the indeterminate of a formal power series is spelled `t` \
here, and `{n}` is not it"

/-- The digit a `casSubDigit` node spells — the LOWER bound of SPEC.md's
`∫₀¹`. Subscript digits are one contiguous block, unlike the superscripts. -/
private def subLit (stx : Syntax) : Except String Nat :=
  match (stx[0].reprint.getD "").trimAscii.toString.toList.head? with
  | some c =>
      if c.toNat ≥ '₀'.toNat && c.toNat ≤ '₉'.toNat then .ok (c.toNat - '₀'.toNat)
      else .error s!"{stx} is not a subscript digit"
  | none => .error s!"{stx} is not a subscript digit"

/-- The variable a definite integral's differential NAMES: `dt` binds `t`. -/
private def intVar (stx : Syntax) : Except String Name :=
  match (stx[0].reprint.getD "").trimAscii.toString with
  | "dt" => .ok `t
  | "dx" => .ok `x
  | other => .error s!"{other} does not name an integration variable"

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

/-- A translator for a `casTerm` production contributed outside this module.
It receives the full recursive translator for its child terms, so a
contributed node composes with every production that already exists. -/
abbrev TermTranslator :=
  (Syntax → Except String CasExpr) → Syntax → Except String CasExpr

/-- Contributed `casTerm` translators. CODE WIRING like the executor table
(`Route.lean`): keyed by syntax node kind, holds no state a notebook can
observe, and is rebuilt identically on every process start by the
contributing modules' `initialize` blocks. `casTerm` is an open syntax
category; this table is what makes that opening real — a production added
outside this module parses AND translates, without an edit to `toExprCore`. -/
initialize termTranslatorsRef : IO.Ref (Array (SyntaxNodeKind × TermTranslator)) ←
  IO.mkRef #[]

/-- Register a translator for a contributed `casTerm` production. A duplicate
kind is a build-time programming error, not a precedence question: it throws.
The kinds `toExprCore` matches itself are not shadowable — the table is
consulted only for nodes the core match does not know. -/
def registerTermTranslator (k : SyntaxNodeKind) (t : TermTranslator) : IO Unit := do
  let table ← termTranslatorsRef.get
  if table.any (·.1 == k) then
    throw <| IO.userError s!"a casTerm translator for '{k}' is already registered"
  termTranslatorsRef.set (table.push (k, t))

partial def toExprCore (ext : SyntaxNodeKind → Option TermTranslator)
    (stx : Syntax) : Except String CasExpr := do
  -- every recursive translation below re-enters with the same extensions
  let toExpr := toExprCore ext
  match stx.getKind with
  | ``casNatDom | ``casNatDomBS => return .dom .nat
  | ``casIntDom | ``casIntDomBS => return .dom .int
  | ``casRatDom | ``casRatDomBS => return .dom .rat
  | ``casRealDom | ``casRealDomBS => return .dom .real
  | ``casComplexDom | ``casComplexDomBS => return .dom .complex
  | ``casAleph => return .lit (.cardinal .countablyInfinite)
  | ``casInfinity => return .lit (.sym (.const `infinity))
  | ``casNum => return .num (Int.ofNat (← natLit stx[0]))
  | ``casImplMul =>
      return .bin .mul (.num (Int.ofNat (← natLit stx[0]))) (← toExpr stx[1])
  | ``casIdent => return .ref stx[0].getId
  | ``casParen => toExpr stx[1]
  | ``casParenMul => return .bin .mul (← toExpr stx[1]) (← toExpr stx[3])
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
  | ``casDiffForm => return .diffForm (← toExpr stx[0])
  -- a bare `dx` IS the 1-form with coefficient 1 — the free generator itself,
  -- which is what makes `(d/dx)` a quotient of two names the surface can read
  | ``casDxAtom => return .diffForm (.num 1)
  | ``casSpec => return .specOf (← toExpr stx[1])
  | ``casIntegral => return .integral (← toExpr stx[1])
  | ``casSeries => do
      seriesIndet stx[3].getId
      return .seriesDom (← toExpr stx[0])
  | ``casTruncTarget => do
      seriesIndet stx[3].getId
      return .truncTarget (← seriesOrder (← toExpr stx[8]))
  | ``casTruncTargetO => do
      seriesIndet stx[3].getId
      return .truncTarget (← seriesOrder (← toExpr stx[9]))
  | ``casSeriesSum => do
      let binder := stx[3].getId
      seriesIndet stx[8].getId
      if stx[10].getId != binder then
        .error s!"the exponent of `t` in a generating sum is the sum's own \
binder ('{binder}'), and `{stx[10].getId}` is not it"
      return .seriesSum binder (← toExpr stx[5]) (← toExpr stx[7])
  | ``casCoeffOf => return .coeffOf (← seriesOrder (← toExpr stx[1])) (← toExpr stx[3])
  | ``casLimit =>
      return .limitOf stx[2].getId (← toExpr stx[4]) (← toExpr stx[6])
  | ``casDefIntSup => do
      let some k := (stx[2].reprint.getD "").trimAscii.toString.toList.head?.bind
        superscriptDigit?
        | .error s!"{stx[2]} is not a superscript digit"
      return .defIntegral (← intVar stx[4]) (.num (Int.ofNat (← subLit stx[1])))
        (.num (Int.ofNat k)) (← toExpr stx[3])
  | ``casDefIntCaret => do
      return .defIntegral (← intVar stx[5]) (.num (Int.ofNat (← subLit stx[1])))
        (← toExpr stx[3]) (← toExpr stx[4])
  | ``casProd => return .setProduct (← toExpr stx[0]) (← toExpr stx[2])
  | ``casPowerset => return .powersetOf (← toExpr stx[2])
  | ``casBigSum => return .aggregate `sum stx[3].getId (← toExpr stx[5]) (← toExpr stx[7])
  | ``casBigProd => return .aggregate `prod stx[3].getId (← toExpr stx[5]) (← toExpr stx[7])
  | ``casSpan =>
      let n := stx[0].getId
      if n != `span_QQ then
        .error s!"`{n}\{…}` is not a recognized construction: the span \
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
      -- SPEC.md §Subspaces and spans writes `φ: ℚ³ → ℚ := (a, b, c) ↦ a+b-c`
      -- — a MULTI-binder definition, a HOM under the 2026-07-31 ruling
      -- (DESIGN.md §Homs are first-class). The binders must be names; whether
      -- the body is linear is `evalHomBinding`'s judgment, where the
      -- nonlinear case stays the disclosed tier-2 gap
      | .vecLit comps => do
          let binders ← comps.mapM fun c =>
            match c with
            | .ref b => pure b
            | _ => Except.error "the binders of a multi-binder `↦` definition \
are names, as in `(a, b, c) ↦ a + b - c`"
          return .lamN binders (← toExpr stx[2])
      | _ => .error s!"the binder of a `↦` definition must be a name, got \
{(stx[0].reprint.getD "").trimAscii.toString}"
  | ``casMap => return .mapTo (← toExpr stx[1]) (← toExpr stx[3])
  | ``casApproxTarget => return .approxTarget (← toExpr stx[4])
  | ``casIndex => return .index (← toExpr stx[0]) (← toExpr stx[2])
  | ``casIndexFamily =>
      .error "D[x_0, x_1, ..., x_n] — a polynomial algebra on a FAMILY of \
indeterminates (SPEC.md §Ellipses) — is the pinned spelling of a tier-2 \
feature, held for demand: the spelling is reserved, and the multivariate \
algebra is refused rather than approximated. One indeterminate — `ℂ[x]` — \
is what this slice presents"
  | ``casInv => return .method (.ref stx[0].getId) `inverse #[]
  | ``casJuxtApp => return .app (.ref stx[0].getId) #[.ref stx[1].getId]
  | ``casInvJuxtApp =>
      return .app (.method (.ref stx[0].getId) `inverse #[]) #[.ref stx[2].getId]
  | ``casParenMethod =>
      return .method (← toExpr stx[1]) stx[4].getId (← stx[6].getSepArgs.mapM toExpr)
  | ``casApply => do
      let args ← stx[2].getSepArgs.mapM toExpr
      -- the ASCRIPTION tail is SPEC.md's `kernel(d/dx : ℚ[x] → ℚ[x])` and
      -- nothing else: `:` has no other meaning in a term here, so a name that
      -- is not `kernel` carrying one is refused rather than reinterpreted
      if !stx[3].isNone then
        let head := match ← toExpr stx[0] with | .ref n => n | _ => Name.anonymous
        if head != `kernel then
          .error s!"`{head}(… : …)` is not a recognized construction: the \
one SPEC.md writes is `kernel(d/dx : ℚ[x] → ℚ[x])`, the kernel of a derivation"
        else if h : args.size = 1 then
          return .kernelOf (args[0]'(by simp [h])) (← toExpr stx[3][1])
        else
          .error s!"`kernel(… : …)` takes one operation, got {args.size}"
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
  -- the guard-position `∈` IS the `contains` call (one relation, one
  -- production), so the guard reaches the same routed membership decision
  -- every other spelling of `∈` does
  | ``casMemFilterSet =>
      return .comprehension (.ref stx[1].getId) stx[1].getId (← toExpr stx[3])
        (some (.method (← toExpr stx[7]) `contains #[← toExpr stx[5]]))
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
  | k =>
      match ext k with
      | some t => t toExpr stx
      | none => .error s!"unsupported cas syntax node '{k}'"

/-- Translate a `casTerm`, consulting the contributed-production table. The
elaborators enter here; `toExprCore` with an empty lookup is the closed core
grammar alone. -/
def toExpr (stx : Syntax) : IO (Except String CasExpr) := do
  let table ← termTranslatorsRef.get
  return toExprCore
    (fun k => table.findSome? fun (n, t) => if n == k then some t else none) stx

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
  | none, some (.multiset dom elems) => Codec.valueToJson (.msetV elems dom)
  | none, some (.arithProg dom first step last?) =>
      Codec.valueToJson (.progV dom first step last?)
  | none, some (.span n basis) => Codec.valueToJson (.spanV n basis)
  | none, some (.coset offset kernel) => Codec.valueToJson (.cosetV offset kernel)
  -- spelled out rather than a wildcard: a new set presentation must fail this
  -- build and be decided, not silently publish `null`
  | none, some (.domainSet _) | none, some (.product _ _) | none, some (.powerset _)
  | none, some (.domainDiff _ _) | none, some (.predicate ..) | none, none => Json.null

private def denoteJson (d : Denote) : Json :=
  Json.mkObj
    [("render", .str d.render),
     ("presentation", .str d.presentation),
     ("value", valueJson d)]

/-! ## Elaborator helpers

Defined ABOVE the command block so their `do`/`let` bodies parse before the
`let` command production exists. -/

private def parseCas (stx : Syntax) : CommandElabM CasExpr := do
  match ← toExpr stx with
  | .ok e => return e
  | .error m => throwError m

private def casCtx (ambient? : Option Domain := none) : CommandElabM EvalCtx := do
  return { env := ← getEnv, ambient?, notes := ← IO.mkRef #[] }

/-- Run an evaluation and surface its accumulated notes as `info` lines.
Drained on BOTH outcomes: a note describes a call that already succeeded
(the roots deficit), and a later failure in the same statement does not
unsay it. -/
private def runCas (ctx : EvalCtx) (x : EvalM α) : CommandElabM α := do
  let r ← x.run
  for note in ← ctx.notes.modifyGet fun ns => (ns, #[]) do logInfo note
  match r with
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
      let ctx ← casCtx
      match ← runCas ctx (eval ctx (← parseCas t)) with
      | .obj (.domainObj d) => return some d
      | other => throwError s!"`in {other.render}` is not a domain"

private def bindObj (n : Name) (o : Obj) : CommandElabM Unit := do
  -- `e` and `i` are reserved SYMBOLS (ruling 2026-07-31, #31 item 3):
  -- Euler's constant and the imaginary unit, which no binding may shadow
  if let some m := reservedConstantMsg? n then throwError m
  modifyEnv fun env => addBinding env (n, o)
  emitOutput {
    data :=
      [("text/plain", .str s!"{n} := {o.presentation}")]
      ++ (o.presentationLatex?.toList.map fun l => ("text/latex", Json.str s!"$${n} := {l}$$"))
  }

/-- `let x [: T] := e [in C]`. Both ascriptions are CHECKED judgments, and a
spelling that carries both carries both checks: the leading `T` decides how
the right-hand side is read (a `↦` body's domains), and the trailing `in C`
is applied to the object that comes out. -/
def elabCasLet (idStx valStx : Syntax) (asc? : Option Syntax)
    (tail? : Option Syntax := none) : CommandElabM Unit := do
  let e ← parseCas valStx
  let a? ← asc?.mapM parseCas
  let t? ← tail?.mapM parseCas
  let ctx ← casCtx
  bindObj idStx.getId (← runCas ctx do
    let o ← evalBinding ctx e a?
    match t? with
    | none => pure o
    | some t => ascribe ctx o (← evalAscription ctx t))

def elabCasLetPoly (idStx xStx valStx ascStx : Syntax) : CommandElabM Unit := do
  let e ← parseCas valStx
  let a ← parseCas ascStx
  let ctx ← casCtx
  bindObj idStx.getId (← runCas ctx (evalPolyBinding ctx xStx.getId e a))

private def relOf (relStx : Syntax) : CommandElabM AssertRel :=
  match relStx.getKind with
  -- `is` "just means `=`" (SPEC.md §Ellipses), so it IS `.eq` — one relation,
  -- two spellings, decided identically both ways
  | ``casRelEq | ``casRelIs => pure .eq
  | ``casRelNe => pure .ne
  | ``casRelMem | ``casRelIn | ``casRelMemBS => pure .mem
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
    match ← runCas ctx (evalAssert ctx rel (← parseCas lhs) (← parseCas rhs)) with
    | some true => pure ()
    | some false => throwError s!"assertion is false: {which}"
    | none => throwError s!"the assertion outcome is unknown: the two sides of \
{which} are not comparable"
  logInfo s!"✓ {stated}"

/-- A bare proposition cell: `gcd(84, 30) = 6`. A proposition is three-valued
— `true | false | unknown` — and the cell displays that truth value, by the
same convention a bare expression cell displays its value. `assert` is the
COLLAPSING form (SPEC.md): it commits only on `true`, and `false` and
`unknown` are both assertion failures there. A chain or `in D` tail reads
exactly as it does under `assert`. Low priority for the reason the
bare-expression cell is. -/
def elabCasAssertBare (parts : Array Syntax) (tail? : Option Syntax)
    : CommandElabM Unit := do
  let ctx ← casCtx (← ambientOf tail?)
  let mut claims : Array (AssertRel × Syntax × Syntax) := #[]
  for p in parts do
    claims := claims.push (← relOf p[1], p[0], p[2])
  -- conjunction on the three-valued lattice: `false` beats `unknown`
  let mut outcome : Option Bool := some true
  for claim in claims do
    let (rel, lhs, rhs) := claim
    if outcome == some false then break
    match ← runCas ctx (evalAssert ctx rel (← parseCas lhs) (← parseCas rhs)) with
    | some true => pure ()
    | some false => outcome := some false
    | none => if outcome == some true then outcome := none
  let truth : String := match outcome with
    | some true => "true" | some false => "false" | none => "unknown"
  emitOutput { data := [("text/plain", .str truth)] }

/-- A bare expression cell: display the value as text and as a structured
MIME bundle. LaTeX-first (#16): a value with a natural LaTeX form carries it
as `text/latex`, wrapped in `$$…$$` so the notebook's MathJax picks it up
without a `show()`, and `text/plain` stays in the bundle as the fallback
every consumer can read. A value with no LaTeX form emits plain text alone.
DISPLAY register, like Sage's `backend_ipython` and IPython's `display.Math`:
a cell RESULT is displayed math, and inline `$…$` typesets a `pmatrix` at
text size with undersized delimiters. -/
def elabCasShow (stx : Syntax) : CommandElabM Unit := do
  let ctx ← casCtx
  let d ← runCas ctx (eval ctx (← parseCas stx))
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
spells the definition both `:=` and `=`, so both are accepted — and it spells
the ascription both `in` and `∈` (`let f(t) = ∑… ∈ ℤ[[t]]`), which is the
ASCII/Unicode pair the assertion relation already carries. -/
syntax (name := casLetPoly)
  "let " ident noWs "(" ident ")" (" := " <|> " = ") casTerm
    (" in " <|> " ∈ " <|> " \\in ") casTerm : command

/-- `let e: ℕ → ℕ := n ↦ 2n` — SPEC.md's leading-ascription spelling. The
type is the same ascription the trailing `in T` carries, checked identically
— and the trailing one may be written TOO (`let φ: ℚ³ → ℚ := … in Mod(ℚ)`).
Without that tail the `in C` is not part of this command at all: it parses
as the next command, a bare display of `C`, so the ascription the author
wrote is never checked and the diagnostic names a term they did not write. -/
syntax (name := casLetTyped)
  "let " ident " : " casTerm " := " casTerm (" in " casTerm)? : command

/-- `assert l (= | ≠ | ∈ | ∉ | ⊆) r (and …)* [in D]` — a TRUSTED COMPUTATIONAL assertion
in the ordinary CAS sense. The predicate is computed and believed; no Lean
proposition is created, no theorem is generated, and no certificate is
required. The outcome is fourfold — `true | false | unknown | error` — and
only `true` lets the cell commit, so a failed assertion rolls the cell's
registrations back with the worker's cell atomicity. `in D` sets the ambient
domain the literals and arithmetic are read in. -/
syntax (name := casAssert)
  "assert " casAssertion (&"and" casAssertion)* (" in " casTerm)? : command

/-- A bare proposition cell: `gcd(84, 30) = 6` — the same shape `assert`
carries (chain and `in D` tail included), displaying the three-valued truth
`true | false | unknown`. Low priority for the reason the bare-expression
cell is. -/
syntax (name := casAssertBare) (priority := low)
  casAssertion (&"and" casAssertion)* (" in " casTerm)? : command

/-- A bare expression cell displays its value. Low priority, so every
genuine Lean command in a cell still parses as Lean. -/
syntax (name := casShow) (priority := low) casTerm : command

/-- `NAME := expr [in T]` — SPEC.md's opening sentence ("Definitions use :=")
written without the `let`, as its §Polynomials line `q := map p to ℂ[x]`
does. Ruled a COMMAND (2026-07-31, #31 item 2): pure sugar for `let`, the
same elaborator, the same checked ascription. Low priority for the reason
the bare-expression cell is. -/
syntax (name := casDef) (priority := low)
  ident " := " casTerm (" in " casTerm)? : command

@[command_elab casLet]
def elabLetCmd : CommandElab := fun stx =>
  elabCasLet stx[1] stx[3] (optTail? stx[4])

@[command_elab casDef]
def elabDefCmd : CommandElab := fun stx =>
  elabCasLet stx[0] stx[2] (optTail? stx[3])

@[command_elab casLetPoly]
def elabLetPolyCmd : CommandElab := fun stx =>
  elabCasLetPoly stx[1] stx[3] stx[6] stx[8]

@[command_elab casLetTyped]
def elabLetTypedCmd : CommandElab := fun stx =>
  elabCasLet stx[1] stx[5] (some stx[3]) (optTail? stx[6])

@[command_elab casAssert]
def elabAssertCmd : CommandElab := fun stx =>
  elabCasAssert (#[stx[1]] ++ stx[2].getArgs.map (·[1])) (optTail? stx[3])

@[command_elab casAssertBare]
def elabAssertBareCmd : CommandElab := fun stx =>
  elabCasAssertBare (#[stx[0]] ++ stx[1].getArgs.map (·[1])) (optTail? stx[2])

@[command_elab casShow]
def elabShowCmd : CommandElab := fun stx => elabCasShow stx[0]

end CasDsl
