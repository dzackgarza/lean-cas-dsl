/-
The surface evaluator: `CasExpr` → `Obj`, with ALL method execution routed
through `resolveMethod → routeFor → execute`.

Two disciplines are load-bearing here:

- **Backend blindness.** Nothing in this module names a backend, tests a
  backend name, or reaches an executor except through `Route.execute`. The
  only executor-shaped call is `Native.polyEval`, and it is not a method
  execution: calling a polynomial is a *coercion inserted by elaboration*
  (DESIGN.md decision 6), the same category of move as `ℤ ⊆ ℚ`.
- **A pure core.** Arithmetic, coefficient embeddings, progression
  construction and the `D[x]`-vs-`e[k]` disambiguation are `Except String`
  functions over plain data, so they are `#guard`-testable without an
  `Environment` and without `IO` — the canonical-map registry reaches them
  as a threaded `Array CanonicalMap`, not as an environment read. `eval`
  adds registry reads and executor calls, nothing else.
-/
import CasDsl.Native

namespace CasDsl

open Lean (Name Environment)

/-! ## The surface AST

Produced by `CasDsl/Syntax.lean`; first-order, with no elaboration state.
Everything the parser cannot decide on its own — whether `D[x]` is a
polynomial ring or an index, whether an ascription names a domain or a
category — is decided here, against the registries. -/

inductive BinOp where
  | add | sub | mul | div | pow
  deriving BEq, Repr, Inhabited

/-- The order comparisons a set-comprehension guard is written with
(`n² ≤ 20`, `0 ≤ n < 6`). Equality is deliberately absent: `=` is the
assertion relation, category-bound, and reading it as a term-level
comparison here would give the surface two meanings for one symbol. -/
inductive CmpOp where
  | le | lt | ge | gt
  deriving BEq, Repr, Inhabited

inductive CasExpr where
  | num (z : Int)
  /-- A literal that is not a numeral: `ℵ₀`, `true`, `false`. -/
  | lit (v : Value)
  /-- A binding name, or the bound polynomial indeterminate. -/
  | ref (n : Name)
  /-- An atomic domain term (`ℕ`, `ℤ`, `ℚ`). -/
  | dom (d : Domain)
  /-- `Matₙ(E)`. -/
  | matDom (size : Nat) (entry : CasExpr)
  | neg (e : CasExpr)
  | bin (op : BinOp) (a b : CasExpr)
  /-- `f(args…)` — polynomial/function call. -/
  | app (f : CasExpr) (args : Array CasExpr)
  /-- `e.m(args…)`. -/
  | method (recv : CasExpr) (m : Name) (args : Array CasExpr)
  /-- `e[a]` — a polynomial ring or an index; decided in `eval`. -/
  | index (recv : CasExpr) (arg : CasExpr)
  | finSet (elems : Array CasExpr)
  /-- `{a, b, …, ...}` / `{a, b, …, ..., z}`: the leading elements and the
  optional inclusive bound. -/
  | progSet (leading : Array CasExpr) (last? : Option CasExpr)
  /-- Row-major; `rows * cols = entries.size`. -/
  | matLit (rows cols : Nat) (entries : Array CasExpr)
  /-- `(1, 2)` — a vector of `Eⁿ`, where `E` is the join of its components'
  domains and `n` their count (SPEC.md §Vectors and matrices). -/
  | vecLit (comps : Array CasExpr)
  | mapTo (e target : CasExpr)
  /-- `ℝ/O(ε)` — the target of SPEC.md's `map √2 to ℝ/O(1/10^{10})`, and
  meaningful ONLY there. It is not a domain, not a set and not a quotient
  (`|a − b| < ε` is not transitive, so there are no classes): it is the
  REQUEST that a decimal presentation meet a tolerance. Written anywhere else
  it is a loud refusal, which is what keeps `ℝ ⊆ ℝ/O(ε)` from being a claim
  this surface can even state. -/
  | approxTarget (eps : CasExpr)
  /-- `binder ↦ body` — a function definition, meaningful only where an
  ascription says which domains it runs between (`evalBinderBinding`). -/
  | lam (binder : Name) (body : CasExpr)
  /-- `S → T` / `S -> T` — a function domain. -/
  | arrow (src tgt : CasExpr)
  /-- `f ∘ g`. -/
  | comp (f g : CasExpr)
  /-- `√e` — the exact square root of a rational (SPEC.md's `√2`, `2√2`). -/
  | sqrt (e : CasExpr)
  /-- `|e|` — SPEC.md's bars, ONE spelling of "the size of e" whose METHOD
  depends on the receiver: `cardinality` for a set, `abs` for an element of
  ℝ or ℂ. Both are ordinary category methods; the bars invent nothing, so
  `|3|` is still the honest "not a method of any category this object
  belongs to". -/
  | magnitude (e : CasExpr)
  /-- `A × B` and `𝒫(A)` / `2^A`. Both DENOTE a set rather than compute one
  (their elements are pairs and sets, which no `Value` presents), so they
  build a presentation exactly as a set literal does — no method, no route. -/
  | setProduct (a b : CasExpr)
  | powersetOf (a : CasExpr)
  /-- `a ≤ b` and the chain `a ≤ b < c`, which is its conjunction. -/
  | cmp (op : CmpOp) (a b : CasExpr)
  | conj (a b : CasExpr)
  /-- A comprehension `{head | binder ∈ index, guard}`. SPEC.md's filtering
  spelling `{n ∈ ℤ | P}` is this node with `head = binder` — one shape, so
  one evaluator decides both. -/
  | comprehension (head : CasExpr) (binder : Name) (index : CasExpr)
      (guard? : Option CasExpr)
  deriving Inhabited

/-! ## Pure core -/

/-- The presented domain of a value, when it has one. Cardinals, truth
values, ideals and factorizations are results, not elements of a presented
domain — they are carried as `Denote.val` rather than given a fake one. -/
def valueDom? : Value → Option Domain
  | .int _ => some .int
  | .rat _ => some .rat
  | .mod n _ => some (.mod n)
  -- the SIGN of the radicand is what a surd presents: `√2` is a real number
  -- and `2 + 2i` is not
  | .alg _ _ d => some (if d < 0 then .complex else .real)
  | .poly c _ => some (.poly c)
  | .mat n e _ => some (.matrix n e)
  | .vec n e _ => some (.vector n e)
  | .func s t _ _ => some (.funcs s t)
  | _ => none

/-! ### The coercion layer

Every coercion the surface inserts (`map e to D`, a mixed-domain join, the
element promotion of a set or matrix literal, a domain ascription) asks the
CANONICAL-MAP REGISTRY which preferred maps exist — `map` means "apply the
preferred canonical map when one is registered, fail otherwise", and the
registered maps need not be injections (`ℤ → ℤ/n` is a quotient). The
engine keeps only the cases that are not a preferred-map choice at all —
they are listed, with their reasons, on `coerceValue` below.

The registry is threaded as a plain `Array CanonicalMap` rather than read from
the `Environment` here, so the whole layer stays `#guard`-testable; `eval`
passes `canonicalMaps ctx.env`. -/

/-- A value with no domain is a RESULT, not an element of one — the shared
wording, so a set literal and a coercion refuse it for the same stated reason. -/
def notAnElement (v : Value) (what : String) : String :=
  s!"{v.render} is a RESULT and not an element of any domain — like a \
factorization or a cardinal, and an approximation with it — so {what}"

/-- Mathematician-facing rendering of a pattern. Defined here because the
canonical-map-registry defect messages name the two rules that clashed; the
diagnostics below share it. -/
partial def renderDomainPattern : DomainPattern → String
  | .exact d => d.render
  | .polyOver p => s!"{renderDomainPattern p}[x]"
  | .matrixOver p => s!"Mat(_, {renderDomainPattern p})"
  | .anyMod => "ℤ/_"
  | .anyFuncs => "_ → _"
  | .anyDom => "_"

def renderCanonicalMap (r : CanonicalMap) : String :=
  let base := s!"{renderDomainPattern r.src} → {renderDomainPattern r.tgt} \
(op {repr r.op})"
  if r.doc.isEmpty then base else s!"{base}: {r.doc}"

/-- The registered preferred canonical map of `srcDom` into `tgtDom`.

`.ok none` = none is registered (the caller reports that in its own words);
`.ok (some r)` = exactly one. MORE than one applicable rule is a defective
registration and is reported with both rules named — the same discipline as
the resolver's `ambiguous`: a coercion is never chosen by registration
order, array position, or specificity invented here. -/
def canonicalMapFor (rules : Array CanonicalMap) (srcDom tgtDom : Domain)
    : Except String (Option CanonicalMap) :=
  let ms := rules.filter (·.applies srcDom tgtDom)
  match ms[0]?, ms[1]?, ms.size with
  | some r, _, 1 => .ok (some r)
  | none, _, _ => .ok none
  | some r1, some r2, n =>
      .error s!"the canonical-map registry is defective: {n} registered rules give a \
preferred canonical map of {srcDom.render} into {tgtDom.render} — \
{renderCanonicalMap r1} and {renderCanonicalMap r2}. A coercion does not rank them; \
unregister one."
  | _, _, _ => .ok none

/-- The preferred common domain of two presentations: the one the other has
a registered canonical map into (`ℕ ⊆ ℤ ⊆ ℚ` as the prelude registers
them), and the same judgment applied under `poly`/`matrix`.

`.ok none` = neither maps into the other, so there is no canonical join —
the caller words that failure. `.error` = a DEFECTIVE registration: both
directions are registered, and a join between two domains that map into
each other has no preferred answer. It is surfaced, never resolved by
picking a side. -/
partial def domJoin (rules : Array CanonicalMap)
    : Domain → Domain → Except String (Option Domain)
  | .poly a, .poly b => do return (← domJoin rules a b).map .poly
  | .matrix n a, .matrix m b =>
      if n == m then do return (← domJoin rules a b).map (Domain.matrix n)
      else return none
  | .vector n a, .vector m b =>
      if n == m then do return (← domJoin rules a b).map (Domain.vector n)
      else return none
  | a, b =>
      if a == b then return some a
      else do
        match ← canonicalMapFor rules a b, ← canonicalMapFor rules b a with
        | some ab, some ba =>
            .error s!"the canonical-map registry is defective: {a.render} and \
{b.render} have canonical maps into each other ({renderCanonicalMap ab} and \
{renderCanonicalMap ba}), so neither is the preferred common domain. Unregister one."
        | some _, none => return some b
        | none, some _ => return some a
        | none, none => return none

/-- The preferred canonical map of a value into `d`, and the ONLY coercion
the surface performs. The BASE CASE — one scalar domain into another — is
decided by the registered canonical maps: exactly one applicable rule
applies, none is an honest error, several is a loud registration defect.

Four cases stay ENGINE-LEVEL, each because it is not a preferred-map choice
between two domains and so cannot be registry data:

- **structural congruence** under `poly`/`matrix` (and a scalar as a constant
  polynomial): a canonical map of coefficient/entry domains INDUCES the one
  on polynomials and matrices, so registering `ℤ[x] → ℚ[x]` separately would
  be a second place to state `ℤ ⊆ ℚ` — and a second place to get it wrong.
  The recursion bottoms out in the registry-driven base case;
- **identity**, when the value already presents the target: the identity of a
  domain is not a preferred choice the prelude gets to make (and `ℤ/n → ℤ/n`
  would need one rule per modulus);
- **`ℕ ← ℤ`**, which is a CHECK, not a map: it is partial, so this is the
  membership judgment "is this integer in ℕ?" and a registry of total
  preferred maps must not be able to state it;
- **`ℤ/m` vs `ℤ/n`**, where the reported fact is the ABSENCE of a canonical
  map between two different rings — no rule can express that.

Nothing here may be widened by adding a "reasonable" conversion: an
unregistered pair is an honest error. -/
partial def coerceValue (rules : Array CanonicalMap) (d : Domain) (v : Value)
    : Except String Value :=
  match d, v with
  -- structural congruence
  | .poly c, .poly _ cs => do return Value.mkPoly c (← cs.mapM (coerceValue rules c))
  | .poly c, s => do return Value.mkPoly c #[← coerceValue rules c s]
  | .matrix n e, .mat m _ rows =>
      if n != m then
        .error s!"a {m}×{m} matrix is not an element of Mat{n}(…)"
      else do
        return .mat n e (← rows.mapM (·.mapM (coerceValue rules e)))
  | .vector n e, .vec m _ comps =>
      if n != m then
        .error s!"a vector of length {m} is not an element of {(Domain.vector n e).render}"
      else do
        return .vec n e (← comps.mapM (coerceValue rules e))
  | d, v =>
      -- identity
      if valueDom? v == some d then .ok v
      else match d, v with
      -- the `ℕ ← ℤ` check
      | .nat, .int z =>
          if z ≥ 0 then .ok v
          else .error s!"{z} is not an element of ℕ"
      -- different rings, no canonical map
      | .mod n, .mod m _ => .error s!"ℤ/{m} and ℤ/{n} are different rings"
      -- the base case: registry data decides
      | d, v => do
          let noEmbedding : Except String Value :=
            .error s!"there is no preferred canonical map of {v.render} into {d.render}"
          let some src := valueDom? v
            | .error (notAnElement v s!"there is nothing to carry into {d.render}")
          match ← canonicalMapFor rules src d with
          | some r => r.op.apply d v
          | none => noEmbedding

/-- `D ⊆ E`: **there is a preferred canonical map of `D` into `E` and it is an
inclusion**. SPEC.md's `assert ℤ ⊆ ℚ and ℚ ⊆ ℝ and ℝ ⊆ ℂ` is exactly that
claim, and the canonical-map registry owns it — DESIGN.md §Coercions already
says which domains include which, and the set layer refuses to restate it
(`Native.normalSubset`), so this is the ONE place it is answered.

The recursion is `coerceValue`'s, for the same reason: a canonical map of
coefficient/entry domains INDUCES the one on polynomials and matrices, and a
scalar is its own constant polynomial (`ℤ ⊆ ℤ[x]`). It bottoms out in the
registry, so unregistering a rule takes the corresponding inclusion with it.

`false` where nothing is registered is not a guess: `⊆` between two domains
MEANS identification along the preferred canonical map, and no such map is
exactly the absence of that identification. `.error` stays the registry's own
defect report. -/
partial def domainSubset (rules : Array CanonicalMap)
    : Domain → Domain → Except String Bool
  | .poly a, .poly b => domainSubset rules a b
  | .matrix n a, .matrix m b =>
      if n == m then domainSubset rules a b else return false
  | .vector n a, .vector m b =>
      if n == m then domainSubset rules a b else return false
  -- a scalar is an element of its own constant polynomials
  | a, .poly c => domainSubset rules a c
  | a, b =>
      if a == b then return true
      else do
        match ← canonicalMapFor rules a b with
        | some r => return r.op.isInclusion
        | none => return false

/-! ### Polynomial arithmetic

Coefficients ride on `Native`'s exact scalar operations (which promote along
`ℤ ⊆ ℚ` internally — the executor's own implementation detail, not a surface
coercion); this layer only manages degrees and the resulting coefficient
domain, which is the registry-driven `domJoin`. -/

/-- A value as `(coefficient domain, ascending coefficients)`; a scalar is
its own constant polynomial. -/
def asPolyCoeffs : Value → Option (Domain × Array Value)
  | .poly c cs => some (c, cs)
  | v@(.int _) => some (.int, #[v])
  | v@(.rat _) => some (.rat, #[v])
  | v@(.mod n _) => some (.mod n, #[v])
  -- an exact algebraic number is a constant of ℝ[x] or ℂ[x], which is what
  -- lets `x² - √2 in ℂ[x]` be written at all
  | v@(.alg _ _ d) => some (if d < 0 then .complex else .real, #[v])
  | _ => none

private def pad (cs : Array Value) (i : Nat) : Value :=
  cs[i]?.getD (.int 0)

def polyAdd (a b : Array Value) : Except String (Array Value) :=
  (Array.range (max a.size b.size)).mapM fun i =>
    Native.scalarAdd (pad a i) (pad b i)

def polySub (a b : Array Value) : Except String (Array Value) :=
  (Array.range (max a.size b.size)).mapM fun i =>
    Native.scalarSub (pad a i) (pad b i)

def polyMul (a b : Array Value) : Except String (Array Value) := do
  if a.isEmpty || b.isEmpty then return #[]
  let mut out := Array.replicate (a.size + b.size - 1) (Value.int 0)
  for i in [0:a.size] do
    for j in [0:b.size] do
      out := out.set! (i + j) (← Native.scalarAdd out[i + j]!
        (← Native.scalarMul a[i]! b[j]!))
  return out

def polyNeg (a : Array Value) : Except String (Array Value) :=
  a.mapM Native.scalarNeg

/-- `p^k` by repeated multiplication; the exponent is a nonnegative
integer, exactly as for scalars. -/
def polyPow (a : Array Value) (k : Nat) : Except String (Array Value) :=
  (List.range k).foldlM (fun acc _ => polyMul acc a) #[Value.int 1]

private def exponentNat? : Value → Option Nat
  | .int z => if z < 0 then none else some z.toNat
  | .rat q => if q.den == 1 && q.num ≥ 0 then some q.num.toNat else none
  | _ => none

/-- Binary arithmetic on values. A polynomial operand pulls the whole
operation into the polynomial ring over the joined coefficient domain (the
join, and the coefficient embeddings into it, come from the registry);
otherwise this is `Native`'s exact scalar arithmetic. -/
def valueBin (rules : Array CanonicalMap) (op : BinOp) (a b : Value)
    : Except String Value := do
  let isPoly : Value → Bool := fun | .poly .. => true | _ => false
  if isPoly a || isPoly b then
    match op with
    | .div =>
        .error s!"polynomial division is not available ({a.render} / {b.render})"
    | .pow =>
        let some (ca, as) := asPolyCoeffs a
          | .error s!"{a.render} is not a polynomial"
        let some k := exponentNat? b
          | .error s!"exponentiation needs a nonnegative integer exponent, got {b.render}"
        return Value.mkPoly ca (← (← polyPow as k).mapM (coerceValue rules ca))
    | _ =>
        let some (ca, as) := asPolyCoeffs a
          | .error s!"{a.render} is not a polynomial"
        let some (cb, bs) := asPolyCoeffs b
          | .error s!"{b.render} is not a polynomial"
        let some d ← domJoin rules ca cb
          | .error s!"{ca.render}[x] and {cb.render}[x] have no common coefficient domain"
        let cs ← match op with
          | .add => polyAdd as bs
          | .sub => polySub as bs
          | _ => polyMul as bs
        return Value.mkPoly d (← cs.mapM (coerceValue rules d))
  else
    match op with
    | .add => Native.scalarAdd a b
    | .sub => Native.scalarSub a b
    | .mul => Native.scalarMul a b
    | .div => Native.scalarDiv a b
    | .pow => Native.scalarPow a b

def valueNeg (a : Value) : Except String Value :=
  match a with
  | .poly c cs => do return Value.mkPoly c (← polyNeg cs)
  | v => Native.scalarNeg v

/-! ### Functions

SPEC.md's functions are `binder ↦ body` with a domain tag (`in ℝ → ℝ`), and
its claims about them — `h(0) = 1`, `h(-t) = h(t)`, `(f ∘ g)(t) = t⁶` — are
IDENTITIES of function expressions, not pointwise samples. They are decided
here by the exact polynomial engine above: every body SPEC.md writes in this
section is a polynomial, and substituting one polynomial into another settles
both the composition and the symmetry claim exactly.

Non-polynomial bodies (`t ↦ sin(t)`, `t ↦ e^t`) are therefore not expressible
yet, and say so at the binding rather than being approximated. -/

/-- The ring the callee's binder is the indeterminate of: its SOURCE domain,
so `k(t)` on a `ℤ/5 → ℤ/5` arrow is symbolic in ℤ/5 and not in ℤ. ℝ is the
exception it always is — it has no `Value`s, so the body's own ring stands in.

`none` = the body is not a polynomial. Every path that builds a `.func`
checks that (`evalBinderBinding`, and `composeFuncs` via `applyPoly`), so
only a hand-built or decoded value reaches it; both call sites fail loudly
rather than defaulting to ℤ. -/
def binderRing (src : Domain) (body : Value) : Option Domain :=
  match src with
  | .real => (asPolyCoeffs body).map (·.1)
  | d => some d

/-- The indeterminate of `c[x]` as a surface value — `x` itself. -/
def indeterminateValue (rules : Array CanonicalMap) (c : Domain)
    : Except String Value := do
  return Value.mkPoly c
    #[← coerceValue rules c (.int 0), ← coerceValue rules c (.int 1)]

/-- Substitute `arg` into a polynomial body, by Horner over `valueBin`.

Deliberately NOT `Native.polyEval`: that one is scalar Horner, which is all a
polynomial CALL needs. Here the argument may itself be a polynomial (`h(-t)`,
`f ∘ g`), which is exactly what makes the SPEC.md identities identities. -/
def applyPoly (rules : Array CanonicalMap) (body arg : Value)
    : Except String Value := do
  let some (_, cs) := asPolyCoeffs body
    | .error s!"a function cannot be applied: its body {body.render} is not a \
polynomial"
  cs.reverse.foldlM (init := Value.int 0) fun acc c => do
    valueBin rules .add (← valueBin rules .mul acc arg) c

/-- One end of a `src → tgt` ascription, ENFORCED: an argument must land in
the source domain and a result in the target, by the ordinary preferred
canonical map, or the call fails.

Two cases pass through, and only two:

- `.real`, which is an ascription TAG — it has no `Value`s to check, which is
  the whole content of "ℝ carries no analysis semantics here";
- a polynomial, which is the SYMBOLIC path: `h(-t)` and `(f ∘ g)(t)` denote
  function expressions, not points of the domain, so a domain check on them
  would be a category error rather than a safety net. -/
def atDomain (rules : Array CanonicalMap) (d : Domain) (v : Value)
    : Except String Value :=
  match d, v with
  | .real, _ => .ok v
  -- the symbolic path is coefficient-wise: `coerceValue` already recurses
  -- under `.poly`, so a ℤ/5 arrow reduces `t + 7` to `t + 2` instead of
  -- carrying an unreduced ℤ polynomial past its own domain
  | d, v@(.poly ..) => coerceValue rules (.poly d) v
  | d, v => coerceValue rules d v

/-- `f ∘ g` = `binder ↦ f(g(binder))`, keeping `g`'s binder.

The domains must meet: composing along `g : A → B` and `f : C → D` with
`B ≠ C` is a mathematical error, never something to coerce past. -/
def composeFuncs (rules : Array CanonicalMap) : Value → Value → Except String Value
  | .func fs ft _ fb, .func gs gt gbinder gb =>
      if fs != gt then
        .error s!"{gs.render} → {gt.render} and {fs.render} → {ft.render} do not \
compose: the target of the right factor is not the source of the left"
      else do return .func gs ft gbinder (← applyPoly rules fb gb)
  | a, b => .error s!"∘ composes two functions; got {a.render} and {b.render}"

/-! ### Set literals -/

/-- Element domain of a literal element list. -/
def elemsDomain (rules : Array CanonicalMap) (vs : Array Value)
    : Except String Domain :=
  vs.foldlM (init := Domain.int) fun d v =>
    match valueDom? v with
    | none => .error (notAnElement v "it cannot be an element of a set literal")
    | some d' => do
        match ← domJoin rules d d' with
        | some j => .ok j
        | none => .error s!"{d.render} and {d'.render} have no common domain"

/-- Build the progression a `{a, b, …, ...}` literal denotes: the step is
inferred from the two leading elements (one leading element means step 1),
and EVERY leading element must lie on the inferred progression — a literal
that is not one is a mistake, not a set to guess at. -/
def progressionOf (rules : Array CanonicalMap) (leading : Array Value)
    (last? : Option Value) : Except String SetPresentation := do
  let some first := leading[0]?
    | .error "a progression literal needs at least one leading element"
  let step ← match leading[1]? with
    | some second => Native.scalarSub second first
    | none => pure (.int 1)
  for i in [0:leading.size] do
    let expect ← Native.scalarAdd first (← Native.scalarMul (.int (Int.ofNat i)) step)
    if Native.valueEq expect leading[i]! != some true then
      .error s!"{leading[i]!.render} is not the element at index {i} of the \
progression starting {first.render} with step {step.render}"
  let d ← elemsDomain rules (leading ++ (last?.toArray))
  return .arithProg d (← coerceValue rules d first) (← coerceValue rules d step)
    (← last?.mapM (coerceValue rules d))

/-! ### Deciding a comprehension guard

`{n ∈ ℤ | n² ≤ 20}` is a claim about ALL integers, so it is decided rather
than sampled: the guard is rewritten as `p(n) ⋈ 0` for an exact polynomial
`p` (each side is evaluated with the binder as the indeterminate, and the
difference taken), and a Cauchy-style bound `N` is extracted with

    |p(n)| ≥ |n|^{d-1}(|a_d||n| − S) ≥ 1 > 0   for |n| ≥ N := max(1, ⌈(S+1)/|a_d|⌉)

where `S = Σ_{i<d}|a_i|`. `p` has no root beyond `±N`, so it keeps ONE sign
on each tail, and evaluating it at `±N` says whether that tail satisfies the
guard: if it does the comprehension is infinite and says so; if it does not,
every solution lies inside the bound and is found by testing each integer
exactly. Nothing here samples, and nothing cuts an enumeration short.

A guard the rewriting does not reach (`n.is_prime()`, a membership test) has
no bound, and the comprehension is REFUSED at the binding — the same move
§Functions makes for a body the polynomial engine cannot express. -/

/-- The bounds on a comprehension binder; `none` = that side is unbounded. -/
structure BinderBounds where
  lo : Option Int := none
  hi : Option Int := none
  deriving Repr, Inhabited

/-- Conjunction of guards intersects their bounds: `0 ≤ n < 6` is bounded
below by one conjunct and above by the other, and by neither alone. -/
def BinderBounds.meet (a b : BinderBounds) : BinderBounds where
  lo := match a.lo, b.lo with
    | some x, some y => some (max x y)
    | some x, none | none, some x => some x
    | none, none => none
  hi := match a.hi, b.hi with
    | some x, some y => some (min x y)
    | some x, none | none, some x => some x
    | none, none => none

/-- Ceiling of a rational. `den > 0`, so Euclidean division of the negated
numerator is the floor of `−q`. -/
def ratCeil (q : Rat) : Int := -(Int.ediv (-q.num) (Int.ofNat q.den))

private def absRat (v : Value) : Option Rat :=
  (Native.toRat? v).map fun q => if q.blt 0 then -q else q

/-- `N ≥ 1` with `p(n) ≠ 0` for every `|n| ≥ N`, from the coefficient bound
above. `none` = the coefficients are not ordered rationals (a `ℤ/n`
polynomial has no such bound), or the polynomial is constant — neither is a
failure of the search, and both are reported as the refusal they are. -/
def polyTailBound (coeffs : Array Value) : Option Int := do
  if coeffs.size < 2 then none
  else
    let d := coeffs.size - 1
    let lead ← absRat coeffs[d]!
    if lead == 0 then none
    else
      let s ← (coeffs.extract 0 d).foldlM (init := (0 : Rat))
        fun acc v => do return acc + (← absRat v)
      return max 1 (ratCeil ((s + 1) / lead))

/-- Does `v ⋈ 0` hold? `none` = `v` is not ordered against zero. -/
def cmpAgainstZero (op : CmpOp) (v : Value) : Option Bool :=
  (Native.scalarCmp v (.int 0)).map fun ord =>
    match op with
    | .le => ord != .gt
    | .lt => ord == .lt
    | .ge => ord != .lt
    | .gt => ord == .gt

/-- A guard that does not mention the binder: it holds for every candidate or
for none, and neither is a bound to extract. "For none" is carried as the
EMPTY range, which enumerates to the empty set — a decided answer, not a
refusal. -/
def constantBounds (op : CmpOp) (v : Value) : Except String BinderBounds :=
  match cmpAgainstZero op v with
  | some true => .ok {}
  | some false => .ok { lo := some 0, hi := some (-1) }
  | none => .error s!"the guard does not order {v.render} against 0"

/-- The binder bounds one comparison `p(n) ⋈ 0` imposes. A tail that
SATISFIES the guard leaves that side unbounded — reported as such, so the
caller can refuse an infinite comprehension instead of truncating it. -/
def boundsOfPoly (op : CmpOp) (coeffs : Array Value) : Except String BinderBounds := do
  let some n := polyTailBound coeffs
    | .error "the guard is not a polynomial comparison with an extractable bound"
  let at? (k : Int) : Except String Bool := do
    let v ← Native.polyEval .int coeffs (.int k)
    match cmpAgainstZero op v with
    | some b => .ok b
    | none => .error s!"the guard does not order {v.render} against 0"
  return { lo := if ← at? (-n) then none else some (-n + 1)
           hi := if ← at? n then none else some (n - 1) }

/-! ### `D[x]` versus `e[k]`

DESIGN.md: brackets containing a lone identifier that is not a binding name
denote a polynomial indeterminate; anything else is an index. The decision
needs only the "is this name bound?" predicate, so it stays pure. -/

def indeterminate? (isBound : Name → Bool) : CasExpr → Option Name
  | .ref n => if isBound n then none else some n
  | _ => none

/-- SPEC.md's PREFIX spelling of a method call, as the rewrite it is:
`gcd(84, 30)` is `84.gcd(30)`.

A name reads this way only when it is UNBOUND and some category declares it
as a method, so the rewrite can never shadow a binding or invent an
operation — it turns what would be a "not bound" error into the call the
mathematician wrote. `eval` dispatches on the rewritten call and
`#explain_route` explains it, so the diagnostic cannot disagree with what
runs. -/
def prefixMethodCall? (isBound : Name → Bool) (env : Environment)
    : CasExpr → Option CasExpr
  | .app (.ref n) args =>
      if isBound n || (methodDecls env n).isEmpty then none
      else args[0]?.map fun recv => .method recv n (args.extract 1 args.size)
  | _ => none

/-- The names SPEC.md writes for a CONSTANT rather than for a binding: `i`,
the imaginary unit (`2 + 2i`). Consulted after the bindings and after the
domain aliases, so `let i := 3 in ℤ` shadows it exactly as `let R := …`
shadows ℝ — a constant is a spelling, not a reserved word. -/
def constantValue? : Name → Option Value
  -- through the normalizing constructor like every other value the surface
  -- produces: `none` here would be the ordinary "not bound" error, never a
  -- surd that skipped its invariant
  | `i => (Value.mkAlg 0 1 (-1)).toOption
  | _ => none

/-- The domains SPEC.md spells as ordinary identifiers rather than as their
own token: `R` and `RR` are ℝ (`let f(t) = t^2 in RR->RR`), `CC` is ℂ.

The Unicode names are here for a PARSER reason rather than a spelling one:
`ℝ.cardinality()` lexes as one hierarchical identifier (Lean's `ident` eats
the dot, and `ℝ` is an identifier character), so a domain used as a METHOD
RECEIVER arrives as a name and never as its own token. Without these arms
`ℝ.cardinality()` was the misleading "'ℝ' is not bound" instead of the honest
"this backend cannot express the cardinality of ℝ".

Consulted only after the bindings, so `let R := …` still shadows the alias —
an alias is a spelling, not a reserved word. -/
def domainAlias? : Name → Option Domain
  | `R | `RR => some .real
  | `CC => some .complex
  | `ℕ => some .nat
  | `ℤ => some .int
  | `ℚ => some .rat
  | `ℝ => some .real
  | `ℂ => some .complex
  | _ => none

/-! ## Evaluation results and errors -/

/-- What a surface expression denotes. `Obj` is the binding-level notion; a
computed value with no presented domain (a cardinal, a truth value, an
ideal, a factorization) stays a `Value` instead of being given a domain it
does not have. -/
inductive Denote where
  | obj (o : Obj)
  | val (v : Value)
  deriving Inhabited

namespace Denote

def render : Denote → String
  | .obj o => o.render
  | .val v => v.render

def presentation : Denote → String
  | .obj o => o.presentation
  | .val v => v.render

/-- The LaTeX form of what this denotes, or `none` when it has none and the
cell emits `text/plain` alone (DESIGN.md §LaTeX-first display). -/
def latex? : Denote → Option String
  | .obj o => o.latex?
  | .val v => v.latex?

def value? : Denote → Option Value
  | .val v => some v
  | .obj (.elem _ v) => some v
  | .obj _ => none

def obj? : Denote → Option Obj
  | .obj o => some o
  | .val v => (valueDom? v).map fun d => Obj.elem d v

/-- The set presentation this denotes — a domain used as a set is one, which
is what lets `𝒫(ℤ)` and `A × ℕ` be written at all. -/
def asSet? : Denote → Option SetPresentation
  | .obj (.setObj s) => some s
  | .obj (.domainObj d) => some (.domainSet d)
  | _ => none

/-- Wrap an executor result: it becomes an object when it presents one. A
set-valued result becomes the ordinary set OBJECT, so `p.roots()` is a set
like any other — the set methods, `∈` and set equality all reach it through
the usual profile rules rather than through a second notion of set. -/
def ofValue (v : Value) : Denote :=
  match v with
  | .setV elems dom => .obj (.setObj (.finite dom elems))
  | .progV dom first step last? => .obj (.setObj (.arithProg dom first step last?))
  | v =>
    match valueDom? v with
    | some d => .obj (.elem d v)
    | none => .val v

end Denote

/-- The ε of `ℝ/O(ε)`: an exact POSITIVE rational, read from the surface
spelling SPEC.md writes (`1/10^{10}`).

Refused HERE, before any backend is asked, because neither bound is a
tolerance rather than because no backend could meet it: no finite decimal
presentation is within 0 of an irrational number, and a negative bound is not
a request at all. That keeps `O(0)` a surface error and not a capability
failure — the two say different things about the system. -/
def notATolerance (q : Rat) : String :=
  if q == 0 then
    "O(0) is not a tolerance: no finite decimal presentation lies within 0 of \
an irrational number, so an absolute tolerance is a POSITIVE rational"
  else
    s!"O({Value.tolText q}) is not a tolerance: an absolute tolerance is a \
POSITIVE rational, and a negative bound is not one a decimal could ever meet"

def toleranceOf (v? : Option Value) (presentation : String) : Except String Rat :=
  match v?.bind Native.toRat? with
  | some q => if Rat.blt 0 q then .ok q else .error (notATolerance q)
  | none =>
      .error s!"the tolerance of `ℝ/O(ε)` is an exact positive rational, and \
{presentation} is not one"

inductive EvalError where
  | msg (m : String)
  | resolve (m : Name) (recv : Obj) (e : ResolveError)
  | gap (g : CapabilityGap)
  | tiedRoutes (m : Name) (rs : Array Route)
  | exec (e : ExecError)
  /-- The failure of an approximation REQUEST, carrying the tolerance that was
  asked for (issue #7's third acceptance criterion). It WRAPS rather than
  replaces: a capability gap under it still renders as the structured
  `NoImplementation` it is, an unreachable backend still says so, and ε is
  visible whichever of them happened — the failure is about what could not be
  computed, never about the value that was asked about. -/
  | approxRequest (eps : Rat) (inner : EvalError)
  deriving Inhabited

/-! ### Rendering the structured failures -/

def renderParam : ParamVal → String
  | .dom d => d.render
  | .nat n => toString n

def renderCat (c : CatRef) : String :=
  if c.params.isEmpty then toString c.name
  else s!"{c.name}({", ".intercalate (c.params.toList.map renderParam)})"

def renderPattern : PresPattern → String
  | .elemOf d => s!"element of {renderDomainPattern d}"
  | .domainIs d => s!"the domain {renderDomainPattern d}"
  | .finiteSet => "a finite set"
  | .progression d => s!"a progression over {renderDomainPattern d}"
  | .domainSetOf d => s!"the underlying set of {renderDomainPattern d}"
  | .productSet => "a cartesian product"
  | .powersetSet => "a powerset"
  | .domainDiffSet => "a difference of two domains"
  | .anySet => "any set"
  | .cyclicMod => "a cyclic module"
  | .anyObj => "any object"

def renderRoute (r : Route) : String :=
  s!"{r.method} for {renderPattern r.pattern} → backend {r.backend}, \
op {repr r.opId}, priority {r.priority}"

/-- How a method became semantically available, in the wording the
diagnostics and the gap share. -/
def renderVia (entry : CatRef) (via : List Name) : String :=
  if via.isEmpty then s!"declared directly on {renderCat entry}"
  else s!"inherited through {" ≤ ".intercalate (renderCat entry :: via.map toString)}"

/-- The full semantic chain, transport step included. A transported
resolution's `entry`/`via` describe the IMAGE, so reporting them alone would
silently omit the only step that explains why a module was routed as a set. -/
def renderSemanticPath (entry : CatRef) (via : List Name)
    (viaFunctor : Option FunctorStep) : String :=
  match viaFunctor with
  | none => renderVia entry via
  | some step =>
      s!"transported by functor '{step.functor}' to {step.image.presentation}, \
then {renderVia entry via}"

/-- The structured capability gap. The literal token `NoImplementation` is
part of the contract: it is what an audit greps for, and it marks the
failure as an execution-layer backlog item rather than a mathematical one. -/
def renderGap (g : CapabilityGap) : String :=
  let routes :=
    if g.routesConsidered.isEmpty then "    (none registered for this method)"
    else String.intercalate "\n"
      (g.routesConsidered.toList.map fun r => s!"    - {renderRoute r}")
  s!"NoImplementation: '{g.method}' is mathematically available here, but no \
registered route can execute it for this presentation.
  method:            {g.method}
  receiver category: {renderCat g.receiverCategory}
  presentation:      {g.presentation}
  semantic path:     {renderSemanticPath g.receiverCategory g.semanticVia g.viaFunctor}
  routes considered: {g.routesConsidered.size}
{routes}
This is a developer backlog item, not a narrowing of the mathematics: the \
method stays available on the category."

def renderResolveError : ResolveError → String
  | .unknownMethod m => s!"there is no method named '{m}' in the registry"
  | .notApplicable m profile declaredOn =>
      let prof := ", ".intercalate (profile.toList.map renderCat)
      let decl := ", ".intercalate (declaredOn.toList.map toString)
      s!"'{m}' is not a method of any category this object belongs to.\n  \
profile:      {if prof.isEmpty then "(none)" else prof}\n  \
declared on:  {if decl.isEmpty then "(nowhere)" else decl}"
  | .ambiguous m cands =>
      let cs := ", ".intercalate (cands.toList.map fun r =>
        match r.viaFunctor with
        | some step => s!"{r.decl.receiver} (transported by functor '{step.functor}')"
        | none => s!"{r.decl.receiver} (via {renderCat r.profileEntry})")
      s!"'{m}' reaches this object along more than one incomparable path: {cs}. \
Declare it on a common subcategory, remove one declaration, or unregister one \
of the competing functors — the resolver does not rank them."
  | .functorTargetMismatch f target imageProfile =>
      let prof := ", ".intercalate (imageProfile.toList.map renderCat)
      s!"the registration of functor '{f}' is defective: it declares target \
'{target}', but the profile of the image it produced here is \
{if prof.isEmpty then "empty" else prof}, which does not reach '{target}'. Fix \
the functor's declared target or its object map; the resolver will not use it."

def renderExecError : ExecError → String
  | .backendUnavailable b d => s!"the '{b}' backend is unavailable: {d}"
  | .backendError b k m => s!"the '{b}' backend failed ({k}): {m}"
  | .badRequest m => s!"invalid request: {m}"
  | .protocolError m => s!"backend protocol failure: {m}"

def EvalError.render : EvalError → String
  | .msg m => m
  | .resolve _ recv e => s!"{renderResolveError e}\n  receiver:     {recv.presentation}"
  | .gap g => renderGap g
  | .approxRequest eps e =>
      s!"no configured backend produced a decimal presentation within \
O({Value.tolText eps}) — a CAPABILITY failure, not a defect in the value that \
was asked about:\n{e.render}\n  requested tolerance: O({Value.tolText eps})"
  | .tiedRoutes m rs =>
      let ls := String.intercalate "\n" (rs.toList.map fun r => s!"    - {renderRoute r}")
      s!"routing for '{m}' is ambiguous: {rs.size} registered routes are tied on \
priority. This is a developer configuration error — give one a higher priority.\n{ls}"
  | .exec e => renderExecError e

/-! ## The evaluator -/

structure EvalCtx where
  env : Environment
  /-- Ambient domain of an `… in D` assertion: literals are read in it. -/
  ambient? : Option Domain := none
  /-- The indeterminate bound by `let p(x) := …`, with its coefficient
  domain, so `x` denotes the polynomial `x`. -/
  indet? : Option (Name × Domain) := none
  /-- The callee's binder while its ARGUMENT is being evaluated, so `h(-t)`
  and `(f ∘ g)(t)` can name the indeterminate. Scoped to that argument on
  purpose: outside a call the binder is not in scope, and a bare `t` is the
  ordinary "not bound" error. Consulted after the bindings, so a `let t := …`
  still wins. -/
  callBinder? : Option (Name × Domain) := none
  /-- A comprehension's binder, bound to the candidate element being tested.
  ONE slot, deliberately: a comprehension may not index over another (the
  index must be ℕ or ℤ), so the only way to nest one is inside a guard or
  head, where the inner binder would shadow the outer for the rest of that
  expression. Losing the outer name there is a LOUD "not bound" error, never
  a wrong answer, which is why one slot is enough.
  This is a REAL local binding, scoped to the braces: it is consulted BEFORE
  the session bindings (the binder wins inside its own comprehension, which
  is ordinary scoping), it is set only while the head and guard are being
  evaluated, and it publishes nothing — outside the braces the name is
  unbound and says so. -/
  local? : Option (Name × Obj) := none

abbrev EvalM := ExceptT EvalError IO

private def ofStr (r : Except String α) : EvalM α :=
  match r with
  | .ok a => pure a
  | .error m => throw (.msg m)

/-- The registered preferred canonical maps — every coercion the surface is
allowed to insert. Read from the environment, exactly like the categories and
routes: nothing in this module knows which embeddings the prelude ships. -/
def EvalCtx.canonMaps (ctx : EvalCtx) : Array CanonicalMap := canonicalMaps ctx.env

def EvalCtx.isBound (ctx : EvalCtx) (n : Name) : Bool :=
  (binding? ctx.env n).isSome || ctx.indet?.any (·.1 == n)
    || ctx.local?.any (·.1 == n)

/-- A literal read in the ambient domain. -/
def EvalCtx.literal (ctx : EvalCtx) (z : Int) : Value :=
  match ctx.ambient? with
  | some .rat => .rat (Rat.ofInt z)
  | some (.mod n) => Value.mkMod n z
  | _ => .int z

/-- The ε an approximation REQUEST carries, whichever spelling asked for it.
`map x to ℝ/O(ε)` and `x.approximate(ε)` are ONE operation, so both must answer
for the tolerance the same way (issue #7, criterion 3, which is not
spelling-scoped); the guard therefore sits in `callMethod`, where every
spelling meets. `none` = not an approximation request. -/
private def approxEps? (m : Name) (args : Array Obj) : Option (Except String Rat) :=
  if m != `approximate then none
  else match (args[0]? : Option Obj) with
    | some (.elem _ v) => some (toleranceOf (some v) v.render)
    | some o => some (toleranceOf none o.presentation)
    -- no argument is an ARITY failure, and `runMethod`'s check owns it: a
    -- tolerance cannot be the reason for a call that carries none
    | none => none

/-- Resolve (semantics), route (computability), execute — the ONLY path from
the surface to an implementation.

Routing and execution use `res.concreteReceiver`, so a resolution that went
through a functor runs against the transported image. Arguments are NOT
transported: a method's arguments belong to its declaration, not to the
receiver's presentation. -/
private def runMethod (ctx : EvalCtx) (recv : Obj) (m : Name) (args : Array Obj)
    : EvalM Denote := do
  match resolveMethod ctx.env recv m with
  | .error e => throw (.resolve m recv e)
  | .ok res =>
    if args.size != res.decl.arity then
      throw (.msg s!"'{m}' takes {res.decl.arity} argument(s), got {args.size}")
    let concrete := res.concreteReceiver recv
    match routeFor ctx.env res concrete with
    | .gap g => throw (.gap g)
    | .ambiguousRoutes rs => throw (.tiedRoutes m rs)
    | .chosen r =>
      match ← execute r concrete args with
      | .error e => throw (.exec e)
      | .ok v => return Denote.ofValue v

/-- Execute a method, and answer for a requested TOLERANCE when the method
carries one: a non-positive ε is a surface refusal (it is not a tolerance),
and any failure to meet a positive one is the capability failure naming it. -/
def callMethod (ctx : EvalCtx) (recv : Obj) (m : Name) (args : Array Obj)
    : EvalM Denote := do
  match approxEps? m args with
  | none => runMethod ctx recv m args
  | some eps? =>
      let eps ← ofStr eps?
      -- ONLY the failures a tolerance could be the reason for: a missing route
      -- and a backend that could not meet it. A resolve or arity failure is
      -- about the receiver or the call, and saying "no backend produced a
      -- decimal" over a body that names the profile would be a lie in the
      -- wrapper's own words.
      tryCatch (runMethod ctx recv m args) fun err =>
        match err with
        | .gap _ | .exec _ => throw (.approxRequest eps err)
        | err => throw err

/-- A result with no domain is not an object. Shared by the two places that ask
for one, so the cause is stated wherever it bites. -/
def notAnObject (rendered : String) : String :=
  s!"{rendered} is not an object: a RESULT with no domain — a factorization, a \
cardinal, an approximation — has none"

private def asValueOf (r : Denote) (what : String := "this position") : Except String Value :=
  match r.value? with
  | some v => .ok v
  | none => .error s!"{what} needs an element value, and {r.presentation} is not one"

private def asObjOf (r : Denote) : Except String Obj :=
  match r.obj? with
  | some o => .ok o
  | none => .error (notAnObject r.render)

/-- How many candidates a comprehension may test before the operation fails
honestly. A loud ceiling, never a truncated answer. Its reach over ℤ is
smaller than the number suggests — the tail bound is symmetric about the
origin, so an offset window costs ~2×|offset| candidates. -/
private def comprehensionCap : Int := 100000

/-- The tail every undecidable-comprehension refusal shares, so the guard and
the head cannot be reported as different KINDS of failure. -/
private def undecidableComprehension (what : String) : EvalError :=
  .msg s!"{what} The comprehension is a structured gap rather than a guess: no \
elements are enumerated, and no membership is sampled"

/-- The refusal for a guard this slice does not decide. Shared by the two
places that can reach it — a shape the bound extraction cannot read, and a
guard whose ELEMENT-world reading does not produce a truth value — so an
undecidable guard cannot be reported two ways depending on which one noticed. -/
private def undecidableGuard (binder : Name) : EvalError :=
  undecidableComprehension s!"this slice decides a comprehension whose guard is \
a polynomial comparison in the binder ('{binder}') — `{binder}² ≤ 20`, \
`0 ≤ {binder} < 6` — and this guard is not one."

/-- …and the same for a HEAD that the index set's elements do not evaluate.
An unguarded comprehension presents its head after reading it ONCE, so
without this the indeterminate world's answer would be the whole verdict. -/
private def undecidableHead (binder : Name) : EvalError :=
  undecidableComprehension s!"the head of this comprehension does not evaluate \
for an element of the index set: inside the braces '{binder}' ranges over \
ELEMENTS, and the head must produce a value for one."

mutual

partial def eval (ctx : EvalCtx) : CasExpr → EvalM Denote
  | .num z => return .obj (.elem (ctx.ambient?.getD .int) (ctx.literal z))
  | .lit v => return Denote.ofValue v
  | .dom d => return .obj (.domainObj d)
  | .ref n => do
      -- the comprehension binder is the innermost scope: inside `{n ∈ ℤ | …}`
      -- the braces' `n` wins over a session `let n := …`, and nowhere else
      if let some (b, o) := ctx.local? then
        if b == n then return .obj o
      if let some (x, c) := ctx.indet? then
        if x == n then
          return .obj (.elem (.poly c) (← ofStr (indeterminateValue ctx.canonMaps c)))
      match binding? ctx.env n with
      | some o => return .obj o
      | none =>
        if let some d := domainAlias? n then
          return .obj (.domainObj d)
        if let some v := constantValue? n then
          return Denote.ofValue v
        -- Inside a call's argument the callee's binder names the
        -- indeterminate of the ring its body lives in, which is what makes
        -- SPEC.md's `h(-t) = h(t)` and `(f ∘ g)(t) = t⁶` identities. The
        -- scope is exactly that argument: everywhere else the name is
        -- unbound, and says so.
        if let some (b, c) := ctx.callBinder? then
          if b == n then
            return .obj (.elem (.poly c) (← ofStr (indeterminateValue ctx.canonMaps c)))
        throw (.msg s!"'{n}' is not bound; introduce it with `let {n} := …`")
  | .matDom size entry => do
      match ← eval ctx entry with
      | .obj (.domainObj d) => return .obj (.domainObj (.matrix size d))
      | other => throw (.msg s!"Mat{size}(…) needs a domain, got {other.presentation}")
  | .neg e => do
      let v ← ofStr (asValueOf (← eval ctx e))
      return Denote.ofValue (← ofStr (valueNeg v))
  | .bin .div a b => do
      -- `ℤ/n` is a domain term, not a division; every other `/` is exact
      -- division in ℚ.
      let x ← eval ctx a
      let y ← eval ctx b
      match x, y with
      | .obj (.domainObj .int), .obj (.elem _ (.int n)) =>
          if n > 0 then return .obj (.domainObj (.mod n.toNat))
          else throw (.msg s!"ℤ/{n} needs a positive modulus")
      | _, _ =>
          return Denote.ofValue
            (← ofStr (valueBin ctx.canonMaps .div (← ofStr (asValueOf x))
              (← ofStr (asValueOf y))))
  | .bin .pow a b => do
      -- `2^X` is SPEC.md's other spelling of `𝒫(X)`; every other `^` is
      -- exponentiation, including `2^|A|` (a cardinal is not a set). The
      -- EXPONENT is evaluated first — it is what decides which reading this
      -- is — so an error on the right is reported before one on the left
      let y ← eval ctx b
      match y.asSet? with
      | some s =>
          match a with
          | .num 2 => return .obj (.setObj (.powerset s))
          | _ => throw (.msg s!"only `2^X` denotes the powerset of a set; there is \
no other reading of an exponent over {s.render}")
      | none =>
          let x ← eval ctx a
          -- `ℚ²`, `ℚ³`: a DOMAIN raised to a positive integer denotes the
          -- vectors of that length over it — SPEC.md's own spelling, and the
          -- one `Domain.render` produces. Like `2^X` this is a DENOTATION
          -- built by elaboration; there is no exponentiation of domains here
          match x, y.value? with
          | .obj (.domainObj d), some (.int n) =>
              if n > 0 then return .obj (.domainObj (.vector n.toNat d))
              else throw (.msg s!"{d.render}^{n} is not a domain: the vectors of \
{d.render} have a POSITIVE length, and this slice presents no other")
          | _, _ =>
            let xv ← ofStr (asValueOf x)
            return Denote.ofValue
              (← ofStr (valueBin ctx.canonMaps .pow xv (← ofStr (asValueOf y))))
  | .bin .sub a b => do
      -- `ℂ - ℚ` (SPEC.md §Polynomials) DENOTES the difference of two domains,
      -- exactly as `A × B` and `𝒫(A)` denote: no method, no route, membership
      -- decided pointwise. Only domains — the difference of two finite sets
      -- is `A \ B`, which computes.
      let x ← eval ctx a
      let y ← eval ctx b
      match x, y with
      | .obj (.domainObj p), .obj (.domainObj m) =>
          return .obj (.setObj (.domainDiff p m))
      | _, _ =>
        if x.asSet?.isSome && y.asSet?.isSome then
          throw (.msg s!"`-` denotes the difference of two DOMAINS; the \
difference of sets that have elements is `\\`, which computes it — \
{x.presentation} \\ {y.presentation}")
        else
          return Denote.ofValue (← ofStr (valueBin ctx.canonMaps .sub
            (← ofStr (asValueOf x)) (← ofStr (asValueOf y))))
  | .bin op a b => do
      let x ← ofStr (asValueOf (← eval ctx a))
      let y ← ofStr (asValueOf (← eval ctx b))
      return Denote.ofValue (← ofStr (valueBin ctx.canonMaps op x y))
  | .setProduct a b => do
      let x ← eval ctx a
      let y ← eval ctx b
      match x.asSet?, y.asSet? with
      | some sa, some sb => return .obj (.setObj (.product sa sb))
      | _, _ => throw (.msg s!"`×` is the cartesian product of two sets; got \
{x.presentation} and {y.presentation}")
  | .powersetOf a => do
      let x ← eval ctx a
      match x.asSet? with
      | some s => return .obj (.setObj (.powerset s))
      | none => throw (.msg s!"𝒫(…) needs a set, got {x.presentation}")
  | .sqrt e => do
      let v ← ofStr (asValueOf (← eval ctx e) "√")
      let some q := Native.toRat? v
        | throw (.msg s!"√ presents the exact square root of a rational; \
{v.render} is not one, and this slice does not approximate it")
      return Denote.ofValue (← ofStr (Value.sqrtOfRat q))
  | .magnitude e => do
      -- the bars are a SPELLING: which method they name is the receiver's
      -- business, and both answers are ordinary category methods
      let r ← eval ctx e
      let o ← ofStr (asObjOf r)
      callMethod ctx o (if r.asSet?.isSome then `cardinality else `abs) #[]
  | .cmp op a b => do
      let x ← ofStr (asValueOf (← eval ctx a))
      let y ← ofStr (asValueOf (← eval ctx b))
      let some ord := Native.scalarCmp x y
        | throw (.msg s!"{x.render} and {y.render} are not comparable")
      return .val (.bool (match op with
        | .le => ord != .gt | .lt => ord == .lt
        | .ge => ord != .lt | .gt => ord == .gt))
  | .conj a b => do
      let x ← ofStr (asValueOf (← eval ctx a))
      let y ← ofStr (asValueOf (← eval ctx b))
      match x, y with
      | .bool p, .bool q => return .val (.bool (p && q))
      | _, _ => throw (.msg s!"`{x.render}` and `{y.render}` are not truth values")
  | .method recv m args => do
      let r ← ofStr (asObjOf (← eval ctx recv))
      let as ← args.mapM fun a => do ofStr (asObjOf (← eval ctx a))
      callMethod ctx r m as
  | .index recv arg => do
      let r ← eval ctx recv
      match r, indeterminate? ctx.isBound arg with
      | .obj (.domainObj d), some _ => return .obj (.domainObj (.poly d))
      | _, _ =>
          let o ← ofStr (asObjOf r)
          let k ← ofStr (asObjOf (← eval ctx arg))
          callMethod ctx o `nth #[k]
  | e@(.app f args) => do
      -- SPEC.md's prefix spelling of a method call is exactly that call
      if let some call := prefixMethodCall? ctx.isBound ctx.env e then
        return (← eval ctx call)
      -- Calling a polynomial evaluates it through the preferred compatible
      -- coefficient map. This is elaboration-inserted coercion, not a
      -- method: no route, no backend, no ceremony (DESIGN.md decision 6).
      let fv ← eval ctx f
      match fv.value? with
      | some (.poly c coeffs) =>
          if args.size != 1 then
            throw (.msg s!"a polynomial is called with exactly one argument, got {args.size}")
          let x ← ofStr (asValueOf (← eval ctx args[0]!))
          return Denote.ofValue (← ofStr (Native.polyEval c coeffs x))
      | some (.func src tgt binder body) =>
          -- Calling a function substitutes into its body: a scalar argument
          -- evaluates it, a polynomial argument composes with it. Same
          -- elaboration-inserted move as calling a polynomial — no route, no
          -- backend (DESIGN.md decision 6) — but the ascribed `src → tgt` is
          -- CHECKED at both ends, so a call outside the source domain fails
          -- instead of computing in some other ring.
          if args.size != 1 then
            throw (.msg s!"a function is called with exactly one argument, got {args.size}")
          -- inside the argument, and only there, the callee's binder names
          -- the indeterminate: that is what `h(-t)` and `(f ∘ g)(t)` mean
          let some ring := binderRing src body
            | throw (.msg s!"{body.render} is not a polynomial body")
          let arg ← eval { ctx with callBinder? := some (binder, ring) } args[0]!
          -- SPEC.md's `e(ℕ)`: applying a function to its SOURCE is the image,
          -- which is the `image` method — one implementation, two spellings
          match arg.asSet? with
          | some (.domainSet d) =>
              if d == src then callMethod ctx (← ofStr (asObjOf fv)) `image #[]
              else throw (.msg s!"{fv.render} is declared on {src.render}, so \
{d.render} is not its source: this slice images the source domain only")
          | some s =>
              throw (.msg s!"this slice computes the image of a function's SOURCE \
domain, not of {s.render}")
          | none =>
            let x ← ofStr (atDomain ctx.canonMaps src (← ofStr (asValueOf arg)))
            let y ← ofStr (applyPoly ctx.canonMaps body x)
            return Denote.ofValue (← ofStr (atDomain ctx.canonMaps tgt y))
      | _ => throw (.msg s!"{fv.presentation} is not callable")
  | .finSet elems => do
      let vs ← elems.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let d ← ofStr (elemsDomain ctx.canonMaps vs)
      return .obj (.setObj (.finite d (← ofStr (vs.mapM (coerceValue ctx.canonMaps d)))))
  | .progSet leading last? => do
      let vs ← leading.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let l ← last?.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      return .obj (.setObj (← ofStr (progressionOf ctx.canonMaps vs l)))
  | .matLit rows cols entries => do
      if rows != cols then
        throw (.msg s!"the slice presents square matrices only, got {rows}×{cols}")
      let vs ← entries.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let d ← ofStr (elemsDomain ctx.canonMaps vs)
      let rs ← (Array.range rows).mapM fun i =>
        ofStr ((Array.range cols).mapM fun j =>
          coerceValue ctx.canonMaps d vs[i * cols + j]!)
      return .obj (.elem (.matrix rows d) (.mat rows d rs))
  | .vecLit comps => do
      let vs ← comps.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let d ← ofStr (elemsDomain ctx.canonMaps vs)
      return .obj (.elem (.vector vs.size d)
        (.vec vs.size d (← ofStr (vs.mapM (coerceValue ctx.canonMaps d)))))
  -- SPEC.md §Exact number systems' `map √2 to ℝ/O(1/10^{10})`. TWO registries
  -- answer, in this order, and neither answers the other's question: the
  -- canonical-map registry decides whether the value may be presented in ℝ at
  -- all (so `map 1/3 to ℝ/O(…)` rides the registered ℚ ⊆ ℝ, and `2 + 2i` is
  -- the honest "there is no preferred canonical map … into ℝ"), and the router
  -- decides whether a decimal to that tolerance can be COMPUTED. `ℝ/O(ε)` is
  -- not a domain, so no third judgment about it exists to get wrong.
  | .mapTo e (.approxTarget epsE) => do
      let d ← eval ctx epsE
      let eps ← ofStr (toleranceOf d.value? d.presentation)
      let v ← ofStr (asValueOf (← eval ctx e) "`map … to ℝ/O(ε)`")
      let r ← ofStr (coerceValue ctx.canonMaps .real v)
      callMethod ctx (.elem .real r) `approximate #[.elem .rat (Value.ofRat eps)]
  | .mapTo e target => do
      let t ← eval ctx target
      let .obj (.domainObj d) := t
        | throw (.msg s!"`map … to` needs a domain, got {t.presentation}")
      let v ← ofStr (asValueOf (← eval ctx e))
      return .obj (.elem d (← ofStr (coerceValue ctx.canonMaps d v)))
  | .approxTarget _ =>
      throw (.msg "`ℝ/O(ε)` is the TARGET of `map … to ℝ/O(ε)` — a requested \
tolerance for a decimal presentation — and nothing else: it is not a domain, \
not a set, and not a quotient of ℝ (|a - b| < ε is not transitive, so there \
are no classes here to be an element of, or to include ℝ in)")
  | .arrow src tgt => do
      let s ← eval ctx src
      let t ← eval ctx tgt
      match s, t with
      | .obj (.domainObj a), .obj (.domainObj b) => return .obj (.domainObj (.funcs a b))
      | _, _ =>
          throw (.msg s!"`{s.presentation} → {t.presentation}` needs a domain on \
each side")
  | .comp f g => do
      let fv ← ofStr (asValueOf (← eval ctx f))
      let gv ← ofStr (asValueOf (← eval ctx g))
      return Denote.ofValue (← ofStr (composeFuncs ctx.canonMaps fv gv))
  | .lam binder _ =>
      throw (.msg s!"`{binder} ↦ …` is a function definition: bind it with the \
domains it runs between, as in `let h := {binder} ↦ {binder}^2 + 1 in ℝ → ℝ`")
  | .comprehension head binder index guard? =>
      evalComprehension ctx head binder index guard?

/-- The bounds a guard puts on the comprehension binder, decided by
`boundsOfPoly` after each comparison is rewritten as `p(n) ⋈ 0`. A guard
shape the rewriting does not reach is refused here, loudly. -/
partial def guardBounds (ctx : EvalCtx) (binder : Name) (dom : Domain)
    : CasExpr → EvalM BinderBounds
  | .conj a b => do
      return (← guardBounds ctx binder dom a).meet (← guardBounds ctx binder dom b)
  | .cmp op a b => do
      -- the binder is the INDETERMINATE here: the guard is read as an exact
      -- polynomial claim about every candidate at once, not sampled at one
      let ictx := { ctx with indet? := some (binder, dom) }
      let x ← ofStr (asValueOf (← eval ictx a))
      let y ← ofStr (asValueOf (← eval ictx b))
      match ← ofStr (valueBin ctx.canonMaps .sub x y) with
      -- a difference of degree ≤ 0 is a CONSTANT however it is presented:
      -- `0*n` and `n - n` reduce to the zero polynomial, and diagnosing those
      -- as a polynomial with no extractable bound would misreport an infinite
      -- (or empty) comprehension as an unsupported guard
      | .poly c cs =>
          ofStr (if cs.size ≤ 1 then constantBounds op (cs[0]?.getD (Native.zeroOf c))
                 else boundsOfPoly op cs)
      | v => ofStr (constantBounds op v)
  | _ => throw (undecidableGuard binder)

/-- `{head | binder ∈ index, guard}`.

Two decided shapes, and nothing in between:

- **guarded** — the guard bounds the binder to a finite candidate range, and
  every candidate in it is TESTED exactly; the head is then evaluated at the
  survivors. This is what makes `{n ∈ ℤ | n² ≤ 20}` the nine integers it is,
  and `{e(n) | n ∈ ℕ, 0 ≤ n < 6}` the six values it is;
- **unguarded over ℕ with a linear head** — the image is exactly an
  arithmetic PROGRESSION, the presentation `{0, 2, 4, ...}` already has, so
  `{2n | n ∈ ℕ}` is that set (SPEC.md's own `Y = {2n | n in ℕ}` identity) and
  its membership, cardinality and equality are the ones ℕ already has.

Everything else — an unbounded guard, an index that is not ℕ or ℤ, a
non-linear head with no guard — is refused at the binding. -/
partial def evalComprehension (ctx : EvalCtx) (head : CasExpr) (binder : Name)
    (index : CasExpr) (guard? : Option CasExpr) : EvalM Denote := do
  let idx ← eval ctx index
  let some (.domainSet dom) := idx.asSet?
    | throw (.msg s!"a comprehension indexes over ℕ or ℤ in this slice, not \
{idx.presentation}")
  unless dom == .nat || dom == .int do
    throw (.msg s!"a comprehension indexes over ℕ or ℤ in this slice, not \
{dom.render}")
  -- ONE element-world reading, at a candidate of the index domain. The
  -- indeterminate world answers for guards and heads that are meaningless for
  -- elements — `n.deg()` is 1 for the indeterminate and a resolver error for
  -- an integer — so every path that enumerates NOTHING (both unguarded
  -- presentations, the empty range, the infinite refusal) would otherwise ship
  -- a verdict no element-world reading ever supported. The guarded loop
  -- re-reads each candidate anyway, so this is the only place that check is
  -- missing.
  let probe (e : CasExpr) (accepts : Value → Bool) (err : EvalError) : EvalM Unit := do
    let kv ← ofStr (coerceValue ctx.canonMaps dom (.int 0))
    let read ← tryCatch (do return (← eval { ctx with
      local? := some (binder, .elem dom kv) } e).value?) fun _ => pure none
    match read with
    | some v => if accepts v then pure () else throw err
    | none => throw err
  match guard? with
  | none =>
      -- a head is asked only for a VALUE: `2n` gives 0, `7` gives 7, a
      -- constant `p.deg()` gives 3, and `n.deg()` fails resolution
      probe head (fun _ => true) (undecidableHead binder)
      let hv ← ofStr (asValueOf (← eval { ctx with indet? := some (binder, dom) } head)
        s!"the head of a comprehension over {dom.render}")
      match hv with
      | .poly c cs =>
          if cs.size == 2 && dom == .nat then
            return .obj (.setObj (.arithProg c cs[0]! cs[1]! none))
          else if cs.size ≤ 1 then
            -- a constant map: its image is the one value it takes
            return .obj (.setObj (.finite c #[cs[0]?.getD (Native.zeroOf c)]))
          else
            throw (.msg s!"an unguarded comprehension is presented only when its \
image is an arithmetic progression — a linear map on ℕ. {hv.render} over \
{dom.render} is not one, so this is a gap rather than a guess")
      | v =>
          let d ← ofStr (elemsDomain ctx.canonMaps #[v])
          return .obj (.setObj (.finite d #[v]))
  | some g =>
      let b ← guardBounds ctx binder dom g
      -- a guard is asked for a TRUTH VALUE, at the same candidate
      let guardProbe : EvalM Unit :=
        probe g (fun | .bool _ => true | _ => false) (undecidableGuard binder)
      -- ℕ contributes its own lower bound; the guard must supply the rest
      let lo? := if dom == .nat then some (max 0 (b.lo.getD 0)) else b.lo
      let some lo := lo?
        | do guardProbe
             throw (.msg s!"the guard does not bound '{binder}' from below, so this \
comprehension is infinite: this slice presents a decided finite set or nothing")
      let some hi := b.hi
        | do guardProbe
             throw (.msg s!"the guard does not bound '{binder}' from above, so this \
comprehension is infinite: this slice presents a decided finite set or nothing")
      if hi < lo then guardProbe
      if hi - lo + 1 > comprehensionCap then
        throw (.msg s!"the guard bounds '{binder}' to {hi - lo + 1} candidates; \
this slice tests at most {comprehensionCap}")
      let mut out : Array Value := #[]
      for i in [0 : (max 0 (hi - lo + 1)).toNat] do
        let k := lo + Int.ofNat i
        let kv ← ofStr (coerceValue ctx.canonMaps dom (.int k))
        let kctx := { ctx with local? := some (binder, .elem dom kv) }
        match ← ofStr (asValueOf (← eval kctx g) s!"the guard at {binder} = {k}") with
        | .bool true =>
            out := out.push (← ofStr (asValueOf (← eval kctx head)
              s!"the head at {binder} = {k}"))
        | .bool false => pure ()
        | v => throw (.msg s!"the guard did not decide at {binder} = {k}: {v.render}")
      let d ← ofStr (elemsDomain ctx.canonMaps out)
      return .obj (.setObj (.finite d (← ofStr (out.mapM (coerceValue ctx.canonMaps d)))))

end

/-- Run the evaluator; the syntax layer lifts this into `CommandElabM`. -/
def runEval (ctx : EvalCtx) (e : CasExpr) : IO (Except EvalError Denote) :=
  (eval ctx e).run

/-! ## Ascription

`let x := e in T` checks a membership judgment, so `T` is resolved against
the registries first: a registered CATEGORY name means the ascription is a
category membership (and may reinterpret the presentation — `ℤ/4` in a
module category is the ℤ-module), anything else is a domain. -/

inductive Ascription where
  | domain (d : Domain)
  | category (c : CatRef)
  /-- `let A := {1, 2, 3} in 𝒫(ℤ)`: the ascription names a SET, and the
  judgment is membership in it — decided by the same routed `contains` the
  surface's `∈` uses, which on a powerset is the inclusion `A ⊆ ℤ`. -/
  | member (s : Obj)

/-- The category an ascription term names, if any. Only the two shapes the
surface produces (`C` and `C(p₁, …)`) are category ascriptions. -/
def categoryAscription? (env : Environment) : CasExpr → Option (Name × Array CasExpr)
  | .ref n => if (catDecl? env n).isSome then some (n, #[]) else none
  | .app (.ref n) args => if (catDecl? env n).isSome then some (n, args) else none
  | _ => none

private def paramOf : Denote → Except String ParamVal
  | .obj (.domainObj d) => .ok (.dom d)
  | .obj (.elem _ (.int k)) =>
      if k ≥ 0 then .ok (.nat k.toNat)
      else .error s!"{k} is not a category parameter"
  | r => .error s!"{r.presentation} is not a category parameter"

def evalAscription (ctx : EvalCtx) (e : CasExpr) : EvalM Ascription := do
  match categoryAscription? ctx.env e with
  | some (n, args) =>
      let ps ← args.mapM fun a => do ofStr (paramOf (← eval ctx a))
      return .category { name := n, params := ps }
  | none =>
      match ← eval ctx e with
      | .obj (.domainObj d) => return .domain d
      | .obj (.setObj s) => return .member (.setObj s)
      | other => throw (.msg s!"{other.presentation} is neither a domain, a set, \
nor a registered category")

/-- Apply and CHECK an ascription. Membership is a judgment: a domain
ascription must admit the preferred canonical map, and a category ascription
must actually hold in the object's profile.

CEILING: the only ascription-directed reinterpretation is `ℤ/n` read as the
cyclic ℤ-module when the ascribed category is a module category. Making
reinterpretation registry-driven is the documented generalization. -/
def ascribe (ctx : EvalCtx) (o : Obj) : Ascription → EvalM Obj
  | .domain d => do
      match o with
      | .elem _ v => return .elem d (← ofStr (coerceValue ctx.canonMaps d v))
      | .domainObj d' =>
          if d' == d then return o
          else throw (.msg s!"{d'.render} is not an element of {d.render}")
      | o => throw (.msg s!"{o.presentation} is not an element of {d.render}")
  | .category c => do
      let o' := match o with
        | .domainObj (.mod n) => Obj.cyclicModule n
        | o => o
      if (profileOf ctx.env o').contains c then return o'
      else
        let prof := ", ".intercalate ((profileOf ctx.env o').toList.map renderCat)
        throw (.msg s!"{o'.presentation} is not in {renderCat c} \
(its profile is {if prof.isEmpty then "empty" else prof})")
  | .member s => do
      match (← callMethod ctx s `contains #[o]).value? with
      | some (.bool true) => return o
      | some (.bool false) =>
          throw (.msg s!"{o.presentation} is not an element of {s.presentation}")
      | other =>
          throw (.msg s!"membership of {o.presentation} in {s.presentation} did not \
decide: {other.elim "no value" (·.render)}")

/-! ## The three notebook judgments -/

private def objOf (d : Denote) : EvalM Obj :=
  match d.obj? with
  | some o => pure o
  | none => throw (.msg (notAnObject d.render))

/-- A binding that introduces a BINDER — `let p(x) := e in D[x]`,
`let h := t ↦ e in ℝ → ℝ`, `let e: ℕ → ℕ := n ↦ …`. The ascription decides
what the binder means, and is therefore evaluated FIRST:

- a polynomial domain reads the binder as the indeterminate of `D[x]`;
- a function domain enters the binder as the indeterminate of `ℤ[x]` and
  keeps whatever the body's own arithmetic makes of it. The ascribed domains
  do NOT supply that coefficient ring: `ℝ → ℝ` is an ascription DOMAIN TAG
  (SPEC.md's spelling) with no analysis semantics at this stage, so a body
  is exactly as exact as the polynomial engine can make it. -/
def evalBinderBinding (ctx : EvalCtx) (binder : Name) (body : CasExpr)
    (asc : Ascription) : EvalM Obj := do
  match asc with
  | .domain (.poly c) =>
      let o ← objOf (← eval { ctx with indet? := some (binder, c) } body)
      ascribe ctx o (.domain (.poly c))
  | .domain (.funcs src tgt) =>
      let d ← eval { ctx with indet? := some (binder, .int) } body
      let some v := d.value?
        | throw (.msg s!"{d.presentation} is not a function body")
      if (asPolyCoeffs v).isNone then
        throw (.msg s!"{v.render} is not a polynomial body: the slice grounds \
functions in the exact polynomial engine, so a body it cannot express is a \
gap, not an approximation")
      return .elem (.funcs src tgt) (.func src tgt binder v)
  | _ =>
      throw (.msg s!"a `{binder} ↦ …` definition must be ascribed to a polynomial \
domain such as ℤ[x] or to a function domain such as ℝ → ℝ")

/-- `let x := e [in T]`; a `↦` lambda on the right is a binder definition. -/
def evalBinding (ctx : EvalCtx) (e : CasExpr) (asc? : Option CasExpr) : EvalM Obj := do
  match e, asc? with
  | .lam binder body, some a =>
      evalBinderBinding ctx binder body (← evalAscription ctx a)
  | .lam binder _, none =>
      throw (.msg s!"`{binder} ↦ …` needs an ascription naming the domains it \
runs between, as in `let h := {binder} ↦ {binder}^2 + 1 in ℝ → ℝ`")
  | _, none => objOf (← eval ctx e)
  | _, some a =>
      let asc ← evalAscription ctx a
      ascribe ctx (← objOf (← eval ctx e)) asc

/-- `let p(x) := e in T` — the same binder definition, spelled with the
argument on the left. -/
def evalPolyBinding (ctx : EvalCtx) (x : Name) (e : CasExpr) (asc : CasExpr)
    : EvalM Obj := do
  evalBinderBinding ctx x e (← evalAscription ctx asc)

inductive AssertRel where
  | eq | ne | mem | notMem | subset
  deriving BEq, Inhabited

def AssertRel.render : AssertRel → String
  | .eq => "=" | .ne => "≠" | .mem => "∈" | .notMem => "∉" | .subset => "⊆"

private def boolOf (d : Denote) : EvalM Bool :=
  match d.value? with
  | some (.bool b) => pure b
  | _ => throw (.msg s!"{d.render} is not a truth value")

private def isSetLike : Denote → Bool
  | .obj (.setObj _) | .obj (.domainObj _) => true
  | _ => false

/-- The binder a function CALLED in this expression brings into scope.

SPEC.md writes `assert (f ∘ g)(t) = t⁶`, naming `t` on the side that is NOT
the call, so a call anywhere in an assertion scopes its binder over the whole
assertion. Nothing wider: outside such an assertion the name is unbound and
says so, and a real `let t := …` still wins (`eval` consults this only after
the bindings). -/
partial def calledBinder? (env : Environment) : CasExpr → Option (Name × Domain)
  | .app f _ => head f
  | .bin _ a b => calledBinder? env a <|> calledBinder? env b
  | .neg e => calledBinder? env e
  | _ => none
where
  head : CasExpr → Option (Name × Domain)
    | .ref n =>
        match binding? env n with
        | some (.elem _ (.func src _ b body)) => (binderRing src body).map (b, ·)
        | _ => none
    -- a composite keeps the right factor's binder, exactly as `composeFuncs` does
    | .comp _ g => head g
    | _ => none

/-- The name a membership assertion writes on BOTH sides — `x ∈ ℤ[x]`.

SPEC.md's polynomial section asserts exactly that, and it is a question about
the ring on the right: which element of `ℤ[x]` could `x` name there but its
indeterminate? The reading is therefore LOCAL to this one assertion and needs
the name to be repeated in the ring's own spelling. It publishes nothing: a
bare `x` in any other cell is still the loud "not bound" error, which is what
keeps a polynomial definition from converting a typo elsewhere into a silent
indeterminate (DESIGN.md §Functions). -/
private def membershipIndet? : CasExpr → CasExpr → Option Name
  | .ref n, .index _ (.ref n') => if n == n' then some n else none
  | _, _ => none

/-- `assert l R r`, with the fourfold CAS outcome: `some true`, `some
false`, `none` (the operands are not comparable — the honest "unknown"), or
a thrown structured error. No proposition is created: this is a computed,
trusted predicate, not a Lean theorem. -/
def evalAssert (ctx : EvalCtx) (rel : AssertRel) (l r : CasExpr)
    : EvalM (Option Bool) := do
  let ctx := { ctx with callBinder? :=
    ctx.callBinder? <|> calledBinder? ctx.env l <|> calledBinder? ctx.env r }
  match rel with
  | .mem | .notMem =>
      -- membership asks about the SET on the right, so it is evaluated first:
      -- a polynomial ring is what lets `x ∈ ℤ[x]` read `x` as its indeterminate
      let b ← eval ctx r
      -- the name is necessarily unbound here: a polynomial DOMAIN on the
      -- right is what `eval`'s `.index` branch produces only when
      -- `indeterminate?` already found the name free (a bound one indexes)
      let ctx := match membershipIndet? l r, b with
        | some n, .obj (.domainObj (.poly c)) => { ctx with indet? := some (n, c) }
        | _, _ => ctx
      let a ← eval ctx l
      let res ← boolOf (← callMethod ctx (← objOf b) `contains #[← objOf a])
      return some (if rel == .mem then res else !res)
  | .subset =>
      let a ← eval ctx l
      let b ← eval ctx r
      match a, b with
      -- Inclusion between two DOMAINS is the canonical-map registry's claim
      -- (`domainSubset`), so it is answered from the registry by elaboration
      -- — the move `A × B` and `𝒫(A)` already make — and NOT by the set
      -- layer, which keeps refusing to restate it. One owner, one answer.
      | .obj (.domainObj d), .obj (.domainObj e) =>
          return some (← ofStr (domainSubset ctx.canonMaps d e))
      -- everything else is inclusion of SETS: a Sets method like membership
      -- and equality, resolved and routed exactly as they are
      | _, _ =>
          return some (← boolOf (← callMethod ctx (← objOf a) `subset #[← objOf b]))
  | _ =>
      let a ← eval ctx l
      let b ← eval ctx r
      let neg := rel == .ne
      if isSetLike a && isSetLike b then
        let res ← boolOf (← callMethod ctx (← objOf a) `set_eq #[← objOf b])
        return some (neg != res)
      else if isSetLike a || isSetLike b then
        -- Exactly one side is a set: the operands live in DIFFERENT
        -- categories, and bare `=` never inserts a functor to reconcile
        -- them — there is no unique module structure on {0, 1, 2, 3}, so
        -- `F = {0, 1, 2, 3}` is trivially false even though U(F) IS that
        -- set (design review 2026-07-30: equality is category-bound). The
        -- Sets question stays one explicit call away — `F.set_eq(X)`
        -- transports its receiver, exactly like `∈`.
        return some neg
      else
        let some va := a.value?
          | throw (.msg s!"{a.render} is not comparable")
        let some vb := b.value?
          | throw (.msg s!"{b.render} is not comparable")
        return (Native.valueEq va vb).map (neg != ·)

end CasDsl
