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

`BinOp`, `CmpOp` and `CasExpr` live in `CasDsl/Value.lean`, below `Value`:
a presentation may carry an expression (`SetPresentation.predicate` stores
the guard the mathematician wrote), so the AST sits with the data model.
Everything the parser cannot decide on its own — whether `D[x]` is a
polynomial ring or an index, whether an ascription names a domain or a
category — is decided here, against the registries. -/

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
  | .hom s t _ _ => some (.funcs s t)
  | .seriesV c _ => some (.series c)
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
  -- structural congruence under `series`, for the reason it holds under
  -- `poly`: a canonical map of coefficient domains INDUCES the one on series.
  -- The coefficients are exact RATIONALS by construction, and every rule this
  -- prelude registers between them moves no data, so the image is a re-tag
  | .series c, .seriesV c' gen =>
      if c == c' then .ok (.seriesV c gen)
      else do
        match ← canonicalMapFor rules c' c with
        | some _ => return .seriesV c gen
        | none => .error s!"there is no preferred canonical map of \
{(Domain.series c').render} into {(Domain.series c).render}"
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
  | .series a, .series b => domainSubset rules a b
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

/-- `Σₖ rₖ·csₖ` over ℚ — one coordinate of a hom's derived rows applied to a
point's coordinates. -/
private def dotRow (r cs : Array Rat) : Rat := Id.run do
  let mut acc : Rat := 0
  for k in [0:cs.size] do
    acc := acc + (r[k]?.getD 0) * cs[k]!
  return acc

/-- The product of two row lists — the composite hom's derived rows. -/
private def matMulRows (a b : Array (Array Rat)) : Array (Array Rat) :=
  let cols := (b[0]?.getD #[]).size
  a.map fun ar => (Array.range cols).map fun j => Id.run do
    let mut acc : Rat := 0
    for k in [0:b.size] do
      let c : Rat := ar[k]?.getD 0
      acc := acc + c * b[k]![j]!
    return acc

/-- `f ∘ g` = `binder ↦ f(g(binder))`, keeping `g`'s binder.

The domains must meet: composing along `g : A → B` and `f : C → D` with
`B ≠ C` is a mathematical error, never something to coerce past. -/
def composeFuncs (rules : Array CanonicalMap) : Value → Value → Except String Value
  | .func fs ft _ fb, .func gs gt gbinder gb =>
      if fs != gt then
        .error s!"{gs.render} → {gt.render} and {fs.render} → {ft.render} do not \
compose: the target of the right factor is not the source of the left"
      else do return .func gs ft gbinder (← applyPoly rules fb gb)
  -- two HOMS compose as homs: the composite keeps the inner map's binders
  -- (its domain is the inner domain), and the DERIVED rows compose as the
  -- matrix product — backend data composing as backend data
  | .hom fs ft _ frows, .hom gs gt gbinders grows =>
      if fs != gt then
        .error s!"{gs.render} → {gt.render} and {fs.render} → {ft.render} do not \
compose: the target of the right factor is not the source of the left"
      else .ok (.hom gs ft gbinders (matMulRows frows grows))
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

/-- The two sides of a coset comprehension's guard, as `(point, other)`.

CEILING, and it is what makes the solve EXACT rather than a fit: exactly one
side must be an application of the BINDER at a point — SPEC.md's `h(0) = 0`.
The members of `p + K` are `p + c` with `c` in the constants, so `h(a)` is
`p(a) + c` and the equation is linear in `c` with slope one BY THE SHAPE, not
by an assumption about it. A guard of any other shape is refused. -/
def cosetGuardSides (binder : Name) (l r : CasExpr)
    : Except String (CasExpr × CasExpr) :=
  match l, r with
  | .app (.ref b) #[pt], other => if b == binder then .ok (pt, other) else notEval
  | other, .app (.ref b) #[pt] => if b == binder then .ok (pt, other) else notEval
  | _, _ => notEval
where
  notEval : Except String (CasExpr × CasExpr) :=
    .error s!"a comprehension over a COSET is decided for an EVALUATION guard \
— SPEC.md writes `\{h ∈ ∫ f dx | h(0) = 0}` — where one side applies the \
binder '{binder}' at a point. The members of a coset differ by a constant, so \
that shape solves for the constant EXACTLY; any other shape is a gap rather \
than a fit"

/-- A series asked past what it KNOWS — a truncation or a coefficient beyond
the terms a `terms` presentation carries. ONE wording, shared by both, because
they are one fact about the presentation: this is what a documented ceiling
says when it is reached, and it is never a shorter answer returned as if it
had been requested. -/
def pastSeriesCeiling (k : Nat) (gen : SeriesGen) : String :=
  match gen with
  | .terms cs =>
      s!"this series is known to {cs.size} terms (t^0 … t^{cs.size - 1}), and t^{k} is past that ceiling. A series presented by finitely many coefficients does not invent the next one, and a shorter answer would not be the one asked for"
  | .rule _ =>
      s!"t^{k} is not a coefficient of this series"

/-- Is `a / b` SPEC.md's derivation `d/dx` rather than a quotient? Only when
both names are free: a binding wins, exactly as it does over a constant. The
LETTER needs no check: `dx` is the surface's own token for the differential of
the indeterminate this slice renders `x`, so there is no `d/dy` to mistake it
for. `let d := 6 in ℤ` gives the division back, exactly as a binding takes a
constant back. -/
def isDerivationSpelling (isBound : Name → Bool) : CasExpr → CasExpr → Bool
  -- `dx` is a TOKEN, so the right operand arrives already read as the free
  -- generator `1 dx` rather than as a name — which is why only `d` needs the
  -- boundness check
  | .ref `d, .diffForm (.num 1) => !isBound `d
  | _, _ => false

/-- The names SPEC.md writes for a CONSTANT rather than for a binding: `i`,
the imaginary unit (`2 + 2i`). Consulted after the bindings and after the
domain aliases. `π` and `d` are SHADOWABLE spellings (`let d := 5 in ℤ`
takes the division back); `e` and `i` are RESERVED symbols under the
2026-07-31 ruling (#31 item 3) — `reservedConstantMsg?` refuses any binding
or binder by either name, so consulting this after the bindings can never
lose them. -/
def constantValue? : Name → Option Value
  -- through the normalizing constructor like every other value the surface
  -- produces: `none` here would be the ordinary "not bound" error, never a
  -- surd that skipped its invariant
  | `i => (Value.mkAlg 0 1 (-1)).toOption
  -- SPEC.md §Elementary calculus writes `e^t` and `∫₀^π`. Neither `e` nor `π`
  -- is an exact algebraic number, so neither is an ELEMENT here: they are the
  -- SYMBOLIC constants a base, a bound or a limit point is written with, and
  -- they carry no arithmetic. The former e-collision (SPEC.md once bound `e`
  -- to the doubling map, and the binding won) was RESOLVED by the ruling
  -- above: that function is now `m2`, `e` is reserved, and `exp(t)` remains
  -- the equivalent spelling — `exp(x) := e^x`, the owner's words.
  | `e => some (.sym (.const `e))
  | `π | `pi => some (.sym (.const `pi))
  -- SPEC.md §Differentials displays a bare `d`: the universal differential.
  -- A constant like the three above, so `let d := 5 in ℤ` shadows it
  | `d => some (.derivation true)
  | _ => none

/-- The two constant names the owner RESERVED outright (ruling 2026-07-31,
#31 item 3): `e` is Euler's constant — `e^t` is what a mathematician
expects, with `exp(x)` as the equivalent spelling — and `i` is the imaginary
unit of ℂ. NO binding or binder may shadow either; `π` and `d` stay ordinary
shadowable constants. These are not TOKENS (an identifier by these spellings
still lexes, so `is_prime` and dotted names are untouched): the reservation
is enforced where a name is INTRODUCED — the session bindings, and every
binder position of this evaluator. -/
def reservedConstantMsg? : Name → Option String
  | `e => some "`e` is Euler's constant, a reserved symbol of this surface \
(owner ruling 2026-07-31): `e^t` means exp(t), `exp(x)` spells the same \
function, and no binding may shadow it"
  | `i => some "`i` is the imaginary unit i ∈ ℂ, a reserved symbol of this \
surface (owner ruling 2026-07-31), and no binding may shadow it"
  | _ => none

/-- Refuse to introduce a reserved constant name — shared by the command
layer's bindings (`bindObj`) and every binder position of this evaluator,
so `e` and `i` cannot be shadowed anywhere a name enters scope. -/
def checkBindableName (n : Name) : Except String Unit :=
  match reservedConstantMsg? n with
  | some m => .error m
  | none => .ok ()

/-! ### Symbolic function expressions

`SPEC.md` §Elementary calculus writes bodies the polynomial engine cannot
express — `sin(t)`, `e^t`, `1/t` — and asks three things of them: a limit, a
definite integral and a Taylor expansion. All three are computed by a backend
FROM THE EXPRESSION, so what this surface needs is a presentation of the
expression and nothing more: no evaluation at a point, no identity between two
of them. `Value.sym` is that presentation and the reader below is the only way
into it. -/

/-- The refusal a body outside the symbolic vocabulary gets — ONE wording, so
an unknown NAME and an unreadable SHAPE are the same kind of gap and cannot be
reported as different ones. It LISTS the vocabulary, because a closed list is
what keeps this surface backend-blind: an unknown name is never handed to a
backend to interpret however it likes. -/
def notSymbolic (what : String) : String :=
  s!"{what} is not a function expression this slice presents. The vocabulary \
is the binder, exact rationals, the constants \
{", ".intercalate (SymExpr.constants.map toString)}, the functions \
{", ".intercalate (SymExpr.functions.map toString)}, and + - * / ^ — \
a body outside it is a GAP that names itself, never a symbol passed to a \
backend to read as it likes"

/-- Read a surface expression as a symbolic expression in `binder`.

A name is the binder, or a symbolic constant, and NOTHING else: a name this
session has BOUND is refused rather than substituted or read as a constant.
Both halves of that matter. There is no substitution here to make a binding
mean anything, and reading a bound name as the constant it shadows would turn
`let e := 5` followed by `t ↦ e^t` into Euler's number — a wrong answer where
the refusal is only an inconvenience. -/
partial def toSymExpr (isBound : Name → Bool) (binder : Name)
    : CasExpr → Except String SymExpr
  | .num z => .ok (.num (Rat.ofInt z))
  -- `∞` is a token of its own rather than a name, so it arrives already read
  | .lit (.sym s) => .ok s
  | .ref n =>
      if n == binder then .ok (.var n)
      else if isBound n then
        .error s!"'{n}' is BOUND in this session, and a symbolic body neither \
substitutes a binding nor reads the name as the constant it shadows: the first \
has nothing to substitute into, and the second would answer with a value the \
mathematician did not write"
      else match constantValue? n with
        | some (.sym s) => .ok s
        | _ => .error (notSymbolic s!"'{n}'")
  | .neg a => do return .neg (← toSymExpr isBound binder a)
  | .bin op a b => do
      let x ← toSymExpr isBound binder a
      let y ← toSymExpr isBound binder b
      return match op with
        | .add => .add x y | .sub => .sub x y | .mul => .mul x y
        | .div => .div x y | .pow => .pow x y
  | .app (.ref f) args =>
      if h : args.size = 1 then
        if SymExpr.functions.contains f then
          do return .app f (← toSymExpr isBound binder (args[0]'(by simp [h])))
        else .error (notSymbolic s!"'{f}'")
      else .error s!"'{f}' takes one argument here, got {args.size}"
  | e => .error (notSymbolic s!"this expression ({repr (reprShape e)})")
where
  /-- The node kind, for the refusal — the expression itself has no rendering
  before it is evaluated, and naming the SHAPE is what tells a mathematician
  which part of the body left the vocabulary. -/
  reprShape : CasExpr → String
    | .method _ m _ => s!"a `.{m}()` call"
    | .index .. => "an index"
    | .finSet _ | .progSet .. => "a set literal"
    | .matLit .. => "a matrix literal"
    | .vecLit _ => "a tuple"
    | .lam .. => "a nested lambda"
    | .comp .. => "a composition"
    | .sqrt _ => "a square root"
    | _ => "that shape"

/-- The function a limit or a definite integral is taken OF: `binder ↦ body`
with the body read symbolically. `ℝ → ℝ` is the ascription tag these
operations run under — the arrow carries no analysis semantics here, and the
OPERATION is what the backend answers. -/
def symFunction (isBound : Name → Bool) (binder : Name) (body : CasExpr)
    : Except String Obj := do
  checkBindableName binder
  return .elem (.funcs .real .real)
    (.func .real .real binder (.sym (← toSymExpr isBound binder body)))

/-- The domains SPEC.md spells as ordinary identifiers rather than as their
own token: `R` and `RR` are ℝ (`let f(t) = t^2 in RR->RR`), `CC` is ℂ.

The Unicode names are here for a PARSER reason rather than a spelling one:
`ℝ.cardinality()` lexes as one hierarchical identifier (Lean's `ident` eats
the dot, and `ℝ` is an identifier character), so a domain used as a METHOD
RECEIVER arrives as a name and never as its own token. Without these arms
`ℝ.cardinality()` was the misleading "'ℝ' is not bound" instead of the honest
"this backend cannot express the cardinality of ℝ".

Consulted only after the bindings, so `let R := …` still shadows the alias —
an alias is a spelling, not a reserved word.

The doubled-letter family is UNIFORM (ruling 2026-07-31, #31 item 5): SPEC.md
§Ellipses writes `NN -> NN` and `ZZ[[t]]`, and `QQ` completes it. -/
def domainAlias? : Name → Option Domain
  | `R | `RR => some .real
  | `CC => some .complex
  | `NN => some .nat
  | `ZZ => some .int
  | `QQ => some .rat
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
  | .spanV n basis => .obj (.setObj (.span n basis))
  | .cosetV offset kernel => .obj (.setObj (.coset offset kernel))
  -- a symbolic expression becomes an OBJECT, which is what lets it be a
  -- method argument: `lim_{t → ∞}` and `∫₀^π` write points that are not
  -- elements of any domain
  | .sym e => .obj (.symObj e)
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

/-- A registered name as the mathematician spells it. Lean escapes a name
that is not an identifier — the category SPEC.md writes `QQ-Mod` prints as
`«QQ-Mod»` — and those guillemets are Lean's syntax for WRITING the name, not
part of it. -/
def renderName (n : Name) : String :=
  match ((toString n).replace "«" "").replace "»" "" with
  -- …and a registered category whose name carries a DOMAIN carries it in
  -- ASCII, because a Lean name may not hold `ℚ`. This is the closed set of
  -- them: `Schemes/QQ` is written `Schemes/ℚ`, and `QQ-Mod` displays as its
  -- CANONICAL spelling `Mod(ℚ)` (ruling 2026-07-31, the four spelling pins;
  -- the hyphenated input spelling stays an accepted alias). A third one is
  -- added here.
  | "Schemes/QQ" => "Schemes/ℚ"
  | "QQ-Mod" => "Mod(ℚ)"
  | s => s

def renderCat (c : CatRef) : String :=
  if c.params.isEmpty then renderName c.name
  else s!"{renderName c.name}({", ".intercalate (c.params.toList.map renderParam)})"

def renderPattern : PresPattern → String
  | .elemOf d => s!"element of {renderDomainPattern d}"
  | .domainIs d => s!"the domain {renderDomainPattern d}"
  | .finiteSet => "a finite set"
  | .progression d => s!"a progression over {renderDomainPattern d}"
  | .domainSetOf d => s!"the underlying set of {renderDomainPattern d}"
  | .productSet => "a cartesian product"
  | .powersetSet => "a powerset"
  | .domainDiffSet => "a difference of two domains"
  | .spanSet => "a subspace of ℚⁿ"
  | .cosetSet => "a coset of the constants"
  | .predicateSet => "a guard-backed predicate set"
  | .anySet => "any set"
  | .cyclicMod => "a cyclic module"
  | .specObj => "an affine scheme"
  | .symbolic => "a symbolic expression"
  | .homElem => "a hom of free ℚ-modules"
  | .anyObj => "any object"

def renderRoute (r : Route) : String :=
  s!"{r.method} for {renderPattern r.pattern} → backend {r.backend}, \
op {repr r.opId}, priority {r.priority}"

/-- How a method became semantically available, in the wording the
diagnostics and the gap share. -/
def renderVia (entry : CatRef) (via : List Name) : String :=
  if via.isEmpty then s!"declared directly on {renderCat entry}"
  else s!"inherited through {" ≤ ".intercalate (renderCat entry :: via.map renderName)}"

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
  | .unknownMethod m =>
      -- SPEC.md §Ellipses' `R.dimension()` is the Krull dimension of a ring,
      -- held for #13 demand with the multivariate algebras it is asked of —
      -- a HELD method, named as one, rather than a name the registry happens
      -- not to carry
      if m == `dimension then
        "dimension() — the Krull dimension of a ring (SPEC.md §Ellipses) — is \
the pinned spelling of a tier-2 feature, held for #13 demand (#31): the \
spelling is reserved, and the dimension is refused rather than approximated. \
A subspace's `dim()` is the dimension this slice computes"
      else s!"there is no method named '{m}' in the registry"
  | .notApplicable m profile declaredOn =>
      let prof := ", ".intercalate (profile.toList.map renderCat)
      let decl := ", ".intercalate (declaredOn.toList.map renderName)
      s!"'{m}' is not a method of any category this object belongs to.\n  \
profile:      {if prof.isEmpty then "(none)" else prof}\n  \
declared on:  {if decl.isEmpty then "(nowhere)" else decl}"
  | .ambiguous m cands =>
      let cs := ", ".intercalate (cands.toList.map fun r =>
        match r.viaFunctor with
        | some step => s!"{renderName r.decl.receiver} (transported by functor '{step.functor}')"
        | none => s!"{renderName r.decl.receiver} (via {renderCat r.profileEntry})")
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
  /-- Advice accumulated while a statement evaluates, drained into `info`
  lines by the command layer (`Syntax.runCas`). A note rides ALONGSIDE a
  result and is never part of it — nothing downstream may read one back,
  which is what keeps this distinct from the opt-in logging layer (#8):
  the one producer today is the ruled `roots` default (`rootsRingNote`),
  where the ruling itself asks for the help. -/
  notes : IO.Ref (Array String)

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

/-! `callMethod` and `rootsRingNote` live INSIDE the `mutual` block below:
the predicate-set intercept (#31 item 7) evaluates a stored guard, so
`callMethod` and `eval` are mutually recursive. -/

/-- The QQbar ↪ ℂ advisory (#31 item 10, log-at-use ruling): every algebraic
number a backend positions in ℂ rides Sage's one fixed embedding of QQbar,
and that CHOICE is logged where it flows — the ℂ[x] `roots`/`factor` calls,
whose results are complex algebraic values — never declared silently. The
declaration registry (a choice named at registration) is CategoryGraph-era
family management and stays deferred. -/
private def embeddingNote (ctx : EvalCtx) (recv : Obj) (m : Name) : EvalM Unit := do
  unless m == `roots || m == `factor do return ()
  let .elem (.poly .complex) _ := recv | return ()
  ctx.notes.modify (·.push "the algebraic numbers of this result are placed \
in ℂ along the backend's one fixed embedding QQbar ↪ ℂ — an embedding choice \
logged at use (#31 item 10); no other embedding is consulted")

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

/-- The exact rational scalar a denote presents — the left factor of the
scaling reading of `*` (#31 item 6). -/
private def scalarOf? (r : Denote) : Option Value :=
  match r.value? with
  | some v => if (Native.toRat? v).isSome then some v else none
  | none => none

/-- How many candidates a comprehension may test before the operation fails
honestly. A loud ceiling, never a truncated answer. Its reach over ℤ is
smaller than the number suggests — the tail bound is symmetric about the
origin, so an offset window costs ~2×|offset| candidates. -/
private def comprehensionCap : Int := 100000

/-- How many ambient candidates a predicate set's TRIAL enumeration may test
(#31 item 7). A loud ceiling naming itself, never a truncated answer. -/
private def predicateTrialCap : Nat := 10000

/-- The domain a comprehension CANDIDATE presents as. A candidate of ℕ is a
plain number, and "plain numbers are naturally elements of ZZ" (SPEC.md's own
sentence) — ℕ itself declares no methods (the empty-ℕ-profile fork is cas#29)
— so a ROUTED guard (`n.is_prime()`) reads the candidate as the integer it
is. The value is unchanged either way; only the tag is. -/
private def candidateDom (dom : Domain) : Domain :=
  if dom == .nat then .int else dom

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

/-- Execute a method, and answer for a requested TOLERANCE when the method
carries one: a non-positive ε is a surface refusal (it is not a tolerance),
and any failure to meet a positive one is the capability failure naming it.

Two ELABORATION-decided receivers are answered before any route is taken,
each for the one-owner reason: inclusion between two DOMAINS is the
canonical-map registry's claim wherever it is spelled (`evalAssert` already
answers `assert D ⊆ E` from the registry, and the method spelling must be
the SAME decision — two spellings, one owner, per the ⊆ ruling of
2026-07-31), and a PREDICATE set's guard is a surface expression only this
evaluator can read (#31 item 7). -/
partial def callMethod (ctx : EvalCtx) (recv : Obj) (m : Name) (args : Array Obj)
    : EvalM Denote := do
  if m == `subset then
    if let .domainObj d := recv then
      if let some (Obj.domainObj e) := args[0]? then
        return Denote.ofValue (.bool (← ofStr (domainSubset ctx.canonMaps d e)))
  if let .setObj (.predicate dom binder guard) := recv then
    if let some r ← predicateSetMethod? ctx dom binder guard m args then
      return r
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

/-- What a PREDICATE set (#31 item 7) answers by ELABORATION, or `none` for
everything else — which then resolves and routes as usual, where the native
layer's honest "no canonical form" owns the refusals (equality, inclusion,
the binary operations) and `presCard` owns the cardinality refusal.

- `contains` evaluates the guard AT the candidate — after the ambient's own
  membership test, so `-1 ∈ {n ∈ ℕ | …}` is `false` before any guard runs;
- `nth` enumerates by TRIAL over the ambient's countable indexing, capped
  LOUDLY at `predicateTrialCap` candidates — a stop that names the ceiling,
  never a truncated answer. -/
partial def predicateSetMethod? (ctx : EvalCtx) (dom : Domain) (binder : Name)
    (guard : CasExpr) (m : Name) (args : Array Obj) : EvalM (Option Denote) := do
  let pres := SetPresentation.predicate dom binder guard
  let decide (v : Value) : EvalM Bool := do
    if !Native.inDomain? dom v then return false
    let r ← eval { ctx with local? := some (binder, .elem (candidateDom dom) v) } guard
    match r.value? with
    | some (.bool b) => pure b
    | _ => throw (.msg s!"the guard of {pres.render} did not decide at \
{binder} = {v.render}: {r.render}")
  match m, args with
  | `contains, #[.elem _ v] =>
      return some (Denote.ofValue (.bool (← decide v)))
  | `contains, #[o] =>
      throw (.msg s!"membership in {pres.render} is decided for an ELEMENT, \
and {o.presentation} is not one")
  | `nth, #[.elem _ kv] => do
      let some kq := Native.toRat? kv
        | throw (.msg s!"an index into {pres.render} is a nonnegative integer, \
and {kv.render} is not one")
      if kq.den != 1 || kq.num < 0 then
        throw (.msg s!"an index into {pres.render} is a nonnegative integer, \
and {kv.render} is not one")
      let k := kq.num.toNat
      let mut found := 0
      for i in [0:predicateTrialCap] do
        let cand ← callMethod ctx (.domainObj dom) `nth #[.elem .int (.int (Int.ofNat i))]
        let some cv := cand.value?
          | throw (.msg s!"{dom.render} answered nth({i}) with \
{cand.presentation}, which is not an element")
        if ← decide cv then
          if found == k then
            return some (.obj (.elem dom (← ofStr (coerceValue ctx.canonMaps dom cv))))
          found := found + 1
      throw (.msg s!"nth({k}) on {pres.render}: {predicateTrialCap} candidates \
of {dom.render} were tried and only {found} member(s) surfaced — the trial \
ceiling (#31 item 7), a loud stop rather than a longer silent search")
  | _, _ => return none

/-- The ruled `roots` default (owner rulings, 2026-07-31; DESIGN.md §Exact
number systems): `p.roots()` answers in `p`'s own coefficient ring, and no
spelling silently applies a field extension. The help the ruling asks for in
exchange is EXACT, not a disjunction: the deficit is decided from the
FACTORIZATION — the same checked route `p.factor()` rides — whose linear
factors carry the root multiplicities, so the note fires precisely when
`p` fails to SPLIT in its ring (Σ mᵢ < deg) and says how many roots lie in
an extension, counted with multiplicity. `(x−1)²` over ℚ splits and gets no
note. A note is ADVICE on an unexpected-but-true result, never a refusal
(owner, 2026-07-31); it names the escalation SPEC.md already writes and the
explicit multiplicity access (`factor`). The comprehension spelling
`{a ∈ D | p(a) = 0}` names its ring itself, so it gets no note; ℂ[x]
receivers get none either, because everything splits there. -/
partial def rootsRingNote (ctx : EvalCtx) (recvStx : CasExpr) (recv : Obj)
    (m : Name) (result : Denote) : EvalM Unit := do
  unless m == `roots do return ()
  let .elem (.poly d) (.poly _ coeffs) := recv | return ()
  if d == .complex then return ()
  let some (.finite _ elems) := result.asSet? | return ()
  -- degree = size − 1 (coefficients ascending, no trailing zeros); constants
  -- promise nothing, so only degree ≥ 1 can be deficient
  let deg := coeffs.size - 1
  -- deg distinct roots already force a split — no factorization needed
  if coeffs.size < 2 || elems.size == deg then return ()
  -- the roots route exists only where the factor route does (ℤ[x], ℚ[x]),
  -- so a factor failure here is a real defect and stays loud
  let .val (.factorization _ factors _) ← callMethod ctx recv `factor #[]
    | throw (.msg s!"`factor` did not answer with a factorization while \
deciding whether {recv.presentation} splits")
  let multTotal := factors.foldl (init := 0) fun t (f, k) =>
    match f with
    | .poly _ cs => if cs.size == 2 then t + k else t
    | _ => t
  if multTotal == deg then return ()
  let p := match recvStx with | .ref n => s!"{n}" | _ => "p"
  ctx.notes.modify (·.push s!"{p} does not split in {d.render}: its \
{elems.size} root(s) there carry total multiplicity {multTotal} of degree \
{deg} (`{p}.factor()` shows the multiplicities), and the remaining \
{deg - multTotal} lie in an extension. For all of them: \
`let {p}C := map {p} to ℂ[x]`, then `{p}C.roots()`")

/-- `k · S` (SPEC.md §Ellipses' `2ℕ`; ruling 2026-07-31, #31 item 6) — the
IMAGE of the scaling map, as a presentation: an arithmetic progression
scales to an arithmetic progression, a finite set scales elementwise, and
`ℕ` is the progression `{0, 1, 2, ...}`. CEILING, and it is stated: those
three presentations under a rational scalar; everything else refuses naming
this rule, never a guess. -/
partial def scaleSet (ctx : EvalCtx) (k : Value) : SetPresentation → EvalM Denote
  | .finite _ elems => do
      let scaled ← ofStr (elems.mapM (Native.scalarMul k))
      let d ← ofStr (elemsDomain ctx.canonMaps scaled)
      return .obj (.setObj (.finite d
        (← ofStr (scaled.mapM (coerceValue ctx.canonMaps d)))))
  | .arithProg dom first step last? => do
      let first' ← ofStr (Native.scalarMul k first)
      let step' ← ofStr (Native.scalarMul k step)
      let last?' ← ofStr (last?.mapM (Native.scalarMul k))
      let de ← ofStr (elemsDomain ctx.canonMaps (#[first', step'] ++ last?'.toArray))
      let d ← match ← ofStr (domJoin ctx.canonMaps dom de) with
        | some j => pure j
        | none => throw (.msg s!"{dom.render} and {de.render} have no common domain")
      return .obj (.setObj (.arithProg d
        (← ofStr (coerceValue ctx.canonMaps d first'))
        (← ofStr (coerceValue ctx.canonMaps d step'))
        (← ofStr (last?'.mapM (coerceValue ctx.canonMaps d)))))
  | .domainSet .nat => scaleSet ctx k (.arithProg .nat (.int 0) (.int 1) none)
  | s => throw (.msg s!"a scalar times a set is the IMAGE of the scaling map, \
presented for an explicit finite set, an arithmetic progression, or ℕ \
(#31 item 6) — and {s.render} is not one of those")

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
      -- SPEC.md §Differentials writes the derivation `(d/dx)`, which the term
      -- grammar reads as a division of two NAMES — and in that reading
      -- neither name is bound, so it has no other meaning. The move
      -- `in QQ-Mod` already makes for a hyphenated category name, and the
      -- boundness check is what keeps it from stealing a real quotient:
      -- `let d := 6 in ℤ` and `let dx := 2 in ℤ` give the division back.
      if isDerivationSpelling ctx.isBound a b then
        return Denote.ofValue (.derivation false)
      -- `Algebras/K` is SPEC.md §Ellipses' spelling of a category FAMILY this
      -- slice does not register, held for #13 demand — so the spelling is
      -- read and refuses BY NAME rather than reporting the `Algebras` half as
      -- an unbound name the author never wrote alone. A bound `Algebras`
      -- still wins, exactly as it does for `AA`.
      if let .ref `Algebras := a then
        if !ctx.isBound `Algebras then
          throw (.msg "Algebras/K — the algebras over K — is the pinned \
spelling of a category FAMILY this slice does not register (#31), held for \
#13 demand: the spelling is reserved, and the family is refused rather than \
approximated. `Mod(K)` is the module category that is registered")
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
      -- `AA^n(K)` is THE affine-space spelling (pinned 2026-07-31, the four
      -- spelling pins), and polynomial maps on AA^n are tier 2, held for #13
      -- demand — so the spelling parses and refuses BY NAME. A bound `AA`
      -- still wins, exactly as a binding wins over a constant.
      if let .ref `AA := a then
        if !ctx.isBound `AA then
          throw (.msg "AA^n(K) — affine n-space over K — is the pinned \
spelling of a tier-2 feature (polynomial maps on AA^n, #31), held for #13 \
demand: the spelling is reserved, and the feature is refused rather than \
approximated")
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
  | .bin .add a b => do
      -- SPEC.md §Indefinite integration writes `x³ + (1/2)x² + x + ℚ` on the
      -- right of an assertion: a value plus a DOMAIN denotes the COSET of
      -- that domain, exactly as `A × B`, `𝒫(A)` and `ℂ - ℚ` denote — built by
      -- elaboration, no method, no route. It goes through `Value.mkCoset`, so
      -- the coset a mathematician writes and the one `∫` computes are the
      -- same value however either was spelled
      let x ← eval ctx a
      let y ← eval ctx b
      match y with
      | .obj (.domainObj k) =>
          let v ← ofStr (asValueOf x "the offset of a coset")
          let (offset, kernel) ← ofStr (Value.mkCoset v k)
          return .obj (.setObj (.coset offset kernel))
      | _ =>
        return Denote.ofValue (← ofStr (valueBin ctx.canonMaps .add
          (← ofStr (asValueOf x)) (← ofStr (asValueOf y))))
  | .bin .mul a b => do
      -- SPEC.md §Ellipses' `2ℕ` (ruling 2026-07-31, #31 item 6): a SCALAR
      -- against a SET is the image of the scaling map, DENOTED by elaboration
      -- exactly as `A × B` and a coset are — no method, no route. Every other
      -- `*` is the arithmetic it always was.
      let x ← eval ctx a
      let y ← eval ctx b
      match scalarOf? x, y.asSet?, scalarOf? y, x.asSet? with
      | some k, some s, _, _ => scaleSet ctx k s
      | _, _, some k, some s => scaleSet ctx k s
      | _, _, _, _ =>
          return Denote.ofValue (← ofStr (valueBin ctx.canonMaps .mul
            (← ofStr (asValueOf x)) (← ofStr (asValueOf y))))
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
  -- SPEC.md §Differentials' `(6x + 1) dx`. DENOTED by elaboration, like a set
  -- literal and like `A × B`: `dx` is the free generator of Ω¹ rather than a
  -- value, so there is nothing to multiply and no route to take
  | .diffForm p => do
      let v ← ofStr (asValueOf (← eval ctx p) "the coefficient of a `dx` form")
      let some (c, _) := asPolyCoeffs v
        | throw (.msg s!"{v.render} is not a coefficient of Ω¹_\{k[x]/k}: a \
differential 1-form here is a POLYNOMIAL against the free generator `dx`")
      return Denote.ofValue (.diff1 c v)
  -- SPEC.md's `∫ f dx`: the `antiderivative` METHOD, applied by elaboration
  -- exactly as the derivation is. What comes back is a COSET — the complete
  -- set of primitives, which is what SPEC.md's `+ ℚ` says
  | .integral f => do
      let recv ← ofStr (asObjOf (← eval ctx f))
      callMethod ctx recv `antiderivative #[]
  -- SPEC.md §Elementary calculus. All three analysis operations are ordinary
  -- METHODS on a FUNCTION — the spelling builds the function by elaboration,
  -- exactly as `{a ∈ ℂ | r(a) = 0}` builds the polynomial it hands to `roots`
  -- — so `#explain_route` explains them and a missing backend is the ordinary
  -- structured gap. The body is read SYMBOLICALLY: a limit and a definite
  -- integral are asked of an EXPRESSION, and the polynomial reading would
  -- decide nothing extra about either.
  | .limitOf binder point body => do
      let f ← ofStr (symFunction ctx.isBound binder body)
      let a ← ofStr (asObjOf (← eval ctx point))
      callMethod ctx f `limit #[a]
  | .defIntegral binder lo hi body => do
      let f ← ofStr (symFunction ctx.isBound binder body)
      let a ← ofStr (asObjOf (← eval ctx lo))
      let b ← ofStr (asObjOf (← eval ctx hi))
      callMethod ctx f `definite_integral #[a, b]
  | .seriesDom coeff => do
      let c ← eval ctx coeff
      let .obj (.domainObj d) := c
        | throw (.msg s!"`E[[t]]` is the formal power series over a DOMAIN, and {c.presentation} is not one")
      return .obj (.domainObj (.series d))
  | .truncTarget k =>
      throw (.msg s!"`E[[t]]/(t^{k})` is the TARGET of `map … to` — a request that a series be presented by its first {k} coefficients — and nothing else: it is not a domain, not a set, and not a quotient ring this surface presents. There is no Domain constructor for it, so it answers no membership, cardinality or inclusion question")
  -- SPEC.md §Ellipses' `∑_{n ∈ ℕ} n² tⁿ`. The RULE is read with the sum's
  -- binder as the indeterminate — the move the root set and the guarded
  -- comprehension both make — so the coefficients come out exactly, and a
  -- rule that is not a polynomial in the binder is a loud refusal
  | .seriesSum binder index rule => do
      ofStr (checkBindableName binder)
      let idx ← eval ctx index
      let some (.domainSet .nat) := idx.asSet?
        | throw (.msg s!"a generating sum indexes over ℕ, and {idx.presentation} is not it")
      let rv ← ofStr (asValueOf (← eval { ctx with indet? := some (binder, .int) } rule)
        s!"the coefficient rule of a generating sum")
      let some (c, cs) := asPolyCoeffs rv
        | throw (.msg s!"{rv.render} is not a polynomial in '{binder}': the rule of a generating sum gives the coefficient of tⁿ as a polynomial in n, and this slice reads no wider rule")
      let some qs := cs.mapM Native.toRat?
        | throw (.msg s!"the rule {rv.render} has a coefficient this slice cannot read as a rational, and a series' coefficients are exact rationals here")
      return Denote.ofValue (.seriesV c (.rule qs))
  | .coeffOf k series => do
      let sv ← ofStr (asValueOf (← eval ctx series) s!"`[t^{k}]…`")
      let .seriesV _ gen := sv
        | throw (.msg s!"`[t^{k}]…` extracts a coefficient of a SERIES, and {sv.render} is not one")
      let some q := Value.seriesCoeff? gen k
        | throw (.msg (pastSeriesCeiling k gen))
      return Denote.ofValue (Value.ofRat q)
  | .specOf ring => do
      let r ← eval ctx ring
      let .obj (.domainObj d) := r
        | throw (.msg s!"`Spec` takes a RING, and {r.presentation} is not one")
      return .obj (.specOf d)
  -- SPEC.md §Indefinite integration: `kernel(d/dx : ℚ[x] → ℚ[x])` is ℚ. The
  -- constants are the kernel of differentiation over a ring where the
  -- integers are invertible, which is what makes the indefinite integral a
  -- COSET of ℚ and not of something smaller — over ℤ/p the p-th powers are
  -- killed too, so that ring is refused rather than answered wrongly.
  | .kernelOf op arrow => do
      let o ← eval ctx op
      let .val (.derivation _) := o
        | throw (.msg s!"`kernel(…)` takes a derivation here — SPEC.md writes \
`kernel(d/dx : ℚ[x] → ℚ[x])` — and {o.presentation} is not one")
      let a ← eval ctx arrow
      let .obj (.domainObj (.funcs src tgt)) := a
        | throw (.msg s!"`kernel(d/dx : …)` needs the arrow the derivation runs \
along, as in `ℚ[x] → ℚ[x]`; got {a.presentation}")
      if src != tgt then
        throw (.msg s!"a derivation runs from a ring to ITSELF, and \
{src.render} → {tgt.render} does not")
      match src with
      | .poly c =>
          if c == .rat || c == .real || c == .complex then
            return .obj (.domainObj c)
          else
            throw (.msg s!"the kernel of d/dx on {src.render} is the constants \
only where the integers are invertible in {c.render}; over {c.render} this \
slice does not state it rather than answering with a ring it has not checked")
      | d => throw (.msg s!"d/dx differentiates a POLYNOMIAL ring, and \
{d.render} is not one")
  | .sqrt e => do
      let v ← ofStr (asValueOf (← eval ctx e) "√")
      let some q := Native.toRat? v
        | throw (.msg s!"√ presents the exact square root of a rational; \
{v.render} is not one, and this slice does not approximate it")
      let r ← ofStr (Value.sqrtOfRat q)
      -- an ALGEBRAIC root is one of two, and the spelling picks a branch —
      -- an embedding choice, logged at use (#31 item 10, log-at-use ruling):
      -- the non-negative root for a positive radicand, i·√|d| upward for a
      -- negative one. A rational root is ordinary arithmetic and gets no note.
      if let .alg .. := r then
        ctx.notes.modify (·.push s!"√ denotes ONE root by convention — the \
non-negative branch (upward, i·√|d|, for a negative radicand): an embedding \
choice made by the spelling, logged at use (#31 item 10)")
      return Denote.ofValue r
  | .magnitude e => do
      -- the bars are a SPELLING: which method they name is the receiver's
      -- business, and both answers are ordinary category methods
      let r ← eval ctx e
      let o ← ofStr (asObjOf r)
      callMethod ctx o (if r.asSet?.isSome then `cardinality else `abs) #[]
  | .cmp op a b => do
      let x ← eval ctx a
      let y ← eval ctx b
      -- SPEC.md's `span_QQ{u₁, u₂} \leq ℚ³`, with its own note: "\leq means
      -- SUBOBJECT in a category". Which reading `≤` has is the operands'
      -- business, exactly as the receiver decides which method `|·|` names
      -- and as two domains decide that `-` denotes a difference: between a
      -- subspace and its ambient space it is the ascription, and the ambient
      -- is CHECKED rather than taken on trust
      match op, x.asSet?, y with
      | .le, some (.span n basis), .obj (.domainObj d) =>
          if d == .vector n .rat then return .obj (.setObj (.span n basis))
          else throw (.msg s!"{(SetPresentation.span n basis).render} is not a \
subobject of {d.render}: a subspace of {(Domain.vector n .rat).render} lies in \
that space and in no other")
      | _, _, _ =>
        let xv ← ofStr (asValueOf x)
        let yv ← ofStr (asValueOf y)
        let some ord := Native.scalarCmp xv yv
          | throw (.msg s!"{xv.render} and {yv.render} are not comparable")
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
      let d ← callMethod ctx r m as
      rootsRingNote ctx recv r m d
      embeddingNote ctx r m
      return d
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
          -- a POLYNOMIAL argument SUBSTITUTES — the move `f ∘ g` already
          -- makes, and what `p(x)` means when `x` is an indeterminate; a
          -- scalar argument is the scalar Horner evaluation it always was
          match x with
          | .poly .. =>
              return Denote.ofValue
                (← ofStr (applyPoly ctx.canonMaps (.poly c coeffs) x))
          | x => return Denote.ofValue (← ofStr (Native.polyEval c coeffs x))
      -- SPEC.md applies a matrix to a vector by juxtaposition — `M v`,
      -- `M(M⁻¹ b)` — and a matrix IS a linear map, so applying it is the
      -- product it already has. Elaboration-inserted like calling a
      -- polynomial: no method, no route, one implementation for both
      -- spellings, and `Native.matApply`'s shape check answers either way
      -- SPEC.md §Differentials' `d(f)` and `(d/dx)(f)` — ONE operation with
      -- two result shapes. Applying a derivation is elaboration-inserted like
      -- calling a polynomial (decision 6), and what it inserts is the ordinary
      -- `derivative` METHOD: same resolver, same router, same executor, and
      -- `#explain_route f.derivative()` explains it. Only the WRAPPING differs
      -- — `d` lands in Ω¹ and `d/dx` lands back in the ring.
      | some (.derivation asForm) =>
          if args.size != 1 then
            throw (.msg s!"a derivation is applied to exactly one element, got \
{args.size}")
          let arg ← ofStr (asObjOf (← eval ctx args[0]!))
          let r ← callMethod ctx arg `derivative #[]
          if !asForm then return r
          let some v := r.value?
            | throw (.msg s!"the derivative {r.presentation} is not a value the \
universal differential can present as a 1-form")
          let some (c, _) := asPolyCoeffs v
            | throw (.msg s!"{v.render} is not a coefficient of Ω¹")
          return Denote.ofValue (.diff1 c v)
      | some m@(.mat ..) =>
          if args.size != 1 then
            throw (.msg s!"a matrix is applied to exactly one vector, got {args.size}")
          let x ← ofStr (asValueOf (← eval ctx args[0]!))
          return Denote.ofValue (← ofStr (valueBin ctx.canonMaps .mul m x))
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
            | throw (.msg (match body with
                -- a symbolic body is a presentation, not a computation: the
                -- backend takes limits, definite integrals and expansions OF
                -- it, and evaluating `sin(2)` here would be an approximation
                -- this surface has no business inventing
                | .sym _ => s!"{fv.render} has a SYMBOLIC body, and this slice \
does not evaluate one at a point — it presents the expression so a limit, a \
definite integral or a Taylor expansion can be taken of it. A decimal for \
{body.render} at a point would be an approximation, which is a separate \
operation on an exact element and not something a call inserts"
                | v => s!"{v.render} is not a polynomial body"))
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
      -- Calling a HOM applies it to a point of its domain, exactly: the
      -- derived standard-frame rows act on the point's coordinates. Same
      -- elaboration-inserted move as calling a function (decision 6).
      | some (.hom src tgt _ rows) => do
          if args.size != 1 then
            throw (.msg s!"a hom is called with exactly one point of its \
domain, got {args.size}")
          let .vector n .rat := src
            | throw (.msg s!"{fv.render} is not a hom on a free ℚ-module")
          let av ← ofStr (asValueOf (← eval ctx args[0]!))
          let some cs := Value.ratComps? n av
            | throw (.msg s!"{av.render} is not a point of {src.render}, the \
domain of this hom")
          let ys := rows.map fun r => dotRow r cs
          match tgt with
          | .rat => return Denote.ofValue (.rat ys[0]!)
          | .vector m .rat => return Denote.ofValue (.vec m .rat (ys.map Value.rat))
          | t => throw (.msg s!"a hom here lands in ℚ or ℚᵐ, not {t.render}")
      | _ => throw (.msg s!"{fv.presentation} is not callable")
  | .finSet elems => do
      let vs ← elems.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let d ← ofStr (elemsDomain ctx.canonMaps vs)
      -- a hand-written duplicate is the same ELEMENT written twice, so the
      -- presentation dedups on construction (after the coercion into the
      -- joined domain, where 1 and 1/1 are one value) — display, membership
      -- and cardinality then all see the one set instead of disagreeing
      return .obj (.setObj (.finite d
        (Native.dedupValues (← ofStr (vs.mapM (coerceValue ctx.canonMaps d))))))
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
  | .spanOf gens => do
      let vs ← gens.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      -- the ambient is the generators' own length, and every one of them
      -- enters ℚⁿ through the ordinary preferred canonical map: `span_QQ` is
      -- spanned OVER ℚ, so an integer generator is its image there
      let some n := vs[0]?.bind fun v => match v with | .vec m .. => some m | _ => none
        | throw (.msg (match vs[0]? with
            | some v => s!"`span_QQ\{…}` spans a subspace of ℚⁿ, so its generators \
are vectors: {v.render} is not a vector"
            | none => "`span_QQ{}` names no ambient space: the ℚⁿ a span lies in \
is read off its generators, so the TRIVIAL subspace is written with the zero \
vector of the space meant — `span_QQ{(0, 0)}` — or obtained, as `M.ker()`"))
      let cs ← ofStr (vs.mapM (coerceValue ctx.canonMaps (.vector n .rat)))
      return .obj (.setObj (.span n (← ofStr (Value.mkSpanBasis n cs))))
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
  -- SPEC.md's `map Tf to ℝ[[t]]/(t^6)` and `map f to ℤ[[t]] / O(t^5)`. The
  -- SAME shape `map … to ℝ/O(ε)` has: a REQUEST, answered by the presentation
  -- itself rather than by a coercion into a domain that does not exist
  | .mapTo e (.truncTarget k) => do
      let v ← ofStr (asValueOf (← eval ctx e) "`map … to E[[t]]/(t^k)`")
      let .seriesV c gen := v
        | throw (.msg s!"a truncation presents a SERIES by its first {k} coefficients, and {v.render} is not one")
      let some qs := Value.seriesUpTo? gen k
        | throw (.msg (pastSeriesCeiling k gen))
      return Denote.ofValue (.seriesV c (.terms qs))
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
  | .lamN _ _ =>
      throw (.msg "a multi-binder `↦` definition is a hom of free ℚ-modules: \
bind it with its function domain, as in \
`let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c`")
  | .comprehension head binder index guard? =>
      evalComprehension ctx head binder index guard?
  -- SPEC.md's `let roots := {a ∈ ℂ | r(a) = 0} in 𝒫(ℂ)`. This is NOT the
  -- guarded comprehension's decision procedure — that one bounds a binder
  -- over ℕ or ℤ from a polynomial COMPARISON and tests candidates. Solving an
  -- EQUATION is a different operation, and it is one the surface already has:
  -- the equation is read with the binder as the INDETERMINATE, moved to
  -- `p(x) = 0`, presented in the index domain's polynomial ring, and handed
  -- to `roots` — same method, same route, same backend, one implementation.
  | .rootSet binder index lhs rhs => do
      ofStr (checkBindableName binder)
      let idx ← eval ctx index
      -- SPEC.md §Indefinite integration's `{h ∈ ∫ f dx | h(0) = 0}` — the same
      -- production, over a COSET rather than a domain. It is a different
      -- equation to solve and it is solved differently, and the ceiling is
      -- stated rather than approximated: the guard must EVALUATE the binder at
      -- a point. `h(a) = p(a) + c` exactly (the kernel is the constants), so
      -- `c = b − p(a)` is the unique solution — no search, no sampling, and no
      -- assumption about a slope, because the SHAPE is checked before the
      -- arithmetic runs.
      if let some (.coset offset kernel) := idx.asSet? then
        let (pt, other) ← ofStr (cosetGuardSides binder lhs rhs)
        let a ← ofStr (asValueOf (← eval ctx pt) "the point a coset guard evaluates at")
        let b ← ofStr (asValueOf (← eval ctx other) "the other side of a coset guard")
        let some (c, cs) := asPolyCoeffs offset
          | throw (.msg s!"{offset.render} is not a polynomial offset")
        let v0 ← ofStr (Native.polyEval c cs a)
        let k ← ofStr (valueBin ctx.canonMaps .sub b v0)
        let sol ← ofStr (valueBin ctx.canonMaps .add offset k)
        let solD ← ofStr (coerceValue ctx.canonMaps (.poly kernel) sol)
        return .obj (.setObj (.finite (.poly kernel) #[solD]))
      let some (.domainSet d) := idx.asSet?
        | throw (.msg s!"`\{x ∈ D | p(x) = q(x)}` is the set of solutions in a \
DOMAIN D, and {idx.presentation} is not one")
      let ictx := { ctx with indet? := some (binder, d) }
      let l ← ofStr (asValueOf (← eval ictx lhs) "the left side of the equation")
      let r ← ofStr (asValueOf (← eval ictx rhs) "the right side of the equation")
      let p ← ofStr (valueBin ctx.canonMaps .sub l r)
      -- the ring the roots are sought in is the INDEX set's own, so the answer
      -- is the roots that lie there — `{a ∈ ℂ | …}` splits and `{a ∈ ℚ | …}`
      -- does not, which is the mathematics rather than a default
      let pd ← match coerceValue ctx.canonMaps (.poly d) p with
        | .ok pd => pure pd
        | .error inner =>
            -- the failure is the SITUATION — the index ring does not admit
            -- the equation — not whichever coefficient tripped first
            throw (.msg s!"the solutions are sought in {d.render}, the index \
set's own ring, but the equation `{p.render} = 0` does not present in \
{(Domain.poly d).render}: {inner}")
      callMethod ctx (.elem (.poly d) pd) `roots #[]
  | .aggregate m binder index body => do
      ofStr (checkBindableName binder)
      let idx ← eval ctx index
      let some s := idx.asSet?
        | throw (.msg s!"`∑_\{x ∈ X} …` aggregates over a SET, and \
{idx.presentation} is not one")
      -- SPEC.md writes `∑_{a ∈ roots} a`, whose body IS the binder: the
      -- receiver is then the index set itself, so an index with no element
      -- list reports the ordinary structured gap rather than a special one
      let bodyIsBinder := match body with | .ref b => b == binder | _ => false
      let recv ←
        if bodyIsBinder then ofStr (asObjOf idx)
        else match s with
          -- any other body aggregates its IMAGE, built by elaboration exactly
          -- as a set literal is — the binder is the same real local binding a
          -- comprehension's is, scoped to this expression and publishing
          -- nothing
          | .finite d elems =>
              let vs ← elems.mapM fun e => do
                ofStr (asValueOf (← eval { ctx with local? := some (binder, .elem d e) }
                  body) s!"the body at {binder} = {e.render}")
              let d' ← ofStr (elemsDomain ctx.canonMaps vs)
              pure (Obj.setObj (.finite d'
                (← ofStr (vs.mapM (coerceValue ctx.canonMaps d')))))
          | s => throw (.msg s!"a body other than the binder is aggregated over \
an EXPLICIT finite set, and {s.render} is not one")
      callMethod ctx recv m #[]

/-- The bounds a guard puts on the comprehension binder, decided by
`boundsOfPoly` after each comparison is rewritten as `p(n) ⋈ 0`. `none` =
the guard is not a comparison the rewriting reads at all — the caller
decides whether that is the lazy predicate presentation (#31 item 7) or a
refusal; an error inside a comparison (an unbound name, an unreadable side)
still propagates as the error it is. -/
partial def guardBounds (ctx : EvalCtx) (binder : Name) (dom : Domain)
    : CasExpr → EvalM (Option BinderBounds)
  | .conj a b => do
      match ← guardBounds ctx binder dom a, ← guardBounds ctx binder dom b with
      | some x, some y => return some (x.meet y)
      | _, _ => return none
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
          some <$> ofStr (if cs.size ≤ 1 then constantBounds op (cs[0]?.getD (Native.zeroOf c))
                 else boundsOfPoly op cs)
      | v => some <$> ofStr (constantBounds op v)
  | _ => return none

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
  ofStr (checkBindableName binder)
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
      local? := some (binder, .elem (candidateDom dom) kv) } e).value?) fun _ => pure none
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
      -- a guard is asked for a TRUTH VALUE, at the same candidate
      let guardProbe : EvalM Unit :=
        probe g (fun | .bool _ => true | _ => false) (undecidableGuard binder)
      -- The LAZY fallback (#31 item 7): a guard the bound extraction does
      -- NOT READ AT ALL (`n.is_prime()`, a membership test) presents the set
      -- BY ITS GUARD — provided the guard decides elementwise (the same
      -- probe as ever) and the head is the binder itself. The IMAGE of a
      -- lazy set has no presentation here, and says so rather than sampling
      -- one. A guard the extraction DOES read keeps its decided outcomes —
      -- a finite enumeration, the empty set, or the loud infinite refusal —
      -- exactly as before.
      let some b ← guardBounds ctx binder dom g |
        (do guardProbe
            if let .ref h := head then
              if h == binder then
                return .obj (.setObj (.predicate dom binder g))
            throw (undecidableComprehension s!"the head is not the binder \
'{binder}': only the filtering spelling `\{{binder} ∈ D | …}` is presented \
lazily by its guard (#31 item 7); the image of a lazy set is not presented."))
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
        let kctx := { ctx with local? := some (binder, .elem (candidateDom dom) kv) }
        match ← ofStr (asValueOf (← eval kctx g) s!"the guard at {binder} = {k}") with
        | .bool true =>
            out := out.push (← ofStr (asValueOf (← eval kctx head)
              s!"the head at {binder} = {k}"))
        | .bool false => pure ()
        | v => throw (.msg s!"the guard did not decide at {binder} = {k}: {v.render}")
      let d ← ofStr (elemsDomain ctx.canonMaps out)
      return .obj (.setObj (.finite d (← ofStr (out.mapM (coerceValue ctx.canonMaps d)))))

end

/-- Run the evaluator against a bare environment, discarding notes — the
test harness's seam. The syntax layer builds its own `EvalCtx` instead,
because it drains the notes into `info` output (`Syntax.runCas`). -/
def runEval (env : Environment) (e : CasExpr) : IO (Except EvalError Denote) := do
  (eval { env, notes := ← IO.mkRef #[] } e).run

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
  -- `Mod(QQ)` — the CANONICAL module-category spelling (ruling 2026-07-31,
  -- the four spelling pins): `Mod(K)` names the registered category `K-Mod`,
  -- whose hyphenated spelling stays the accepted alias. The registered NAME
  -- stays ASCII (a Lean name), exactly as `Schemes/QQ` does; `renderName`
  -- displays the canonical form. Before the generic application arm, which
  -- would otherwise swallow the unregistered name `Mod` and answer nothing.
  | .app (.ref `Mod) #[arg] =>
      -- the base is a domain TOKEN (`ℚ`) or a domain ALIAS ident (`QQ`) —
      -- the same two spellings every domain position accepts
      let d? := match arg with
        | .dom d => some d
        | .ref a => domainAlias? a
        | _ => none
      match d? with
      | some d =>
          let n := Name.mkSimple s!"{asciiDomain d}-Mod"
          if (catDecl? env n).isSome then some (n, #[]) else none
      | none => none
  | .app (.ref n) args => if (catDecl? env n).isSome then some (n, args) else none
  -- SPEC.md writes a HYPHENATED category name — `in QQ-Mod` — which the term
  -- grammar reads as a subtraction of two names. In ASCRIPTION position that
  -- reading has no other meaning (neither name is bound, and a difference of
  -- two unbound names is an error), so `A-B` names the registered category
  -- `A-B` when there is one, and is the ordinary error when there is not
  | .bin .sub (.ref a) (.ref b) =>
      let n := Name.mkSimple s!"{a}-{b}"
      if (catDecl? env n).isSome then some (n, #[]) else none
  -- …and SPEC.md §Differentials writes a SLASHED one, `in Schemes/ℚ`, which
  -- the term grammar reads as a quotient of a name by a domain. The reading
  -- is the same move for the same reason: in ascription position it has no
  -- other meaning, so it names the registered category when there is one.
  -- The domain is spelled in ASCII inside the registered name (`Schemes/QQ`)
  -- because a Lean name may not carry `ℚ`; `renderName` puts it back
  | .bin .div (.ref a) (.dom d) =>
      let n := Name.mkSimple s!"{a}/{asciiDomain d}"
      if (catDecl? env n).isSome then some (n, #[]) else none
  | _ => none
where
  asciiDomain : Domain → String
    | .nat => "NN" | .int => "ZZ" | .rat => "QQ"
    | .real => "RR" | .complex => "CC" | d => d.render

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
      -- a hom is a MORPHISM, and a category ascription states membership
      -- among a category's OBJECTS. `let φ: ℚ³ → ℚ := … in Mod(ℚ)` is the
      -- morphism-is-not-an-object hold (#31 item 4) — CategoryGraph-era
      -- ontology, and refused BY NAME rather than as an empty profile
      if let .elem _ (.hom ..) := o then
        throw (.msg s!"a hom is a MORPHISM, and `in {renderCat c}` states \
membership among a category's OBJECTS: a map is not an object of the \
category it runs in. Ascribing a hom to a category is held (#31 item 4) for \
the CategoryGraph-era ontology, and is refused rather than read as \
membership — the arrow `{o.presentation}` already names its domains")
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
  ofStr (checkBindableName binder)
  match asc with
  | .domain (.poly c) =>
      let o ← objOf (← eval { ctx with indet? := some (binder, c) } body)
      ascribe ctx o (.domain (.poly c))
  | .domain (.funcs src tgt) =>
      -- TWO readings, in a fixed order with a stated reason rather than a
      -- fallback: the POLYNOMIAL one is preferred wherever it applies,
      -- because it is the one that DECIDES things (`h(-t) = h(t)` and
      -- `(f ∘ g)(t) = t⁶` are settled by substitution, and two polynomial
      -- bodies compare). Only a body it cannot express is read SYMBOLICALLY,
      -- and a symbolic body decides nothing — it is a presentation the
      -- backend computes limits, integrals and expansions FROM. A body
      -- neither reading reaches is the refusal that lists the vocabulary.
      -- ONLY an EXPRESSIBILITY failure falls through to the symbolic reading.
      -- `EvalError` is already structured, so this discriminates rather than
      -- catching everything: a routing GAP, a resolver failure, tied routes,
      -- a backend error or an approximation request is about something other
      -- than what the polynomial engine can express, and laundering one into
      -- "not in the vocabulary" would report the wrong problem.
      let poly? : Except String (Option Value) ← tryCatch
        (do
          let d ← eval { ctx with indet? := some (binder, .int) } body
          match d.value? with
          | some v => return .ok (if (asPolyCoeffs v).isSome then some v else none)
          | none => return .ok none)
        (fun e => match e with
          | .msg m => pure (.error m)
          | e => throw e)
      match poly? with
      | .ok (some v) => return .elem (.funcs src tgt) (.func src tgt binder v)
      | tried =>
        match toSymExpr ctx.isBound binder body with
        | .ok sy => return .elem (.funcs src tgt) (.func src tgt binder (.sym sy))
        -- NEITHER reading reaches it, so the refusal carries both reasons:
        -- the vocabulary the symbolic reader lists, and what the polynomial
        -- engine actually said when it tried
        | .error symMsg =>
            throw (.msg (match tried with
              | .error polyMsg =>
                  s!"{symMsg}.\n  The polynomial reading was tried first and \
said: {polyMsg}"
              | .ok _ => symMsg))
  -- SPEC.md §Ellipses' `let f(t) = ∑_{n ∈ ℕ} n² tⁿ ∈ ℤ[[t]]`: the outer
  -- binder is the SERIES' indeterminate, which this slice spells `t`, and the
  -- generating sum binds its own summation variable. There is nothing for the
  -- outer binder to be an indeterminate OF here — a series' coefficients are
  -- indexed, not substituted into — so it is checked and then stands aside
  | .domain (.series c) =>
      if binder != `t then
        throw (.msg s!"the indeterminate of a formal power series is spelled \
`t` here, and `{binder}` is not it")
      let o ← objOf (← eval ctx body)
      ascribe ctx o (.domain (.series c))
  | _ =>
      throw (.msg s!"a `{binder} ↦ …` definition must be ascribed to a polynomial \
domain such as ℤ[x], a function domain such as ℝ → ℝ, or a series domain such \
as ℤ[[t]]")

/-- The rational a CONSTANT subexpression of a linear body denotes, when it
is one: numerals, negation, and the four operations over constants. `none` =
not a constant, which for the linear reader means "mentions a binder". -/
partial def ratConst? : CasExpr → Option Rat
  | .num z => some (Rat.ofInt z)
  | .neg e => (ratConst? e).map (- ·)
  | .bin .add a b => do return (← ratConst? a) + (← ratConst? b)
  | .bin .sub a b => do return (← ratConst? a) - (← ratConst? b)
  | .bin .mul a b => do return (← ratConst? a) * (← ratConst? b)
  | .bin .div a b => do
      let d ← ratConst? b
      if d == 0 then none else return (← ratConst? a) / d
  | _ => none

/-- The disclosed gap a body OUTSIDE the linear vocabulary is — tier 2 of
the 2026-07-31 ruling, held for #13 demand (#31). -/
private def nonlinearGap (what : String) : String :=
  s!"a multi-binder body is read as a LINEAR map here — a ℚ-combination of \
the binders, SPEC.md's `(a, b, c) ↦ a + b - c` — and this body is not one: \
{what}. Polynomial maps in several variables are a disclosed GAP (tier 2, \
#31), refused rather than approximated"

/-- One coordinate of a linear body, read STRUCTURALLY as a ℚ-combination of
the binders: the coefficient row it denotes in the standard frame. The
vocabulary is exactly linearity's own — binders, constants, `+ - ·` with a
constant factor, `/` by a constant — and anything outside it is the
disclosed tier-2 gap, never an approximation. -/
partial def linearRow (binders : Array Name) (e : CasExpr) : Except String (Array Rat) := do
  let n := binders.size
  let scale (q : Rat) (r : Array Rat) : Array Rat := r.map (q * ·)
  match e with
  | .ref x =>
      match binders.findIdx? (· == x) with
      | some i => return (Array.replicate n (0 : Rat)).set! i 1
      | none => .error (nonlinearGap s!"'{x}' is not one of its binders")
  | .neg a => return scale (-1) (← linearRow binders a)
  | .bin .add a b =>
      let (ra, rb) := (← linearRow binders a, ← linearRow binders b)
      return (Array.range n).map fun i => ra[i]! + rb[i]!
  | .bin .sub a b =>
      let (ra, rb) := (← linearRow binders a, ← linearRow binders b)
      return (Array.range n).map fun i => ra[i]! - rb[i]!
  | .bin .mul a b =>
      match ratConst? a, ratConst? b with
      | some q, _ => return scale q (← linearRow binders b)
      | _, some q => return scale q (← linearRow binders a)
      | none, none => .error (nonlinearGap "a product of two binder terms")
  | .bin .div a b =>
      match ratConst? b with
      | some q =>
          if q == 0 then .error "division by zero in a linear body"
          else return scale q⁻¹ (← linearRow binders a)
      | none => .error (nonlinearGap "a division by a binder term")
  | e =>
      match ratConst? e with
      | some q =>
          if q == 0 then return Array.replicate n (0 : Rat)
          else .error (nonlinearGap
            s!"the constant term {(Value.rat q).render} makes it affine, not linear")
      | none => .error (nonlinearGap "a shape outside the linear vocabulary")

/-- `let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c` — a HOM binding (owner ruling
2026-07-31, DESIGN.md §Homs are first-class). The VALUE is the map as the
mathematician wrote it — domain, codomain, images of a general element — and
the coefficient rows it derives are its matrix in the standard frame the
`ℚⁿ` spelling itself provides: backend data, never the entity. CEILING: free
ℚ-modules (`ℚⁿ → ℚ`, `ℚⁿ → ℚᵐ`), the span machinery's own base; the
fp-over-a-PID general case is CategoryGraph-era and nothing here pre-commits
against it. -/
def evalHomBinding (binders : Array Name) (body : CasExpr) (asc : Ascription)
    : EvalM Obj := do
  let .domain (.funcs src tgt) := asc
    | throw (.msg "a multi-binder `↦` definition is a hom of free ℚ-modules, \
and is ascribed its function domain: `let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c`")
  let .vector n .rat := src
    | throw (.msg s!"this slice reads a multi-binder map on a free ℚ-module \
ℚⁿ, and {src.render} is not one — the ceiling the span machinery has")
  if n != binders.size then
    throw (.msg s!"{src.render} has {n} coordinates, and this map binds \
{binders.size} names")
  if (binders.toList.eraseDups).length != binders.size then
    throw (.msg "the binders of a multi-binder map are distinct names")
  binders.forM fun b => ofStr (checkBindableName b)
  let comps ← match tgt, body with
    | .vector m .rat, .vecLit es =>
        if es.size != m then
          throw (.msg s!"{tgt.render} has {m} coordinates, and this body \
writes {es.size}")
        else pure es
    | .vector _ .rat, _ =>
        throw (.msg s!"a map into {tgt.render} writes its coordinates as a \
tuple, one linear form per coordinate")
    | .rat, e => pure #[e]
    | t, _ =>
        throw (.msg s!"this slice reads a multi-binder map into ℚ or ℚᵐ, and \
{t.render} is not one — the ceiling the span machinery has")
  let rows ← comps.mapM fun c => ofStr (linearRow binders c)
  return .elem (.funcs src tgt) (.hom src tgt binders rows)

/-- `let x := e [in T]`; a `↦` lambda on the right is a binder definition. -/
def evalBinding (ctx : EvalCtx) (e : CasExpr) (asc? : Option CasExpr) : EvalM Obj := do
  match e, asc? with
  | .lam binder body, some a =>
      evalBinderBinding ctx binder body (← evalAscription ctx a)
  | .lam binder _, none =>
      throw (.msg s!"`{binder} ↦ …` needs an ascription naming the domains it \
runs between, as in `let h := {binder} ↦ {binder}^2 + 1 in ℝ → ℝ`")
  | .lamN binders body, some a =>
      evalHomBinding binders body (← evalAscription ctx a)
  | .lamN _ _, none =>
      throw (.msg "a multi-binder `↦` definition needs the ascription naming \
its free modules, as in `let φ: ℚ³ → ℚ := (a, b, c) ↦ a + b - c`")
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

/-- The indeterminate a bound POLYNOMIAL brings into scope across an
assertion, under the name this slice RENDERS it with.

SPEC.md §Differentials writes `assert d(f) = (6x + 1) dx` and §Indefinite
integration writes `assert F(x) = x³ + (1/2)x² + x`, naming `x` on a side that
is not the polynomial. A `let f := x ↦ … in ℚ[x]` binding records no binder —
a `Value.poly` has none, its indeterminate is anonymous and prints as `x` —
so the name has to come from the RENDERING convention, and it does: this
slice spells that indeterminate `x` everywhere, which is also why `d/dx` is
its derivation and `d/dy` is a spelling of nothing.

Consulted after `calledBinder?` and after the session bindings, and scoped to
ONE assertion exactly as both of those are: a bare `x` elsewhere is still the
loud "not bound" error, and a real `let x := …` wins. Disclosed residue, the
same one `calledBinder?` carries: inside an assertion that mentions a
polynomial, a typo `x` reads as the indeterminate — and the outcome is then
an honest `unknown` or a false assertion, never a wrong answer. -/
partial def polyIndet? (env : Environment) : CasExpr → Option (Name × Domain)
  | .ref n =>
      match binding? env n with
      | some (.elem (.poly c) _) => some (`x, c)
      | _ => none
  | .app f args => polyIndet? env f <|> anyOf env args
  | .method r _ args => polyIndet? env r <|> anyOf env args
  | .bin _ a b => polyIndet? env a <|> polyIndet? env b
  | .neg a | .diffForm a | .integral a => polyIndet? env a
  | _ => none
where
  anyOf (env : Environment) (es : Array CasExpr) : Option (Name × Domain) :=
    es.foldl (init := none) fun acc e => acc <|> polyIndet? env e

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
  -- the indeterminate this assertion may name, in resolution order: a callee's
  -- own binder first, then the anonymous indeterminate a bound polynomial
  -- brings in under the name it renders with
  let indetHere :=
    calledBinder? ctx.env l <|> calledBinder? ctx.env r
      <|> polyIndet? ctx.env l <|> polyIndet? ctx.env r
  let ctx := { ctx with callBinder? := ctx.callBinder? <|> indetHere }
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
