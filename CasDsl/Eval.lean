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

inductive CasExpr where
  | num (z : Int)
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
  | mapTo (e target : CasExpr)
  /-- `binder ↦ body` — a function definition, meaningful only where an
  ascription says which domains it runs between (`evalBinderBinding`). -/
  | lam (binder : Name) (body : CasExpr)
  /-- `S → T` / `S -> T` — a function domain. -/
  | arrow (src tgt : CasExpr)
  /-- `f ∘ g`. -/
  | comp (f g : CasExpr)
  deriving Inhabited

/-! ## Pure core -/

/-- The presented domain of a value, when it has one. Cardinals, truth
values, ideals and factorizations are results, not elements of a presented
domain — they are carried as `Denote.val` rather than given a fake one. -/
def valueDom? : Value → Option Domain
  | .int _ => some .int
  | .rat _ => some .rat
  | .mod n _ => some (.mod n)
  | .poly c _ => some (.poly c)
  | .mat n e _ => some (.matrix n e)
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

/-- Mathematician-facing rendering of a pattern. Defined here because the
canonical-map-registry defect messages name the two rules that clashed; the
diagnostics below share it. -/
partial def renderDomainPattern : DomainPattern → String
  | .exact d => d.render
  | .polyOver p => s!"{renderDomainPattern p}[x]"
  | .matrixOver p => s!"Mat(_, {renderDomainPattern p})"
  | .anyMod => "ℤ/_"
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
          let some src := valueDom? v | noEmbedding
          match ← canonicalMapFor rules src d with
          | some r => r.op.apply d v
          | none => noEmbedding

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
    | .error s!"{body.render} is not a polynomial body"
  cs.reverse.foldlM (init := Value.int 0) fun acc c => do
    valueBin rules .add (← valueBin rules .mul acc arg) c

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
    | none => .error s!"{v.render} cannot be an element of a set literal"
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

/-! ### `D[x]` versus `e[k]`

DESIGN.md: brackets containing a lone identifier that is not a binding name
denote a polynomial indeterminate; anything else is an index. The decision
needs only the "is this name bound?" predicate, so it stays pure. -/

def indeterminate? (isBound : Name → Bool) : CasExpr → Option Name
  | .ref n => if isBound n then none else some n
  | _ => none

/-- The domains SPEC.md spells as ordinary identifiers rather than as their
own token: `R` and `RR` are ℝ (`let f(t) = t^2 in RR->RR`). Consulted only
after the bindings, so `let R := …` still shadows the alias — an alias is a
spelling, not a reserved word. -/
def domainAlias? : Name → Option Domain
  | `R | `RR => some .real
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

def value? : Denote → Option Value
  | .val v => some v
  | .obj (.elem _ v) => some v
  | .obj _ => none

def obj? : Denote → Option Obj
  | .obj o => some o
  | .val v => (valueDom? v).map fun d => Obj.elem d v

/-- Wrap an executor result: it becomes an object when it presents one. -/
def ofValue (v : Value) : Denote :=
  match valueDom? v with
  | some d => .obj (.elem d v)
  | none => .val v

end Denote

inductive EvalError where
  | msg (m : String)
  | resolve (m : Name) (recv : Obj) (e : ResolveError)
  | gap (g : CapabilityGap)
  | tiedRoutes (m : Name) (rs : Array Route)
  | exec (e : ExecError)
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

/-- A literal read in the ambient domain. -/
def EvalCtx.literal (ctx : EvalCtx) (z : Int) : Value :=
  match ctx.ambient? with
  | some .rat => .rat (Rat.ofInt z)
  | some (.mod n) => Value.mkMod n z
  | _ => .int z

/-- Execute a method: resolve (semantics), route (computability), execute.
The ONLY path from the surface to an implementation.

Routing and execution use `res.concreteReceiver`, so a resolution that went
through a functor runs against the transported image. Arguments are NOT
transported: a method's arguments belong to its declaration, not to the
receiver's presentation. -/
def callMethod (ctx : EvalCtx) (recv : Obj) (m : Name) (args : Array Obj)
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

partial def eval (ctx : EvalCtx) : CasExpr → EvalM Denote
  | .num z => return .obj (.elem (ctx.ambient?.getD .int) (ctx.literal z))
  | .dom d => return .obj (.domainObj d)
  | .ref n => do
      if let some (x, c) := ctx.indet? then
        if x == n then
          return .obj (.elem (.poly c) (← ofStr (indeterminateValue ctx.canonMaps c)))
      match binding? ctx.env n with
      | some o => return .obj o
      | none =>
        if let some d := domainAlias? n then
          return .obj (.domainObj d)
        -- A bound function's binder names the indeterminate of the ring its
        -- body lives in, so SPEC.md may write `h(-t) = h(t)` and
        -- `(f ∘ g)(t) = t⁶` without ever binding `t`. A name no function in
        -- scope binds is still the loud "not bound" error: this reading is
        -- earned by a definition, never assumed for an unknown identifier.
        if (bindings ctx.env).any (fun (_, o) => o.funcBinder? == some n) then
          return .obj (.elem (.poly .int)
            (← ofStr (indeterminateValue ctx.canonMaps .int)))
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
  | .bin op a b => do
      let x ← ofStr (asValueOf (← eval ctx a))
      let y ← ofStr (asValueOf (← eval ctx b))
      return Denote.ofValue (← ofStr (valueBin ctx.canonMaps op x y))
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
  | .app f args => do
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
      | some (.func _ _ _ body) =>
          -- Calling a function substitutes into its body: a scalar argument
          -- evaluates it, a polynomial argument composes with it. Same
          -- elaboration-inserted move as calling a polynomial — no route, no
          -- backend (DESIGN.md decision 6).
          if args.size != 1 then
            throw (.msg s!"a function is called with exactly one argument, got {args.size}")
          let x ← ofStr (asValueOf (← eval ctx args[0]!))
          return Denote.ofValue (← ofStr (applyPoly ctx.canonMaps body x))
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
  | .mapTo e target => do
      let t ← eval ctx target
      let .obj (.domainObj d) := t
        | throw (.msg s!"`map … to` needs a domain, got {t.presentation}")
      let v ← ofStr (asValueOf (← eval ctx e))
      return .obj (.elem d (← ofStr (coerceValue ctx.canonMaps d v)))
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
where
  asValueOf (r : Denote) : Except String Value :=
    match r.value? with
    | some v => .ok v
    | none => .error s!"{r.presentation} is not an element value"
  asObjOf (r : Denote) : Except String Obj :=
    match r.obj? with
    | some o => .ok o
    | none => .error s!"{r.render} is not an object"

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
      | other => throw (.msg s!"{other.presentation} is neither a domain nor a \
registered category")

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

/-! ## The three notebook judgments -/

private def objOf (d : Denote) : EvalM Obj :=
  match d.obj? with
  | some o => pure o
  | none => throw (.msg s!"{d.render} is not an object")

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
  | eq | ne | mem | notMem
  deriving BEq, Inhabited

def AssertRel.render : AssertRel → String
  | .eq => "=" | .ne => "≠" | .mem => "∈" | .notMem => "∉"

private def boolOf (d : Denote) : EvalM Bool :=
  match d.value? with
  | some (.bool b) => pure b
  | _ => throw (.msg s!"{d.render} is not a truth value")

private def isSetLike : Denote → Bool
  | .obj (.setObj _) | .obj (.domainObj _) => true
  | _ => false

/-- `assert l R r`, with the fourfold CAS outcome: `some true`, `some
false`, `none` (the operands are not comparable — the honest "unknown"), or
a thrown structured error. No proposition is created: this is a computed,
trusted predicate, not a Lean theorem. -/
def evalAssert (ctx : EvalCtx) (rel : AssertRel) (l r : CasExpr)
    : EvalM (Option Bool) := do
  let a ← eval ctx l
  let b ← eval ctx r
  match rel with
  | .mem | .notMem =>
      let res ← boolOf (← callMethod ctx (← objOf b) `contains #[← objOf a])
      return some (if rel == .mem then res else !res)
  | _ =>
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
