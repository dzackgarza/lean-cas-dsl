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
  `Environment` and without `IO`. `eval` adds registry reads and executor
  calls, nothing else.
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
  | _ => none

/-- The preferred common domain of two presentations: `ℕ ⊆ ℤ ⊆ ℚ`, and the
same inclusion applied under `poly`/`matrix`. `none` = no canonical
embedding of either into the other. -/
partial def domJoin : Domain → Domain → Option Domain
  | .nat, .nat => some .nat
  | .nat, .int | .int, .nat | .int, .int => some .int
  | .nat, .rat | .rat, .nat | .int, .rat | .rat, .int | .rat, .rat => some .rat
  | .mod n, .mod m => if n == m then some (.mod n) else none
  | .poly a, .poly b => (domJoin a b).map .poly
  | .matrix n a, .matrix m b =>
      if n == m then (domJoin a b).map (Domain.matrix n) else none
  | _, _ => none

/-- The canonical embedding of a value into `d`, and the ONLY coercion the
surface performs. It is deliberately a small closed set — `ℤ ⊆ ℚ`, an
integer naming its residue class in `ℤ/n`, the coefficient- and
entry-wise images of those, and a scalar as a constant polynomial.

CEILING: the preferred embeddings are code-level. Registry-driven
embeddings (a `Functor`/`Embedding` registry the notebook could extend) are
the documented future extension; nothing here may be widened by adding a
"reasonable" conversion — a missing embedding is an honest error. -/
partial def coerceValue (d : Domain) (v : Value) : Except String Value :=
  match d, v with
  | .int, .int _ => .ok v
  | .nat, .int z =>
      if z ≥ 0 then .ok v
      else .error s!"{z} is not an element of ℕ"
  | .rat, .int z => .ok (.rat (Rat.ofInt z))
  | .rat, .rat _ => .ok v
  | .mod n, .int z => .ok (Value.mkMod n z)
  | .mod n, .mod m _ =>
      if n == m then .ok v
      else .error s!"ℤ/{m} and ℤ/{n} are different rings"
  | .poly c, .poly _ cs => do return Value.mkPoly c (← cs.mapM (coerceValue c))
  | .poly c, s => do return Value.mkPoly c #[← coerceValue c s]
  | .matrix n e, .mat m _ rows =>
      if n != m then
        .error s!"a {m}×{m} matrix is not an element of Mat{n}(…)"
      else do
        return .mat n e (← rows.mapM (·.mapM (coerceValue e)))
  | d, v => .error s!"there is no preferred embedding of {v.render} into {d.render}"

/-! ### Polynomial arithmetic

Coefficients ride on `Native`'s exact scalar operations (which already
promote along `ℤ ⊆ ℚ`); this layer only manages degrees and the resulting
coefficient domain. -/

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
operation into the polynomial ring over the joined coefficient domain;
otherwise this is `Native`'s exact scalar arithmetic. -/
def valueBin (op : BinOp) (a b : Value) : Except String Value := do
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
        return Value.mkPoly ca (← (← polyPow as k).mapM (coerceValue ca))
    | _ =>
        let some (ca, as) := asPolyCoeffs a
          | .error s!"{a.render} is not a polynomial"
        let some (cb, bs) := asPolyCoeffs b
          | .error s!"{b.render} is not a polynomial"
        let some d := domJoin ca cb
          | .error s!"{ca.render}[x] and {cb.render}[x] have no common coefficient domain"
        let cs ← match op with
          | .add => polyAdd as bs
          | .sub => polySub as bs
          | _ => polyMul as bs
        return Value.mkPoly d (← cs.mapM (coerceValue d))
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

/-! ### Set literals -/

/-- Element domain of a literal element list. -/
def elemsDomain (vs : Array Value) : Except String Domain :=
  vs.foldlM (init := Domain.int) fun d v =>
    match valueDom? v with
    | none => .error s!"{v.render} cannot be an element of a set literal"
    | some d' =>
        match domJoin d d' with
        | some j => .ok j
        | none => .error s!"{d.render} and {d'.render} have no common domain"

/-- Build the progression a `{a, b, …, ...}` literal denotes: the step is
inferred from the two leading elements (one leading element means step 1),
and EVERY leading element must lie on the inferred progression — a literal
that is not one is a mistake, not a set to guess at. -/
def progressionOf (leading : Array Value) (last? : Option Value)
    : Except String SetPresentation := do
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
  let d ← elemsDomain (leading ++ (last?.toArray))
  return .arithProg d (← coerceValue d first) (← coerceValue d step)
    (← last?.mapM (coerceValue d))

/-! ### `D[x]` versus `e[k]`

DESIGN.md: brackets containing a lone identifier that is not a binding name
denote a polynomial indeterminate; anything else is an index. The decision
needs only the "is this name bound?" predicate, so it stays pure. -/

def indeterminate? (isBound : Name → Bool) : CasExpr → Option Name
  | .ref n => if isBound n then none else some n
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

partial def renderDomainPattern : DomainPattern → String
  | .exact d => d.render
  | .polyOver p => s!"{renderDomainPattern p}[x]"
  | .matrixOver p => s!"Mat(_, {renderDomainPattern p})"
  | .anyDom => "_"

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
          return .obj (.elem (.poly c) (Value.mkPoly c #[← ofStr (coerceValue c (.int 0)),
            ← ofStr (coerceValue c (.int 1))]))
      match binding? ctx.env n with
      | some o => return .obj o
      | none => throw (.msg s!"'{n}' is not bound; introduce it with `let {n} := …`")
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
            (← ofStr (valueBin .div (← ofStr (asValueOf x)) (← ofStr (asValueOf y))))
  | .bin op a b => do
      let x ← ofStr (asValueOf (← eval ctx a))
      let y ← ofStr (asValueOf (← eval ctx b))
      return Denote.ofValue (← ofStr (valueBin op x y))
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
      | _ => throw (.msg s!"{fv.presentation} is not callable")
  | .finSet elems => do
      let vs ← elems.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let d ← ofStr (elemsDomain vs)
      return .obj (.setObj (.finite d (← ofStr (vs.mapM (coerceValue d)))))
  | .progSet leading last? => do
      let vs ← leading.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let l ← last?.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      return .obj (.setObj (← ofStr (progressionOf vs l)))
  | .matLit rows cols entries => do
      if rows != cols then
        throw (.msg s!"the slice presents square matrices only, got {rows}×{cols}")
      let vs ← entries.mapM fun e => do ofStr (asValueOf (← eval ctx e))
      let d ← ofStr (elemsDomain vs)
      let rs ← (Array.range rows).mapM fun i =>
        ofStr ((Array.range cols).mapM fun j => coerceValue d vs[i * cols + j]!)
      return .obj (.elem (.matrix rows d) (.mat rows d rs))
  | .mapTo e target => do
      let t ← eval ctx target
      let .obj (.domainObj d) := t
        | throw (.msg s!"`map … to` needs a domain, got {t.presentation}")
      let v ← ofStr (asValueOf (← eval ctx e))
      return .obj (.elem d (← ofStr (coerceValue d v)))
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
ascription must admit the preferred embedding, and a category ascription
must actually hold in the object's profile.

CEILING: the only ascription-directed reinterpretation is `ℤ/n` read as the
cyclic ℤ-module when the ascribed category is a module category. Making
reinterpretation registry-driven is the documented generalization. -/
def ascribe (ctx : EvalCtx) (o : Obj) : Ascription → EvalM Obj
  | .domain d => do
      match o with
      | .elem _ v => return .elem d (← ofStr (coerceValue d v))
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

/-- `let x := e [in T]`. -/
def evalBinding (ctx : EvalCtx) (e : CasExpr) (asc? : Option CasExpr) : EvalM Obj := do
  match asc? with
  | none => objOf (← eval ctx e)
  | some a =>
      let asc ← evalAscription ctx a
      ascribe ctx (← objOf (← eval ctx e)) asc

/-- `let p(x) := e in D[x]`. The ascription is evaluated FIRST: it supplies
the coefficient domain the indeterminate is read in. -/
def evalPolyBinding (ctx : EvalCtx) (x : Name) (e : CasExpr) (asc : CasExpr)
    : EvalM Obj := do
  let a ← evalAscription ctx asc
  let .domain (.poly c) := a
    | throw (.msg "a `let p(x) := …` binding must be ascribed to a polynomial \
domain such as ℤ[x]")
  let o ← objOf (← eval { ctx with indet? := some (x, c) } e)
  ascribe ctx o (.domain (.poly c))

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
      if isSetLike a || isSetLike b then
        let res ← boolOf (← callMethod ctx (← objOf a) `set_eq #[← objOf b])
        return some (neg != res)
      else
        let some va := a.value?
          | throw (.msg s!"{a.render} is not comparable")
        let some vb := b.value?
          | throw (.msg s!"{b.render} is not comparable")
        return (Native.valueEq va vb).map (neg != ·)

end CasDsl
