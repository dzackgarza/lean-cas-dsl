# CasDsl — design of the vertical slice

A categorically organized CAS hosted in Lean, shipped as a DSL plugin for
[lean-jupyter-kernel](https://github.com/dzackgarza/lean-jupyter-kernel).
Governing plans live in the project vault
(`FEATURE-LEAN-CAS-DSL`, `SPEC-CATEGORICAL-CAS-PROBLEM`,
`PLAN-CAS-TYPE-PREPASS`, `PLAN-CAS-VERTICAL-SLICE`,
`DECISION-CAS-DSL-ANTI-DRIFT`). This file is the implementation-facing
contract: the module map, the core data model, and the decisions every
module must respect.

## The invariant pipeline

```text
surface expression                     (backend-blind mathematical syntax)
  -> object + category profile         (rich memberships, not one nominal class)
  -> method resolution                 (direct + subcategory-inherited, ONE boundary)
  -> backend-neutral request           (method id + typed presentation)
  -> capability router                 (developer policy; deterministic)
  -> executor                          (native Lean, or a direct backend adapter)
  -> trusted typed Value               (ordinary CAS trust; no proof obligation)
  -> notebook state                    (env-extension bindings; snapshot/replay safe)
```

Two judgments are always kept separate:

- **semantic availability** — the category graph says the method is
  meaningful for this object;
- **implementation availability** — a registered route can currently
  execute it for this presentation.

A missing route is a structured `NoImplementation` gap surfaced at
execution. It never removes the method, narrows a category, weakens a type,
or picks a different operation.

## Module map

```text
CasDsl/Value.lean       Domain, Value, SetPresentation, Obj  (core data model)
CasDsl/Category.lean    CatRef, category/method/route/binding registry TYPES
CasDsl/Registry.lean    env extensions + registration API (semantic state)
CasDsl/Resolve.lean     the method resolver (the ONE lookup boundary)
CasDsl/Route.lean       capability router + structured gaps
CasDsl/Native.lean      native Lean executors (arith, poly eval, nth, annihilator)
CasDsl/Port.lean        generic framed child-process port (no Sage branches)
CasDsl/Backends/Sage.lean  direct Sage adapter (Lean side)
CasDsl/Eval.lean        casTerm evaluator: resolve -> route -> execute
CasDsl/Syntax.lean      surface syntax: commands + casTerm category
CasDsl/Diagnostics.lean #explain_route, #capabilities, #capability_gaps
CasDsl/Std.lean         standard universe: categories, methods, routes, profiles
CasDsl/Notebook.lean    the prelude module (the plugin manifest)
backends/sage_adapter.py   Python half of the Sage adapter (runs under sage -python)
tests/                  Lean #guard test module + Python roundtrip + E2E notebook run
```

Dependency arrows flow downward only. `Port.lean` knows nothing about Sage
operations; `Backends/Sage.lean` knows nothing about surface syntax.

## Core data model (`Value.lean`)

Presentations and values are first-order, serializable data (they live in
env extensions, so no closures):

```lean
inductive Domain
  | nat | int | rat
  | mod (n : Nat)                  -- ℤ/n
  | poly (coeff : Domain)          -- coeff[x], univariate
  | matrix (n : Nat) (entry : Domain)   -- Matₙ(entry), square in the slice

inductive Value
  | int (z : Int)                  -- also ℕ elements
  | rat (q : Rat)
  | mod (n : Nat) (v : Nat)        -- normalized v < n on construction
  | poly (coeff : Domain) (coeffs : Array Value)   -- ascending, no trailing zeros
  | mat (n : Nat) (entry : Domain) (rows : Array (Array Value))
  | factorization (unit : Value) (factors : Array (Value × Nat)) (dom : Domain)
  | idealV (gens : Array Value) (ring : Domain)    -- e.g. annihilator result
  | cardinal (c : Cardinality)     -- finite n | countablyInfinite
  | bool (b : Bool)

inductive SetPresentation
  | finite (dom : Domain) (elems : Array Value)
  | arithProg (dom : Domain) (first step : Value) (last? : Option Value)
  | domainSet (d : Domain)         -- the underlying set of ℤ, ℕ, ℚ, …

inductive Obj                       -- the thing a notebook binding names
  | elem (dom : Domain) (v : Value)         -- 360 ∈ ℤ, q ∈ ℚ[x], M ∈ Mat₂(ℚ)
  | domainObj (d : Domain)                  -- ℤ itself (a set-with-structure)
  | setObj (s : SetPresentation)            -- {0, 2, 4, ...}
  | cyclicModule (n : Nat)                  -- the ℤ-module ℤ/n (module fixture)
```

Set equality (`X = ℕ`) is presentation normalization: `arithProg 0 1 none`
over ℕ normalizes to `domainSet nat`, etc. This is a documented ceiling,
not a general decision procedure.

## Categories (`Category.lean`, `Registry.lean`)

```lean
inductive ParamVal | dom (d : Domain) | nat (n : Nat)

structure CatRef where
  name   : Name              -- inheritance graph node
  params : Array ParamVal    -- instantiation data, preserved along edges
```

- The **inheritance graph** is on category *names*: a `CatDecl` registers
  `parents : Array Name`; params pass through unchanged along an edge
  (`SmallModules(ℤ) ≤ Modules(ℤ)` because `SmallModules ≤ Modules`).
- An object's **profile** is the set of `CatRef`s it directly inhabits
  (computed by `Std.profileOf : Obj → Array CatRef`); the resolver closes
  over parent edges. Profiles are rich: `ℤ` enters with sets, countable
  sets, commutative rings, euclidean domains, … — never one weakest class.
- **Method declarations** are category-owned:

```lean
structure MethodDecl where
  id        : Name           -- stable mathematical identity, e.g. `factor
  receiver  : Name           -- receiver category NAME (any params)
  argDoc    : String         -- slice keeps arg validation at execution
  resultDoc : String
  doc       : String
```

  No method declaration names a backend, algorithm, or capability limit.

- **Routes** live in a *separate* registry (the computability layer):

```lean
structure Route where
  method   : Name
  pattern  : PresPattern     -- first-order matcher on the receiver Obj
  backend  : Name            -- `native or `sage (executor looked up by name)
  opId     : String          -- backend operation identity
  priority : Nat             -- deterministic tie-break: highest wins, tie = error
```

- **Bindings** (`let` results) are an env-extension map `Name → Obj`.
  All four registries are `SimplePersistentEnvExtension`s: cell atomicity,
  restart replay, and the olean session cache come for free from the
  plugin state law. No semantic state in `IO.Ref`s, ever.

## The resolver (`Resolve.lean`) — the one boundary

```lean
structure Resolution where
  decl : MethodDecl
  declaredOn : CatRef        -- instantiated receiver category
  via  : List Name           -- inheritance chain from a profile entry (possibly [])

resolveMethod (env : Environment) (profile : Array CatRef) (m : Name)
    : Except ResolveError Resolution
```

Round one: direct lookup on profile entries, then upward closure through
registered parent edges (BFS, deduplicating diamond paths). Two *distinct*
applicable declarations from incomparable categories = `ambiguous` error.
Method not declared on any reachable category = `notApplicable`, and the
error names the categories where the method IS declared.

**Future seam**: functorial transport will extend exactly this function
with receiver transformation along preferred functors. Nothing else — no
call site, no method declaration, no backend contract — may assume the
resolver only does direct/inherited lookup. No functor registry, path
search, or result lifting is implemented in this slice.

## Routing and gaps (`Route.lean`)

`routeFor` filters routes by method id + pattern match on the concrete
receiver, then selects deterministically by priority. Failure produces the
structured gap the plans demand:

```lean
structure CapabilityGap where
  method : Name
  receiverCategory : CatRef
  presentation : String        -- rendered Obj presentation
  semanticVia : List Name      -- how the method was semantically available
  routesConsidered : Array Route
```

Gap rendering is a first-class output (text + JSON MIME), an auditable
developer backlog item — never a parse/type/category error.

## The port (`Port.lean`) and the Sage adapter

Generic framed child-process port, mirroring the worker's discipline:

- frame = ASCII byte length, `\n`, UTF-8 JSON, over the child's
  stdin/stdout (stderr is a log stream, never framed);
- on start the adapter emits
  `{"op":"ready","protocol":1,"backend":"sage","backend_version":…,
  "adapter_version":…,"capabilities":[opIds]}`;
- requests carry `request_id`; replies echo it;
  unknown op → `{"status":"unsupported"}`;
- the connection handle is a non-semantic process cache in an `IO.Ref`
  (like the worker's output sink: wiring, not state). Replays re-execute
  backend calls.

Typed values on the wire (bignums as strings):
`{"t":"int","v":"360"}`, `{"t":"rat","num":"1","den":"2"}`,
`{"t":"poly","coeffs":[rat…]}`, `{"t":"mat","rows":[[rat…]…]}`,
`{"t":"factorization","unit":…,"factors":[[value,mult]…]}`.

First Sage ops: `factor_int`, `factor_poly_q`, `mat_det_q`, `mat_inv_q`.
The adapter (`backends/sage_adapter.py`) runs under `sage -python`, builds
native Sage parents/elements from the typed request, and returns trusted
typed results with provenance versions. It never receives generated Sage
source and never proxies another CAS. Adapter discovery: env
`CASDSL_SAGE` (default `sage`) and `CASDSL_ADAPTER` (default
`backends/sage_adapter.py` relative to the worker cwd = the project dir).

## Surface (`Syntax.lean`)

Backend-blind; a `casTerm` syntax category plus commands:

```text
let n := 360 in ℤ                         -- binding with domain ascription
let p(x) := x^3 - 2x + 1 in ℤ[x]          -- univariate polynomial binding
let q := map p to ℚ[x]                    -- explicit coercion along ℤ ⊆ ℚ
let X := {0, 1, 2, ...}                   -- progression set literals
let M := [1, 2; 3, 4] in Mat₂(ℚ)          -- matrix literal
n.factor()   M.det()   M.inverse()  F.annihilator()   X.cardinality()
q(1)                                      -- polynomial call coercion
ℤ[3]                                      -- nth element (numeral ⇒ index)
assert 2 + 3 = 5      assert 2 + 3 = 0 in ℤ/5
assert 8 ∈ Y          assert 9 ∉ Y        assert X = ℕ
#explain_route <expr>   #capabilities   #capability_gaps
```

Parser decisions (load-bearing):

- brackets after a domain: `D[ident]` is a polynomial ring in that
  indeterminate; `D[numeral/expr]` is nth-element indexing (matches the
  plans' `ℤ[3]`; ring adjunction `ℤ[√2]` is out of scope — ceiling).
- implicit multiplication is supported only as `numeral ident` (`2x`);
- a bare `casTerm` cell displays its value (our own command production, low
  priority so genuine Lean commands still parse);
- `assert` outcomes are fourfold — `true | false | unknown | error` — only
  `true` commits the cell; false/unknown/error give distinct diagnostics.
  `assert` is a trusted computational assertion, never a Lean theorem.

Ellipses implement exactly the Haskell-style progressions
`{a, ...} {a, b, ...} {a, ..., z} {a, b, ..., z}`; nothing more.

## Standard universe (`Std.lean`)

Category graph (names; `≤` = registered parent edge):

```text
FiniteSets ≤ CountableSets ≤ Sets
EuclideanElems ≤ FactorizationElems ≤ CommRingElems
SmallModules ≤ Modules            (the plan's inheritance demo)
MatrixElems                       (dets/inverses; params (n, entry))
```

Profiles (selected): `ℤ` (domainObj) ∈ {Sets, CountableSets, …};
`n ∈ ℤ` (elem) ∈ {EuclideanElems(ℤ)}; `q ∈ ℚ[x]` ∈ {EuclideanElems(ℚ[x])};
`M ∈ Mat₂(ℚ)` ∈ {MatrixElems(2, ℚ)}; `cyclicModule n` ∈ {SmallModules(ℤ)}.

Methods: `factor` on FactorizationElems; `det`, `inverse` on MatrixElems;
`annihilator` on Modules; `nth`, `cardinality`, `contains` on the set
hierarchy. Inheritance is exercised twice for real: `factor` reaches
integers via `EuclideanElems ≤ FactorizationElems`, and `annihilator`
reaches the fixture via `SmallModules ≤ Modules` with **no forwarding
declaration**.

Deliberate capability gaps shipped in the slice (honest, auditable):
`ℚ` is countable — `nth` is semantically available — but no enumeration
route is registered, so `ℚ[3]` fails with a structured gap. Same for
`factor` on `ℤ/6` elements (declared, no route).

## Decisions inherited from the anti-drift record (binding)

1. Ordinary syntax is backend-blind; no `using Sage`, ever.
2. Sage is reached by a direct adapter and brokers nothing else.
3. Methods are category-owned; subcategory inheritance is the only
   non-direct transport in round one; the resolver is the future seam.
4. Capability gaps never flow upward into semantics; no
   implementation-shaped categories (no `EnumerableCountableSet`).
5. Results are trusted CAS values: no certificates, no theorem generation,
   no recomputation, no proof obligations on ordinary computation.
6. Mathematician-facing coercions (polynomial call, `ℤ ⊆ ℚ`) are inserted
   by elaboration; internal distinctions stay internal.
7. Backend owns factorization order/unit convention; we keep only the
   neutral result shape.
8. Eager reflection of small values is a slice choice, not a permanent
   semantic requirement (future: typed computation descriptions + caches).

## Open questions (kept open — do not silently resolve)

- user-defined categories in the notebook (slice: prelude-registered only);
- default enumeration convention for `ℤ` (slice: 0, 1, −1, 2, −2, …,
  zero-based — a *registered choice*, revisitable);
- backend provenance in normal output (slice: diagnostics only);
- retry/migration policy for failed long computations (slice: fail loudly,
  no retry);
- which backend follows Sage.

## Ceilings (deliberate, documented)

- set equality by presentation normalization only;
- argument validation at execution, not declaration;
- no backend-call cancellation beyond process teardown with the kernel;
- `#capability_gaps` crosses declared methods with registered
  representative presentations (not all conceivable objects);
- sandbox mode: Sage is unavailable inside bubblewrap — its routes surface
  as capability gaps there, which is exactly the honest behavior.
