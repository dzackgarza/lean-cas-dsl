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
CasDsl/Category.lean    CatRef, category/method/functor/route/canonical-map TYPES
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

- **Functors** are the transport layer, and are registry data too:

```lean
structure FunctorDecl where
  name   : Name
  source : Name              -- category NAME, never a backend
  target : Name
  objMap : ObjMap            -- first-order object map (no closures)
  doc    : String
```

- **Preferred canonical maps** are the coercion layer, and registry data too:

```lean
structure CanonicalMap where
  src : DomainPattern           -- patterns on BOTH sides, so ℤ → ℤ/n is ONE rule
  tgt : DomainPattern
  op  : CanonOp                 -- first-order value transform (no closures)
  doc : String
```

- **Bindings** (`let` results) are an env-extension map `Name → Obj`.
  Every registry is a `SimplePersistentEnvExtension`: cell atomicity,
  restart replay, and the olean session cache come for free from the
  plugin state law. No semantic state in `IO.Ref`s, ever.

## The resolver (`Resolve.lean`) — the one boundary

```lean
structure Resolution where
  decl : MethodDecl
  profileEntry : CatRef      -- instantiated receiver category
  via  : List Name           -- inheritance chain from a profile entry (possibly [])
  viaFunctor : Option FunctorStep   -- set when the RECEIVER was transported

resolveMethod (env : Environment) (o : Obj) (m : Name)
    : Except ResolveError Resolution
```

**Round one — method transport along inclusions.** Direct lookup on profile
entries, then upward closure through registered parent edges (BFS,
deduplicating diamond paths). Two *distinct* applicable declarations from
incomparable categories = `ambiguous` error. Method not declared on any
reachable category = `notApplicable`, and the error names the categories
where the method IS declared.

**Round two — receiver transport along functors.** `X.m()` where `m` is
declared on `D` and a registered `F : C → D` applies to `X` resolves as
`F(X).m()`, recorded in `viaFunctor`. Rules, all load-bearing:

- round one runs first and wins unconditionally, so registering a functor
  can never take a method away from an object that already had it;
- only `notApplicable` opens round two; a functor applies when the
  receiver's profile reaches its `source` and its object map is defined on
  the presentation;
- the image's profile must reach the functor's declared `target`, or the
  REGISTRATION is defective: `functorTargetMismatch`, and resolution stops
  rather than working around it;
- exactly one transported candidate resolves; several competing functors are
  the ordinary `ambiguous` error carrying all of them (never an order
  heuristic), and none leaves the original `notApplicable` unchanged.

Every caller routes and executes against `res.concreteReceiver o` — the
transported image, not the object it passed in. Nothing else — no method
declaration, no backend contract — may assume the resolver does only
direct/inherited lookup.

Ceilings of round two (deliberate): **one hop** (the image is resolved by
round one only — no functor composition, no path search, no preferred-path
registry); **no result lifting** (the image's result is the answer; no
shipped transported method needs a value carried back along `F`); and the
`ObjMap` ceiling — an object map that is not expressible adds a constructor,
exactly as `DomainPattern` does.

## Coercions (`Eval.lean` + the canonical-map registry)

`map e to D` means: **apply the preferred canonical map into `D` when one
exists, and fail otherwise** (design review 2026-07-30). Canonical maps are
preferred choices, not necessarily injections — a monomorphism in some
category (`ℤ ⊆ ℚ`), a universal-property-supplied map (the quotient
`ℤ → ℤ/n`; cokernels, when they arrive), and, behind this same lookup, a
later round may let transport along a preferred functor supply one.

Every coercion the surface inserts — `map e to D`, a mixed-domain join, the
element promotion of a set or matrix literal, a domain ascription — goes
through `coerceValue`/`domJoin`, and the BASE CASE (one scalar domain into
another) is decided by the registered `CanonicalMap`s. The prelude registers
`ℕ ⊆ ℤ`, `ℕ ⊆ ℚ`, `ℤ ⊆ ℚ` and the quotient `ℤ → ℤ/n`; `ℤ ⊆ ℚ` in the
surface is sugar for the registered map (decision 6). No engine module knows
those particular facts: unregister a rule and the corresponding `map` stops
working, with the honest "there is no preferred canonical map of … into …"
error.

Exactly one applicable rule coerces. Zero is that honest error. MORE than one
— or two rules mapping two domains into each other, which leaves a join
with no preferred answer — is a defective registration, reported loudly with
both rules named. A coercion is never chosen by registration order, array
position, or invented specificity: the same discipline as the resolver's
`ambiguous` and the router's tied routes.

Four cases stay ENGINE-LEVEL because they are not canonical injections
between two domains and so cannot be registry data:

- **structural congruence** under `poly`/`matrix`, plus a scalar as a constant
  polynomial: a canonical map of coefficient/entry domains *induces* the one on
  polynomials and matrices, so a registered `ℤ[x] → ℚ[x]` would be a second
  place to state `ℤ ⊆ ℚ`. The recursion bottoms out in the registry;
- **identity**, when the value already presents the target domain;
- **`ℕ ← ℤ`**, a partial CHECK (a membership judgment, "is this integer in
  ℕ?"), not an injection — a registry of canonical injections must not be
  able to state it;
- **`ℤ/m` vs `ℤ/n`**, where the fact reported is the ABSENCE of a canonical
  map between different rings.

Two neighbouring mechanisms are deliberately NOT canonical maps. `Native.lean`'s
internal scalar promotion (`toRat?`/`promote` inside the executors) is the
trusted computation layer's own implementation detail — the analogue of
Sage's internal coercions — and stays code-level: it decides how an executor
computes `1 + 1/2`, never which domains the surface may move a value between.
And reading a literal in an ambient domain (`assert 2 + 3 = 0 in ℤ/5`) is
literal interpretation, not a map applied to an existing value.

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

**Op signatures (design review 2026-07-30).** The DSL surface can never
produce a wrong-shaped call — but the agreement between a route's pattern
("which objects") and its op ("which implementation") used to be a
convention, caught only by defensive arms in the executors. It is now a
checked invariant: each backend registers, per `opId`, the receiver
patterns that op accepts (`OpSig`, ordinary registry data declared by the
backend's own Lean half next to its encoders), and `addRouteChecked`
rejects any route naming an undeclared op or carrying a pattern the op's
signature does not accept (`PresPattern.implies`, the syntactic subsumption
order). A mismatched or typo'd route therefore fails `lake build`. The
executors' residual shape arms collapse to one shared diagnostic that can
only fire if a signature *declaration* misstates its encoder. Shapes only:
partiality within an accepted shape (out-of-range index, no membership
test for a domain) stays a loud runtime error.

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
- **equality is category-bound** (design review 2026-07-30): bare `=` never
  inserts a functor, so equality between objects of different categories is
  TRIVIALLY FALSE — `F = {0, 1, 2, 3}` is false for the module fixture even
  though `U(F)` *is* that set, because there is no unique module structure
  on it. Comparing across categories requires explicitly moving into a
  common comparison category: `F.set_eq({0, 1, 2, 3})` is the Sets question
  (its receiver transports, exactly like `∈`), and it is true.

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

One functor ships: `UnderlyingSet : Modules → Sets` (object map: the
ℤ-module ℤ/n to the finite set of its residues). It is what makes
`F.cardinality()` work on the module fixture — a method declared on `Sets`,
which the module does not inhabit, reached by transporting the receiver and
routed against the image. `annihilator` on the same object still resolves
directly through the inclusion edge, untransported; both claims are asserted
in `acceptanceProofs`.

The deliberate capability gap shipped by the universe (honest, auditable):
`det`/`inverse` on matrices whose entry domain is not ℚ — `det` is
meaningful on any `MatrixElems` member, only ℚ-entry matrices are routed,
and `Mat₂(ℤ/5).det()` is the notebook's fails-on-purpose demo. (The
original gaps — `nth` on ℚ and `factor` on ℤ[x] — were routed in round
three per the user-decided closure paths, #17/#18; the ℚ enumeration is
the registered Cantor zigzag, revisitable like ℤ's convention.)

## Decisions inherited from the anti-drift record (binding)

1. Ordinary syntax is backend-blind; no `using Sage`, ever.
2. Sage is reached by a direct adapter and brokers nothing else.
3. Methods are category-owned. Non-direct availability comes from exactly
   two registered mechanisms, both behind the resolver: subcategory
   inclusion (method transport) and preferred functors (receiver
   transport). Neither is ever a forwarding declaration on a leaf.
4. Capability gaps never flow upward into semantics; no
   implementation-shaped categories (no `EnumerableCountableSet`).
5. Results are trusted CAS values: no certificates, no theorem generation,
   no recomputation, no proof obligations on ordinary computation.
6. Mathematician-facing coercions (polynomial call, `ℤ ⊆ ℚ`) are inserted
   by elaboration; internal distinctions stay internal. `ℤ ⊆ ℚ` denotes the
   REGISTERED preferred structure-preserving map, not a code-level
   conversion, and an unregistered pair of domains has no coercion at all —
   it is never widened to a "reasonable" one.
7. Backend owns factorization order/unit convention; we keep only the
   neutral result shape.
8. Eager reflection of small values is a slice choice, not a permanent
   semantic requirement (future: typed computation descriptions + caches).

## Decided by user review, 2026-07-30 (vault: DECISION-CAS-ROUND2-REVIEW)

Formerly open questions, now user-decided — none was silently resolved:

- **user-defined categories**: the declaration surface SHIPS (issue #6);
  the concrete syntax returns as a proposal for review first;
- **backend provenance**: never default output — an opt-in `info`-level
  logging layer with per-line/per-cell verbosity directives (issue #8);
  results themselves become LaTeX-first with plain-text fallback (#16);
- **retry/migration policy**: ADOPTED — no automatic retry or migration,
  ever. Backend failure is a structured report; re-running a cell is the
  user's explicit act and re-routes from scratch. Revisit only when
  long-running computations exist (#4, deferred until a workload hurts);
- **which backend follows Sage**: GAP, direct adapter, justified by
  `unit_group` on ℤ/n (issue #3);
- **enumeration of ℚ**: Cantor zigzag (reduced-fraction skipping), a
  registered revisitable choice like ℤ's; implementing it must also
  replace the notebook's fails-on-purpose `ℚ[3]` demo (issue #17);
- **`factor` on ℤ[x]**: routed via Sage, content × primitive (#18) — the
  `map p to ℚ[x]` demo stays, reframed as the canonical-map demo;
- **route/op agreement**: checked at build time via registered op
  signatures, not left to runtime defensive arms (see §Routing and gaps).

## Open questions (kept open — do not silently resolve)

- default enumeration convention for `ℤ` (slice: 0, 1, −1, 2, −2, …,
  zero-based — a *registered choice*, revisitable);
- the concrete declaration syntax for notebook-level categories (proposal
  owed under issue #6);
- the logging layer's level surface and directive syntax (#8);
- which methods beyond `unit_group` the GAP bridge routes first (#3).

## Ceilings (deliberate, documented)

- set equality by presentation normalization only;
- argument validation at execution, not declaration;
- receiver transport is ONE hop, with no result lifting and no
  preferred-path registry; an object map that is not one of `ObjMap`'s
  constructors is not registrable;
- a canonical map whose value transform is not one of `CanonOp`'s constructors
  is not registrable either (the `ObjMap`/`DomainPattern` ceiling again: a
  new transform is a visible edit to the engine's vocabulary, never a closure
  in the environment);
- a coercion applies ONE rule: rules do not compose, which is why `ℕ ⊆ ℚ` is
  registered explicitly next to `ℕ ⊆ ℤ` and `ℤ ⊆ ℚ`;
- no backend-call cancellation beyond process teardown with the kernel;
- `#capability_gaps` crosses declared methods with registered
  representative presentations (not all conceivable objects);
- sandbox mode: Sage is unavailable inside bubblewrap — its routes surface
  as capability gaps there, which is exactly the honest behavior.
