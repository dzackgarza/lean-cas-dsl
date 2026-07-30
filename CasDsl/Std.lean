/-
The standard universe: the category graph, the method catalogue, the
profile rules, the capability routes and the audit representatives that the
prelude ships (DESIGN.md §Standard universe).

Everything here is REGISTRATION DATA — literal arrays, handed to the
checked adders by the `run_cmd` lines at the end of each section. There is
no engine code in this module: a new category, presentation family, method
or backend route is added by registering more data, never by editing the
resolver or the router. A clash fails `lake build`.

Two load-bearing separations are visible in the layout below:

- methods are declared on the category where the mathematics first makes
  sense (`factor` on FactorizationElems, `annihilator` on Modules) and
  reach objects only by membership + registered inclusion edges — there is
  no forwarding declaration anywhere in this file;
- routes are a separate section, the only place naming a backend; deleting
  every route in it would remove no method from any object, only the
  ability to run them.

The universe ships one DELIBERATE capability gap (semantically available,
no route): `nth` on ℚ. It is an honest backlog item and is asserted as
such by the proofs at the end of this file. (`factor` on ℤ[x] elements was
the second such gap until round three routed it, #18.) Repairing a gap by
narrowing a category, adding a capability-shaped category, or registering
a route to an operation that does not implement it is forbidden (DESIGN.md
§Decisions inherited from the anti-drift record, 4).
-/
import CasDsl.Register
import CasDsl.Route

namespace CasDsl.Std

open Lean Elab Command

/-! ## Fixture presentations

Shared by the audit representatives, the proofs at the end of this module
and `CasDslTests/Std.lean`, so all three talk about the same objects. -/

/-- `x^3 − 2x + 1 ∈ ℤ[x]` — the notebook's polynomial before the embedding
into ℚ[x]. -/
def polyZ : Obj :=
  .elem (.poly .int) (Value.mkPoly .int #[.int 1, .int (-2), .int 0, .int 1])

/-- The same polynomial after `map p to ℚ[x]`. -/
def polyQ : Obj :=
  .elem (.poly .rat) (Value.mkPoly .rat #[.rat 1, .rat (-2), .rat 0, .rat 1])

/-- `[1, 2; 3, 4] ∈ Mat₂(ℚ)`. -/
def mat2Q : Obj :=
  .elem (.matrix 2 .rat) (.mat 2 .rat #[#[.rat 1, .rat 2], #[.rat 3, .rat 4]])

/-! ## 1 · The category graph

`parents` are the registered inclusion edges; params ride along them
unchanged. The graph is mathematical structure only: no node names an
implementation, a backend, or a current capability limit. The docs are
user-facing — they are what `#capabilities` prints. -/

private def stdCategories : Array CatDecl := #[
  { name := `Sets,
    doc := "sets: cardinality, membership, and equality of presentations" },
  { name := `CountableSets, parents := #[`Sets],
    doc := "sets equipped with a registered enumeration (countable), so their \
elements can be indexed" },
  { name := `FiniteSets, parents := #[`CountableSets],
    doc := "sets presented by an explicit finite list of elements" },
  { name := `CommRingElems,
    doc := "elements of a commutative ring" },
  { name := `FactorizationElems, parents := #[`CommRingElems],
    doc := "elements of a unique factorization domain: a factorization into \
irreducibles exists and is unique up to units and order" },
  { name := `EuclideanElems, parents := #[`FactorizationElems],
    doc := "elements of a euclidean domain (a division algorithm, hence also \
a UFD)" },
  { name := `Modules,
    doc := "modules over a commutative ring" },
  { name := `SmallModules, parents := #[`Modules],
    doc := "modules small enough to present by explicit finite data" },
  { name := `MatrixElems,
    doc := "square matrices over a commutative ring; params (size, entry domain)" }
]

run_cmd stdCategories.forM registerCategory!

/-! ## 2 · The method catalogue

Each declaration names the category where the operation first makes sense —
NOT the categories that can currently execute it. `annihilator` is declared
once, on `Modules`; `SmallModules` deliberately carries no declaration of
its own, so the notebook's fixture receives it purely through the registered
inclusion edge. -/

private def stdMethods : Array MethodDecl := #[
  { id := `factor, receiver := `FactorizationElems,
    resultDoc := "a factorization: a unit and irreducible factors with multiplicity",
    doc := "factor into irreducibles/primes with multiplicity" },
  { id := `det, receiver := `MatrixElems,
    resultDoc := "a scalar of the entry domain",
    doc := "the determinant" },
  { id := `inverse, receiver := `MatrixElems,
    resultDoc := "a matrix over the entry domain (or its fraction field)",
    doc := "the multiplicative inverse, when it exists" },
  { id := `annihilator, receiver := `Modules,
    resultDoc := "an ideal of the base ring",
    doc := "the annihilator ideal of the module" },
  { id := `nth, receiver := `CountableSets, arity := 1,
    argDoc := "a nonnegative index (0-based)",
    resultDoc := "the element at that index",
    doc := "the element at an index of the REGISTERED enumeration of this set \
(for ℤ: 0, 1, −1, 2, −2, …) — a documented, revisitable choice, never a claim \
that the set is intrinsically ordered that way" },
  { id := `cardinality, receiver := `Sets,
    resultDoc := "a cardinal (finite n, or ℵ₀)",
    doc := "the number of elements" },
  { id := `contains, receiver := `Sets, arity := 1,
    argDoc := "a candidate element",
    resultDoc := "a boolean",
    doc := "membership of an element in the set" },
  { id := `set_eq, receiver := `Sets, arity := 1,
    argDoc := "another set",
    resultDoc := "a boolean",
    doc := "equality of two sets, by presentation normalization (a documented \
ceiling, not a general decision procedure)" }
]

run_cmd stdMethods.forM registerMethod!

/-! ## 3 · Profile rules — which categories an object inhabits

Rules record only the MOST SPECIFIC membership: `FiniteSets ≤ CountableSets
≤ Sets` means a finite set already reaches `nth`, `cardinality` and
`contains` through the closure, so a redundant direct membership would only
be a second place to get the mathematics wrong.

Memberships are stated at their true strength: ℤ[x] is a UFD but NOT
euclidean, and ℤ/n is a commutative ring that is not a domain. Weakening or
strengthening either one to make a route apply is exactly the drift this
design forbids. -/

private def stdProfileRules : Array ProfileRule := #[
  -- ring elements
  { pattern := .elemOf (.exact .int), cat := `EuclideanElems, slots := #[.elemDom] },
  { pattern := .elemOf (.polyOver (.exact .rat)), cat := `EuclideanElems,
    slots := #[.elemDom] },
  -- ℤ[x] is a UFD, not a euclidean domain
  { pattern := .elemOf (.polyOver (.exact .int)), cat := `FactorizationElems,
    slots := #[.elemDom] },
  -- ℤ/n is a commutative ring; for composite n it is not a domain, so its
  -- elements stop at CommRingElems — and `factor`, declared strictly below
  -- on FactorizationElems, correctly does not reach them.
  -- CEILING: the moduli this slice exercises are registered one at a time.
  -- `DomainPattern.anyMod` (added for the embedding rules below) could match
  -- every modulus in ONE rule, but a profile rule must state membership at its
  -- true strength and that strength differs per modulus — ℤ/5 is a field while
  -- ℤ/6 is not even a domain — so a blanket rule would have to state one of
  -- them wrongly. An unregistered modulus has no profile at all, which
  -- resolves as an honest `notApplicable` — never a wrong membership.
  { pattern := .elemOf (.exact (.mod 5)), cat := `CommRingElems, slots := #[.elemDom] },
  -- matrices carry their instantiation data
  { pattern := .elemOf (.matrixOver .anyDom), cat := `MatrixElems,
    slots := #[.matSize, .matEntry] },
  -- ℕ, ℤ and ℚ as objects, and the same domains used as sets
  { pattern := .domainIs (.exact .nat), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainSetOf (.exact .nat), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainIs (.exact .int), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainSetOf (.exact .int), cat := `CountableSets, slots := #[.setDom] },
  -- ℚ is countable: the deliberate `nth` gap below is a MISSING ROUTE, not
  -- a weaker category
  { pattern := .domainIs (.exact .rat), cat := `CountableSets, slots := #[.setDom] },
  { pattern := .domainSetOf (.exact .rat), cat := `CountableSets, slots := #[.setDom] },
  -- an arithmetic progression is countable; a BOUNDED one is finite, but
  -- `PresPattern.progression` cannot see the bound, so it enters at
  -- CountableSets — a missed specificity, never a false claim
  { pattern := .progression .anyDom, cat := `CountableSets, slots := #[.setDom] },
  { pattern := .finiteSet, cat := `FiniteSets, slots := #[.setDom] },
  -- the module fixture: ℤ/n as a ℤ-module, in the PROPER subcategory only.
  -- `Modules` membership arrives through the inclusion edge, which is what
  -- makes `annihilator` a real inheritance demonstration.
  { pattern := .cyclicMod, cat := `SmallModules, slots := #[.const (.dom .int)] }
]

run_cmd stdProfileRules.forM registerProfileRule!

/-! ## 3b · Functors — receiver transport

A functor is what carries a method declared on one category to a receiver of
another: `F.cardinality()` on the module fixture resolves as
`UnderlyingSet(F).cardinality()`. Registration is data, exactly like a profile
rule, and `source`/`target` are category names — nothing here names a backend
or an implementation.

The resolver consults these only where round one found NOTHING, so registering
a functor can never take a method away from an object that already had it:
`annihilator` still reaches the fixture directly through `SmallModules ≤
Modules`, and the acceptance proofs below assert exactly that. -/

private def stdFunctors : Array FunctorDecl := #[
  { name := `UnderlyingSet, source := `Modules, target := `Sets,
    objMap := .cyclicToFiniteSet,
    doc := "the forgetful functor to underlying sets: a module presented by \
explicit finite data becomes the finite set of its elements, so the set \
methods (cardinality, contains, nth) apply to it" }
]

run_cmd stdFunctors.forM registerFunctor!

/-! ## 3c · Preferred canonical maps — the coercions the surface may insert

The preferred canonical maps of the standard universe, and the whole content
of `ℤ ⊆ ℚ` as the surface understands it: `map p to ℚ[x]`, a matrix literal
of integers ascribed to Mat₂(ℚ), `1 + 1/2`, and `let x := 7 in ℤ/5` all
coerce through exactly these rules. The engine knows none of these facts —
unregister a rule and the corresponding `map` stops working, with the honest
"there is no preferred canonical map" error (`CasDslTests/CanonicalMaps.lean`
proves it).

A canonical map is a preferred choice, not necessarily an injection (design
review 2026-07-30): the inclusions are monomorphisms, while ℤ → ℤ/n is the
ring quotient — supplied by its universal property, as cokernels and other
canonical choices would be. There is deliberately no rule out of ℚ —
`ℚ → ℤ` is not defined everywhere, and the partial `ℕ ← ℤ` reading stays an
engine-level CHECK rather than becoming a registered map — and none for the
coefficient- or entry-wise image of a rule, which `coerceValue` induces
structurally instead. -/

private def stdCanonicalMaps : Array CanonicalMap := #[
  { src := .exact .nat, tgt := .exact .int, op := .identity,
    doc := "ℕ ⊆ ℤ: an element of ℕ already IS an integer (they share the \
`Value.int` representation), so the injection moves no data" },
  { src := .exact .nat, tgt := .exact .rat, op := .intToRat,
    doc := "ℕ ⊆ ℚ: the composite of ℕ ⊆ ℤ ⊆ ℚ, registered explicitly because \
the coercion layer takes ONE hop (it does not compose rules)" },
  { src := .exact .int, tgt := .exact .rat, op := .intToRat,
    doc := "ℤ ⊆ ℚ: the fraction field of ℤ — the notebook's `map p to ℚ[x]` \
is this rule applied coefficient-wise" },
  { src := .exact .int, tgt := .anyMod, op := .intToMod,
    doc := "ℤ → ℤ/n for EVERY modulus n (one rule, by `anyMod`): the ring \
quotient — an integer naming its residue class, which is what an ascription \
such as `let x := 7 in ℤ/5` inserts" }
]

run_cmd stdCanonicalMaps.forM registerCanonicalMap!

/-! ## 4 · Capability routes — what can currently be executed

The computability layer. Every pattern below is disjoint from its siblings
for the same method, so every route ships at priority 0: selection never
depends on a tie-break. The `opId`s are exactly the operations
`Native.run` and the Sage adapter implement.

One route is deliberately ABSENT and must stay absent:

- `nth` on ℚ (`domainIs`/`domainSetOf (exact rat)`): ℚ is countable, so
  `nth` is semantically available, but no enumeration of ℚ is implemented.
  `ℚ[3]` is the acceptance proof's structured gap. -/

private def stdRoutes : Array Route := #[
  -- factorization
  { method := `factor, pattern := .elemOf (.exact .int),
    backend := `sage, opId := "factor_int" },
  { method := `factor, pattern := .elemOf (.polyOver (.exact .rat)),
    backend := `sage, opId := "factor_poly_q" },
  { method := `factor, pattern := .elemOf (.polyOver (.exact .int)),
    backend := `sage, opId := "factor_poly_z" },
  -- exact matrix algebra over ℚ
  { method := `det, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `sage, opId := "mat_det_q" },
  { method := `inverse, pattern := .elemOf (.matrixOver (.exact .rat)),
    backend := `sage, opId := "mat_inv_q" },
  -- modules
  { method := `annihilator, pattern := .cyclicMod,
    backend := `native, opId := "annihilator_cyclic" },
  -- enumeration: exactly the presentations `Native.run "nth"` implements —
  -- ℕ, ℤ, progressions, and explicit finite lists
  { method := `nth, pattern := .domainIs (.exact .nat), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainSetOf (.exact .nat), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainIs (.exact .int), backend := `native, opId := "nth" },
  { method := `nth, pattern := .domainSetOf (.exact .int), backend := `native, opId := "nth" },
  { method := `nth, pattern := .progression .anyDom, backend := `native, opId := "nth" },
  { method := `nth, pattern := .finiteSet, backend := `native, opId := "nth" },
  -- set operations; `anySet` also accepts a domain used as a set
  { method := `cardinality, pattern := .anySet, backend := `native, opId := "cardinality" },
  { method := `contains, pattern := .anySet, backend := `native, opId := "contains" },
  { method := `set_eq, pattern := .anySet, backend := `native, opId := "set_eq" }
]

run_cmd stdRoutes.forM registerRoute!

/-! ## 5 · Audit representatives

`#capability_gaps` crosses the declared methods with these concrete
presentations (the documented ceiling: representatives, not all conceivable
objects). Labels are human-facing and appear verbatim in the audit. -/

private def stdRepresentatives : Array Representative := #[
  ("ℤ", .domainObj .int),
  ("ℚ", .domainObj .rat),
  ("ℕ", .domainObj .nat),
  ("360 ∈ ℤ", .elem .int (.int 360)),
  ("x^3 − 2x + 1 ∈ ℤ[x]", polyZ),
  ("sample q ∈ ℚ[x]", polyQ),
  ("[1,2;3,4] ∈ Mat₂(ℚ)", mat2Q),
  ("ℤ/4 as ℤ-module", .cyclicModule 4),
  ("{0,2,4,…}", .setObj (.arithProg .int (.int 0) (.int 2) none))
]

run_cmd stdRepresentatives.forM registerRepresentative!

/-! ## 6 · Proofs of the universe

These run at ELABORATION time, so a registration mistake fails the build
rather than the notebook. They are stated as one reusable action so
`CasDslTests/Std.lean` can re-run the identical claims against the
*imported* environment — which additionally proves the registries survive
the olean round trip that the kernel's session cache depends on. -/

/-- The transport step of a resolution, as the name of the functor that
produced it (`none` = the method arrived without transport). Asserted
explicitly everywhere below: "resolves" and "resolves *directly*" are
different claims, and round two must never blur them. -/
private def transportOf (res : Resolution) : Option Name :=
  res.viaFunctor.map (·.functor)

/-- `m` is semantically available on `o` through the inheritance chain `via`
(after transport along `functor?`, when given), and routes to `backend`. -/
def expectRouted (env : Environment) (o : Obj) (m : Name) (via : List Name)
    (backend : Name) (functor? : Option Name := none) : CommandElabM Unit := do
  match resolveMethod env o m with
  | .error e => throwError s!"{m} is not available on {o.presentation}: {repr e}"
  | .ok res =>
    unless res.via == via do
      throwError s!"{m} on {o.presentation} arrived via {res.via}, expected {via}"
    unless transportOf res == functor? do
      throwError s!"{m} on {o.presentation} was transported by {repr (transportOf res)}, \
expected {repr functor?}"
    match routeFor env res (res.concreteReceiver o) with
    | .chosen r =>
        unless r.backend == backend do
          throwError s!"{m} on {o.presentation} routed to '{r.backend}', expected '{backend}'"
    | .gap _ =>
        throwError s!"{m} on {o.presentation} has no route, expected backend '{backend}'"
    | .ambiguousRoutes rs =>
        throwError s!"{m} on {o.presentation} matched {rs.size} routes tied on priority"

/-- `m` is semantically available on `o` through `via` and has NO route: a
deliberate, structured capability gap. Both halves are asserted, because
the separation of the two judgments is the whole point. -/
def expectGap (env : Environment) (o : Obj) (m : Name) (via : List Name)
    (functor? : Option Name := none) : CommandElabM Unit := do
  match resolveMethod env o m with
  | .error e =>
      throwError s!"{m} must stay AVAILABLE on {o.presentation}; a missing route may \
never remove it: {repr e}"
  | .ok res =>
    unless res.via == via do
      throwError s!"{m} on {o.presentation} arrived via {res.via}, expected {via}"
    unless transportOf res == functor? do
      throwError s!"{m} on {o.presentation} was transported by {repr (transportOf res)}, \
expected {repr functor?}"
    match routeFor env res (res.concreteReceiver o) with
    | .gap g =>
        unless g.semanticVia == via do
          throwError s!"the gap for {m} on {o.presentation} recorded via {g.semanticVia}"
    | .chosen r =>
        throwError s!"{m} on {o.presentation} unexpectedly routed to '{r.backend}'/{r.opId}; \
this gap is deliberate"
    | .ambiguousRoutes rs =>
        throwError s!"{m} on {o.presentation} matched {rs.size} routes tied on priority"

/-- `m` does not reach `o` at all: it is declared strictly below every
category `o` inhabits and no registered functor carries it there, so it must
not leak upward — nor sideways along a functor. -/
def expectNotApplicable (env : Environment) (o : Obj) (m : Name)
    : CommandElabM Unit := do
  match resolveMethod env o m with
  | .error (.notApplicable ..) => pure ()
  | .error e =>
      throwError s!"{m} on {o.presentation} failed with {repr e}, expected notApplicable"
  | .ok res =>
      let how := match transportOf res with
        | some f => s!"transported by functor '{f}'"
        | none => "by membership or inheritance"
      throwError s!"{m} leaked to {o.presentation} from category \
'{res.decl.receiver}' ({how})"

/-- The claims the standard universe exists to make true. -/
def acceptanceProofs (env : Environment) : CommandElabM Unit := do
  -- EuclideanElems ≤ FactorizationElems carries `factor` to integers, and
  -- the developer routed it to sage
  expectRouted env (.elem .int (.int 360)) `factor [`FactorizationElems] `sage
  -- THE inheritance demo: `annihilator` is declared only on Modules and
  -- reaches the fixture through SmallModules ≤ Modules — DIRECTLY, with no
  -- transport, even though a functor out of Modules is registered: round one
  -- wins unconditionally, so round two can never take this method away
  expectRouted env (.cyclicModule 4) `annihilator [`Modules] `native (functor? := none)
  -- THE central separation: ℚ is countable, so `nth` is available; no
  -- enumeration of ℚ is implemented, so executing it is a gap
  expectGap env (.domainObj .rat) `nth []
  -- ℤ[x] is a UFD, so `factor` is meaningful where the polynomial lives —
  -- and since round three (#18) it is routed there, not only on ℚ[x]
  expectRouted env polyZ `factor [] `sage
  -- no upward leak: ℤ/5 elements are CommRingElems, `factor` lives below
  expectNotApplicable env (.elem (.mod 5) (Value.mkMod 5 2)) `factor
  -- a finite set reaches `cardinality` through FiniteSets ≤ CountableSets ≤ Sets
  expectRouted env (.setObj (.finite .int #[.int 1, .int 2, .int 3])) `cardinality
    [`CountableSets, `Sets] `native
  -- THE transport demo: `cardinality` is declared on Sets, which the module
  -- fixture does not inhabit; it arrives by transporting the receiver along
  -- the forgetful functor and routes against the IMAGE (a finite set)
  expectRouted env (.cyclicModule 4) `cardinality [`CountableSets, `Sets] `native
    (functor? := `UnderlyingSet)
  expectRouted env (.cyclicModule 4) `contains [`CountableSets, `Sets] `native
    (functor? := `UnderlyingSet)
  expectRouted env (.cyclicModule 4) `nth [`CountableSets] `native
    (functor? := `UnderlyingSet)

run_cmd acceptanceProofs (← getEnv)

end CasDsl.Std
