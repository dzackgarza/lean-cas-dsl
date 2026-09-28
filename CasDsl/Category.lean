/-
Category references, method declarations, capability routes, and the
structured records the two availability judgments produce.

The load-bearing separation (DESIGN.md): `MethodDecl` is the SEMANTIC layer
(what is mathematically meaningful — owned by categories); `Route` is the
COMPUTABILITY layer (what a registered implementation can currently execute
for a concrete presentation). Nothing in `MethodDecl` may name a backend;
nothing in `Route` may widen or narrow mathematical meaning.
-/
import Lean
import CasDsl.Value

namespace CasDsl

open Lean (Name)

/-- The surface signature of a method: its arity and documentation, keyed by the method NAME.
Its mathematical owner and meaning are the registered method row of that name in the
`CasCatalogue` registry (the functor it names); nothing here states where the method lives, and
nothing here may name a backend. -/
structure MethodDecl where
  id : Name
  /-- Number of surface arguments after the receiver (`nth` has 1). -/
  arity : Nat := 0
  argDoc : String := ""
  resultDoc : String := ""
  doc : String := ""
  /-- The Mathlib constant giving this method's MEANING — what a trusted
  backend answer is an answer to (`factor ↦
  UniqueFactorizationMonoid.factors`). Registration checks the constant
  exists. `.anonymous` is permitted only where Mathlib holds no carrier for
  the operation; `conventions` must then say so. -/
  anchor : Name := .anonymous
  /-- Where the method's answer and the anchor differ by a stated
  convention — unit normalization for `factor`, associates for `gcd` — the
  convention is declared here, beside the anchor, never left implicit. -/
  conventions : String := ""
  /-- An advisory TEMPLATE for an unexpected-but-true result of this method
  (a note is ADVICE, never a refusal — owner ruling 2026-07-31). The TEXT
  lives here at the declaration; the method's own semantics decide when it
  fires and substitute the `{…}` placeholders (`Eval.renderAdvisory`).
  Empty = the method carries no advisory. -/
  advisory : String := ""
  deriving BEq, Repr, Inhabited

/-- First-order matcher over `Domain` (serializable — no closures). -/
inductive DomainPattern where
  | exact (d : Domain)
  | polyOver (coeff : DomainPattern)
  | matrixOver (entry : DomainPattern)
  /-- `Eⁿ` for every length `n`, entries matching `entry`. -/
  | vectorOver (entry : DomainPattern)
  /-- `ℤ/n` for EVERY modulus `n` — what makes `ℤ → ℤ/n` one embedding rule
  instead of one per modulus. -/
  | anyMod
  /-- `src → tgt` for every pair: what a function element presents. -/
  | anyFuncs
  | anyDom
  deriving BEq, Repr, Inhabited

/-- First-order matcher over the receiver `Obj` presentation. -/
inductive PresPattern where
  | elemOf (d : DomainPattern)
  | domainIs (d : DomainPattern)
  | finiteSet
  /-- A finite set whose element domain matches the pattern. -/
  | finiteSetOver (d : DomainPattern)
  /-- A finite multiset (`p.roots()`'s result presentation). Distinct from
  `finiteSet` so the finite-set binary operations are never claimed for it —
  what a multiset answers is `∈`, `=`, `⊆` and `|·|`. -/
  | multisetPres
  | progression (dom : DomainPattern)
  | domainSetOf (d : DomainPattern)
  /-- `A × B`; the factors are not inspected (a pattern language over one
  presentation cannot state their strength — see the profile rules). -/
  | productSet
  /-- `𝒫(A)`, likewise. -/
  | powersetSet
  /-- `ℂ - ℚ`, likewise: the two domains are not inspected here. -/
  | domainDiffSet
  /-- `span_ℚ{…} ≤ ℚⁿ`; the ambient length is not inspected (a pattern over
  one presentation cannot state a strength that depends on it). -/
  | spanSet
  /-- `p + K` — a coset of the constants; the ring is not inspected. -/
  | cosetSet
  /-- `{n ∈ ℕ | P(n)}` — a guard-backed predicate set (#31 item 7); the
  guard is not inspected (a pattern over one presentation cannot state a
  strength that depends on it — the profile rules' rule). -/
  | predicateSet
  | anySet
  | cyclicMod
  /-- `Spec R`; the ring is not inspected (a pattern over one presentation
  cannot state a strength that depends on it — the profile rules' rule). -/
  | specObj
  /-- A symbolic expression used as an object. No profile rule names it: an
  expression is what operations are performed WITH, not ON. -/
  | symbolic
  /-- A first-class HOM value (DESIGN.md §Homs are first-class). Its domain
  is a function domain by construction, so this implies `elemOf anyFuncs`. -/
  | homElem
  /-- `Dihedral(n)`, a presentation of a dihedral group. -/
  | dihedralPres
  | anyObj
  deriving BEq, Repr, Inhabited

namespace DomainPattern

partial def accepts : DomainPattern → Domain → Bool
  | .exact d, d' => d == d'
  | .polyOver p, .poly c => p.accepts c
  | .polyOver _, _ => false
  | .matrixOver p, .matrix _ e => p.accepts e
  | .matrixOver _, _ => false
  | .vectorOver p, .vector _ e => p.accepts e
  | .vectorOver _, _ => false
  | .anyMod, .mod _ => true
  | .anyMod, _ => false
  | .anyFuncs, .funcs .. => true
  | .anyFuncs, _ => false
  | .anyDom, _ => true

/-- `p.implies q`: every domain accepted by `p` is accepted by `q` — the
subsumption order the op-signature check uses. Syntactic like `accepts`, and
exact on this pattern algebra (an `exact` pattern accepts one domain, so it
implies whatever accepts that domain). -/
partial def implies : DomainPattern → DomainPattern → Bool
  | _, .anyDom => true
  | .exact d, q => q.accepts d
  | .polyOver p, .polyOver q => p.implies q
  | .matrixOver p, .matrixOver q => p.implies q
  | .vectorOver p, .vectorOver q => p.implies q
  | .anyMod, .anyMod => true
  | .anyFuncs, .anyFuncs => true
  | _, _ => false

end DomainPattern

namespace PresPattern

def accepts : PresPattern → Obj → Bool
  | .elemOf p, .elem d _ => p.accepts d
  | .domainIs p, .domainObj d => p.accepts d
  | .finiteSet, .setObj (.finite ..) => true
  | .finiteSetOver p, .setObj (.finite d _) => p.accepts d
  | .multisetPres, .setObj (.multiset ..) => true
  | .progression p, .setObj (.arithProg d ..) => p.accepts d
  | .domainSetOf p, .setObj (.domainSet d) => p.accepts d
  | .productSet, .setObj (.product ..) => true
  | .powersetSet, .setObj (.powerset _) => true
  | .domainDiffSet, .setObj (.domainDiff ..) => true
  | .spanSet, .setObj (.span ..) => true
  | .cosetSet, .setObj (.coset ..) => true
  | .predicateSet, .setObj (.predicate ..) => true
  | .anySet, .setObj _ => true
  | .anySet, .domainObj _ => true   -- a domain used as a set
  | .cyclicMod, .cyclicModule _ => true
  | .specObj, .specOf _ => true
  | .symbolic, .symObj _ => true
  | .homElem, .elem (.funcs ..) (.hom ..) => true
  | .dihedralPres, .dihedralGroup _ => true
  | .anyObj, _ => true
  | _, _ => false

/-- `p.implies q`: every object accepted by `p` is accepted by `q`. `anySet`
also accepts a domain used as a set, so `domainIs`, `domainSetOf`,
`finiteSet` and `progression` all imply it. -/
def implies : PresPattern → PresPattern → Bool
  | _, .anyObj => true
  | .elemOf p, .elemOf q => p.implies q
  | .domainIs p, .domainIs q => p.implies q
  | .domainSetOf p, .domainSetOf q => p.implies q
  | .progression p, .progression q => p.implies q
  | .finiteSet, .finiteSet => true
  | .finiteSetOver p, .finiteSetOver q => p.implies q
  | .finiteSetOver _, .finiteSet => true
  | .finiteSetOver _, .anySet => true
  | .multisetPres, .multisetPres => true
  | .productSet, .productSet => true
  | .powersetSet, .powersetSet => true
  | .domainDiffSet, .domainDiffSet => true
  | .spanSet, .spanSet => true
  | .cosetSet, .cosetSet => true
  | .predicateSet, .predicateSet => true
  | .cyclicMod, .cyclicMod => true
  | .specObj, .specObj => true
  | .symbolic, .symbolic => true
  | .homElem, .homElem => true
  | .dihedralPres, .dihedralPres => true
  -- a hom element's domain is a function domain by construction, so the
  -- element patterns wide enough to accept every function domain subsume it
  | .homElem, .elemOf .anyFuncs => true
  | .homElem, .elemOf .anyDom => true
  | .anySet, .anySet => true
  | .domainIs _, .anySet => true
  | .domainSetOf _, .anySet => true
  | .finiteSet, .anySet => true
  | .multisetPres, .anySet => true
  | .progression _, .anySet => true
  | .productSet, .anySet => true
  | .powersetSet, .anySet => true
  | .domainDiffSet, .anySet => true
  | .spanSet, .anySet => true
  | .cosetSet, .anySet => true
  | .predicateSet, .anySet => true
  | _, _ => false

end PresPattern

/-- A typing rule: presentations matching `pattern` are CONSTRUCTED as points of the registered
`CasCatalogue` category `category` (for a module fibre, over the ring `base`). Typing happens once,
when a value is made; the value then carries its category, and transport never re-derives it
(CC-SEP). When several rules match, the one with the most specific pattern types the value.

`classes` are the Mathlib classes the claim needs at the presentation's denoted domain; for a
concrete domain they are synthesized at registration, so a false typing fails the build. -/
structure TypingRule where
  pattern : PresPattern
  category : String
  base : Option Domain := none
  classes : Array Name := #[]
  doc : String := ""
  deriving BEq, Repr, Inhabited

/-! ## Preferred canonical maps (the coercion layer)

`map e to D`, a mixed-domain join, the element promotion of a set or matrix
literal and a domain ascription all insert THE preferred canonical map of
one domain into another, when one is registered — and fail honestly
otherwise. *Which* maps exist is registry data, exactly like profile rules
and functors: the prelude registers `ℕ ⊆ ℤ ⊆ ℚ` and `ℤ → ℤ/n`, and no
engine module knows those particular facts.

A canonical map is a PREFERRED CHOICE, not necessarily an injection
(design review 2026-07-30): it may be a monomorphism in some category
(`ℤ ⊆ ℚ`), or supplied by a universal property — the quotient `ℤ → ℤ/n`,
cokernels — and, behind the same lookup, a later round may let transport
along a preferred functor supply one. What every entry must be is THE
canonical such map for its pair, by convention or universal property.

`ℤ ⊆ ℚ` in the surface is therefore sugar for the registered preferred
structure-preserving map (anti-drift record: mathematician-facing coercions
are inserted by elaboration). An unregistered pair has no coercion — an
honest error, never widened to a "reasonable" conversion. -/

/-- The value transform of a registered canonical map, as registry data.

CEILING (the same shape as `ObjMap`'s and `DomainPattern`'s): a canonical
map whose transform is not one of these constructors adds a constructor
here. That is a deliberate, visible edit to the engine's vocabulary rather
than a closure smuggled into the environment; nothing infers a transform
from the two domains. -/
inductive CanonOp where
  /-- The value representation is unchanged — `ℕ ⊆ ℤ`, whose elements are
  already carried as `Value.int`. -/
  | identity
  | intToRat
  /-- An integer names its residue class in the target `ℤ/n`. -/
  | intToMod
  deriving BEq, Repr, Inhabited

namespace CanonOp

/-- Is this transform an INCLUSION — does the map identify its source with a
SUBSET of its target? That is exactly the question `D ⊆ E` asks of the
registry (DESIGN.md §Coercions), and it is a per-constructor mathematical
claim rather than a property inferred from a pair of domains.

`identity` moves no data and `intToRat` is the fraction field's injection;
the quotient `ℤ → ℤ/n` is the one that is NOT one, which is what makes
`ℤ ⊆ ℤ/5` false rather than true-because-a-map-exists. -/
def isInclusion : CanonOp → Bool
  | .identity | .intToRat => true
  | .intToMod => false

/-- Apply the transform. `tgt` is the CONCRETE target domain: the pattern
that matched need not determine it (`intToMod` needs the modulus). A value
the transform is not defined on means the RULE was registered for a source it
cannot carry — a defective registration, reported as such. -/
def apply : CanonOp → Domain → Value → Except String Value
  | .identity, _, v => .ok v
  | .intToRat, _, .int z => .ok (.rat (Rat.ofInt z))
  | .intToMod, .mod n, .int z => .ok (Value.mkMod n z)
  | op, tgt, v => .error s!"the registered canonical-map op {repr op} does not apply to \
{v.render} → {tgt.render}: that registration is defective"

end CanonOp

/-- A registered preferred canonical map: THE canonical map from every
domain matching `src` into every domain matching `tgt`.

Patterns on both sides is what keeps `ℤ → ℤ/n` a single rule. A rule is a
mathematical claim (this map exists and is the preferred one — an
inclusion, a quotient, or any universal-property-supplied choice), so
nothing here names a backend. What is a registration mistake is a SECOND
rule for the same pair, or a map that is not the canonical choice: the
registry records preferences, it does not rank alternatives. -/
structure CanonicalMap where
  src : DomainPattern
  tgt : DomainPattern
  op : CanonOp
  doc : String := ""
  deriving BEq, Repr, Inhabited

/-- Does this rule carry the concrete `srcDom` into the concrete `tgtDom`? -/
def CanonicalMap.applies (r : CanonicalMap) (srcDom tgtDom : Domain) : Bool :=
  r.src.accepts srcDom && r.tgt.accepts tgtDom

/-- Execution-layer failure (distinct from `ResolveError` and
`CapabilityGap`: by the time an `ExecError` exists, the method was
meaningful AND a route was selected). -/
inductive ExecError where
  /-- The selected backend cannot be reached (e.g. `sage` not on PATH, or
  sandboxed). Selection happened before execution; this is not silently
  retried elsewhere. -/
  | backendUnavailable (backend : Name) (detail : String)
  | backendError (backend : Name) (kind message : String)
  /-- Argument validation happens at execution in this slice. -/
  | badRequest (message : String)
  | protocolError (message : String)
  deriving Repr, Inhabited

/-- A registered implementation route — the computability layer. Adding,
replacing, or rerouting one never changes notebook syntax or a
`MethodDecl`. -/
structure Route where
  method : Name
  pattern : PresPattern
  /-- Executor name (`native`, `sage`, …) looked up in the executor table. -/
  backend : Name
  /-- Backend operation identity (e.g. `"factor_int"`). -/
  opId : String
  /-- Deterministic selection: highest wins; a tie among applicable routes
  is an explicit ambiguity error, never a silent pick. -/
  priority : Nat := 0
  /-- One line on what this particular binding means (when the method's own
  doc does not cover it), rendered by the diagnostics. -/
  doc : String := ""
  /-- Where this binding's implementation or documentation lives (a source
  or docs link), rendered by the diagnostics. Overrides the op's own. -/
  docUrl : String := ""
  /-- For a FUSED route: the semantic composite it realizes, as the registered method id and the
  labels of the route's steps (CC-ROUTE). Such a route runs on the receiver of a semantic point
  itself, computing `m(U(x))` in one backend call; it realizes that composite and nothing else. -/
  realizes : Option (String × Array String) := none
  deriving BEq, Repr, Inhabited

/-- The declared receiver signature of one backend operation: `opId` of
`backend` accepts a receiver iff SOME pattern in `accepts` accepts it.

This is the executor's receiver match, restated as registry data by the
backend's own Lean half — which is what lets `addRouteChecked` verify at
BUILD time that a route only ever sends an op the receiver shapes it
implements (design review 2026-07-30: the route/op agreement is a checked
invariant, not a convention caught at runtime). Shapes only: partiality
WITHIN an accepted shape (an out-of-range index, a domain with no membership
test) remains a loud runtime error in the executor. -/
structure OpSig where
  backend : Name
  opId : String
  accepts : Array PresPattern
  /-- The REAL function the backend runs — `Integer.factor()`, not the wire
  op id. What the diagnostics display; the op id stays wire bookkeeping.
  Empty for an op that is its own implementation (a native op). -/
  backendFn : String := ""
  /-- Presentation conventions specific to THIS op — the receiver-specific
  choices that do not belong at the method's generality (the unit is ±1 with
  all factors positive in ℤ; factors are monic over a field). -/
  conventions : String := ""
  /-- One line on what this op computes, rendered by the diagnostics. -/
  doc : String := ""
  /-- Where the EXTERNAL function's documentation lives (the Sage reference
  page for `backendFn`); for a native op, the implementation source. -/
  docUrl : String := ""
  /-- A static advisory pushed alongside every result of this op: the
  PROVIDER's own disclosure of a choice the answer rides (Sage's fixed
  embedding QQbar ↪ ℂ on the ℂ[x] ops). Registration data, rendered
  generically — no advisory text lives in the evaluator. -/
  advisory : String := ""
  deriving BEq, Repr, Inhabited

/-- The structured capability gap: the method resolves (the registry found its owner and a
route), and no registered implementation runs it on this presentation. An auditable backlog item,
surfaced at execution, never repaired by narrowing semantics. -/
structure CapabilityGap where
  method : Name
  /-- The resolved route, rendered by the registry. -/
  route : String
  /-- The presentation routing was attempted for: the route's image. -/
  presentation : String
  routesConsidered : Array Route
  deriving Repr, Inhabited

end CasDsl
