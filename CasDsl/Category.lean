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

/-- Category instantiation parameter. -/
inductive ParamVal where
  | dom (d : Domain)
  | nat (n : Nat)
  deriving BEq, Repr, Hashable, Inhabited

/-- An instantiated category: a node of the name-level inheritance graph
plus instantiation data. Params are preserved unchanged along inheritance
edges (`EuclideanElems(ℤ) ≤ PIDElems(ℤ)` because `EuclideanElems ≤ PIDElems`). -/
structure CatRef where
  name : Name
  params : Array ParamVal := #[]
  deriving BEq, Repr, Hashable, Inhabited

/-- A registered category. The category is the primary object; this entry
is its name in the extracted graph the resolver walks, `anchor` ties the
name to the category it means in Mathlib, and each parent NAME stands for
an inclusion functor (the subcategory inclusions of round one — the only
non-direct method transport). -/
structure CatDecl where
  name : Name
  parents : Array Name := #[]
  doc : String := ""
  /-- The Mathlib classes this category's membership MEANS, in dependency
  order (`SPEC-REGISTRY-TYPE-PREPASS` §3.2): registering an object into this
  category elaborates each class at the object's denoted type, so a
  membership the classes cannot discharge fails the build. Empty is honest
  only for `Sets` (every type), for nodes whose claim lives in
  `paramTelescope`, and, during the migration, for nodes slated for
  re-anchoring or deletion. -/
  telescope : Array Name := #[]
  /-- The ring-parameterized layer of the telescope: classes elaborated at
  the entry's first category parameter and the member's carrier together —
  `Modules(ℤ)` membership means `Module ℤ M`. Same discipline as
  `telescope`; the split exists because the arities differ. -/
  paramTelescope : Array Name := #[]
  /-- The category this entry means, where Mathlib names it (`ModuleCat`,
  `FintypeCat`, `CategoryTheory.types`, `AlgebraicGeometry.Scheme`). When
  the category has no Mathlib name of its own, the constant that defines
  it: the class cutting a full subcategory (`EuclideanDomain` cuts
  euclidean domains out of `CommRingCat`), or the object whose elements the
  entry fibres over (`Complex`). Required at registration — a name with no
  mathematics behind it is not registrable. -/
  anchor : Name := .anonymous
  deriving BEq, Repr, Inhabited

/-- A category-owned method declaration. Owns mathematical identity and
interface — never a backend, algorithm, or current capability limit. -/
structure MethodDecl where
  id : Name
  /-- Receiver category NAME; applies at any instantiation of it. -/
  receiver : Name
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
  | anyObj
  deriving BEq, Repr, Inhabited

namespace DomainPattern

partial def accepts : DomainPattern → Domain → Bool
  | .exact d, d' => d == d'
  | .polyOver p, .poly c => p.accepts c
  | .polyOver _, _ => false
  | .matrixOver p, .matrix _ e => p.accepts e
  | .matrixOver _, _ => false
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
  | .anyMod, .anyMod => true
  | .anyFuncs, .anyFuncs => true
  | _, _ => false

end DomainPattern

namespace PresPattern

def accepts : PresPattern → Obj → Bool
  | .elemOf p, .elem d _ => p.accepts d
  | .domainIs p, .domainObj d => p.accepts d
  | .finiteSet, .setObj (.finite ..) => true
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

/-- How one instantiation parameter of a profile-rule category is derived
from the matched object. First-order so profile rules are registry data. -/
inductive ParamSlot where
  | const (v : ParamVal)
  /-- The domain of a matched `.elem`. -/
  | elemDom
  /-- The `n` of a matched `.elem` in `Matₙ(entry)`. -/
  | matSize
  /-- The entry domain of a matched matrix element. -/
  | matEntry
  /-- The element domain of a matched set presentation / `domainObj`. -/
  | setDom
  deriving BEq, Repr, Inhabited

/-- A registered category-membership rule: objects matching `pattern`
inhabit `cat` instantiated by `slots`. Profiles are data — a new category
or presentation family registers rules; it never edits the engine. -/
structure ProfileRule where
  pattern : PresPattern
  cat : Name
  slots : Array ParamSlot := #[]
  deriving BEq, Repr, Inhabited

namespace ParamSlot

/-- Instantiate one slot against the matched object. `none` when the slot
does not apply to this presentation (the rule then contributes nothing —
a registration mistake surfaced by `#capabilities`, not a crash). -/
def instantiate : ParamSlot → Obj → Option ParamVal
  | .const v, _ => some v
  | .elemDom, .elem d _ => some (.dom d)
  | .matSize, .elem (.matrix n _) _ => some (.nat n)
  | .matEntry, .elem (.matrix _ e) _ => some (.dom e)
  | .setDom, .setObj (.finite d _) => some (.dom d)
  | .setDom, .setObj (.arithProg d ..) => some (.dom d)
  | .setDom, .setObj (.domainSet d) => some (.dom d)
  | .setDom, .domainObj d => some (.dom d)
  | _, _ => none

end ParamSlot

namespace ProfileRule

/-- The instantiated category this rule assigns to `o`, if it accepts. -/
def apply (r : ProfileRule) (o : Obj) : Option CatRef := do
  guard <| r.pattern.accepts o
  let params ← r.slots.mapM (·.instantiate o)
  return { name := r.cat, params }

end ProfileRule

/-! ## Functors (the transport layer)

A registered functor is what lets a method declared on category `D` reach a
receiver of category `C`: `X.m()` becomes `F(X).m()` when `F : C → D` is
registered. Like every other registry payload these are first-order,
serializable data — so the OBJECT MAP is an inductive tag, not a Lean
function. -/

/-- The object map of a registered functor, as registry data.

CEILING (the same shape as `DomainPattern`'s): a functor whose object map is
not expressible by one of these constructors adds a constructor here. That is
a deliberate, visible edit to the engine's vocabulary rather than a closure
smuggled into the environment; nothing infers an object map. -/
inductive ObjMap where
  /-- The forgetful map of the module fixture: the ℤ-module `ℤ/n` to its
  underlying set, presented as the explicit finite list of residues. -/
  | cyclicToFiniteSet
  deriving BEq, Repr, Inhabited

namespace ObjMap

/-- The image of `o`, or `none` when the map is not defined on this
presentation (the functor then simply does not apply — never a guess). -/
def apply : ObjMap → Obj → Option Obj
  | .cyclicToFiniteSet, .cyclicModule n =>
      -- `ℤ/0 ≅ ℤ` is not finite, so the finite-list presentation is not its
      -- underlying set: the map is undefined there rather than wrong.
      if n == 0 then none
      else some (.setObj (.finite (.mod n)
        ((Array.range n).map fun i => Value.mkMod n (Int.ofNat i))))
  | .cyclicToFiniteSet, _ => none

end ObjMap

/-- A registered functor along which the resolver may transport a receiver.

`source` and `target` are category NAMES — this is the semantic layer, so no
field of it may ever name a backend. -/
structure FunctorDecl where
  name : Name
  source : Name
  target : Name
  objMap : ObjMap
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

/-- One transport step: the functor that was applied, and the receiver it
produced. The image is what routing and execution see. -/
structure FunctorStep where
  functor : Name
  image : Obj
  deriving Repr, Inhabited

/-- How a method became semantically available for a receiver. -/
structure Resolution where
  decl : MethodDecl
  /-- The instantiated category on the receiver's profile that supplied the
  method (directly or through parents). When `viaFunctor` is set this is a
  category of the IMAGE's profile, not the original receiver's. -/
  profileEntry : CatRef
  /-- Name-level inheritance chain from `profileEntry.name` up to
  `decl.receiver` (empty = declared directly on the profile entry). -/
  via : List Name
  /-- Set when the method was reached by transporting the receiver along a
  registered functor. Every caller must route and execute against
  `concreteReceiver`, never the object it passed in. -/
  viaFunctor : Option FunctorStep := none
  deriving Repr, Inhabited

/-- The receiver that routing and execution must use: the transported image
when the method was reached through a functor, otherwise `o` unchanged. -/
def Resolution.concreteReceiver (res : Resolution) (o : Obj) : Obj :=
  match res.viaFunctor with
  | some step => step.image
  | none => o

inductive ResolveError where
  /-- Not declared on any category reachable from the profile. `declaredOn`
  lists where the method IS declared, for an honest error message. -/
  | notApplicable (method : Name) (profile : Array CatRef) (declaredOn : Array Name)
  /-- Distinct declarations reachable from incomparable profile entries, or
  (for transport) more than one registered functor carrying the method to this
  receiver. Competing candidates are reported, never ordered. -/
  | ambiguous (method : Name) (candidates : Array Resolution)
  | unknownMethod (method : Name)
  /-- A registered functor applied to the receiver, but the profile of its
  image does not reach its declared `target`: the REGISTRATION is defective.
  Resolution stops here — a functor whose declared target is not the one it
  actually lands in may not be used, and guessing past it would launder a
  broken registration into a mathematical answer. -/
  | functorTargetMismatch (functor : Name) (target : Name) (imageProfile : Array CatRef)
  deriving Repr, Inhabited

/-- The structured capability gap: semantically available, no executable
route. An auditable developer backlog item — surfaced at execution, never
repaired by narrowing semantics. -/
structure CapabilityGap where
  method : Name
  receiverCategory : CatRef
  /-- The presentation routing was attempted for — the TRANSPORTED receiver
  when `viaFunctor` is set. -/
  presentation : String
  /-- Inheritance chain that made the method semantically available. -/
  semanticVia : List Name
  /-- The transport step, when the method reached this receiver through a
  functor: without it the reported semantic chain would not explain how a
  module ended up being routed as a set. -/
  viaFunctor : Option FunctorStep := none
  routesConsidered : Array Route
  deriving Repr, Inhabited

end CasDsl
