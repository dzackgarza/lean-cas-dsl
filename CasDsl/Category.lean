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
edges (`SmallModules(ℤ) ≤ Modules(ℤ)` because `SmallModules ≤ Modules`). -/
structure CatRef where
  name : Name
  params : Array ParamVal := #[]
  deriving BEq, Repr, Hashable, Inhabited

/-- A registered category: its name and its registered parent NAMES
(the subcategory inclusions of round one — the only non-direct method
transport). -/
structure CatDecl where
  name : Name
  parents : Array Name := #[]
  doc : String := ""
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
  deriving BEq, Repr, Inhabited

/-- First-order matcher over `Domain` (serializable — no closures). -/
inductive DomainPattern where
  | exact (d : Domain)
  | polyOver (coeff : DomainPattern)
  | matrixOver (entry : DomainPattern)
  | anyDom
  deriving BEq, Repr, Inhabited

/-- First-order matcher over the receiver `Obj` presentation. -/
inductive PresPattern where
  | elemOf (d : DomainPattern)
  | domainIs (d : DomainPattern)
  | finiteSet
  | progression (dom : DomainPattern)
  | domainSetOf (d : DomainPattern)
  | anySet
  | cyclicMod
  | anyObj
  deriving BEq, Repr, Inhabited

namespace DomainPattern

partial def accepts : DomainPattern → Domain → Bool
  | .exact d, d' => d == d'
  | .polyOver p, .poly c => p.accepts c
  | .polyOver _, _ => false
  | .matrixOver p, .matrix _ e => p.accepts e
  | .matrixOver _, _ => false
  | .anyDom, _ => true

end DomainPattern

namespace PresPattern

def accepts : PresPattern → Obj → Bool
  | .elemOf p, .elem d _ => p.accepts d
  | .domainIs p, .domainObj d => p.accepts d
  | .finiteSet, .setObj (.finite ..) => true
  | .progression p, .setObj (.arithProg d ..) => p.accepts d
  | .domainSetOf p, .setObj (.domainSet d) => p.accepts d
  | .anySet, .setObj _ => true
  | .anySet, .domainObj _ => true   -- a domain used as a set
  | .cyclicMod, .cyclicModule _ => true
  | .anyObj, _ => true
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
  deriving BEq, Repr, Inhabited

/-- How a method became semantically available for a receiver. -/
structure Resolution where
  decl : MethodDecl
  /-- The instantiated category on the receiver's profile that supplied the
  method (directly or through parents). -/
  profileEntry : CatRef
  /-- Name-level inheritance chain from `profileEntry.name` up to
  `decl.receiver` (empty = declared directly on the profile entry). -/
  via : List Name
  deriving Repr, Inhabited

inductive ResolveError where
  /-- Not declared on any category reachable from the profile. `declaredOn`
  lists where the method IS declared, for an honest error message. -/
  | notApplicable (method : Name) (profile : Array CatRef) (declaredOn : Array Name)
  /-- Distinct declarations reachable from incomparable profile entries. -/
  | ambiguous (method : Name) (candidates : Array Resolution)
  | unknownMethod (method : Name)
  deriving Repr, Inhabited

/-- The structured capability gap: semantically available, no executable
route. An auditable developer backlog item — surfaced at execution, never
repaired by narrowing semantics. -/
structure CapabilityGap where
  method : Name
  receiverCategory : CatRef
  presentation : String
  /-- Inheritance chain that made the method semantically available. -/
  semanticVia : List Name
  routesConsidered : Array Route
  deriving Repr, Inhabited

end CasDsl
