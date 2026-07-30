/-
The method resolver — the ONE lookup boundary (DESIGN.md §The resolver).

Round one transports methods along registered subcategory edges: direct
declaration on a profile entry, or declaration on a category reachable from
it through parent edges (params ride along unchanged). Round two transports
the RECEIVER along a registered functor, and runs only where round one found
nothing (`transportCandidates`, `resolveCoreWithTransport`).

The decision logic is pure over plain data (`resolveCore`, `parentClosure`,
`profileFrom`, `transportCandidates`) so it is `#guard`-testable without an
`Environment`; the environment-facing wrappers add nothing but registry
reads.
-/
import Lean
import CasDsl.Registry

namespace CasDsl

open Lean

/-- Every category reachable from `start` through registered parent edges,
paired with the inheritance chain that reaches it (excluding `start`, so
`start` itself carries `[]`). Breadth-first: the chain recorded is a
shortest one, diamonds collapse to a single entry, and a cycle in the
registrations terminates instead of looping. -/
partial def parentClosure (cats : Array CatDecl) (start : Name)
    : Array (Name × List Name) :=
  go [(start, [])] ({} : NameSet) #[]
where
  parentsOf (n : Name) : Array Name :=
    match cats.find? (·.name == n) with
    | some d => d.parents
    | none => #[]
  go : List (Name × List Name) → NameSet → Array (Name × List Name) →
      Array (Name × List Name)
    | [], _, acc => acc
    | (n, revChain) :: rest, visited, acc =>
        if visited.contains n then
          go rest visited acc
        else
          let next := (parentsOf n).toList.map fun p => (p, p :: revChain)
          go (rest ++ next) (visited.insert n) (acc.push (n, revChain.reverse))

/-- `a ≤ b` strictly: `b` is reachable upward from `a` but not conversely,
i.e. `a` is the more specific receiver. Cyclic registrations make two
categories mutually reachable; they are then incomparable rather than each
suppressing the other. -/
def strictlyBelow (cats : Array CatDecl) (a b : Name) : Bool :=
  (parentClosure cats a).any (·.1 == b) && !(parentClosure cats b).any (·.1 == a)

private def dedupNames (ns : Array Name) : Array Name :=
  ns.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n

/-- Pure resolution over registry contents.

A declaration with `receiver = R` applies to profile entry `c` when `R` is
in the parent closure of `c.name`; the resulting `Resolution` carries `c`
instantiated exactly as the profile produced it (params pass through
inheritance edges unchanged).

The same declaration reached from several profile entries or along several
paths is ONE candidate (shortest chain kept). Distinct declarations of the
same method id are filtered by specificity: a declaration is dropped when a
surviving candidate declares the method on a strictly more specific
receiver. More than one survivor is a genuine ambiguity and is reported, not
resolved by an order heuristic. -/
def resolveCore (cats : Array CatDecl) (decls : Array MethodDecl)
    (profile : Array CatRef) (m : Name) : Except ResolveError Resolution :=
  let byId := decls.filter (·.id == m)
  if byId.isEmpty then
    .error (.unknownMethod m)
  else
    let cands : Array Resolution := Id.run do
      let mut out : Array Resolution := #[]
      for c in profile do
        for (n, chain) in parentClosure cats c.name do
          for d in byId do
            if d.receiver == n then
              match out.findIdx? (·.decl.receiver == d.receiver) with
              | some i =>
                  if chain.length < out[i]!.via.length then
                    out := out.set! i { decl := d, profileEntry := c, via := chain }
              | none =>
                  out := out.push { decl := d, profileEntry := c, via := chain }
      return out
    if cands.isEmpty then
      .error (.notApplicable m profile (dedupNames (byId.map (·.receiver))))
    else
      let kept := cands.filter fun d2 =>
        !cands.any fun d1 => strictlyBelow cats d1.decl.receiver d2.decl.receiver
      match kept[0]?, kept.size with
      | some r, 1 => .ok r
      | _, _ => .error (.ambiguous m kept)

/-- The categories `o` inhabits directly, from the registered profile rules.
Rich by construction: an object enters every category whose rule matches, and
the resolver closes over parent edges from all of them. -/
def profileFrom (rules : Array ProfileRule) (o : Obj) : Array CatRef :=
  rules.foldl (init := #[]) fun acc r =>
    match r.apply o with
    | some c => if acc.contains c then acc else acc.push c
    | none => acc

def profileOf (env : Environment) (o : Obj) : Array CatRef :=
  profileFrom (profileRules env) o

/-! ## Round two: receiver transport along registered functors

A method declared on `D` reaches a receiver of `C` when a functor
`F : C → D`-side is registered: `X.m()` resolves as `F(X).m()`, and every
caller routes and executes against `Resolution.concreteReceiver`.

Three ceilings are deliberate and load-bearing:

- **ONE HOP.** The image is resolved by round one only (`resolveCore`) — no
  functor composition, no path search, no preferred-path registry. A method
  reachable only after two functors stays `notApplicable`.
- **NO RESULT LIFTING.** The transported call returns the image's result as
  is. No shipped transported method needs a value carried back along `F`
  (`cardinality`, `contains` and `nth` of the underlying set ARE the answers
  about the module); a method that did would need a result map registered
  next to the object map, and would be a different feature.
- **NEVER A PREEMPTION.** Transport is consulted only when round one returned
  `notApplicable`, so a direct or inherited declaration always wins and a new
  functor registration can never take a method away from the object that
  already had it. -/

/-- Is `cat` reachable upward from something this profile already inhabits?
Both halves of a transport step ask exactly this: the receiver must reach the
functor's source, and the image must reach its declared target. -/
def profileReaches (cats : Array CatDecl) (profile : Array CatRef) (cat : Name) : Bool :=
  profile.any fun c => (parentClosure cats c.name).any (·.1 == cat)

/-- Every single-hop transported candidate for `m` on `o`.

For each registered functor whose source the receiver reaches and whose object
map is defined on the presentation: the image's own profile must reach the
functor's declared `target` (a mismatch is a defective registration and stops
resolution — see `ResolveError.functorTargetMismatch`), and the method is then
resolved on the image by round one only. -/
def transportCandidates (cats : Array CatDecl) (decls : Array MethodDecl)
    (rules : Array ProfileRule) (fs : Array FunctorDecl)
    (profile : Array CatRef) (o : Obj) (m : Name)
    : Except ResolveError (Array Resolution) := do
  let mut out : Array Resolution := #[]
  for f in fs do
    if profileReaches cats profile f.source then
      if let some image := f.objMap.apply o then
        let imageProfile := profileFrom rules image
        unless profileReaches cats imageProfile f.target do
          throw (.functorTargetMismatch f.name f.target imageProfile)
        if let .ok res := resolveCore cats decls imageProfile m then
          out := out.push { res with viaFunctor := some { functor := f.name, image } }
  return out

/-- Resolution over registry contents: round one, then transport.

Round one runs FIRST and wins unconditionally when it succeeds. Only its
`notApplicable` opens round two, and then exactly one transported candidate
resolves; several competing functors are the ordinary `ambiguous` error
carrying all of them, and none leaves the original `notApplicable` untouched. -/
def resolveCoreWithTransport (cats : Array CatDecl) (decls : Array MethodDecl)
    (rules : Array ProfileRule) (fs : Array FunctorDecl) (o : Obj) (m : Name)
    : Except ResolveError Resolution :=
  let profile := profileFrom rules o
  match resolveCore cats decls profile m with
  | .ok res => .ok res
  | .error err@(.notApplicable ..) => do
      let cands ← transportCandidates cats decls rules fs profile o m
      match cands[0]?, cands.size with
      | some res, 1 => .ok res
      | none, _ => .error err
      | _, _ => .error (.ambiguous m cands)
  | .error err => .error err

/-- Resolve method `m` for the receiver `o` — the ONE lookup boundary.

No caller may assume the lookup is only direct/inherited, that
`Resolution.via` is a parent chain, or that the receiver reaching the router
and the executor is the object passed in: it is
`res.concreteReceiver o`. -/
def resolveMethod (env : Environment) (o : Obj) (m : Name)
    : Except ResolveError Resolution :=
  resolveCoreWithTransport (categories env) (methods env) (profileRules env)
    (functors env) o m

end CasDsl
