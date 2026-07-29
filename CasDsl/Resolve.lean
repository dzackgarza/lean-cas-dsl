/-
The method resolver — the ONE lookup boundary (DESIGN.md §The resolver).

Round one transports methods along registered subcategory edges only:
direct declaration on a profile entry, or declaration on a category
reachable from it through parent edges (params ride along unchanged).

The decision logic is pure over plain data (`resolveCore`, `parentClosure`)
so it is `#guard`-testable without an `Environment`; the environment-facing
wrappers add nothing but registry reads.
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
def profileOf (env : Environment) (o : Obj) : Array CatRef :=
  (profileRules env).foldl (init := #[]) fun acc r =>
    match r.apply o with
    | some c => if acc.contains c then acc else acc.push c
    | none => acc

/-- Resolve method `m` for the receiver `o`.

FUTURE-TRANSPORT SEAM: functorial transport is added *here*, by extending
this function with receiver transformation along preferred functors. No
caller may assume the lookup is only direct/inherited, that `Resolution.via`
is a parent chain, or that the receiver reaching the executor is the object
passed in. -/
def resolveMethod (env : Environment) (o : Obj) (m : Name)
    : Except ResolveError Resolution :=
  resolveCore (categories env) (methods env) (profileOf env o) m

end CasDsl
