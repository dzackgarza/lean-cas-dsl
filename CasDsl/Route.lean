/-
The capability router and the executor table.

Routing is the COMPUTABILITY layer: it selects a registered implementation
for a concrete presentation, and its failures never travel back into
semantics. `routeFor` therefore reports three distinct outcomes rather than
collapsing them — a structured capability gap (auditable developer backlog),
a configuration ambiguity (two applicable routes tied on priority), or a
choice.
-/
import Lean
import CasDsl.Resolve

namespace CasDsl

open Lean

/-- A backend implementation: operation id, receiver, arguments. -/
abbrev Executor := String → Obj → Array Obj → IO (Except ExecError Value)

/-- The executor table is CODE WIRING, not semantic state: it maps a
`(backend, opId)` pair to a Lean function, holds no registrations a notebook
can observe, and is rebuilt identically on every process start by the
`initialize` blocks of the backend modules. The plugin state law (all
semantic state in the `Environment`) therefore does not reach it — routes,
the semantic half, live in `routeExt`.

Keying by `(backend, opId)` rather than backend alone is what lets a module
outside `Native.lean` contribute an operation to an existing backend: it
registers its own `OpSig`, route and executor entry, and never edits the
backend's dispatch. -/
initialize executorTableRef : IO.Ref (Array ((Name × String) × Executor)) ← IO.mkRef #[]

/-- Register a backend implementation for one operation. A duplicate
`(backend, opId)` is a build-time programming error, not a precedence
question: it throws. -/
def registerExecutor (backend : Name) (opId : String) (e : Executor) : IO Unit := do
  let table ← executorTableRef.get
  if table.any (·.1 == (backend, opId)) then
    throw <| IO.userError
      s!"executor for op '{opId}' on backend '{backend}' is already registered"
  executorTableRef.set (table.push ((backend, opId), e))

def getExecutor? (backend : Name) (opId : String) : IO (Option Executor) := do
  return (← executorTableRef.get).findSome? fun (k, e) =>
    if k == (backend, opId) then some e else none

/-- The three honest results of routing. Rendering each one distinctly is
the caller's job: a gap is a backlog item, tied routes are a developer
configuration error, and neither is a mathematical failure. -/
inductive RouteOutcome where
  | chosen (r : Route)
  | gap (g : CapabilityGap)
  | ambiguousRoutes (rs : Array Route)
  deriving Repr, Inhabited

/-- Select the implementation for a resolved method on a concrete receiver.

`o` must be the CONCRETE receiver — `res.concreteReceiver`, i.e. the
transported image when the resolution went through a functor. Passing the
original object there would route a module as a module and then execute it as
a set.

`routesConsidered` in a gap deliberately lists *every* route registered for
the method id, including the ones whose pattern did not match — that list is
the audit value of the gap. -/
def routeFor (env : Environment) (res : Resolution) (o : Obj) : RouteOutcome :=
  let all := routesFor env res.decl.id
  let applicable := all.filter (·.pattern.accepts o)
  if applicable.isEmpty then
    .gap {
      method := res.decl.id
      receiverCategory := res.profileEntry
      presentation := o.presentation
      semanticVia := res.via
      viaFunctor := res.viaFunctor
      routesConsidered := all
    }
  else
    let best := applicable.foldl (init := 0) fun p r => max p r.priority
    let top := applicable.filter (·.priority == best)
    match top[0]?, top.size with
    | some r, 1 => .chosen r
    | _, _ => .ambiguousRoutes top

/-- Run a selected route. Selection happened before execution, so a missing
executor is reported as an unavailable backend and never rerouted. -/
def execute (route : Route) (o : Obj) (args : Array Obj)
    : IO (Except ExecError Value) := do
  match ← getExecutor? route.backend route.opId with
  | some e => e route.opId o args
  | none =>
      return .error <| .backendUnavailable route.backend
        s!"no executor is registered for op '{route.opId}' on backend '{route.backend}'"

end CasDsl
