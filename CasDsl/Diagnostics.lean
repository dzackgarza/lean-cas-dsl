/-
Developer diagnostics: the ONE place where backend identity is visible.

`#explain_route` reports a routing decision WITHOUT taking it (the method is
never executed); `#capabilities` lists the semantic surface against the
registered implementations; `#capability_gaps` crosses the registered
representative presentations with the declared methods and reports the holes
as an auditable backlog.

These commands read the registries and name backends because that is their
job. They do not import any backend module: a backend's identity reaches
them as the `Route.backend` name, exactly as the router sees it, so adding a
backend never touches this file. (Live adapter provenance — `Sage.provenance`
and its siblings — would require a backend-specific import here; it is
deliberately left to the backend's own diagnostics.)
-/
import CasDsl.Syntax

namespace CasDsl

open Lean Elab Command
open Worker (emitOutput)

/-! ## Shared rendering -/

/-- Left-align in a column, never letting a long cell run into the next one. -/
private def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (max 1 (n - s.length)) ' ')

private def routeJson (r : Route) : Json :=
  Json.mkObj
    [("method", .str r.method.toString), ("pattern", .str (renderPattern r.pattern)),
     ("backend", .str r.backend.toString), ("opId", .str r.opId),
     ("priority", .num r.priority)]

/-! ## `#explain_route` -/

/-- The routing decision for one method call, taken apart. `functor?` is the
registered declaration behind a transport step, so the explanation can name
`source → target` rather than just the functor's name. -/
private structure Explanation where
  method : Name
  receiver : Obj
  res : Resolution
  functor? : Option FunctorDecl
  outcome : RouteOutcome

private def explain (ctx : EvalCtx) (e : CasExpr) : EvalM Explanation := do
  -- the prefix spelling IS a method call, rewritten exactly as `eval` does it
  let .method recvE m _ := (prefixMethodCall? ctx.isBound ctx.env e).getD e
    | throw (.msg "#explain_route needs a method call, e.g. `#explain_route n.factor()`")
  -- only the receiver is evaluated: explaining a route must not take it
  let some recv := (← eval ctx recvE).obj?
    | throw (.msg "the receiver of the explained call is not an object")
  match resolveMethod ctx.env recv m with
  | .error err => throw (.resolve m recv err)
  | .ok res =>
    return {
      method := m, receiver := recv, res
      functor? := res.viaFunctor.bind fun s => functorDecl? ctx.env s.functor
      outcome := routeFor ctx.env res (res.concreteReceiver recv)
    }

/-- The transport step, or the empty string when the method arrived without
one. `source → target` comes from the registration; a step whose functor is
not in the registry says so rather than inventing an edge. -/
private def transportLine (x : Explanation) : String :=
  match x.res.viaFunctor with
  | none => ""
  | some step =>
      let edge := match x.functor? with
        | some f => s!"{f.source} → {f.target}"
        | none => "source → target UNKNOWN: no such functor is registered"
      s!"transport:     functor {step.functor} : {edge}\n  \
image:         {step.image.presentation}\n  "

private def explanationText (x : Explanation) : String :=
  let head := s!"method:        {x.method}\n  \
receiver:      {x.receiver.presentation}\n  \
{transportLine x}\
profile entry: {renderCat x.res.profileEntry}\n  \
availability:  {renderVia x.res.profileEntry x.res.via}\n  "
  let tail := match x.outcome with
    | .chosen r =>
        s!"route:         backend {r.backend}, op {repr r.opId}, priority {r.priority}\n  \
pattern:       {renderPattern r.pattern}"
    | .gap g => renderGap g
    | .ambiguousRoutes rs =>
        let ls := String.intercalate "\n" (rs.toList.map fun r => s!"    - {renderRoute r}")
        s!"route:         AMBIGUOUS — {rs.size} routes tied on priority\n{ls}"
  s!"  {head}{tail}"

private def explanationJson (x : Explanation) : Json :=
  let decision := match x.outcome with
    | .chosen r =>
        Json.mkObj [("decision", .str "chosen"), ("route", routeJson r)]
    | .gap g =>
        Json.mkObj
          [("decision", .str "gap"),
           ("routesConsidered", .arr (g.routesConsidered.map routeJson))]
    | .ambiguousRoutes rs =>
        Json.mkObj
          [("decision", .str "ambiguous"), ("routes", .arr (rs.map routeJson))]
  let transport := match x.res.viaFunctor, x.functor? with
    | none, _ => Json.null
    | some step, f? =>
        Json.mkObj
          [("functor", .str step.functor.toString),
           ("source", match f? with | some f => .str f.source.toString | none => .null),
           ("target", match f? with | some f => .str f.target.toString | none => .null),
           ("image", .str step.image.presentation)]
  Json.mkObj
    [("method", .str x.method.toString),
     ("receiver", .str x.receiver.presentation),
     ("transport", transport),
     ("profileEntry", .str (renderCat x.res.profileEntry)),
     ("via", .arr ((x.res.via.map fun n => Json.str n.toString)).toArray),
     ("declaredOn", .str x.res.decl.receiver.toString),
     ("routing", decision)]

def elabExplainRoute (stx : Syntax) : CommandElabM Unit := do
  let e ← match toExpr stx with
    | .ok e => pure e
    | .error m => throwError m
  let ctx : EvalCtx := { env := ← getEnv }
  let x ← match ← (explain ctx e).run with
    | .ok x => pure x
    | .error err => throwError err.render
  logInfo (explanationText x)
  emitOutput {
    data :=
      [("text/plain", .str (explanationText x)),
       ("application/vnd.casdsl.route+json", explanationJson x)]
  }

/-! ## `#capabilities` -/

private def capabilityLines (env : Environment) : Array String × Array Json := Id.run do
  let mut lines : Array String := #[]
  let mut js : Array Json := #[]
  for d in methods env do
    let rs := routesFor env d.id
    let impl :=
      if rs.isEmpty then "NO ROUTE"
      else "; ".intercalate (rs.toList.map fun r =>
        s!"{renderPattern r.pattern} → {r.backend}:{r.opId}")
    lines := lines.push s!"  {pad d.id.toString 14}{pad d.receiver.toString 22}{impl}"
    if !d.doc.isEmpty then
      lines := lines.push s!"  {pad "" 36}{d.doc}"
    js := js.push <| Json.mkObj
      [("method", .str d.id.toString), ("receiver", .str d.receiver.toString),
       ("arity", .num d.arity), ("doc", .str d.doc),
       ("routes", .arr (rs.map routeJson))]
  return (lines, js)

def elabCapabilities : CommandElabM Unit := do
  let env ← getEnv
  let (lines, js) := capabilityLines env
  let orphans := (methods env).filter (routesFor env ·.id |>.isEmpty)
  let header := s!"  {pad "method" 14}{pad "receiver category" 22}routes"
  let footer :=
    if orphans.isEmpty then "  (every declared method has at least one route)"
    else s!"  {orphans.size} method(s) with no registered route: \
{", ".intercalate (orphans.toList.map (·.id.toString))}"
  let text := String.intercalate "\n" (header :: lines.toList ++ [footer])
  logInfo text
  emitOutput {
    data :=
      [("text/plain", .str text),
       ("application/vnd.casdsl.capabilities+json",
        Json.mkObj [("methods", .arr js)])]
  }

/-! ## `#capability_gaps`

The audit crosses the REGISTERED representative presentations with the
declared methods (a documented ceiling: not all conceivable objects). Four
outcomes are distinguished, and only the last three are backlog:

- implemented — resolves and routes;
- no route registered for the method at all;
- routes registered for the method, none matching this presentation;
- routes tied on priority (a developer configuration error). -/

private inductive GapClass where
  | implemented
  | noRoute
  | noMatchingRoute (considered : Nat)
  | tied (n : Nat)

private def gapClassText : GapClass → String
  | .implemented => "implemented"
  | .noRoute => "no route is registered for this method"
  | .noMatchingRoute n =>
      s!"no route matches this presentation ({n} registered for the method, none matching)"
  | .tied n => s!"{n} routes tied on priority (configuration error)"

private def gapClassTag : GapClass → String
  | .implemented => "implemented"
  | .noRoute => "no-route"
  | .noMatchingRoute _ => "no-matching-route"
  | .tied _ => "ambiguous-routes"

private def classify (env : Environment) (o : Obj) (m : Name)
    : Option (Resolution × GapClass) :=
  match resolveMethod env o m with
  | .error _ => none
  | .ok res =>
      match routeFor env res (res.concreteReceiver o) with
      | .chosen _ => some (res, .implemented)
      | .ambiguousRoutes rs => some (res, .tied rs.size)
      | .gap g =>
          some (res,
            if g.routesConsidered.isEmpty then .noRoute
            else .noMatchingRoute g.routesConsidered.size)

private def methodIds (env : Environment) : Array Name :=
  (methods env).foldl (init := #[]) fun acc d =>
    if acc.contains d.id then acc else acc.push d.id

def elabCapabilityGaps : CommandElabM Unit := do
  let env ← getEnv
  let mut lines : Array String := #[]
  let mut js : Array Json := #[]
  let mut implemented : Nat := 0
  for (label, o) in representatives env do
    for m in methodIds env do
      match classify env o m with
      | none => pure ()
      | some (_, .implemented) => implemented := implemented + 1
      | some (res, cls) =>
        lines := lines.push
          s!"  {pad label 18}{pad m.toString 14}{pad (renderCat res.profileEntry) 22}\
{gapClassText cls}"
        lines := lines.push
          s!"  {pad "" 32}available by: \
{renderSemanticPath res.profileEntry res.via res.viaFunctor}"
        js := js.push <| Json.mkObj
          [("representative", .str label), ("presentation", .str o.presentation),
           ("method", .str m.toString),
           ("receiverCategory", .str (renderCat res.profileEntry)),
           ("via", .arr ((res.via.map fun n => Json.str n.toString)).toArray),
           -- the transport step, when the method reached this representative
           -- through a functor: the image is what routing was attempted for
           ("transport", match res.viaFunctor with
             | some step =>
                 Json.mkObj [("functor", .str step.functor.toString),
                             ("image", .str step.image.presentation)]
             | none => .null),
           ("class", .str (gapClassTag cls))]
  let header :=
    if representatives env |>.isEmpty then
      "  (no representative presentations are registered — nothing to audit)"
    else s!"  {pad "representative" 18}{pad "method" 14}{pad "category" 22}status"
  let footer := s!"  {implemented} method/representative pair(s) are implemented; \
{js.size} are backlog."
  let text := String.intercalate "\n" (header :: lines.toList ++ [footer])
  logInfo text
  emitOutput {
    data :=
      [("text/plain", .str text),
       ("application/vnd.casdsl.gaps+json",
        Json.mkObj [("gaps", .arr js), ("implemented", .num implemented)])]
  }

/-! ## `#canonical_maps`

The coercion layer's audit surface (#9): the complete list of preferred
canonical maps the surface may insert, from the registry the prelude
filled. Semantic-layer data — unlike the other diagnostics it names no
backend, because there is none to name. -/

private def canonOpTag : CanonOp → String
  | .identity => "identity"
  | .intToRat => "intToRat"
  | .intToMod => "intToMod"

def elabCanonicalMaps : CommandElabM Unit := do
  let env ← getEnv
  let rules := canonicalMaps env
  let mut lines : Array String := #[]
  let mut js : Array Json := #[]
  for r in rules do
    let edge := s!"{renderDomainPattern r.src} → {renderDomainPattern r.tgt}"
    lines := lines.push s!"  {pad edge 12}{canonOpTag r.op}"
    if !r.doc.isEmpty then
      lines := lines.push s!"  {pad "" 12}{r.doc}"
    js := js.push <| Json.mkObj
      [("src", .str (renderDomainPattern r.src)),
       ("tgt", .str (renderDomainPattern r.tgt)),
       ("op", .str (canonOpTag r.op)), ("doc", .str r.doc)]
  let text :=
    if rules.isEmpty then
      "  (no preferred canonical maps are registered — the surface inserts \
no coercions)"
    else
      String.intercalate "\n" (s!"  {pad "map" 12}op" :: lines.toList)
  logInfo text
  emitOutput {
    data :=
      [("text/plain", .str text),
       ("application/vnd.casdsl.canonicalmaps+json",
        Json.mkObj [("canonicalMaps", .arr js)])]
  }

/-! ## Commands -/

/-- `#explain_route e.m(…)` reports how `m` became available for `e` and
which implementation would run it — WITHOUT running it. Only the receiver is
evaluated. -/
syntax (name := casExplainRoute) "#explain_route " casTerm : command

/-- `#capabilities` — every declared method against the routes registered
for it; methods with no route are flagged. -/
syntax (name := casCapabilities) "#capabilities" : command

/-- `#capability_gaps` — the registered representative presentations crossed
with the declared methods, reporting every pair that is mathematically
available but not currently executable. -/
syntax (name := casCapabilityGaps) "#capability_gaps" : command

/-- `#canonical_maps` — every registered preferred canonical map: the
complete, auditable list of coercions the surface may insert. -/
syntax (name := casCanonicalMaps) "#canonical_maps" : command

@[command_elab casExplainRoute]
def elabExplainRouteCmd : CommandElab := fun stx => elabExplainRoute stx[1]

@[command_elab casCapabilities]
def elabCapabilitiesCmd : CommandElab := fun _ => elabCapabilities

@[command_elab casCapabilityGaps]
def elabCapabilityGapsCmd : CommandElab := fun _ => elabCapabilityGaps

@[command_elab casCanonicalMaps]
def elabCanonicalMapsCmd : CommandElab := fun _ => elabCanonicalMaps

end CasDsl
