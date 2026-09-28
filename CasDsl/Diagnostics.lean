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

/-- Whether this process is the notebook worker (the kernelspec exports
`NBDSL_PROJECT` to it, and children inherit it). Under the kernel the MIME
bundle is the ONE emission — `logInfo` would render the same text twice;
outside it (plain `lake env lean`, the `#guard_msgs` wording pins) the
bundle has no renderer and `logInfo` is the one emission. -/
initialize underNotebookKernel : Bool ← do
  return (← IO.getEnv "NBDSL_PROJECT").isSome

/-- Emit a diagnostic ONCE: as its bundle under the kernel, as an info
message anywhere else (one emission per event — DESIGN.md ruling 3). A
markdown rendering, when given, joins the bundle so the notebook typesets
the mathematics and links the docs; the plain text stays the fallback. -/
private def emitDiagnostic (text : String) (mime : String) (payload : Json)
    (markdown : Option String := none) : CommandElabM Unit := do
  unless underNotebookKernel do logInfo text
  emitOutput { data :=
    [("text/plain", .str text)]
    ++ (markdown.toList.map fun m => ("text/markdown", Json.str m))
    ++ [(mime, payload)] }

/-- Left-align in a column, never letting a long cell run into the next one. -/
private def pad (s : String) (n : Nat) : String :=
  s ++ String.ofList (List.replicate (max 1 (n - s.length)) ' ')

private def routeJson (r : Route) : Json :=
  Json.mkObj
    [("method", .str r.method.toString), ("pattern", .str (renderPattern r.pattern)),
     ("backend", .str r.backend.toString), ("opId", .str r.opId),
     ("priority", .num r.priority), ("doc", .str r.doc), ("docUrl", .str r.docUrl)]

/-! ## `#explain_route` -/

/-- The routing decision for one method call, taken apart: the receiver, the registry's
resolution (rendered route) and the chosen realization, with the method's surface signature and
the chosen op's declared signature. -/
private structure Explanation where
  method : Name
  receiver : Obj
  route : String
  decl : MethodDecl
  outcome : Realization
  sig? : Option OpSig

private def explain (ctx : EvalCtx) (e : CasExpr) : EvalM Explanation := do
  -- the prefix spelling IS a method call, rewritten exactly as `eval` does it
  let .method recvE m args := (prefixMethodCall? ctx.isBound ctx.env e).getD e
    | throw (.msg "#explain_route needs a method call, e.g. `#explain_route n.factor()`")
  -- only the receiver is evaluated: explaining a route must not take it
  let some recv := (← eval ctx recvE).obj?
    | throw (.msg "the receiver of the explained call is not an object")
  let outcome ← match ← (realizationOf ctx.env recv m (!args.isEmpty) : IO _) with
    | .ok o => pure o
    | .error err => throw (.msg err)
  let route := match outcome with
    | .lean _ r | .backend _ _ r => r
    | .gap g => g.route
    | .tied _ => ""
  return {
    method := m, receiver := recv, route
    decl := ((methodDecls ctx.env m)[0]?).getD { id := m }
    outcome
    sig? := match outcome with
      | .backend r _ _ => opSig? ctx.env r.backend r.opId
      | _ => none }

/-- The availability path: the receiver, the category it is a point of, and the registry's route
of structural functors to the method's owner (owner ruling 2026-08-06: availability is a path of
functors). -/
private def chainText (x : Explanation) : String :=
  let start := match x.receiver with
    | .elem d v => s!"{v.render} ⟶ {d.render}"
    | o => o.presentation
  s!"{start}\n  resolved: {x.route}"

/-- What a trusted answer is an answer TO: the method's meaning (the registered functor named in
the route), its documentation and generality-level conventions. -/
private def meaningText (x : Explanation) : String :=
  let head := if x.decl.anchor == .anonymous then s!"{x.method}"
    else s!"{x.method} ≐ {x.decl.anchor}"
  let doc := if x.decl.doc.isEmpty then "" else s!": {x.decl.doc}"
  let conv := if x.decl.conventions.isEmpty then "" else s!" — {x.decl.conventions}"
  head ++ doc ++ conv

/-- The chosen implementation: the backend and the REAL function it runs
(the wire op id stays in the JSON payload), its op-level conventions, its
standing advisory, and the EXTERNAL documentation link. -/
private def routeText (x : Explanation) (r : Route) : String :=
  let fn := match x.sig? with
    | some sig => if sig.backendFn.isEmpty then s!"op {repr r.opId}" else sig.backendFn
    | none => s!"op {repr r.opId}"
  let conv := match x.sig? with
    | some sig => if sig.conventions.isEmpty then "" else s!" — {sig.conventions}"
    | none => ""
  let sigDoc := match x.sig? with
    | some sig => if sig.doc.isEmpty then "" else s!"\n{sig.doc}"
    | none => ""
  let advisory := match x.sig? with
    | some sig => if sig.advisory.isEmpty then "" else s!"\nadvisory: {sig.advisory}"
    | none => ""
  let docs :=
    let url := if r.docUrl.isEmpty then (x.sig?.map (·.docUrl)).getD "" else r.docUrl
    if url.isEmpty then "" else s!"\ndocs: {url}"
  s!"via {r.backend}, {fn}{conv}"
  ++ (if r.priority == 0 then "" else s!" (priority {r.priority})")
  ++ (if r.doc.isEmpty then "" else s!"\n{r.doc}")
  ++ sigDoc ++ advisory ++ docs

private def explanationText (x : Explanation) : String :=
  let tail := match x.outcome with
    | .lean _ _ => "via composed Lean-native actions (a Lean-checked computation)"
    | .backend r _ _ =>
        routeText x r
        ++ (if x.decl.resultDoc.isEmpty then ""
            else s!"\nresult: {x.decl.resultDoc}")
    | .gap g => renderGap g
    | .tied rs =>
        let ls := String.intercalate "\n" (rs.toList.map fun r => s!"  - {renderRoute r}")
        s!"route: AMBIGUOUS — {rs.size} implementations tied on priority \
(a configuration error):\n{ls}"
  s!"{chainText x}\n{meaningText x}\n{tail}"

/-- A name inside math mode: `\mathrm` for the ASCII identifiers Mathlib
class names are, `\text` for anything carrying notation of its own. -/
private def mathName (s : String) : String :=
  if s.all (fun c => c.isAlphanum || c == '.' || c == '_') then s!"\\mathrm\{{s}}"
  else s!"\\text\{{s}}"

/-- The markdown rendering: the same sentences, typeset — the chain as
inline math, the docs link clickable, the method doc's own `$…$` left for
MathJax. -/
private def explanationMarkdown (x : Explanation) : String :=
  let start := match x.receiver with
    | .elem d v =>
        let vl := (v.latex?).getD s!"\\text\{{v.render}}"
        s!"{vl} \\longrightarrow {d.latex}"
    | o => (o.latex?).getD s!"\\text\{{o.presentation}}"
  let chainLine := s!"${start}$ — resolved: `{x.route}`"
  let meaningLine :=
    let head := if x.decl.anchor == .anonymous then s!"**{x.method}**"
      else s!"**{x.method}** ≐ `{x.decl.anchor}`"
    let doc := if x.decl.doc.isEmpty then "" else s!": {x.decl.doc}"
    let conv := if x.decl.conventions.isEmpty then "" else s!" — {x.decl.conventions}"
    head ++ doc ++ conv
  let tail := match x.outcome with
    | .lean _ _ => "via composed Lean-native actions (a Lean-checked computation)"
    | .backend r _ _ =>
        let url := if r.docUrl.isEmpty
          then (x.sig?.map (fun (s : OpSig) => s.docUrl)).getD "" else r.docUrl
        let fn := match x.sig? with
          | some sig => if sig.backendFn.isEmpty then s!"op `{r.opId}`" else s!"`{sig.backendFn}`"
          | none => s!"op `{r.opId}`"
        let fnLinked := if url.isEmpty then fn else s!"[{fn}]({url})"
        let conv := match x.sig? with
          | some sig => if sig.conventions.isEmpty then "" else s!" — {sig.conventions}"
          | none => ""
        let advisory := match x.sig? with
          | some sig => if sig.advisory.isEmpty then "" else s!"\n\n*advisory: {sig.advisory}*"
          | none => ""
        s!"via {r.backend}, {fnLinked}{conv}"
        ++ (if r.doc.isEmpty then "" else s!"\n\n{r.doc}")
        ++ advisory
        ++ (if x.decl.resultDoc.isEmpty then "" else s!"\n\nresult: {x.decl.resultDoc}")
    | .gap g => renderGap g
    | .tied _ => ""  -- the plain text carries the configuration error
  s!"{chainLine}\n\n{meaningLine}\n\n{tail}"

private def explanationJson (x : Explanation) : Json :=
  let decision := match x.outcome with
    | .lean _ _ => Json.mkObj [("decision", .str "lean")]
    | .backend r _ _ =>
        Json.mkObj
          [("decision", .str "chosen"), ("route", routeJson r),
           ("backendFn", .str ((x.sig?.map (·.backendFn)).getD "")),
           ("opConventions", .str ((x.sig?.map (·.conventions)).getD "")),
           ("opDoc", .str ((x.sig?.map (·.doc)).getD "")),
           ("advisory", .str ((x.sig?.map (·.advisory)).getD "")),
           ("docs", .str (if r.docUrl.isEmpty then
             (x.sig?.map (·.docUrl)).getD "" else r.docUrl))]
    | .gap g =>
        Json.mkObj
          [("decision", .str "gap"),
           ("routesConsidered", .arr (g.routesConsidered.map routeJson))]
    | .tied rs =>
        Json.mkObj
          [("decision", .str "ambiguous"), ("routes", .arr (rs.map routeJson))]
  Json.mkObj
    [("method", .str x.method.toString),
     ("receiver", .str x.receiver.presentation),
     ("resolution", .str x.route),
     ("routing", decision)]

def elabExplainRoute (stx : Syntax) : CommandElabM Unit := do
  let e ← match ← toExpr stx with
    | .ok e => pure e
    | .error m => throwError m
  let ctx : EvalCtx := { env := ← getEnv, notes := ← IO.mkRef #[],
                         annotations := ← IO.mkRef #[] }
  let x ← match ← (explain ctx e).run with
    | .ok x => pure x
    | .error err => throwError err.render
  emitDiagnostic (explanationText x) "application/vnd.casdsl.route+json"
    (explanationJson x) (markdown := some (explanationMarkdown x))

/-! ## `#capabilities` -/

/-- Each method in the register `#explain_route` speaks: the method ≐ its
anchor with its declaring category, then the implementations as routes
naming the REAL backend functions — never a table of record fields. -/
private def capabilityLines (env : Environment) (state : CasCatalogue.RegistryState) :
    Array String × Array Json := Id.run do
  -- a method's owners are the registry's method (or property) rows of its name
  let owned (m : Name) : String :=
    let ms := (state.methods.filter (·.name == m.toString)).map fun r =>
      s!"{state.categoryName r.owner} ({r.functor.raw})"
    let ps := (state.properties.filter (·.name == m.toString)).map fun p => p.classifier.raw
    let all := ms ++ ps
    if all.isEmpty then "(no registered owner)" else ", ".intercalate all.toList
  let mut lines : Array String := #[]
  let mut js : Array Json := #[]
  for d in methods env do
    let rs := routesFor env d.id
    let anchor := if d.anchor == .anonymous then "" else s!" ≐ {d.anchor}"
    let impl :=
      if rs.isEmpty then "NO ROUTE is registered"
      else "; ".intercalate (rs.toList.map fun r =>
        let fn := match opSig? env r.backend r.opId with
          | some sig => if sig.backendFn.isEmpty then s!"op {repr r.opId}" else sig.backendFn
          | none => s!"op {repr r.opId}"
        s!"{renderPattern r.pattern} → {r.backend} {fn}")
    let owners := owned d.id
    lines := lines.push s!"{d.id}{anchor} — owned by {owners}"
    lines := lines.push s!"  {impl}"
    if !d.doc.isEmpty then
      lines := lines.push s!"  {d.doc}"
    js := js.push <| Json.mkObj
      [("method", .str d.id.toString), ("owners", .str (owned d.id)),
       ("arity", .num d.arity), ("doc", .str d.doc),
       ("anchor", .str (if d.anchor == .anonymous then "" else d.anchor.toString)),
       -- the declaration's advisory TEMPLATE, `{…}` placeholders as declared
       ("advisory", .str d.advisory),
       ("routes", .arr (rs.map routeJson))]
  return (lines, js)

def elabCapabilities : CommandElabM Unit := do
  let env ← getEnv
  let (lines, js) := capabilityLines env (← liftTermElabM CasCatalogue.registryState)
  let orphans := (methods env).filter (routesFor env ·.id |>.isEmpty)
  let footer :=
    if orphans.isEmpty then "(every declared method has at least one route)"
    else s!"methods with no registered route: \
{", ".intercalate (orphans.toList.map (·.id.toString))}"
  let text := String.intercalate "\n" (lines.toList ++ [footer])
  emitDiagnostic text "application/vnd.casdsl.capabilities+json"
    (Json.mkObj [("methods", .arr js)])

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

private def gapClassTag : GapClass → String
  | .implemented => "implemented"
  | .noRoute => "no-route"
  | .noMatchingRoute _ => "no-matching-route"
  | .tied _ => "ambiguous-routes"

private def classify (env : Environment) (o : Obj) (m : Name) (arity : Nat) :
    IO (Option (String × GapClass)) := do
  match ← realizationOf env o m (arity > 0) with
  | .error _ => return none
  | .ok (.lean _ route) | .ok (.backend _ _ route) => return some (route, .implemented)
  | .ok (.tied rs) => return some ("", .tied rs.size)
  | .ok (.gap g) =>
      return some (g.route,
        if g.routesConsidered.isEmpty then .noRoute
        else .noMatchingRoute g.routesConsidered.size)

private def methodIds (env : Environment) : Array Name :=
  (methods env).foldl (init := #[]) fun acc d =>
    if acc.contains d.id then acc else acc.push d.id

def elabCapabilityGaps : CommandElabM Unit := do
  let env ← getEnv
  -- grouped by method: sixty near-identical rows compress to one line per
  -- method naming the presentations it gaps on. The per-pair record —
  -- category, availability path, transport — stays in the JSON payload
  let mut groups : Array (Name × String × Array String) := #[]
  let mut js : Array Json := #[]
  let mut implemented : Nat := 0
  for (label, o) in representatives env do
    for m in methodIds env do
      let arity := ((methodDecls env m)[0]?.map (·.arity)).getD 0
      match ← classify env o m arity with
      | none => pure ()
      | some (_, .implemented) => implemented := implemented + 1
      | some (route, cls) =>
        let short := match cls with
          | .implemented => "implemented"
          | .noRoute => "no route registered"
          | .noMatchingRoute _ => "no route accepts"
          | .tied n => s!"{n} routes tied on priority (configuration error)"
        match groups.findIdx? (fun (m', s, _) => m' == m && s == short) with
        | some i =>
            let (m', s, ls) := groups[i]!
            groups := groups.set! i (m', s, ls.push label)
        | none => groups := groups.push (m, short, #[label])
        js := js.push <| Json.mkObj
          [("representative", .str label), ("presentation", .str o.presentation),
           ("method", .str m.toString),
           ("resolution", .str route),
           ("class", .str (gapClassTag cls))]
  let lines := groups.map fun (m, short, ls) =>
    s!"  {pad m.toString 18}{short}: {"; ".intercalate ls.toList}"
  let header :=
    if representatives env |>.isEmpty then
      "  (no representative presentations are registered — nothing to audit)"
    else "  method            unimplemented for"
  let footer := s!"  implemented: {implemented} method/representative pairs; \
unimplemented: {js.size}."
  let text := String.intercalate "\n" (header :: lines.toList ++ [footer])
  emitDiagnostic text "application/vnd.casdsl.gaps+json"
    (Json.mkObj [("gaps", .arr js), ("implemented", .num implemented)])

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
      "  (no preferred canonical maps are registered — no coercions are \
ever inserted)"
    else
      String.intercalate "\n" (s!"  {pad "map" 12}op" :: lines.toList)
  emitDiagnostic text "application/vnd.casdsl.canonicalmaps+json"
    (Json.mkObj [("canonicalMaps", .arr js)])

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
