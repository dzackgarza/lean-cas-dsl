/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Registry
public import CasContract.Failure

@[expose] public section

/-!
# Method resolution by structural projection (#53 §8, CC-TRANSPORT, CC-UNIFORM, CC-RESOLVE)

`receiver.method` for a receiver in the category `A` resolves to a *route*: a composite
`U : A → C` of structural functors ending at the method's owner `C`, followed by the method's
registered functor `M` (on `C`, or on `Core(C)` for an isomorphism invariant). The value is
`M(U(x))`, never a value of `x` (CC-TRANSPORT): the semantic reading (`CasCatalogue.Semantic`)
forms it, and the realized reading (`CasCatalogue.Realize`) evaluates the same term.

* **One kind of edge** (CC-UNIFORM). The edges are the registered functor rows marked
  `structural` together with the classifier forgetful functors `total(c) → host(c)` of the
  registered classifier totals. Inclusions, forgetful functors, fibre inclusions and fibration
  projections are all such rows; nothing is consulted "first".
* **No selection rule** (CC-RESOLVE). Every route is enumerated. None is an error; more than one
  is an ambiguity listing every route. No shortest-path, declaration-order or priority rule picks
  one. Identifying two routes needs a registered comparison (CC-COHERE); a caller may instead
  name functors the route must pass through (`via`), which selects a port without choosing by
  order.
* **Provenance** is the route itself: its steps and their composite.

Construction functors (base change, change of values, reindexing along a parameter morphism) are
not edges: they need data the receiver does not carry.
-/

open Lean Meta Elab Term Command

namespace CasCatalogue

/-- A resolved method call: the method row, the route to its owner, and the registered
comparisons that identified every other candidate route with it (its provenance). -/
structure Resolution where
  method : MethodEntry
  route : Route
  comparisons : Array NaturalTransformationId := #[]
  /-- For a method that returns to the source side, the registered lift serving each route
  step (CC-LIFT). -/
  lifts : Array LiftId := #[]

instance : Inhabited Resolution :=
  ⟨{ method := { id := default, name := "", owner := .atom default, functor := ⟨""⟩
                 shape := .object }
     route := { source := .atom default, target := .atom default, steps := #[] } }⟩

/-- Whether `a` becomes `b` by replacing one occurrence of `left` with `right`. -/
def rewritesTo (a b left right : Array EdgeRef) : Bool :=
  (List.range (a.size + 1)).any fun i =>
    a.extract i (i + left.size) == left &&
      b == a.extract 0 i ++ right ++ a.extract (i + left.size) a.size

/-- The registered comparisons from route `a` to route `b` (CC-COHERE): invertible cells between
two distinct structural composites, whose `left` occurs in `a` and is replaced by their `right` in
`b`. -/
def RegistryState.comparisonsFrom (state : RegistryState) (a b : Route) :
    Array NaturalTransformationId :=
  (state.cells.filter fun c =>
      c.invertible && c.left != c.right && !c.left.isEmpty && !c.right.isEmpty &&
        rewritesTo a.refs b.refs c.left c.right).map (·.id)

/-- A class of routes identified by registered comparisons. -/
structure CoherenceClass (α : Type) where
  members : Array α
  /-- The comparisons used to identify the members. -/
  comparisons : Array NaturalTransformationId
  /-- Pairs of members related by more than one comparison: an ambiguity (no comparison is
  chosen). -/
  ambiguities : Array (α × α × Array NaturalTransformationId)
  /-- The members no comparison points into: the route a call runs on is the unique one. -/
  sources : Array α

/-- Partition candidates into classes of routes connected by registered comparisons; only
candidates with the same `key` (the same method or property) are ever identified. A comparison is
directed (its `left` to its `right`); a class's call runs on its unique source route, so no route
is chosen by an order of candidates, rows or renderings. -/
def RegistryState.classify {α : Type} [Inhabited α] (state : RegistryState) (candidates : Array α)
    (key : α → String) (route : α → Route) : Array (CoherenceClass α) := Id.run do
  let n := candidates.size
  let mut classOf : Array Nat := Array.range n
  let mut incoming : Array Bool := Array.replicate n false
  let mut used : Array NaturalTransformationId := #[]
  let mut ambiguities : Array (Nat × Nat × Array NaturalTransformationId) := #[]
  for i in [0:n] do
    for j in [0:n] do
      if i != j && key candidates[i]! == key candidates[j]! then
        let cells := state.comparisonsFrom (route candidates[i]!) (route candidates[j]!)
        if cells.size > 1 then
          ambiguities := ambiguities.push (i, j, cells)
        unless cells.isEmpty do
          incoming := incoming.set! j true
          let (ci, cj) := (classOf[i]!, classOf[j]!)
          if ci != cj then
            classOf := classOf.map fun k => if k == cj then ci else k
          for c in cells do
            unless used.contains c do used := used.push c
  let reps := (classOf.toList.eraseDups).toArray
  return reps.map fun r =>
    let indices := (Array.range n).filter (classOf[·]! == r)
    { members := indices.map (candidates[·]!)
      comparisons := if indices.size > 1 then used else #[]
      ambiguities := (ambiguities.filter fun (i, _, _) => classOf[i]! == r).map
        fun (i, j, cells) => (candidates[i]!, candidates[j]!, cells)
      sources := (indices.filter (!incoming[·]!)).map (candidates[·]!) }

/-- Classes of method candidates. -/
def RegistryState.coherenceClasses (state : RegistryState) (candidates : Array Resolution) :
    Array (CoherenceClass Resolution) :=
  state.classify candidates (·.method.id.raw) (·.route)

/-- A resolved property query: the property row, its classifier, the route to the classifier's
host, and the comparisons that identified other routes with it. -/
structure PropertyResolution where
  property : PropertyEntry
  classifier : ClassifierEntry
  route : Route
  comparisons : Array NaturalTransformationId := #[]

instance : Inhabited PropertyResolution :=
  ⟨{ property := { id := default, name := "", classifier := default }
     classifier := { id := default, declaration := .anonymous, host := .atom default
                     realization := .anonymous }
     route := { source := .atom default, target := .atom default, steps := #[] } }⟩

/-- Why a method call does not resolve. -/
inductive ResolutionError
  /-- No method row has this name. -/
  | unknownMethod (name : String)
  /-- Methods with this name exist, but no structural route reaches an owner. -/
  | notApplicable (name : String) (owners : Array CategoryExpr)
  /-- Several routes reach an owner, and nothing identifies them. -/
  | ambiguous (name : String) (candidates : Array Resolution)
  /-- Several routes reach the host of a property's classifier, and nothing identifies them. -/
  | ambiguousProperty (name : String) (candidates : Array PropertyResolution)
  /-- The method's result must return to the receiver's side, and a route step has no
  registered lift of subobjects. -/
  | missingLift (name : String) (resolution : Resolution) (step : EdgeRef)
  /-- Two routes are related by several registered comparisons; none is chosen. -/
  | ambiguousComparison (name : String) (a b : Route) (cells : Array NaturalTransformationId)
  /-- Identified routes with no unique source route to run on. -/
  | noSourceRoute (name : String) (sources : Array Route)

/-- The display name of a category expression: its registered id, if it has one. -/
partial def RegistryState.categoryName (state : RegistryState) (expression : CategoryExpr) :
    String :=
  match state.categories.find? (·.expression.syntacticEq expression) with
  | some entry => entry.id.raw
  | none =>
      let parameter : ParameterExpr → String := fun
        | .variable id => id.raw
        | _ => "…"
      match expression with
      | .atom id | .opaque id => id.raw
      | .construct constructor args =>
          let rendered := args.toList.map fun
            | .category category => state.categoryName category
            | .object id => id.raw
            | .functor id => id.raw
          s!"{constructor.raw}({", ".intercalate rendered})"
      | .familyApp family args => s!"{family.raw}({", ".intercalate (args.toList.map parameter)})"
      | .familyTotal family => s!"total({family.raw})"
      | .classifierTotal classifier => s!"total({classifier.raw})"
      | .refine base classifier => s!"{state.categoryName base}|{classifier.raw}"

/-- A route, rendered as `A --F--> B --G--> C`. -/
def RegistryState.renderRoute (state : RegistryState) (route : Route) : String :=
  route.steps.foldl (init := state.categoryName route.source) fun acc edge =>
    s!"{acc} --{edge.ref.label}--> {state.categoryName edge.target}"

/-- A resolution, rendered with its method functor. -/
def RegistryState.renderResolution (state : RegistryState) (resolution : Resolution) : String :=
  let shape := match resolution.method.shape with
    | .object => ""
    | .isoInvariant => " on the core"
  let comparisons := if resolution.comparisons.isEmpty then "" else
    s!" ; identified by {resolution.comparisons.toList.map (·.raw)}"
  let lifts := if resolution.lifts.isEmpty then "" else
    s!" ; lifted back by {resolution.lifts.toList.map (·.raw)}"
  s!"{state.renderRoute resolution.route} ; {resolution.method.id.raw} = \
    {resolution.method.functor.raw}{shape}{comparisons}{lifts}"

/-- A property resolution, rendered. -/
def RegistryState.renderPropertyResolution (state : RegistryState)
    (resolution : PropertyResolution) : String :=
  let comparisons := if resolution.comparisons.isEmpty then "" else
    s!" ; identified by {resolution.comparisons.toList.map (·.raw)}"
  s!"{state.renderRoute resolution.route} ; {resolution.property.id.raw} = \
    {resolution.classifier.id.raw}{comparisons}"

def ResolutionError.render (state : RegistryState) : ResolutionError → String
  | .unknownMethod name => s!"no method is named `{name}`"
  | .notApplicable name owners =>
      s!"`{name}` is not available here: no structural route reaches its owner(s) \
        {owners.toList.map state.categoryName}"
  | .ambiguous name candidates =>
      s!"`{name}` is ambiguous: {candidates.size} structural routes and no registered \
        comparison identifies them:\n" ++
        "\n".intercalate (candidates.toList.map fun c => "  " ++ state.renderResolution c)
  | .missingLift name resolution step =>
      s!"`{name}` resolves to {state.renderResolution resolution}, but its result must return \
        to the receiver's side and no lift of subobjects is registered along {step.label} \
        (CC-LIFT)"
  | .ambiguousComparison name a b cells =>
      s!"`{name}`: the routes {state.renderRoute a} and {state.renderRoute b} are related by \
        several registered comparisons {cells.toList.map (·.raw)}; choosing one is not made here"
  | .noSourceRoute name sources =>
      s!"`{name}`: the identified routes have {sources.size} source routes under their \
        comparisons, so none is designated to run on:\n" ++
        "\n".intercalate (sources.toList.map fun r => "  " ++ state.renderRoute r)
  | .ambiguousProperty name candidates =>
      s!"`{name}` is ambiguous: {candidates.size} structural routes and no registered \
        comparison identifies them:\n" ++
        "\n".intercalate
          (candidates.toList.map fun c => "  " ++ state.renderPropertyResolution c)

/-- Resolve `receiver.name`, optionally requiring the route to pass through the functors `via`. -/
def RegistryState.resolveMethod (state : RegistryState) (receiver : CategoryExpr) (name : String)
    (through : Array FunctorId := #[]) : Except ResolutionError Resolution := do
  let methods := state.methods.filter (·.name == name)
  if methods.isEmpty then throw (.unknownMethod name)
  let candidates := methods.flatMap fun method =>
    ((state.routes receiver method.owner).filter fun route =>
        through.all fun id => route.functorIds.contains id).map fun route =>
      { method, route : Resolution }
  if candidates.isEmpty then throw (.notApplicable name (methods.map (·.owner)))
  match (state.coherenceClasses candidates).toList with
  | [cls] =>
      -- One semantic route (#53 §8 steps 6–7), run on the source of its comparisons.
      if let some (a, b, cells) := cls.ambiguities[0]? then
        throw (.ambiguousComparison name a.route b.route cells)
      let #[source] := cls.sources
        | throw (.noSourceRoute name (cls.sources.map (·.route)))
      let resolution := { source with comparisons := cls.comparisons }
      if !resolution.method.returnsToSource then return resolution
      let mut lifts := #[]
      for step in resolution.route.refs do
        match state.lifts.find? (fun l => l.kind == .subobjects && l.edge == step) with
        | some lift => lifts := lifts.push lift.id
        | none => throw (.missingLift name resolution step)
      pure { resolution with lifts }
  | _ => throw (.ambiguous name candidates)

/-- How a limit of a registered shape in a registered category is computed (CC-UNIV, CC-LIFT): a
registered presentation in the category itself, or one in the target of a registered creation lift
out of it, returned along that lift, which the resolution names. -/
structure LimitResolution where
  limit : LimitId
  lift : Option LiftId := none
  deriving Repr, BEq

/-- Resolve a limit (or, with `colimit`, a colimit) of shape `shape` in `category`: its own
registered presentation, else, for a limit, the unique registered creation lift of `shape` limits
out of `category` into a category with one. -/
def RegistryState.resolveLimit (state : RegistryState) (category : CategoryId) (shape : String)
    (colimit : Bool := false) : Except String LimitResolution := do
  let direct := state.limits.filter fun l =>
    l.colimit == colimit && l.category == category && l.shape == shape
  if let some l := direct[0]? then
    if direct.size > 1 then throw s!"{category.raw} has {direct.size} registered {shape} limits"
    return { limit := l.id }
  let some entry := state.categories.find? (·.id == category)
    | throw s!"{category.raw} is not a registered category"
  -- Creation lifts return limits only.
  if colimit then
    throw s!"no {shape} colimit is registered in {category.raw}"
  let returned := state.lifts.filterMap fun lift => do
    guard (lift.kind == .createsLimits shape)
    let edge ← state.structuralEdge? lift.edge
    guard (edge.source.syntacticEq entry.expression)
    let target ← state.category? edge.target
    let limit ← state.limits.find? fun l => !l.colimit && l.category == target.id && l.shape == shape
    pure ({ limit := limit.id, lift := some lift.id } : LimitResolution)
  match returned.toList with
  | [r] => return r
  | [] => throw s!"no {shape} limit is registered in {category.raw} or returned to it along a \
      registered lift"
  | _ => throw s!"{shape} limits in {category.raw} are returned along several lifts"

/-- Resolve the property query `receiver.name` (CC-PROP): a property row with this name (an
alias only on its own receiver), and the unique route to its classifier's host. -/
def RegistryState.resolveProperty (state : RegistryState) (receiver : CategoryExpr)
    (name : String) (through : Array FunctorId := #[]) :
    Except ResolutionError PropertyResolution := do
  let named := state.properties.filter (·.name == name)
  if named.isEmpty then throw (.unknownMethod name)
  let applicable := named.filter fun p => p.receiver.all (·.syntacticEq receiver)
  let entries := applicable.filterMap fun p =>
    (state.classifier? p.classifier).map fun c => (p, c)
  let candidates := entries.flatMap fun (property, classifier) =>
    ((state.routes receiver classifier.host).filter fun route =>
        through.all fun id => route.functorIds.contains id).map fun route =>
      { property, classifier, route : PropertyResolution }
  if candidates.isEmpty then
    throw (.notApplicable name (entries.map (·.2.host)))
  match (state.classify candidates (·.property.id.raw) (·.route)).toList with
  | [cls] =>
      if let some (a, b, cells) := cls.ambiguities[0]? then
        throw (.ambiguousComparison name a.route b.route cells)
      let #[source] := cls.sources
        | throw (.noSourceRoute name (cls.sources.map (·.route)))
      pure { source with comparisons := cls.comparisons }
  | _ => throw (.ambiguousProperty name candidates)

/-! ## The generated operation surface (CC-CLOSURE) -/

/-- One operation available on a receiver, with how it is reached. -/
structure ClosureRow where
  name : String
  /-- `method` or `property`. -/
  kind : String
  /-- Whether the call resolves (`some` route rendering) or why not (`none`, with `status`). -/
  resolved : Bool
  status : String

/-- The receiver's arrow category `Arr(A)`, through the registered arrow constructor. -/
def RegistryState.arrowsOf? (state : RegistryState) (receiver : CategoryExpr) :
    Option CategoryExpr :=
  (state.constructors.find? (·.semantics == `CasCatalogue.Constructors.arrow)).map fun entry =>
    .construct entry.id #[.category receiver]

/-- The operations available on `receiver`: every method and property whose owner is reachable by
structural routes, with the route, or with the reason it does not resolve (ambiguity, a missing
lift). Nothing here is declared per receiver: the surface is computed from the registry (#53 §8
"Static closure"), and no leaf changes it. -/
def RegistryState.closure (state : RegistryState) (receiver : CategoryExpr) : Array ClosureRow :=
  let methodNames := (state.methods.map (·.name)).toList.eraseDups
  let propertyNames := (state.properties.map (·.name)).toList.eraseDups
  let methods := methodNames.filterMap fun name =>
    match state.resolveMethod receiver name with
    | .ok r => some { name, kind := "method", resolved := true
                      status := state.renderResolution r : ClosureRow }
    | .error (.notApplicable ..) | .error (.unknownMethod _) => none
    | .error e => some { name, kind := "method", resolved := false, status := e.render state }
  let properties := propertyNames.filterMap fun name =>
    match state.resolveProperty receiver name with
    | .ok r => some { name, kind := "property", resolved := true
                      status := state.renderPropertyResolution r : ClosureRow }
    | .error (.notApplicable ..) | .error (.unknownMethod _) => none
    | .error e => some { name, kind := "property", resolved := false, status := e.render state }
  (methods ++ properties).toArray

/-- Report the operation surface of a registered category: on its objects, and on its morphisms
(the arrow category). -/
def closureReport (category : String) : TermElabM String := do
  let state ← registryState
  let some entry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let render (rows : Array ClosureRow) : String :=
    "\n".intercalate (rows.toList.map fun row =>
      s!"  {row.name} ({row.kind}){if row.resolved then "" else " [unavailable]"}: {row.status}")
  let objects := state.closure entry.expression
  let morphisms := match state.arrowsOf? entry.expression with
    | some arrows => state.closure arrows
    | none => #[]
  return s!"on objects of {category}:\n{render objects}\non morphisms of {category}:\n\
    {render morphisms}"

def reportClosure (category : String) : TermElabM Unit := do
  logInfo (← closureReport category)

/-! ## Elaboration: the composite as a checked Lean term -/

/-- The typed symbolic composite of a route, as a Lean `Expr` of type `FunctorExpr A B`. Lean
checks that consecutive steps share their middle category. -/
def Route.compositeExpr (route : Route) : MetaM Expr := do
  let mut acc := mkApp (mkConst ``FunctorExpr.identity) (toExpr route.source)
  for edge in route.steps do
    acc ← mkAppM ``FunctorExpr.comp #[acc, toExpr edge.expression]
  return acc

/-- The object a method's functor receives: the image itself, or, for an iso-invariant method (a
functor on the core), the same object as an object of the core. -/
def methodArgument (method : MethodEntry) (image : Expr) : MetaM Expr :=
  match method.shape with
  | .isoInvariant => mkAppM ``CategoryTheory.Core.mk #[image]
  | _ => pure image

/-- Report the resolution of `name` on the category `category`, or why there is none. -/
def reportResolution (name category : String) (through : Array String) : TermElabM Unit := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  match state.resolveMethod categoryEntry.expression name (through.map fun raw => ⟨raw⟩) with
  | .ok resolution =>
      discard <| resolution.route.compositeExpr
      logInfo m!"{state.renderResolution resolution}"
  | .error error => throwStratum .invalid (error.render state)

end CasCatalogue
