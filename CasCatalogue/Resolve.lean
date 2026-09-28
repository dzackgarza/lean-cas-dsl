/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Registry.Extension

@[expose] public section

/-!
# Method resolution by structural projection (#53 §8, CC-TRANSPORT, CC-UNIFORM, CC-RESOLVE)

`receiver.method` for a receiver in the category `A` resolves to a *route*: a composite
`U : A → C` of structural functors ending at the method's owner `C`, followed by the method's
registered functor `M` (on `C`, or on `Core(C)` for an isomorphism invariant). Execution receives
`U(x)`, never `x` (CC-TRANSPORT).

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
  comparisons : Array ComparisonId := #[]
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

/-- The registered comparison identifying two routes by one rewrite, if any. -/
def RegistryState.comparisonBetween? (state : RegistryState) (a b : Route) :
    Option ComparisonId :=
  (state.comparisons.find? fun c =>
      rewritesTo a.refs b.refs c.left c.right || rewritesTo a.refs b.refs c.right c.left).map (·.id)

/-- Partition candidates into classes of routes connected by registered comparisons; only
candidates with the same `key` (the same method or property) are ever identified. Returns, for
each class, its members and the comparisons used. -/
def RegistryState.classify {α : Type} [Inhabited α] (state : RegistryState) (candidates : Array α)
    (key : α → String) (route : α → Route) : Array (Array α × Array ComparisonId) := Id.run do
  let n := candidates.size
  let mut classOf : Array Nat := Array.range n
  let mut used : Array ComparisonId := #[]
  -- naive union-find over the (small) candidate set
  for i in [0:n] do
    for j in [i+1:n] do
      if key candidates[i]! == key candidates[j]! then
        if let some c := state.comparisonBetween? (route candidates[i]!) (route candidates[j]!) then
          let (ci, cj) := (classOf[i]!, classOf[j]!)
          if ci != cj then
            classOf := classOf.map fun k => if k == cj then ci else k
            unless used.contains c do used := used.push c
  let reps := (classOf.toList.eraseDups).toArray
  return reps.map fun r =>
    let members := (Array.range n).filter (classOf[·]! == r) |>.map (candidates[·]!)
    (members, if members.size > 1 then used else #[])

/-- Classes of method candidates. -/
def RegistryState.coherenceClasses (state : RegistryState) (candidates : Array Resolution) :
    Array (Array Resolution × Array ComparisonId) :=
  state.classify candidates (·.method.id.raw) (·.route)

/-- A resolved property query: the property row, its classifier, the route to the classifier's
host, and the comparisons that identified other routes with it. -/
structure PropertyResolution where
  property : PropertyEntry
  classifier : ClassifierEntry
  route : Route
  comparisons : Array ComparisonId := #[]

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
  | [(members, comparisons)] =>
      -- One semantic route (#53 §8 steps 6–7). The representative is chosen only now, after
      -- equivalence is established, canonically by its rendered route, never by order.
      let sorted := members.qsort fun a b => state.renderRoute a.route < state.renderRoute b.route
      let resolution := { sorted[0]! with comparisons }
      if !resolution.method.returnsToSource then return resolution
      let mut lifts := #[]
      for step in resolution.route.refs do
        match state.lifts.find? (·.edge == step) with
        | some lift => lifts := lifts.push lift.id
        | none => throw (.missingLift name resolution step)
      pure { resolution with lifts }
  | _ => throw (.ambiguous name candidates)

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
  | [(members, comparisons)] =>
      let sorted := members.qsort fun a b => state.renderRoute a.route < state.renderRoute b.route
      pure { sorted[0]! with comparisons }
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
lift). Nothing here is declared per receiver: the surface is computed from the registry, so adding
a leaf's structural functors regenerates it (#53 §8 "Static closure"). -/
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
def reportClosure (category : String) : TermElabM Unit := do
  let state ← registryState
  let some entry := state.categories.find? (·.id.raw == category)
    | throwError "no registered category {category}"
  let render (rows : Array ClosureRow) : String :=
    "\n".intercalate (rows.toList.map fun row =>
      s!"  {row.name} ({row.kind}){if row.resolved then "" else " [unavailable]"}: {row.status}")
  let objects := state.closure entry.expression
  let morphisms := match state.arrowsOf? entry.expression with
    | some arrows => state.closure arrows
    | none => #[]
  logInfo m!"on objects of {category}:\n{render objects}\non morphisms of {category}:\n\
    {render morphisms}"

/-! ## Elaboration: the composite as a checked Lean term -/

/-- The typed symbolic composite of a route, as a Lean `Expr` of type `FunctorExpr A B`. Lean
checks that consecutive steps share their middle category. -/
def Route.compositeExpr (route : Route) : MetaM Expr := do
  let mut acc := mkApp (mkConst ``FunctorExpr.identity) (toExpr route.source)
  for edge in route.steps do
    acc ← mkAppM ``FunctorExpr.comp #[acc, toExpr edge.expression]
  return acc

/-- The unique registered action on functor `id` that composes after `acc` (or starts a
composite, when `acc` is `none`). -/
def composeAction (state : RegistryState) (acc : Option Expr) (edge : EdgeRef) :
    MetaM Expr := do
  let candidates := state.actions.filter (·.edge == edge)
  if candidates.isEmpty then
    throwError "no registered action realizes {edge.label}"
  let mut composed : Array Expr := #[]
  for candidate in candidates do
    -- A realization indexed by parameters (the free modules over `ℤ/n`) gets metavariables for
    -- them, assigned by composing after the realization so far.
    let constant ← mkConstWithFreshMVarLevels candidate.realization
    let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
    let action := mkAppN constant arguments
    let result? ← match acc with
      | none => pure (some action)
      | some previous =>
          let saved ← saveState
          try pure (some (← mkAppHere ``RealizedAction.comp #[previous, action]))
          catch _ => saved.restore; pure none
    if let some result := result? then composed := composed.push (← instantiateMVars result)
  match composed.toList with
  | [result] => pure result
  | [] => throwError "no registered action on {edge.label} composes with the realization so far"
  | _ => throwError "several registered actions on {edge.label} compose; choosing one is a \
      realization choice (CC-ROUTE), not made here"

/-- The route's registered actions composed after the identity action on `denotation`, the
receiver's realizer (CC-SEP): the realizer, not the uniqueness of an action, selects each step's
action. -/
def composeRouteFrom (state : RegistryState) (denotation : Expr) (route : Route) :
    MetaM Expr := do
  let mut acc ← mkAppM ``RealizedAction.id #[denotation]
  for edge in route.steps do
    acc ← composeAction state (some acc) edge.ref
  return acc

/-- The executable image `U(x)` of a handle `x` of the realizer `denotation` along a resolved
route, and the method's value on it when a registered action realizes the method (`none` when the
method is realized only by a backend). Both are closed terms, ready for evaluation. -/
def realizedCall (state : RegistryState) (resolution : Resolution) (denotation handle : Expr) :
    MetaM (Expr × Option Expr) := do
  let routeAction ← composeRouteFrom state denotation resolution.route
  let image ← mkAppM ``RealizedAction.obj #[routeAction, handle]
  let methodAction? ← try some <$> composeAction state none (.functor resolution.method.functor)
    catch _ => pure none
  let value? ← methodAction?.mapM fun action => mkAppM ``RealizedAction.obj #[action, image]
  return (image, value?)

/-- Elaborate `method% name (receiver) in "cat.id" via "fun.id" …` (syntax in
`CasCatalogue.ResolveSyntax`): resolve the route, check its
symbolic composite, compose the registered actions along it and apply the method's action. The
result is an ordinary Lean term: a `let` binding the checked composite `FunctorExpr`, around the
application of the composed `RealizedAction` to the receiver. -/
def elabMethodCall (name : String) (receiver : Term) (category : String)
    (through : Array String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwError "no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name
      (through.map fun raw => ⟨raw⟩) with
    | .ok resolution => pure resolution
    | .error error => throwError error.render state
  logInfo m!"resolved: {state.renderResolution resolution}"
  let composite ← resolution.route.compositeExpr
  let mut acc : Option Expr := none
  for edge in resolution.route.steps do
    acc ← some <$> composeAction state acc edge.ref
  let methodAction ← composeAction state none (.functor resolution.method.functor)
  let x ← elabTerm receiver none
  let image ← match acc with
    | some routeAction => mkAppM ``RealizedAction.obj #[routeAction, x]
    | none => pure x
  let value ← mkAppM ``RealizedAction.obj #[methodAction, image]
  return .letE `route (← inferType composite) composite value (nondep := true)

/-- CC-SEP: the receiver's handle must be realized by a registered realizer of the named category;
its category is never read off the handle. Checked on the first action's source denotation. -/
def checkRealizer (state : RegistryState) (category : CategoryId) (action : Expr) :
    TermElabM Unit := do
  let type ← whnfR (← inferType action)
  unless type.isAppOfArity ``RealizedAction 9 do return
  let sourceDenotation := type.getAppArgs[7]!
  for realizer in state.realizers.filter (·.category == category) do
    let registered ← mkConstWithFreshMVarLevels realizer.denotation
    if ← withoutModifyingState (isDefEq sourceDenotation registered) then return
  throwError "no registered realizer of {category.raw} realizes this receiver (CC-SEP)"

/-- Elaborate `run% name (x) in "cat.id"` (optionally `using "impl.id"`): the value of `x.name`
with its epistemic status and provenance (CC-TRUST). Without `using`, the value is computed by the
composed Lean-native actions; with it, by the named fused implementation of the same semantic
composite (CC-ROUTE). -/
def elabRun (name : String) (receiver : Term) (category : String) (implementation : Option String)
    (proved : Bool := false) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwError "no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name with
    | .ok resolution => pure resolution
    | .error error => throwError error.render state
  let x ← elabTerm receiver none
  let rendered := state.renderResolution resolution
  match implementation with
  | none =>
      let mut acc : Option Expr := none
      for edge in resolution.route.steps do
        acc ← some <$> composeAction state acc edge.ref
      if let some routeAction := acc then checkRealizer state categoryEntry.id routeAction
      let methodAction ← composeAction state none (.functor resolution.method.functor)
      let image ← match acc with
        | some routeAction => mkAppM ``RealizedAction.obj #[routeAction, x]
        | none => pure x
      let value ← mkAppM ``RealizedAction.obj #[methodAction, image]
      if proved then
        -- Kernel reduction, not compiled evaluation: the normal form, with `rfl` for the kernel.
        let normal ← withTransparency .all <| Meta.reduce value (skipTypes := true)
        let proof ← mkEqRefl value
        mkAppM ``Result.ofKernel #[value, normal, proof,
          toExpr s!"{rendered} ; composed Lean-native actions, reduced by the kernel"]
      else
        mkAppM ``Result.mk #[value, mkConst ``Trust.leanChecked,
          toExpr s!"{rendered} ; composed Lean-native actions"]
  | some implementationId =>
      let some entry := state.implementations.find? (·.id.raw == implementationId)
        | throwError "no registered implementation {implementationId}"
      unless entry.method == resolution.method.id && entry.route == resolution.route.refs do
        throwError "implementation {implementationId} realizes a different composite"
      let fused ← mkConstWithFreshMVarLevels entry.realization
      let provenance := toExpr s!"{rendered} ; fused by {entry.backend} ({implementationId})"
      match entry.trust with
      | .certificateChecked => mkAppM ``CertifiedImplementation.run #[fused, x, provenance]
      | _ =>
          let value ← mkAppM ``TrustedImplementation.obj #[fused, x]
          mkAppM ``Result.mk #[value, mkConst ``Trust.trustedAssertion, provenance]

/-- The method audit (CC-ROUTE): the one semantic owner of `name` on `category` and every
registered realization of it. -/
def reportAudit (name category : String) : TermElabM Unit := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwError "no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name with
    | .ok resolution => pure resolution
    | .error error => throwError error.render state
  let fused := state.implementations.filter fun e =>
    e.method == resolution.method.id && e.route == resolution.route.refs
  let lines := #[s!"owner: {resolution.method.id.raw} ({resolution.method.functor.raw})",
      s!"route: {state.renderRoute resolution.route}",
      "realization: composed Lean-native actions (Lean-checked computation)"] ++
    fused.map fun e => s!"realization: {e.id.raw} by {e.backend} ({e.trust.label})"
  logInfo m!"{"\n".intercalate lines.toList}"

/-- Elaborate `transport% (x) from K₁ to K₂`: move the element `x` of `K₁` to `K₂` along a
registered isomorphism (CC-CARRIER). Two presentations are never silently identified: with no
registered isomorphism the call reports its absence. -/
def elabTransport (element source target : Term) : TermElabM Expr := do
  let state ← registryState
  unless source.raw.isIdent && target.raw.isIdent do throwError "transport needs named objects"
  let sourceName ← resolveGlobalConstNoOverload source.raw
  let targetName ← resolveGlobalConstNoOverload target.raw
  let some entry := state.handleIsos.find? fun (e : HandleIsoEntry) =>
      e.source == sourceName && e.target == targetName
    | throwError "no registered isomorphism from {sourceName} to {targetName}: the two \
        presentations are distinct objects, and no comparison relates them (CC-CARRIER)"
  let evidence ← mkConstWithFreshMVarLevels entry.evidence
  let hom ← mkAppM ``HandleIso.hom #[evidence]
  let act ← mkAppM ``ElementAction.act #[hom]
  let .forallE _ domain codomain _ ← whnf (← inferType act)
    | throwError "the realizer's element action is not a function"
  let x ← elabTermEnsuringType element (← whnf domain)
  -- Expose the target's element type in normal form, so its operations are found.
  mkExpectedTypeHint (mkApp act x) (← whnf codomain)

/-- Elaborate `ask% name (receiver) in "cat.id"`: resolve the property, compose the registered
actions along the route, and apply the unique registered decider of the classifier to the image.
The result is a `Decision` about the image's denotation, inside a `let` of the checked composite
`FunctorExpr`. -/
def elabPropertyQuery (name : String) (receiver : Term) (category : String)
    (through : Array String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwError "no registered category {category}"
  let resolution ← match state.resolveProperty categoryEntry.expression name
      (through.map fun raw => ⟨raw⟩) with
    | .ok resolution => pure resolution
    | .error error => throwError error.render state
  logInfo m!"resolved: {state.renderPropertyResolution resolution}"
  let composite ← resolution.route.compositeExpr
  let mut acc : Option Expr := none
  for edge in resolution.route.steps do
    acc ← some <$> composeAction state acc edge.ref
  let x ← elabTerm receiver none
  let image ← match acc with
    | some routeAction => mkAppM ``RealizedAction.obj #[routeAction, x]
    | none => pure x
  let deciders := state.deciders.filter (·.classifier == resolution.classifier.id)
  let mut decisions : Array Expr := #[]
  for decider in deciders do
    let procedure ← mkConstWithFreshMVarLevels decider.realization
    try decisions := decisions.push (← mkAppM ``Decider.decide #[procedure, image])
    catch _ => pure ()
  match decisions.toList with
  | [decision] => return .letE `route (← inferType composite) composite decision (nondep := true)
  | [] => throwError "no registered decision procedure for {resolution.classifier.id.raw} \
      applies to this realization"
  | _ => throwError "several registered decision procedures apply; choosing one is a \
      realization choice (CC-ROUTE), not made here"

/-- Report the resolution of `name` on the category `category`, or why there is none. -/
def reportResolution (name category : String) (through : Array String) : TermElabM Unit := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwError "no registered category {category}"
  match state.resolveMethod categoryEntry.expression name (through.map fun raw => ⟨raw⟩) with
  | .ok resolution =>
      discard <| resolution.route.compositeExpr
      logInfo m!"{state.renderResolution resolution}"
  | .error error => throwError error.render state

end CasCatalogue
