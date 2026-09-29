/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Registry.Extension
public import CasCatalogue.Memo
public import CasCatalogue.Refine
public import CasCatalogue.Failure

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

/-- Resolve a limit of shape `shape` in `category`: its own registered presentation, else the
unique registered creation lift of `shape` limits out of `category` into a category with one. -/
def RegistryState.resolveLimit (state : RegistryState) (category : CategoryId) (shape : String) :
    Except String LimitResolution := do
  let direct := state.limits.filter fun l =>
    !l.colimit && l.category == category && l.shape == shape
  if let some l := direct[0]? then
    if direct.size > 1 then throw s!"{category.raw} has {direct.size} registered {shape} limits"
    return { limit := l.id }
  let some entry := state.categories.find? (·.id == category)
    | throw s!"{category.raw} is not a registered category"
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

/-- The unique registered action on the step `edge` that composes after `acc`, the realization so
far: a composition always starts at the identity action of the receiver's realizer
(`composeRouteFrom`), which selects each step's action (CC-SEP). -/
def composeAction (state : RegistryState) (acc : Expr) (edge : EdgeRef) : MetaM Expr := do
  let candidates := state.actions.filter (·.edge == edge)
  if candidates.isEmpty then
    throwStratum .noImplementation m!"no registered action realizes {edge.label}"
  let mut composed : Array Expr := #[]
  for candidate in candidates do
    -- A realization indexed by parameters (the free modules over `ℤ/n`) gets metavariables for
    -- them, assigned by composing after the realization so far.
    let constant ← mkConstWithFreshMVarLevels candidate.realization
    let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType constant)
    let action := mkAppN constant arguments
    let saved ← saveState
    try composed := composed.push (← instantiateMVars
        (← mkAppHere ``RealizedAction.comp #[acc, action]))
    catch _ => saved.restore
  match composed.toList with
  | [result] => pure result
  | [] => throwStratum .noImplementation
            m!"no registered action on {edge.label} composes with the realization so far"
  | _ => throwStratum .ambiguousRealization
           m!"several registered actions on {edge.label} compose with the realization so far; \
             choosing one is a realization choice (CC-ROUTE), not made here"

/-- Whether `e` mentions a noncomputable constant. -/
def mentionsNoncomputable (env : Environment) (e : Expr) : Bool :=
  (e.find? fun sub => sub.isConst && Lean.isNoncomputable env sub.constName!).isSome

/-- The executable form of a term built from realized actions. A realized action bundles its
handle functor with a square between noncomputable denotations (meaning, CC-SEP); only the handle
functor is ever executed. So: a noncomputable or reducible head is unfolded; a projection is
reduced by bringing its structure to a constructor and taking the field (so the square, another
field, is dropped unevaluated); arguments, bodies and types are treated the same way; every
other head, and every subterm that mentions no noncomputable constant, is kept as it is (it
compiles). Proofs are kept. -/
partial def executable (e : Expr) : MetaM Expr := do
  unless mentionsNoncomputable (← getEnv) e do return e
  if ← isProof e then return e
  match e with
  | .lam .. => lambdaTelescope e fun xs body => do mkLambdaFVars xs (← executable body)
  | .forallE .. => forallTelescope e fun xs body => do mkForallFVars xs (← executable body)
  | .mdata _ b => executable b
  | .letE _ _ v b _ => executable (b.instantiate1 v)
  | _ =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .proj _ i struct => projectField struct i args
      | .const c _ =>
          let env ← getEnv
          if Lean.isNoncomputable env c || (← isReducible c) ||
              (← getProjectionFnInfo? c).isSome then
            match ← withTransparency .all (unfoldDefinition? e) with
            | some e' => executable e'.headBeta
            | none => return mkAppN fn (← args.mapM executable)
          else
            return mkAppN fn (← args.mapM executable)
      | _ => return mkAppN fn (← args.mapM executable)
where
  /-- The field `i` of `struct`, applied to `args`: `struct` is brought to a constructor. -/
  projectField (struct : Expr) (i : Nat) (args : Array Expr) : MetaM Expr := do
    let struct' ← withTransparency .all <| whnf struct
    if let .const c _ := struct'.getAppFn then
      if let some (.ctorInfo ctor) := (← getEnv).find? c then
        return ← executable (mkAppN struct'.getAppArgs[ctor.numParams + i]! args).headBeta
    return mkAppN (.proj (← inferStructName struct') i (← executable struct'))
      (← args.mapM executable)
  inferStructName (struct : Expr) : MetaM Name := do
    let type ← whnf (← inferType struct)
    match type.getAppFn with
    | .const n _ => return n
    | _ => throwError "executable: projection of a non-structure"

/-- The handle a method's functor receives: the image itself, or, for an iso-invariant method (a
functor on the core), the same object as an object of the core of its realization. -/
def methodInput (method : MethodEntry) (image : Expr) : MetaM Expr :=
  match method.shape with
  | .isoInvariant => mkAppM ``CategoryTheory.Core.mk #[image]
  | _ => pure image

/-- A type whose data arguments (the objects of a hom type, say) are in executable form, so that
code using a value of it receives no denotation through its implicit arguments. -/
def executableType (type : Expr) : MetaM Expr := do
  let type ← whnfR type
  return mkAppN type.getAppFn (← type.getAppArgs.mapM executable)

/-- The executable form of `e`, carrying the kernel-checked equation `executable e = e`: the
value computed is, by definition, the value of the composed realized actions. The equation is a
proof, erased from compiled code. -/
def certifiedExecutable (e : Expr) : MetaM Expr := do
  let value ← executable e
  let equation ← mkEq value e
  let proof ← mkExpectedTypeHint (← mkEqRefl value) equation
  let value ← mkExpectedTypeHint value (← executableType (← inferType e))
  return .letE `realizes equation proof value (nondep := true)

/-- `α.obj x` for a realized action `α`, in executable form. -/
def realizedObj (action handle : Expr) : MetaM Expr := do
  executable (← mkAppM ``RealizedAction.obj #[action, handle])

/-- The route's registered actions composed after the identity action on `denotation`, the
receiver's realizer (CC-SEP): the realizer, not the uniqueness of an action, selects each step's
action. -/
def composeRouteFrom (state : RegistryState) (denotation : Expr) (route : Route) :
    MetaM Expr := do
  let mut acc ← mkAppM ``RealizedAction.id #[denotation]
  for edge in route.steps do
    acc ← composeAction state acc edge.ref
  return acc

/-- CC-SEP: the receiver, elaborated as a handle of the unique registered realizer of `category`
whose handles accept it, with that realizer's denotation. The realizer, never the handle's shape
or the uniqueness of an action, selects the actions a call composes. -/
def receiverRealization (state : RegistryState) (category : CategoryId) (receiver : Term) :
    TermElabM (Expr × Expr) := do
  let attempt (realizer : RealizerEntry) : TermElabM (Expr × Expr) := do
    let denotation ← mkConstWithFreshMVarLevels realizer.denotation
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType denotation)
    let denotation := mkAppN denotation args
    let handles := (← whnfR (← inferType denotation)).getAppArgs[0]!
    let x ← withoutErrToSorry <| elabTermEnsuringType receiver handles
    synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars denotation, ← instantiateMVars x)
  let mut accepting : Array RealizerEntry := #[]
  for realizer in state.realizers.filter (·.category == category) do
    let saved ← saveState
    try
      discard <| attempt realizer
      accepting := accepting.push realizer
    catch _ => pure ()
    saved.restore
  match accepting with
  | #[realizer] => attempt realizer
  | #[] => throwStratum .noImplementation
             m!"no registered realizer of {category.raw} realizes this receiver (CC-SEP)"
  | _ => throwStratum .ambiguousRealization
           m!"the receiver is a handle of {accepting.size} registered realizers of {category.raw} \
             ({accepting.toList.map (·.id.raw)}); which realization it is must be stated"

/-- The target denotation of a realized action. -/
def targetDenotation (action : Expr) : MetaM Expr := do
  return (← whnfR (← inferType action)).getAppArgs[10]!

/-- The source denotation of a realized action. -/
def sourceDenotation (action : Expr) : MetaM Expr := do
  return (← whnfR (← inferType action)).getAppArgs[9]!

/-- The unique registered action of the method's functor on the realization of the image (for an
iso-invariant method, on the core of that realization). -/
def methodActionFor (state : RegistryState) (method : MethodEntry) (imageDenotation : Expr) :
    MetaM Expr := do
  let expected ← match method.shape with
    | .isoInvariant => mkAppM ``CategoryTheory.Functor.core #[imageDenotation]
    | .object => pure imageDenotation
  let mut found : Array Expr := #[]
  for candidate in state.actions.filter (·.edge == .functor method.functor) do
    let constant ← mkConstWithFreshMVarLevels candidate.realization
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType constant)
    let action := mkAppN constant args
    let source ← sourceDenotation action
    if ← withoutModifyingState (withTransparency .all (isDefEq source expected)) then
      discard <| isDefEq (← sourceDenotation action) expected
      found := found.push (← instantiateMVars action)
  match found with
  | #[action] => return action
  | #[] => throwStratum .noImplementation
             m!"no registered action of {method.functor.raw} acts on this realization"
  | _ => throwStratum .ambiguousRealization
           m!"several registered actions of {method.functor.raw} act on this realization"

/-- The composed route action from the receiver's realization, the image, and the method's value,
for a resolved method call. -/
def realizedMethodCall (state : RegistryState) (resolution : Resolution) (denotation x : Expr) :
    MetaM (Option Expr × Expr × Expr) := do
  let routeAction? ← if resolution.route.steps.isEmpty then pure none
    else some <$> composeRouteFrom state denotation resolution.route
  let image ← match routeAction? with
    | some routeAction => mkAppM ``RealizedAction.obj #[routeAction, x]
    | none => pure x
  let imageDenotation ← match routeAction? with
    | some routeAction => targetDenotation routeAction
    | none => pure denotation
  let methodAction ← methodActionFor state resolution.method imageDenotation
  let value ← mkAppM ``RealizedAction.obj #[methodAction, ← methodInput resolution.method image]
  return (routeAction?, image, value)

/-- The executable image `U(x)` of a handle `x` of the realizer `denotation` along a resolved
route, and the method's value on it when a registered action realizes the method (`none` when the
method is realized only by a backend). Both are closed terms, ready for evaluation. -/
def realizedCall (state : RegistryState) (resolution : Resolution) (denotation handle : Expr) :
    MetaM (Expr × Option Expr) := do
  let routeAction ← composeRouteFrom state denotation resolution.route
  let image ← realizedObj routeAction handle
  let value? ← try
      let action ← methodActionFor state resolution.method (← targetDenotation routeAction)
      some <$> realizedObj action (← methodInput resolution.method
        (← mkAppM ``RealizedAction.obj #[routeAction, handle]))
    catch _ => pure none
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
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name
      (through.map fun raw => ⟨raw⟩) with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  logInfo m!"resolved: {state.renderResolution resolution}"
  let composite ← resolution.route.compositeExpr
  let (denotation, x) ← receiverRealization state categoryEntry.id receiver
  let (_, _, value) ← realizedMethodCall state resolution denotation x
  let value ← certifiedExecutable value
  return .letE `route (← inferType composite) composite value (nondep := true)

/-- Elaborate `memo% (table) name (receiver) in "cat.id" via …` (CC-MEMO): the call of
`method% name (receiver) in "cat.id"`, resolved once into the function `y ↦ y.name` on the
receiver's handles, and applied through the memo table `table : Option (MemoTable R V)`, keyed by
the resolution and the handle (`memoApply`). With `none` it is the plain call. -/
def elabMemoCall (table : Term) (name : String) (receiver : Term) (category : String)
    (through : Array String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name
      (through.map fun raw => ⟨raw⟩) with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let key := state.renderResolution resolution
  logInfo m!"resolved: {key}"
  let (denotation, x) ← receiverRealization state categoryEntry.id receiver
  let handles ← instantiateMVars (← inferType x)
  let call ← withLocalDeclD `y handles fun y => do
    let (_, _, value) ← realizedMethodCall state resolution denotation y
    mkLambdaFVars #[y] (← certifiedExecutable value)
  let .forallE _ _ values _ ← whnfR (← inferType call)
    | throwError "the resolved call is not a function of the receiver"
  let tableType ← mkAppM ``Option #[← mkAppOptM ``MemoTable #[handles, values, none, none]]
  let table ← elabTermEnsuringType table tableType
  mkAppOptM ``memoApply #[handles, values, none, none, table, toExpr key, call, x]

/-- CC-SEP: the receiver's handle must be realized by a registered realizer of the named category;
its category is never read off the handle. Checked on the first action's source denotation. -/
def checkRealizer (state : RegistryState) (category : CategoryId) (action : Expr) :
    TermElabM Unit := do
  let type ← whnfR (← inferType action)
  unless type.isAppOfArity ``RealizedAction 11 do return
  let sourceDenotation := type.getAppArgs[9]!
  for realizer in state.realizers.filter (·.category == category) do
    let registered ← mkConstWithFreshMVarLevels realizer.denotation
    if ← withoutModifyingState (isDefEq sourceDenotation registered) then return
  throwStratum .noImplementation
      m!"no registered realizer of {category.raw} realizes this receiver (CC-SEP)"

/-- Elaborate `run% name (x) in "cat.id"` (optionally `using "impl.id"`): the value of `x.name`
with its epistemic status and provenance (CC-TRUST). Without `using`, the value is computed by the
composed Lean-native actions; with it, by the named fused implementation of the same semantic
composite (CC-ROUTE). -/
def elabRun (name : String) (receiver : Term) (category : String) (implementation : Option String)
    (proved : Bool := false) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let rendered := state.renderResolution resolution
  match implementation with
  | none =>
      let (denotation, x) ← receiverRealization state categoryEntry.id receiver
      let (_, _, value) ← realizedMethodCall state resolution denotation x
      let value ← executable value
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
        | throwStratum .invalid m!"no registered implementation {implementationId}"
      unless entry.method == resolution.method.id && entry.route == resolution.route.refs do
        throwStratum .invalid m!"implementation {implementationId} realizes a different composite"
      let x ← elabTerm receiver none
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
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveMethod categoryEntry.expression name with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
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
  unless source.raw.isIdent && target.raw.isIdent do
    throwStratum .invalid m!"transport needs named objects"
  let sourceName ← resolveGlobalConstNoOverload source.raw
  let targetName ← resolveGlobalConstNoOverload target.raw
  let some entry := state.handleIsos.find? fun (e : HandleIsoEntry) =>
      e.source == sourceName && e.target == targetName
    | throwStratum .noImplementation
        m!"no registered isomorphism from {sourceName} to {targetName}: the two \
        presentations are distinct objects, and no comparison relates them (CC-CARRIER)"
  let evidence ← mkConstWithFreshMVarLevels entry.evidence
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[evidence]
  let act ← mkAppM ``ElementAction.act #[hom]
  let .forallE _ domain codomain _ ← whnf (← inferType act)
    | throwStratum .invalid m!"the realizer's element action is not a function"
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
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveProperty categoryEntry.expression name
      (through.map fun raw => ⟨raw⟩) with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  logInfo m!"resolved: {state.renderPropertyResolution resolution}"
  let composite ← resolution.route.compositeExpr
  let (denotation, x) ← receiverRealization state categoryEntry.id receiver
  let image ← if resolution.route.steps.isEmpty then pure x
    else mkAppM ``RealizedAction.obj #[← composeRouteFrom state denotation resolution.route, x]
  let deciders := state.deciders.filter (·.classifier == resolution.classifier.id)
  let mut decisions : Array Expr := #[]
  for decider in deciders do
    let procedure ← mkConstWithFreshMVarLevels decider.realization
    try decisions := decisions.push (← executable (← mkAppM ``Decider.decide #[procedure, image]))
    catch _ => pure ()
  match decisions.toList with
  | [decision] => return .letE `route (← inferType composite) composite decision (nondep := true)
  | [] => throwStratum .noImplementation
            m!"no registered decision procedure for {resolution.classifier.id.raw} applies to \
              this realization"
  | _ => throwStratum .ambiguousRealization
           m!"several registered decision procedures apply; choosing one is a realization choice \
             (CC-ROUTE), not made here"

/-- Elaborate `eq% (f) (g) in "cat.id"`: the category's equality of the morphism handles `f` and
`g`, decided by the unique registered equality procedure of a realizer of the category whose
handles they are. The result is a `Decision` about their denotations (CC-DECIDE). -/
def elabEqualityQuery (f g : Term) (category : String) : TermElabM Expr := do
  let state ← registryState
  let some categoryEntry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let f ← elabTerm f none
  let g ← elabTerm g none
  synthesizeSyntheticMVarsNoPostponing
  let mut decisions : Array Expr := #[]
  for equality in state.equalities do
    unless state.realizers.any fun r => r.id == equality.realizer && r.category == categoryEntry.id do
      continue
    let procedure ← mkConstWithFreshMVarLevels equality.realization
    try
      let decision ← executable (← mkAppM ``HomEquality.decide #[procedure, f, g])
      decisions := decisions.push decision
    catch _ => pure ()
  match decisions.toList with
  | [decision] => return decision
  | [] => throwStratum .noImplementation
            m!"no registered equality of {category} applies to these morphisms"
  | _ => throwStratum .ambiguousRealization
           m!"several registered equalities of {category} apply to these morphisms"

/-- The registered classifiers on `source` that are classifiers of a property (`ofProperty P`,
found by unification) with total `target`, as `(classifier, P)`. -/
def propertyClassifierInto (state : RegistryState) (source target : NamedCategoryEntry) :
    MetaM (Option (ClassifierEntry × Expr × Expr)) := do
  let attempt (entry : ClassifierEntry) : MetaM (Expr × Expr) := do
    let declared ← mkConstWithFreshMVarLevels target.declaration
    let (targetArgs, _, _) ← forallMetaTelescopeReducing (← inferType declared)
    let total := mkAppN declared targetArgs
    let c ← mkConstWithFreshMVarLevels entry.declaration
    let (args, _, _) ← forallMetaTelescopeReducing (← inferType c)
    let classifier := mkAppN c args
    let host := (← whnfR (← inferType classifier)).appArg!
    let P ← mkFreshExprMVar (← mkAppOptM ``CategoryTheory.ObjectProperty
      #[← mkAppM ``CategoryTheory.Bundled.α #[host], none])
    unless ← withTransparency .all <| isDefEq classifier
        (← mkAppOptM ``LeanCategories.Classifier.ofProperty #[host, P]) do
      throwStratum .invalid m!"{entry.id.raw} is not the classifier of a property"
    unless ← withTransparency .all <| isDefEq
        (← mkAppM ``LeanCategories.Classifier.total #[classifier]) total do
      throwStratum .invalid m!"{entry.id.raw} does not have the total {target.id.raw}"
    return (← instantiateMVars classifier, ← instantiateMVars P)
  let candidates := state.classifiers.filter (·.host.syntacticEq source.expression)
  let mut matching : Array ClassifierEntry := #[]
  for entry in candidates do
    if ← withoutModifyingState (try discard (attempt entry); pure true catch _ => pure false) then
      matching := matching.push entry
  match matching.toList with
  | [entry] => return some (entry, ← attempt entry)
  | [] => return none
  | _ => throwStratum .invalid
           m!"several property classifiers on {source.id.raw} have the total {target.id.raw}"

/-- Elaborate `refine% (x) in "cat.src" to "cat.tgt"` (CC-PROP, CC-DECIDE): `cat.tgt` is the total
of the unique registered classifier of a property `P` on `cat.src`; its registered decider on the
receiver's realization decides `Holds`, which is `P` of the denotation
(`Classifier.holds_ofProperty`), and `refine` re-types the receiver: `some` of the same handle in
the refinement when proved, `none` otherwise. -/
def elabRefine (receiver : Term) (source target : String) : TermElabM Expr := do
  let state ← registryState
  let some src := state.categories.find? (·.id.raw == source)
    | throwStratum .invalid m!"no registered category {source}"
  let some tgt := state.categories.find? (·.id.raw == target)
    | throwStratum .invalid m!"no registered category {target}"
  let some (entry, classifier, P) ← propertyClassifierInto state src tgt
    | throwStratum .invalid m!"{target} is not the refinement of {source} by a registered property"
  let (denotation, x) ← receiverRealization state src.id receiver
  let mut decisions : Array Expr := #[]
  for decider in state.deciders.filter (·.classifier == entry.id) do
    let procedure ← mkConstWithFreshMVarLevels decider.realization
    try
      let decision ← mkAppM ``Decider.decide #[procedure, x]
      decisions := decisions.push decision
    catch _ => pure ()
  let [decision] := decisions.toList
    | throwStratum .noImplementation
        m!"no unique registered decider of {entry.id.raw} applies to this realization"
  let denoted := (← instantiateMVars (← inferType decision)).appArg!.appArg!
  let host := (← whnfR (← inferType classifier)).appArg!
  -- The classifier's parameters and universes are those of the receiver's denotation.
  unless ← withTransparency .all <| isDefEq (← inferType denoted)
      (← mkAppM ``CategoryTheory.Bundled.α #[host]) do
    throwStratum .invalid m!"the receiver does not denote an object of the host of {entry.id.raw}"
  let host ← instantiateMVars host
  let P ← instantiateMVars P
  let property ← mkAppM ``Decision.map
    #[← mkAppOptM ``Classifier.holds_ofProperty #[host, P, denoted], decision]
  mkAppOptM ``refine #[none, none, none, none, denotation, P, x, property]

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

/-! ## Implementation gaps (derived, `specs/architecture.md` "Failure is stratified") -/

/-- How a resolved method is realized on the handles of a realizer. -/
inductive Coverage
  /-- By the registered actions along its route and of its method, composed. -/
  | actions
  /-- By fused implementations of its composite. -/
  | implementations (ids : Array ImplementationId)
  /-- By nothing: the realization failure, `NoImplementation` or an ambiguous realization. -/
  | gap (reason : String)

/-- The coverage of `resolution` on the handles of `realizer`. Only a realization failure is a
gap; any other failure propagates. -/
def RegistryState.coverage (state : RegistryState) (resolution : Resolution)
    (realizer : RealizerEntry) : MetaM Coverage := do
  let fused := state.implementations.filter fun i =>
    i.method == resolution.method.id && i.route == resolution.route.refs
  try
    withoutModifyingState do
      let denotation ← mkConstWithFreshMVarLevels realizer.denotation
      let (args, _, _) ← forallMetaTelescopeReducing (← inferType denotation)
      let denotation := mkAppN denotation args
      let handles := (← whnfR (← inferType denotation)).getAppArgs[0]!
      withLocalDeclD `x handles fun x =>
        discard <| realizedMethodCall state resolution denotation x
    return .actions
  catch e =>
    match Exception.stratum? e with
    | some .noImplementation | some .ambiguousRealization =>
        if fused.isEmpty then return .gap (← e.toMessageData.toString)
        else return .implementations (fused.map (·.id))
    | _ => throw e

/-- The implementation gaps of a registered category: for each method on its surface and each
registered realizer of it, how the method is realized, or the gap. The backends declaring an
answer to the method are listed with it. Only realizations enter this report; the surface it
ranges over is `closure`, which reads semantic rows only. -/
def gapsReport (category : String) : TermElabM String := do
  let state ← registryState
  let some entry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let realizers := state.realizers.filter (·.category == entry.id)
  let names := (state.methods.map (·.name)).toList.eraseDups
  let mut lines : Array String := #[]
  for name in names do
    let .ok resolution := state.resolveMethod entry.expression name | continue
    let backends := (state.backendOperations.filter (·.operation == resolution.method.id.raw)).map
      (·.backend)
    let answered := if backends.isEmpty then "" else s!" ; answered by {backends.toList}"
    if realizers.isEmpty then
      lines := lines.push
        s!"  {name}: NoImplementation: no registered realizer of {category}{answered}"
    for realizer in realizers do
      let status := match ← state.coverage resolution realizer with
        | .actions => "composed actions"
        | .implementations ids => s!"implementations {ids.toList.map ImplementationId.raw}"
        | .gap reason => reason
      lines := lines.push s!"  {name} on {realizer.id.raw}: {status}{answered}"
  return s!"implementation gaps of {category}:\n" ++ "\n".intercalate lines.toList

end CasCatalogue
