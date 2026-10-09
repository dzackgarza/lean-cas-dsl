/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public import CasContract.Registration

@[expose] public section

/-!
# Admission of registrations against the catalogue (`specs/leaf-registration.md`)

A registration names an operation and an input form by the catalogue's own stable ids, and a
backend by its name in the manifest. The kernel admits it only when all three resolve:

* **Operations** are the catalogue's operation rows, by id: a method (`meth.cardinality`), a
  property (`prop.is_finite`), a registered limit (`lim.sets.product`), an element operation
  (`op.boolean_algebras.union`) or a morphism family (`mor.*`).
* **Forms** are what the kernel encodes with its structural codec, by id: a registered literal
  form (`lit.cardinals`, the values of its type), a registered graph-literal form
  (`graph.sets`, the morphisms of its category by their graphs), a registered subset-literal
  form (`lit.sets.finite_subsets`, the finite subsets of a power object's sets by their
  elements), a registered named object at its explicit parameters (`obj.sets.fin`,
  `obj.sets.integers_mod_power`), or the diagrams of a registered category (`cat.sets`: a
  diagram of a registered shape, in the forms of its objects and arrows). Which forms exist is
  the catalogue's; a leaf declares none.
* A form is **accepted** by an operation when the operation applies to its values: a method or a
  property when the form's category resolves it by a structural route (the same resolution the
  semantic reading performs) and the catalogue does not send the form elsewhere along that route
  (CC-TRANSPORT), a limit when the form is the diagrams of its category, an element operation or
  morphism family when it is registered in the form's category.

Everything else in a manifest is ignored. A registration that is not admitted is reported with
its reason, and carries no meaning.
-/

open Lean

namespace CasCatalogue

/-- A concrete port address for the already published callable field. This creates no
semantic row: the declaration and its dependent signature remain the object's metadata. -/
def ObjectEntry.applicationAddress (entry : ObjectEntry) : String :=
  entry.id.raw ++ "#application"

/-- A form the kernel encodes: values of a registered literal type, morphisms of a registered
category given by their graphs, a registered named object at its parameters, or the diagrams of a
registered category (the input of its registered limits), encoded in the forms of their objects
and arrows. -/
inductive Form
  | literal (entry : LiteralEntry)
  | graph (entry : GraphLiteralEntry)
  /-- The finite subsets of a power object's sets, as literals of its registered subset-literal
  form; `category` is the power object's. -/
  | subset (entry : SubsetLiteralEntry) (category : CategoryId)
  | object (entry : ObjectEntry)
  | namedMorphism (entry : MorphismEntry)
  /-- The complete request for a published object's application field. -/
  | application (entry : ObjectEntry)
  /-- The complete request for a published binder's operation. -/
  | binder (entry : BinderEntry)
  /-- Canonical typed zero or identity data inside an already accepted diagram. -/
  | canonicalMorphism (entry : NamedCategoryEntry)
  | generator (entry : ObjectEntry)
  | element (entry : ObjectEntry)
  | limitApex (entry : LimitEntry)
  /-- The formal apex of an accepted creation lift, with complete opaque construction data. -/
  | createdApex (entry : LimitEntry) (category : CategoryId)
  /-- An actual object image of an already registered functor, at its selected target schema. -/
  | functorImage (entry : FunctorEntry) (category : CategoryId)
  /-- An object image of an accepted structural edge at its independently fixed target. -/
  | edgeImage (edge : EdgeRef) (category : NamedCategoryEntry)
  /-- An object of a registered arrow category, retaining both endpoints and its map. -/
  | arrow (entry : NamedCategoryEntry)
  /-- A monic arrow in the registered subobject category, with its full defining data. -/
  | subobject (entry : NamedCategoryEntry)
  /-- A registered comparison arrow, with its source category resolved from its object row. -/
  | presentation (entry : PresentationComparisonEntry) (category : CategoryId)
  | diagrams (entry : NamedCategoryEntry)

/-- A stable structural-edge descriptor, independent of pretty-printing and declaration parameters.
Actual ordered parameters remain in the typed value and wire descriptor. -/
def edgeImageDescriptor : EdgeRef → Json
  | .functor id => Json.mkObj [("functor", toJson id.raw)]
  | .classifierForget id => Json.mkObj [("classifierForget", toJson id.raw)]
  | .constructMap id inner => Json.mkObj
      [("constructorMap", Json.arr #[toJson id.raw, edgeImageDescriptor inner])]

/-- Constructed image registration identity includes its entire edge and target schema. -/
def edgeImageId (edge : EdgeRef) (category : CategoryId) : String :=
  "image:" ++ (Json.arr #[toJson category.raw, edgeImageDescriptor edge]).compress

/-- The form's id: a literal, graph-literal, subset-literal or object row's; for diagrams, their
category's. -/
def Form.id : Form → String
  | .literal entry => entry.id.raw
  | .graph entry => entry.id.raw
  | .subset entry _ => entry.id.raw
  | .object entry => entry.id.raw
  | .namedMorphism entry => entry.id.raw
  | .application entry => entry.applicationAddress
  | .binder entry => entry.id.raw
  | .canonicalMorphism entry => entry.id.raw
  | .generator entry => entry.id.raw
  | .element entry => entry.id.raw
  | .limitApex entry => entry.id.raw
  | .createdApex entry _ => entry.id.raw
  | .functorImage entry _ => entry.id.raw
  | .edgeImage edge category => edgeImageId edge category.id
  | .arrow entry => entry.id.raw
  | .subobject entry => entry.id.raw
  | .presentation entry _ => entry.id.raw
  | .diagrams entry => entry.id.raw

def Form.category : Form → CategoryId
  | .literal entry => entry.category
  | .graph entry => entry.category
  | .subset _ category => category
  | .object entry => entry.category
  | .namedMorphism entry => entry.category
  | .application entry => entry.category
  | .binder entry => entry.category
  | .canonicalMorphism entry => entry.id
  | .generator entry => entry.category
  | .element entry => entry.category
  | .limitApex entry => entry.category
  | .createdApex _ category => category
  | .functorImage _ category => category
  | .edgeImage _ category => category.id
  | .arrow entry => entry.id
  | .subobject entry => entry.id
  | .presentation _ category => category
  | .diagrams entry => entry.id

/-- The category of the power object `id`: that of its family `𝒫`. -/
def RegistryState.powerObjectCategory? (state : RegistryState) (id : PowerObjectId) :
    Option CategoryId := do
  let power ← state.powerObjects.find? (·.id == id)
  let object ← state.objects.find? (·.id == power.object)
  pure object.category

/-- The form `id` names. -/
def RegistryState.imageEdges (state : RegistryState) : Array StructuralEdge :=
  state.categories.foldl (fun edges category =>
    (state.edgesFrom category.expression).foldl (fun edges edge =>
      if edges.any (fun existing => existing.ref == edge.ref &&
          existing.source.syntacticEq edge.source && existing.target.syntacticEq edge.target)
      then edges else edges.push edge) edges) state.structuralEdges

def RegistryState.edgeImageForm? (state : RegistryState) (id : String) : Option Form := do
  if id.startsWith "image:" then
    let candidates := state.imageEdges.flatMap fun edge =>
      state.categories.filterMap fun category =>
        let targetMatches := category.expression.syntacticEq edge.target ||
          match category.expression, edge.target with
          | .familyApp left _, .familyApp right _ => left == right
          | _, _ => false
        if targetMatches && edgeImageId edge.ref category.id == id then
          some (edge.ref, category)
        else none
    let #[(edge, category)] := candidates | none
    return .edgeImage edge category
  -- Legacy short aliases remain usable only when they identify exactly one full edge/target.
  let edges := state.imageEdges.filter fun edge => match edge.ref with
    | .classifierForget classifier => classifier.raw == id
    | .constructMap constructor _ => constructor.raw == id
    | _ => false
  let targets := state.categories.filter fun category =>
    edges.any (fun edge => category.expression.syntacticEq edge.target)
  let #[target] := targets | none
  let candidates := edges.filter (·.target.syntacticEq target.expression)
  let #[edge] := candidates | none
  some (.edgeImage edge.ref target)

def RegistryState.form? (state : RegistryState) (id : String) : Option Form :=
  (state.literals.find? (·.id.raw == id) |>.map .literal) <|>
  (state.graphLiterals.find? (·.id.raw == id) |>.map .graph) <|>
  (state.subsetLiterals.find? (·.id.raw == id) |>.bind fun entry =>
    (state.powerObjectCategory? entry.powerObject).map (.subset entry ·)) <|>
  (state.objects.find? (·.id.raw == id) |>.map .object) <|>
  (state.morphisms.find? (·.id.raw == id) |>.map .namedMorphism) <|>
  (state.objects.find? (fun entry => entry.application.isSome &&
      entry.applicationAddress == id) |>.map .application) <|>
  (state.binders.find? (·.id.raw == id) |>.map .binder) <|>
  (state.limits.find? (·.id.raw == id) |>.map .limitApex) <|>
  (state.functors.find? (·.id.raw == id) |>.bind fun entry => do
    let category ← (state.categories.find? (·.expression.syntacticEq entry.target)).orElse fun _ => do
      let .familyApp family _ := entry.target | none
      let candidates := state.categories.filter fun category =>
        match category.expression with
        | .familyApp other _ => family == other
        | _ => false
      let #[category] := candidates | none
      some category
    some (.functorImage entry category.id)) <|>
  (state.presentations.find? (·.id.raw == id) |>.bind fun entry =>
    (state.objects.find? (·.id == entry.source)).map (fun object =>
      .presentation entry object.category)) <|>
  state.edgeImageForm? id <|>
  (state.categories.find? (·.id.raw == id) |>.map fun category =>
    match category.expression with
    | .construct constructor #[.category _] =>
        if state.constructors.any (fun entry => entry.id == constructor &&
            entry.semantics == `CasCatalogue.Constructors.arrow) then .arrow category
        else if state.constructors.any (fun entry => entry.id == constructor &&
            entry.semantics == `CasCatalogue.Constructors.subobjects) then .subobject category
        else .diagrams category
    | _ => .diagrams category)

/-- A catalogue operation a registration may compute. -/
inductive Operation
  | method (entry : MethodEntry)
  | property (entry : PropertyEntry)
  | limit (entry : LimitEntry)
  | operation (entry : OperationEntry)
  | morphism (entry : MorphismEntry)
  | application (entry : ObjectEntry)
  | binder (entry : BinderEntry)
  | functor (entry : FunctorEntry)
  | presentation (entry : PresentationComparisonEntry)

def Operation.id : Operation → String
  | .method entry => entry.id.raw
  | .property entry => entry.id.raw
  | .limit entry => entry.id.raw
  | .operation entry => entry.id.raw
  | .morphism entry => entry.id.raw
  | .application entry => entry.applicationAddress
  | .binder entry => entry.id.raw
  | .functor entry => entry.id.raw
  | .presentation entry => entry.id.raw

/-- The operation `id` names. -/
def RegistryState.operation? (state : RegistryState) (id : String) : Option Operation :=
  (state.methods.find? (·.id.raw == id) |>.map .method) <|>
  (state.properties.find? (·.id.raw == id) |>.map .property) <|>
  (state.limits.find? (·.id.raw == id) |>.map .limit) <|>
  (state.operations.find? (·.id.raw == id) |>.map .operation) <|>
  (state.morphisms.find? (·.id.raw == id) |>.map .morphism) <|>
  (state.objects.find? (fun entry => entry.application.isSome &&
      entry.applicationAddress == id) |>.map .application) <|>
  (state.binders.find? (·.id.raw == id) |>.map .binder) <|>
  (state.functors.find? (·.id.raw == id) |>.map .functor) <|>
  (state.presentations.find? (·.id.raw == id) |>.map .presentation)

/-- The actual public callable declaration and category at a concrete address. Consumers
instantiate and check its full signature; no definition is unfolded to invent an operation. -/
def RegistryState.callable? (state : RegistryState) (id : String) :
    Option (Name × CategoryId) := do
  match ← state.operation? id with
  | .morphism entry => return (entry.declaration, entry.category)
  | .application entry => return (← entry.application, entry.category)
  | .binder entry => return (entry.operation, entry.category)
  | .operation entry => return (entry.declaration, entry.category)
  | _ => none

/-- The named object the catalogue sends `entry` to along the structural route `route`, with the
route left to walk (CC-TRANSPORT): while `entry` refines a base along a route that begins the
remaining route (`ObjectRefinement`: `route.obj (entry params) ≅ base params`), it is that base at
the same parameters, that far along. An object no refinement row sends further stays where it is,
with the rest of the route. Only the catalogue's rows move an object; nothing else does. -/
def RegistryState.transport (state : RegistryState) (entry : ObjectEntry)
    (route : Array EdgeRef) : ObjectEntry × Array EdgeRef :=
  -- A chain of refinements visits each object at most once: the objects bound its length.
  go entry route (state.objects.size + 1)
where
  go (entry : ObjectEntry) (route : Array EdgeRef) : Nat → ObjectEntry × Array EdgeRef
    | 0 => (entry, route)
    | fuel + 1 =>
      match entry.refines with
      | some refinement =>
          if !refinement.route.isEmpty &&
              route.extract 0 refinement.route.size == refinement.route then
            match state.objects.find? (·.id == refinement.base) with
            | some base => go base (route.extract refinement.route.size route.size) fuel
            | none => (entry, route)
          else (entry, route)
      | none => (entry, route)

/-- Why `operation` does not apply to the values of `form`, or `none` when it does. A method or a
property applies to a form when the form's category resolves it by a structural route, and the
catalogue does not send the form elsewhere along that route: an object refining another one
along the route is computed as that one (`transport`), so a registration on it would never be
selected, and is not admitted. -/
def RegistryState.rejects (state : RegistryState) (operation : Operation) (form : Form) :
    Option String :=
  if let .presentation entry := operation then
    let rec endpoint (object : ObjectEntry) (fuel : Nat) : Bool :=
      if object.id == entry.source || object.id == entry.target then true else
        match fuel, object.refines with
        | fuel + 1, some refinement =>
            match state.objects.find? (·.id == refinement.base) with
            | some base => endpoint base fuel
            | none => false
        | _, _ => false
    match form with
    | .object object | .generator object | .element object =>
        if endpoint object (state.objects.size + 1) then none
        else some s!"{entry.id.raw} requires its registered source or target endpoint"
    | _ => some s!"{entry.id.raw} requires an element of a registered endpoint"
  else if let .namedMorphism input := form then
    match operation with
    | .morphism entry => if entry.id == input.id then none else
        some s!"{entry.id.raw} requires its own complete declaration input"
    | _ => some s!"{operation.id} expects an object or diagram input, not a named arrow"
  else if let .application input := form then
    match operation with
    | .application entry => if entry.id == input.id then none else
        some s!"{operation.id} requires its own published application request"
    | _ => some s!"{operation.id} is not this published application"
  else if let .binder input := form then
    match operation with
    | .binder entry => if entry.id == input.id then none else
        some s!"{operation.id} requires its own published binder request"
    | _ => some s!"{operation.id} is not this published binder"
  else if let .canonicalMorphism _ := form then
    some s!"{operation.id} expects an object or diagram input, not a canonical arrow"
  else if let .presentation _ _ := form then
    some s!"{operation.id} expects an object or diagram input, not a presentation arrow"
  else if let .generator _ := form then
    some s!"{operation.id} expects an object or diagram input, not a generator arrow"
  else if let .element _ := form then
    some s!"{operation.id} expects an object or diagram input, not an element arrow"
  else
    let movedAlong (route : Array EdgeRef) : Option String :=
      match form with
      | .object entry =>
          let (target, _) := state.transport entry route
          if target.id == entry.id then none
          else some s!"the catalogue computes {operation.id} of {entry.id.raw} on {target.id.raw}, \
            along its refinement; register it on {target.id.raw}"
      | _ => none
    let notResolved := some s!"{operation.id} does not apply to the values of {form.id}"
    match operation with
    | .method entry =>
        match state.categories.find? (·.id == form.category) with
        | some category =>
            match state.resolveMethod category.expression entry.name #[] with
            | .ok resolution =>
                if resolution.method.id == entry.id then movedAlong resolution.route.refs
                else notResolved
            | .error _ => notResolved
        | none => notResolved
    | .property entry =>
        match state.categories.find? (·.id == form.category) with
        | some category =>
            match state.resolveProperty category.expression entry.name #[] with
            | .ok resolution =>
                if resolution.property.id == entry.id then movedAlong resolution.route.refs
                else notResolved
            | .error _ => notResolved
        | none => notResolved
    | .limit entry =>
        -- The input of a limit is a diagram of its category.
        match form with
        | .diagrams category => if entry.category == category.id then none else notResolved
        | _ => some s!"the input of {entry.id.raw} is a diagram of {entry.category.raw}, in the \
            forms of its objects and arrows; register it on {entry.category.raw}"
    | .operation entry => if entry.category == form.category then none else notResolved
    | .morphism entry => if entry.category == form.category then none else notResolved
    | .application entry => if entry.category == form.category then none else notResolved
    | .binder entry => if entry.category == form.category then none else notResolved
    | .presentation _ => notResolved
    | .functor entry =>
        match form with
        | .arrow category =>
            if category.expression.syntacticEq entry.source then none else notResolved
        | .subobject category =>
            if category.expression.syntacticEq entry.source then none else notResolved
        | .object object =>
            match state.categories.find? (·.id == object.category) with
            | some category => if category.expression.syntacticEq entry.source then none else
                match category.expression, entry.source with
                | .familyApp sourceFamily _, .familyApp targetFamily _ =>
                    if sourceFamily == targetFamily then none else notResolved
                | _, _ => notResolved
            | none => notResolved
        | .functorImage _ categoryId =>
            match state.categories.find? (·.id == categoryId) with
            | some category => if category.expression.syntacticEq entry.source then none else
                match category.expression, entry.source with
                | .familyApp sourceFamily _, .familyApp targetFamily _ =>
                    if sourceFamily == targetFamily then none else notResolved
                | _, _ => notResolved
            | none => notResolved
        | .edgeImage _ category =>
            if category.expression.syntacticEq entry.source then none else
              match category.expression, entry.source with
              | .familyApp sourceFamily _, .familyApp targetFamily _ =>
                  if sourceFamily == targetFamily then none else notResolved
              | _, _ => notResolved
        | .limitApex limit =>
            match state.categories.find? (·.id == limit.category) with
            | some category => if category.expression.syntacticEq entry.source then none else
                match category.expression, entry.source with
                | .familyApp sourceFamily _, .familyApp targetFamily _ =>
                    if sourceFamily == targetFamily then none else notResolved
                | _, _ => notResolved
            | none => notResolved
        | .createdApex _ id =>
            match state.categories.find? (·.id == id) with
            | some category => if category.expression.syntacticEq entry.source then none else notResolved
            | none => notResolved
        | _ => notResolved

/-- Whether `operation` applies to the values of `form`. -/
def RegistryState.accepts (state : RegistryState) (operation : Operation) (form : Form) : Bool :=
  (state.rejects operation form).isNone

/-- An admitted registration, with the rows it resolved to. -/
structure Admitted where
  registration : Registration
  operation : Operation
  form : Form

/-- The admitted registrations of a manifest, and why each other one is not admitted. -/
structure Admission where
  admitted : Array Admitted := #[]
  rejected : Array String := #[]

/-- Admit the registrations of `manifest` against the catalogue. -/
def RegistryState.admit (state : RegistryState) (manifest : Manifest) : Admission := Id.run do
  let mut admitted : Array Admitted := #[]
  let mut rejected : Array String := #[]
  for r in manifest.registrations do
    let describe := s!"{r.operation} on {r.input} by {r.backend}"
    match state.operation? r.operation, state.form? r.input with
    | none, _ => rejected := rejected.push s!"{describe}: {r.operation} is not a catalogue \
        operation"
    | _, none => rejected := rejected.push s!"{describe}: {r.input} is not a registered form"
    | some operation, some form =>
        if let some reason := state.rejects operation form then
          rejected := rejected.push s!"{describe}: {reason}"
        else if !manifest.backends.any (·.name == r.backend) then
          rejected := rejected.push s!"{describe}: the backend {r.backend} is not declared in \
            the manifest"
        else
          admitted := admitted.push { registration := r, operation, form }
  return { admitted, rejected }

end CasCatalogue
