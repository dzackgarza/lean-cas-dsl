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
  form (`lit.cardinals`, the values of its type) or a registered named object at its explicit
  parameters (`obj.sets.fin`, `obj.sets.integers_mod_power`). Which forms exist is the
  catalogue's; a leaf declares none.
* A form is **accepted** by an operation when the operation applies to its values: a method or a
  property when the form's category resolves it by a structural route (the same resolution the
  semantic reading performs), a limit, element operation or morphism family when it is registered
  in the form's category.

Everything else in a manifest is ignored. A registration that is not admitted is reported with
its reason, and carries no meaning.
-/

open Lean

namespace CasCatalogue

/-- A form the kernel encodes: values of a registered literal type, or a registered named object
at its parameters. -/
inductive Form
  | literal (entry : LiteralEntry)
  | object (entry : ObjectEntry)

def Form.id : Form → String
  | .literal entry => entry.id.raw
  | .object entry => entry.id.raw

def Form.category : Form → CategoryId
  | .literal entry => entry.category
  | .object entry => entry.category

/-- The form `id` names. -/
def RegistryState.form? (state : RegistryState) (id : String) : Option Form :=
  match state.literals.find? (·.id.raw == id) with
  | some entry => some (.literal entry)
  | none => (state.objects.find? (·.id.raw == id)).map .object

/-- A catalogue operation a registration may compute. -/
inductive Operation
  | method (entry : MethodEntry)
  | property (entry : PropertyEntry)
  | limit (entry : LimitEntry)
  | operation (entry : OperationEntry)
  | morphism (entry : MorphismEntry)

def Operation.id : Operation → String
  | .method entry => entry.id.raw
  | .property entry => entry.id.raw
  | .limit entry => entry.id.raw
  | .operation entry => entry.id.raw
  | .morphism entry => entry.id.raw

/-- The operation `id` names. -/
def RegistryState.operation? (state : RegistryState) (id : String) : Option Operation :=
  (state.methods.find? (·.id.raw == id) |>.map .method) <|>
  (state.properties.find? (·.id.raw == id) |>.map .property) <|>
  (state.limits.find? (·.id.raw == id) |>.map .limit) <|>
  (state.operations.find? (·.id.raw == id) |>.map .operation) <|>
  (state.morphisms.find? (·.id.raw == id) |>.map .morphism)

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
  | .limit entry => if entry.category == form.category then none else notResolved
  | .operation entry => if entry.category == form.category then none else notResolved
  | .morphism entry => if entry.category == form.category then none else notResolved

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
