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

/-- Whether `operation` applies to the values of `form`. -/
def RegistryState.accepts (state : RegistryState) (operation : Operation) (form : Form) : Bool :=
  match operation with
  | .method entry =>
      match state.categories.find? (·.id == form.category) with
      | some category =>
          (state.resolveMethod category.expression entry.name #[]).toOption.any
            (·.method.id == entry.id)
      | none => false
  | .property entry =>
      match state.categories.find? (·.id == form.category) with
      | some category =>
          (state.resolveProperty category.expression entry.name #[]).toOption.any
            (·.property.id == entry.id)
      | none => false
  | .limit entry => entry.category == form.category
  | .operation entry => entry.category == form.category
  | .morphism entry => entry.category == form.category

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
        if !state.accepts operation form then
          rejected := rejected.push s!"{describe}: {r.operation} does not apply to the values \
            of {r.input}"
        else if !manifest.backends.any (·.name == r.backend) then
          rejected := rejected.push s!"{describe}: the backend {r.backend} is not declared in \
            the manifest"
        else
          admitted := admitted.push { registration := r, operation, form }
  return { admitted, rejected }

end CasCatalogue
