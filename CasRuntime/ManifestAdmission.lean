module

public import CasContract.Registration
public import CasCatalogue.Admission
public import CasCompiler.LiftFamily
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Registry.Computation

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue

/-- The published family that an operation address names: the family address itself, or the
address of one of its fields (`<id>#map`). An unknown address creates no operation. -/
def publishedFamily? (state : SemanticState) (address : String) : Option ComputationRef :=
  let id := (address.splitOn "#").head!
  (state.operations.find? (·.id.raw == id) |>.map (.operation ·.id)) <|>
  (state.methods.find? (·.id.raw == id) |>.map (.method ·.id)) <|>
  (state.functors.find? (·.id.raw == id) |>.map (.functor ·.id)) <|>
  (state.constructions.find? (·.id.raw == id) |>.map (.construction ·.id)) <|>
  (state.morphisms.find? (·.id.raw == id) |>.map (.morphism ·.id))

/-- A named comparison uses its original full operation address in both directions. -/
def publishedPresentation? (state : SemanticState) (address : String) :
    Option PresentationComparisonEntry :=
  state.presentations.find? (·.id.raw == address)

/-- Properties keep their accepted public address independently of ComputationRef families. -/
def publishedProperty? (state : SemanticState) (address : String) : Option PropertyEntry :=
  state.properties.find? (·.id.raw == address)

/-- The exact source registry admits property forms by the same classifier/receiver route
that source reading uses. Unknown or differently selected forms create no registration. -/
def propertyFormDefect (state : SemanticState) (row : PropertyEntry)
    (input : String) : Option String :=
  let registry : RegistryState := { toSemanticState := state }
  match registry.form? input with
  | none => some s!"{input} is not a published property input form"
  | some form => registry.rejects (.property row) form

/-- The public complete-request address and admitted endpoint forms are peers. The own
address becomes eligible only for a complete presentationApply demand, never for an arrow
descriptor. Reuse: RegistryState.form?/rejects and the released presentation wire contract. -/
def presentationFormDefect (state : SemanticState) (row : PresentationComparisonEntry)
    (input : String) : Option String :=
  if input == row.id.raw then none
  else
    let registry : RegistryState := { toSemanticState := state }
    match registry.form? input with
    | none => some s!"{input} is not a published presentation input form"
    | some form => registry.rejects (.presentation row) form

/-- The selected lift and computation that a lift port names (`<lift id>#<field>`; leaf contract
api/wire-examples.md, "Prescribed subobject lifts" and "Separate universal factor"). -/
def publishedLift? (state : SemanticState) (address : String) :
    Option (LiftEntry × LiftPort) := do
  let [id, field] := address.splitOn "#" | none
  let row ← state.lifts.find? (·.id.raw == id)
  if row.computation.isNone then none
  if #["obj", "hom", "forward", "backward"].contains field then some (row, .computation)
  else if field == "factor" then some (row, .factor)
  else none

/-- Why a declared preferred route is malformed, if it is: its receiver is a registered category,
its name a registered surface name, and its route a chain of structural edges from the receiver
(contract api/manifest.md). Whether it is a surviving route is decided when a reading uses it. -/
def preferenceDefect (state : SemanticState) (preference : PreferredRoute) :
    Option String := Id.run do
  let some receiver := state.categories.find? (·.id.raw == preference.receiver)
    | return some s!"{preference.receiver} is not a registered category"
  let named := state.objects.any (·.name == preference.name) ||
    state.morphisms.any (·.name == preference.name) ||
    state.operations.any (·.name == preference.name)
  unless named do return some s!"{preference.name} is not a registered surface name"
  let mut current := receiver.expression
  for label in preference.route do
    let some edge := state.structuralEdges.find? (·.ref.label == label)
      | return some s!"{label} is not a structural edge"
    unless edge.source.syntacticEq current do
      return some s!"the edge {label} does not continue the route from {preference.receiver}"
    current := edge.target
  return none

/-- Admit registrations against the source inventory and the declared backends. -/
def admitManifest (parsed : Manifest) : MetaM (Manifest × Array String) := do
  let state ← semanticState
  let mut admitted := #[]
  let mut rejected := #[]
  for registration in parsed.registrations do
    let described :=
      s!"{registration.operation} on {registration.input} by {registration.backend}"
    if (publishedFamily? state registration.operation).isNone &&
        (publishedLift? state registration.operation).isNone &&
        (publishedPresentation? state registration.operation).isNone &&
        (publishedProperty? state registration.operation).isNone then
      rejected := rejected.push s!"{described}: {registration.operation} is not a published operation"
    else if !parsed.backends.any (·.name == registration.backend) then
      rejected := rejected.push
        s!"{described}: the backend {registration.backend} is not declared in the manifest"
    else if let some defect := registration.preferredRoutes.findSome? (preferenceDefect state) then
      rejected := rejected.push s!"{described}: a declared preferred route is malformed: {defect}"
    else if let some row := publishedProperty? state registration.operation then
      if let some defect := propertyFormDefect state row registration.input then
        rejected := rejected.push s!"{described}: {defect}"
      else admitted := admitted.push registration
    else if let some row := publishedPresentation? state registration.operation then
      if let some defect := presentationFormDefect state row registration.input then
        rejected := rejected.push s!"{described}: {defect}"
      else admitted := admitted.push registration
    else admitted := admitted.push registration
  let installed := { parsed with registrations := admitted }
  return (installed, rejected)

end CasRuntime
