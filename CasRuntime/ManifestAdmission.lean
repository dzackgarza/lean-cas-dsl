module

public import CasContract.Registration
public import CasCatalogue.Admission
public import CasCompiler.LiftFamily
public import CasCompiler.PublishedPorts
public import LeanCategories.Catalogue.Registry.Semantic
public import LeanCategories.Catalogue.Registry.Computation

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue

/-- The published family that an operation address names: the family address itself, or the
address of one of its fields (`<id>#map`). An unknown address creates no operation. -/
def publishedFamily? (state : SemanticState) (address : String) : MetaM (Option ComputationRef) :=
  PublishedPorts.family? state address

/-- A universal subfamily is selected by its complete original native limit presentation. -/
def publishedLimitUniversal? (state : SemanticState) (address : String) :
    MetaM (Option LimitUniversalFamily) :=
  PublishedPorts.limitUniversal? state address

/-- An accepted creation lift publishes its complete native LiftsToLimit data family. -/
def publishedCreation? (state : SemanticState) (address : String) :
    MetaM (Option CreationFamily) :=
  PublishedPorts.creation? state address

/-- A named comparison uses its original full operation address in both directions. -/
def publishedPresentation? (state : SemanticState) (address : String) :
    Option PresentationComparisonEntry :=
  state.presentations.find? (·.id.raw == address)

/-- Properties keep their accepted public address independently of ComputationRef families. -/
def publishedProperty? (state : SemanticState) (address : String) : Option PropertyEntry :=
  state.properties.find? (·.id.raw == address)

/-- The existing object-application address names one exact registered field. No suffix is
ignored and no native carrier comparison can supply another object owner. -/
def publishedApplication? (state : SemanticState) (address : String) : Option ObjectEntry :=
  match state.objects.filter (fun entry => entry.application.isSome &&
      entry.applicationAddress == address) with
  | #[entry] => some entry
  | _ => none

/-- A generated application port cannot silently take another row's authored address.
The existing raw-ID registry guard does not include these generated field addresses. -/
def applicationAddressConflict (state : SemanticState) (address : String) : Bool :=
  (publishedApplication? state address).isSome &&
    state.entries.any (·.stableId == address)

/-- Reuse the released .application operation and form admission, including its complete
own-address request and the original owner's compatible object/category forms. -/
def applicationFormDefect (state : SemanticState) (row : ObjectEntry)
    (input : String) : Option String :=
  let registry : RegistryState := { toSemanticState := state }
  match registry.form? input with
  | none => some s!"{input} is not a published application input form"
  | some form => registry.rejects (.application row) form

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
    MetaM (Option (LiftEntry × LiftPort)) := do
  return (← LiftFamily.forAddress? state address).map fun (row, family, _) => (row, family.port)

/-- The exact public address boundary shared by manifest installation and export. Recursive
constructor paths use the released grammar and their complete registered source owners. -/
def publishedOperation (state : SemanticState) (address : String) : MetaM Bool := do
  return (← publishedFamily? state address).isSome ||
    (← publishedLift? state address).isSome ||
    (← publishedLimitUniversal? state address).isSome ||
    (← publishedCreation? state address).isSome ||
    (publishedPresentation? state address).isSome ||
    (publishedProperty? state address).isSome ||
    ((publishedApplication? state address).isSome && !applicationAddressConflict state address) ||
    ((PublishedPorts.component? state address).toOption.bind id).isSome ||
    ((PublishedPorts.cartesian? state address).toOption.bind id).isSome ||
    ((PublishedPorts.edge? state address).toOption.bind id).isSome ||
    (state.binders.filter (·.id.raw == address)).size == 1 ||
    (state.limits.filter (·.id.raw == address)).size == 1

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
    if !(← publishedOperation state registration.operation) then
      rejected := rejected.push s!"{described}: {registration.operation} is not a published operation"
    else if !parsed.backends.any (·.name == registration.backend) then
      rejected := rejected.push
        s!"{described}: the backend {registration.backend} is not declared in the manifest"
    else if let some defect := registration.preferredRoutes.findSome? (preferenceDefect state) then
      rejected := rejected.push s!"{described}: a declared preferred route is malformed: {defect}"
    else if applicationAddressConflict state registration.operation then
      rejected := rejected.push s!"{described}: the application address also names another registered row"
    else if let some row := publishedApplication? state registration.operation then
      if let some defect := applicationFormDefect state row registration.input then
        rejected := rejected.push s!"{described}: {defect}"
      else admitted := admitted.push registration
    else if let some row := publishedProperty? state registration.operation then
      if let some defect := propertyFormDefect state row registration.input then
        rejected := rejected.push s!"{described}: {defect}"
      else admitted := admitted.push registration
    else if let some row := publishedPresentation? state registration.operation then
      if let some defect := presentationFormDefect state row registration.input then
        rejected := rejected.push s!"{described}: {defect}"
      else admitted := admitted.push registration
    else if let some family ← publishedLimitUniversal? state registration.operation then
      if registration.input == family.input then admitted := admitted.push registration
      else
        rejected := rejected.push
          s!"{described}: the universal family requires its complete native input {family.input}"
    else if let some family ← publishedCreation? state registration.operation then
      let input := family.entry.id.raw ++ "#input"
      if registration.input == input then admitted := admitted.push registration
      else
        rejected := rejected.push
          s!"{described}: the creation family requires its complete native input {input}"
    else admitted := admitted.push registration
  let installed := { parsed with registrations := admitted }
  return (installed, rejected)

end CasRuntime
