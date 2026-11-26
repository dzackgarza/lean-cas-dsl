module

public import CasCompiler.Layout
import all CasCompiler.Layout
public import CasCompiler.ConstructorTransport
public import CasCompiler.FieldType
public import CasRuntime.Owner
public import CasContract.Port
public import CasRuntime.CallablePacket
import CasContract.Failure
import Lean.Util.PtrSet

public section

namespace CasRuntime

open Lean Meta CasCompiler CasCatalogue.Backend

private def sameNativeSource (left right : ClosedTerm) : Bool :=
  left.context.exactlyMatches right.context && left.expression.equal right.expression &&
    left.type.equal right.type && left.universeParams == right.universeParams &&
    left.nativeDeclarations.exactlyMatches right.nativeDeclarations

private def compareNativeFieldRoles (left right : SourceLayout) : Bool :=
  let sameTerms := fun (left right : Array ClosedTerm) =>
    left.size == right.size && (left.zip right).all (fun (left, right) =>
      sameNativeSource left right)
  let sameProjection := match left.inputProjection, right.inputProjection with
    | none, none => true
    | some left, some right =>
      left.path == right.path && (match left.target, right.target with
        | .argument left, .argument right => left == right
        | .context left, .context right => left == right
        | _, _ => false)
    | _, _ => false
  left.address == right.address && left.kind == right.kind &&
    sameNativeSource left.source right.source &&
    left.contextDependencies == right.contextDependencies && sameProjection &&
    sameTerms left.recordAncestors right.recordAncestors &&
    left.selectionBinding == right.selectionBinding &&
    SourceSelectionScope.exactlyMatches sameNativeSource left.selections right.selections &&
    left.fields.size == right.fields.size &&
    (left.fields.zip right.fields).all (fun (left, right) =>
      left.address == right.address && left.projection == right.projection &&
        left.sourceIndex == right.sourceIndex && left.wireIndex == right.wireIndex &&
        left.precedingDependencies == right.precedingDependencies && left.kind == right.kind &&
        sameNativeSource left.source right.source &&
        sameNativeSource left.typeFamily right.typeFamily &&
        sameTerms left.recordAncestors right.recordAncestors &&
        SourceSelectionScope.exactlyMatches sameNativeSource left.selections right.selections)

private unsafe def sameNativeFieldRoleUnsafe (left right : SourceLayout) : Bool :=
  if ptrEq left right then true else compareNativeFieldRoles left right

/-- Every observed field is reflexive on an immutable layout. Pointer identity preserves
the complete role; distinct layout objects retain the full native comparison. -/
@[implemented_by sameNativeFieldRoleUnsafe]
private def sameNativeFieldRole (left right : SourceLayout) : Bool :=
  compareNativeFieldRoles left right

/-- One exact record occurrence's prepared source and runtime association identity. -/
structure RecordAssociation where
  private mk ::
  id : RuntimeId .association
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  layout : RecordLayout
  bindings : Array BindingId

/-- One prepared application's source slots and selected result dependencies.
Actual values remain in the binding below, independently of the original producing node. -/
structure ApplicationAssociation where
  private mk ::
  id : RuntimeId .association
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  layout : ApplicationLayout
  path : Array Name
  dependencies : Array Nat
  contextDependencies : Array Nat

/-- Original consuming field data, with an optional checked descendant dependency view.
The parameter permits the same data to be retained inside a recursive ValueBinding.
Creating this record cannot attach an association to a value; that boundary remains private. -/
structure FieldInstantiationData (binding : Type) where
  id : RuntimeId .association
  association : RecordAssociation
  field : FieldLayout
  preceding : Array (Option binding)
  view : Option FieldDependencyView := none

def FieldInstantiationData.typeFamily (value : FieldInstantiationData binding) : ClosedTerm :=
  (value.view.map (·.typeFamily)).getD value.field.typeFamily

def FieldInstantiationData.precedingDependencies (value : FieldInstantiationData binding) :
    Array Nat :=
  (value.view.map (·.precedingDependencies)).getD value.field.precedingDependencies

def FieldInstantiationData.projectionPath (value : FieldInstantiationData binding) : Array Name :=
  (value.view.map (·.path)).getD #[]

/-- A native constructor slot has this complete immutable producer context when the same
actual port is viewed at its source-prescribed result field. Parameters remain inert provenance;
only the selected type dependencies contribute owners. As with FieldInstantiationData,
constructing this generic record cannot attach it to a value: inTelescope remains private. -/
structure TelescopeInstantiationData (binding : Type) where
  id : RuntimeId .association
  sourceBinding : BindingId
  transport : ConstructorProjectionTransport
  source : SourceLayout
  selected : binding
  parameters : Array (Option binding)
  path : Array Name

/-- Immutable graph-visibility obligations. Every constructor is private to the binding
owner. Guarded bodies retain shared immutable arrays, rather than expanding their descendants. -/
inductive ValueVisibilityCheck where
  | private value (id : RuntimeId .value)
  | private association (id : RuntimeId .association) (message : String)
  | private worker (worker : String) (message : String)
  | private failure (message : String)
  | private firstVisit (id : RuntimeId .association) (body : Array ValueVisibilityCheck)
  | private remember (id : RuntimeId .association)

/-- Exact structural graph obligations retained by one binding constructor.
No owner, liveness, native type, selection, or result-admission decision is stored here. -/
structure ValueVisibility where
  private mk ::
  private checks : Array ValueVisibilityCheck

private def ValueVisibility.single (check : ValueVisibilityCheck) : ValueVisibility :=
  ⟨#[check]⟩

private def ValueVisibility.require (condition : Bool) (message : String) : ValueVisibility :=
  if condition then ⟨#[]⟩ else .single (.failure message)

/-- These checks can be contracted only after an earlier check at this same sequential level.
An association guard already reached either entered and remembered its ID, or skipped because
the ID was already visited. Its later repetition therefore cannot enter its body. Nested
guards never contribute IDs to this comparison at their enclosing sequential level. -/
private def ValueVisibilityCheck.repeated (left right : ValueVisibilityCheck) : Bool :=
  match left, right with
  | .value left, .value right => left == right
  | .association left leftMessage, .association right rightMessage =>
    left == right && leftMessage == rightMessage
  | .worker left leftMessage, .worker right rightMessage =>
    left == right && leftMessage == rightMessage
  | .failure left, .failure right => left == right
  | .firstVisit left _, .firstVisit right _ => left == right
  | .remember left, .remember right => left == right
  | _, _ => false

/-- Keep the original first occurrence of each redundant check, without descending any
guarded body. All remaining bodies are shared as immutable data and checked only when entered. -/
private def ValueVisibility.concat (parts : Array ValueVisibility) : ValueVisibility := Id.run do
  let mut checks : Array ValueVisibilityCheck := #[]
  for part in parts do
    for check in part.checks do
      unless checks.any (·.repeated check) do
        checks := checks.push check
  return ⟨checks⟩

private def ValueVisibility.whenFresh (id : RuntimeId .association)
    (body : ValueVisibility) : ValueVisibility :=
  .single (.firstVisit id body.checks)

/-- A consuming role retains its underlying binding and actual dependent prefix.
The recursive data keep earlier associations when an existing node fills another role.
Source: the data model's ResultBinding and dependency-ordered DataInterface contract. -/
inductive ValueBinding where
  /-- Issued only by checked input admission or an exact prepared input-result route.
  The displayed consuming role stays on binding; native retains its complete original interface. -/
  | private inNativeInterface (binding native : ValueBinding) (visibility : ValueVisibility)
  | private direct (value : RuntimeId .value) (role : SourceLayout)
  | private atRole (binding : ValueBinding) (role : SourceLayout)
      (parameters : Option (Array (Option ValueBinding)))
      (sourceDependencies : Array ValueBinding) (visibility : ValueVisibility)
  | private inField (id : RuntimeId .association) (binding : ValueBinding) (role : SourceLayout)
      (association : RecordAssociation) (field : FieldLayout)
      (preceding : Array (Option ValueBinding)) (view : Option FieldDependencyView)
      (visibility : ValueVisibility)
  | private inApplication (binding : ValueBinding) (role : SourceLayout)
      (association : ApplicationAssociation)
      (parameters applicationParameters arguments : Array (Option ValueBinding))
      (callable access : Option ValueBinding) (fields : Array ValueBinding)
      (visibility : ValueVisibility)
  | private inProjection (id : RuntimeId .association) (binding : ValueBinding)
      (role : SourceLayout) (parent : ValueBinding) (path : Array Name)
      (basis : ValueBinding) (fields : Array ValueBinding)
      (dependencies : Array (FieldInstantiationData ValueBinding))
      (visibility : ValueVisibility)
  | private inTelescope (binding : ValueBinding) (role : SourceLayout)
      (instantiation : TelescopeInstantiationData ValueBinding)
      (fields : Option (Array ValueBinding)) (visibility : ValueVisibility)

def ValueBinding.value : ValueBinding → RuntimeId .value
  | .direct value _ => value
  | .inNativeInterface binding _ _ => binding.value
  | .atRole binding .. | .inField _ binding .. | .inApplication binding ..
  | .inProjection _ binding .. | .inTelescope binding .. => binding.value

def ValueBinding.role : ValueBinding → SourceLayout
  | .inNativeInterface binding _ _ => binding.role
  | .direct _ role | .atRole _ role .. | .inField _ _ role .. | .inApplication _ role ..
  | .inProjection _ _ role .. | .inTelescope _ role .. => role

/-- Read only the explicit admission relation at this exact consuming view. -/
def ValueBinding.admittedInterface? : ValueBinding → Option ValueBinding
  | .inNativeInterface _ native _ => some native
  | _ => none

/-- The native operation interface is either explicitly admitted or the displayed interface.
No earlier role, payload, or descriptive source is searched. -/
def ValueBinding.nativeInterface (binding : ValueBinding) : ValueBinding :=
  binding.admittedInterface?.getD binding

def ValueBinding.nativeRole (binding : ValueBinding) : SourceLayout :=
  binding.nativeInterface.role

abbrev FieldInstantiation := FieldInstantiationData ValueBinding
abbrev TelescopeInstantiation := TelescopeInstantiationData ValueBinding

/-- Native telescope transports remain in the original role chain, independently of later
field, projection and application views of the same node. -/
def ValueBinding.telescopeInstantiations : ValueBinding → Array TelescopeInstantiation
  | .inNativeInterface binding _ _ => binding.telescopeInstantiations
  | .direct .. => #[]
  | .atRole binding .. | .inField _ binding .. | .inApplication binding ..
  | .inProjection _ binding .. => binding.telescopeInstantiations
  | .inTelescope binding _ instantiation _ _ =>
    binding.telescopeInstantiations.push instantiation

/-- Source type families are instantiated by these exact references, never decoded Lean terms. -/
def ValueBinding.instantiations : ValueBinding → Array FieldInstantiation
  | .inNativeInterface binding _ _ => binding.instantiations
  | .direct .. => #[]
  | .atRole binding .. => binding.instantiations
  | .inField id binding _ association field preceding view _ =>
    binding.instantiations.push ⟨id, association, field, preceding, view⟩
  | .inApplication binding .. | .inTelescope binding .. => binding.instantiations
  | .inProjection _ binding _ _ _ _ _ dependencies _ => binding.instantiations ++ dependencies

structure ApplicationInstantiation where
  private mk ::
  association : ApplicationAssociation
  parameters : Array (Option ValueBinding)
  applicationParameters : Array (Option ValueBinding)
  arguments : Array (Option ValueBinding)
  callable : Option ValueBinding
  access : Option ValueBinding

/-- Retain every consuming application in order, including earlier views of an aliased node. -/
def ValueBinding.applications : ValueBinding → Array ApplicationInstantiation
  | .inNativeInterface binding _ _ => binding.applications
  | .direct .. => #[]
  | .atRole binding .. | .inField _ binding .. | .inProjection _ binding ..
  | .inTelescope binding .. =>
    binding.applications
  | .inApplication binding _ association parameters applicationParameters arguments callable access _ _ =>
    binding.applications.push ⟨association, parameters, applicationParameters, arguments, callable, access⟩

/-- Field and application identities share one ordered role chain on the same actual node. -/
def ValueBinding.associationIds : ValueBinding → Array (RuntimeId .association)
  | .inNativeInterface binding _ _ => binding.associationIds
  | .direct .. => #[]
  | .atRole binding .. => binding.associationIds
  | .inField id binding .. => binding.associationIds.push id
  | .inApplication binding _ association .. => binding.associationIds.push association.id
  | .inProjection id binding .. => binding.associationIds.push id
  | .inTelescope binding _ instantiation _ _ =>
    binding.associationIds.push instantiation.id

/-- Each private association constructor retains its own exact summary. Reading a child
summary never traverses the child's association body or expands a shared parameter DAG. -/
private def ValueBinding.visibility : ValueBinding → ValueVisibility
  | .direct identity _ => .single (.value identity)
  | .inNativeInterface _ _ visibility
  | .atRole _ _ _ _ visibility
  | .inField _ _ _ _ _ _ _ visibility
  | .inApplication _ _ _ _ _ _ _ _ _ visibility
  | .inProjection _ _ _ _ _ _ _ _ visibility
  | .inTelescope _ _ _ _ visibility => visibility

/-- Only designated admission owners attach this existing native-interface relation.
The visibility summary is derived from the exact two bindings at the same attachment. -/
private def ValueBinding.attachNativeInterface (binding native : ValueBinding) : ValueBinding :=
  let visibility := if binding.value == native.value &&
      native.associationIds.toList.isPrefixOf binding.associationIds.toList then
    ValueVisibility.concat #[binding.visibility, native.visibility]
  else ValueVisibility.single
    (.failure "an admitted native interface changed its original runtime occurrence")
  .inNativeInterface binding native visibility

private def ValueBinding.attachField (identity : RuntimeId .association) (binding : ValueBinding)
    (role : SourceLayout) (association : RecordAssociation) (field : FieldLayout)
    (preceding : Array (Option ValueBinding)) (view : Option FieldDependencyView) : ValueBinding :=
  let message := "the field association has a foreign worker or incomplete source prefix"
  let checks : Array ValueVisibility := #[
    .single (.association identity "the field association is outside the visible graph"),
    .single (.worker identity.worker message),
    .single (.worker association.id.worker message),
    .require (field.sourceIndex == preceding.size) message,
    .single (.remember identity), binding.visibility]
  let visibility := ValueVisibility.whenFresh identity <| .concat <| checks ++
    (preceding.filterMap id).map (·.visibility)
  .inField identity binding role association field preceding view visibility

private def ValueBinding.attachApplication (binding : ValueBinding) (role : SourceLayout)
    (association : ApplicationAssociation)
    (parameters applicationParameters arguments : Array (Option ValueBinding))
    (callable access : Option ValueBinding) (fields : Array ValueBinding) : ValueBinding :=
  let message := "the application association belongs to a different worker"
  let checks : Array ValueVisibility := #[
    .single (.association association.id "the application association is outside the visible graph"),
    .single (.worker association.id.worker message),
    .single (.worker association.program.worker message),
    .single (.worker association.occurrence.worker message),
    .single (.remember association.id), binding.visibility]
  let references := parameters.filterMap id ++ applicationParameters.filterMap id ++
    arguments.filterMap id ++
    (match callable with | none => #[] | some value => #[value]) ++
    (match access with | none => #[] | some value => #[value]) ++ fields
  let visibility := ValueVisibility.whenFresh association.id <|
    .concat <| checks ++ references.map (·.visibility)
  .inApplication binding role association parameters applicationParameters arguments
    callable access fields visibility

private def ValueBinding.attachProjection (identity : RuntimeId .association)
    (binding : ValueBinding) (role : SourceLayout) (parent : ValueBinding) (path : Array Name)
    (basis : ValueBinding) (fields : Array ValueBinding)
    (dependencies : Array FieldInstantiation) : ValueBinding := Id.run do
  let message := "the projection association is outside the visible graph"
  let mut checks : Array ValueVisibility := #[
    .single (.association identity message),
    .single (.worker identity.worker message),
    .require (!path.isEmpty) message,
    .single (.remember identity), binding.visibility, parent.visibility]
  checks := checks ++ fields.map (·.visibility)
  for dependency in dependencies do
    let message := "a projected field dependency lost its original association or prefix"
    checks := checks ++ #[
      .single (.association dependency.id message),
      .single (.worker dependency.id.worker message),
      .single (.worker dependency.association.id.worker message),
      .require (dependency.field.sourceIndex == dependency.preceding.size) message]
    checks := checks ++ (dependency.preceding.filterMap id).map (·.visibility)
  let visibility := ValueVisibility.whenFresh identity (.concat checks)
  return .inProjection identity binding role parent path basis fields dependencies visibility

private def ValueBinding.attachTelescope (binding : ValueBinding) (role : SourceLayout)
    (instantiation : TelescopeInstantiation) (fields : Option (Array ValueBinding)) : ValueBinding :=
  let message := "the native telescope association lost its original complete source scope"
  let checks : Array ValueVisibility := #[
    .single (.association instantiation.id message),
    .single (.worker instantiation.id.worker message),
    .require (instantiation.parameters.size == instantiation.transport.plan.context.entries.size) message,
    .single (.remember instantiation.id), binding.visibility, instantiation.selected.visibility]
  let visibility := ValueVisibility.whenFresh instantiation.id <| .concat <| checks ++
    (instantiation.parameters.filterMap id).map (·.visibility) ++
    (fields.getD #[]).map (·.visibility)
  .inTelescope binding role instantiation fields visibility

/-- Recompute a new role frame's visibility from its exact full constructor fields.
No value or association identity selects a reusable role summary. -/
private def roleVisibility (binding : ValueBinding) (role : SourceLayout)
    (parameters : Option (Array (Option ValueBinding)))
    (dependencies : Array ValueBinding) : ValueVisibility :=
  let localCheck := match parameters with
    | some parameters =>
      ValueVisibility.require (parameters.size == role.source.context.entries.size)
        "a consuming role lost its complete source parameter table"
    | none =>
      ValueVisibility.require (role.source.context.exactlyMatches binding.role.source.context)
        "a consuming role lost its original source context"
  .concat <| #[localCheck, binding.visibility] ++
    ((parameters.getD #[]).filterMap id).map (·.visibility) ++ dependencies.map (·.visibility)

/-- The exact record accesses retained in binding order, through later aliases and projections.
Reuse: the immutable binding chain; no expression or value search selects a parent. -/
def ValueBinding.projectionAccesses : ValueBinding → Array (ValueBinding × Array Name)
  | .inNativeInterface binding _ _ => binding.projectionAccesses
  | .direct .. => #[]
  | .atRole binding .. | .inField _ binding .. | .inApplication binding ..
  | .inTelescope binding .. =>
    binding.projectionAccesses
  | .inProjection _ binding _ parent path _ _ _ _ => binding.projectionAccesses.push (parent, path)

/-- The selected binding before this access added consuming associations.
Reuse: the exact projection producer, retained parent identities and native paths. This baseline
lets a later reply retain an already visible captured value without naming fresh access IDs. -/
def ValueBinding.projectionBasis (value parent : ValueBinding) (path : Array Name) :
    Option ValueBinding :=
  match value with
  | .inNativeInterface binding _ _ => binding.projectionBasis parent path
  | .direct .. => none
  | .atRole binding .. | .inField _ binding .. | .inApplication binding ..
  | .inTelescope binding .. =>
    binding.projectionBasis parent path
  | .inProjection _ binding _ selected selectedPath basis _ _ _ =>
    if selected.value == parent.value && selected.associationIds == parent.associationIds &&
        selectedPath == path then some basis
    else binding.projectionBasis parent path

/-- A projection view retains its exact pre-access binding. This relation identifies an
intermediate parent without erasing unrelated field or application associations. -/
private def ValueBinding.projectionParent : ValueBinding → ValueBinding
  | .inNativeInterface binding _ _ => binding.projectionParent
  | .atRole binding .. | .inTelescope binding .. => binding.projectionParent
  | .inProjection _ _ _ _ _ basis _ _ _ => basis.projectionParent
  | binding => binding

/-- Only the native type's selected actual references contribute owners at this source view. -/
def ValueBinding.sourceDependencies : ValueBinding → Array ValueBinding
  | .inNativeInterface binding _ _ => binding.sourceDependencies
  | .direct .. => #[]
  | .atRole binding _ _ dependencies _ => binding.sourceDependencies ++ dependencies
  | .inField _ binding .. | .inApplication binding .. | .inProjection _ binding ..
  | .inTelescope binding .. =>
    binding.sourceDependencies

/-- Earlier checked native type roles that introduced actual bound dependencies.
They remain in the existing role chain when a later view changes the displayed source role. -/
def ValueBinding.dependencyRoles : ValueBinding → Array SourceLayout
  | .inNativeInterface binding _ _ => binding.dependencyRoles
  | .direct .. => #[]
  | .atRole binding role _ dependencies _ =>
    if dependencies.isEmpty then binding.dependencyRoles else binding.dependencyRoles.push role
  | .inField _ binding .. | .inApplication binding .. | .inProjection _ binding ..
  | .inTelescope binding .. =>
    binding.dependencyRoles

/-- Complete parameter positions carried by the displayed source view, when the role
association itself owns them. A direct node obtains its table from its immutable origin. -/
def ValueBinding.sourceParameters? : ValueBinding → Option (Array (Option ValueBinding))
  | .inNativeInterface binding _ _ => binding.sourceParameters?
  | .direct .. => none
  | .atRole binding _ parameters _ _ =>
    match parameters with | some _ => parameters | none => binding.sourceParameters?
  | .inApplication _ _ _ parameters .. => some parameters
  | .inField _ binding .. | .inProjection _ binding .. | .inTelescope binding .. =>
    binding.sourceParameters?

/-- One stored source-role association, retained as inert observation provenance.
The optional parameter table and dependency array are the exact fields of that association. -/
structure SourceRoleFrame where
  role : SourceLayout
  parameters : Option (Array (Option ValueBinding))
  dependencies : Array ValueBinding

/-- Stored source-role frames in their original inner-to-outer order.
This reports the existing chain; it does not select an execution interface or a supplier. -/
def ValueBinding.sourceRoleFrames : ValueBinding → Array SourceRoleFrame
  | .inNativeInterface binding _ _ => binding.sourceRoleFrames
  | .direct .. => #[]
  | .atRole binding role parameters dependencies _ =>
    binding.sourceRoleFrames.push ⟨role, parameters, dependencies⟩
  | .inField _ binding .. | .inApplication binding .. | .inProjection _ binding ..
  | .inTelescope binding .. =>
    binding.sourceRoleFrames

private def ValueBinding.compareViews [Monad m]
    (compare : ValueBinding → ValueBinding → m Bool)
    (left right : ValueBinding) : m Bool := do
  unless left.value == right.value && left.associationIds == right.associationIds &&
      sameNativeFieldRole left.role right.role do return false
  match left.sourceParameters?, right.sourceParameters? with
  | none, none => pure ()
  | some left, some right =>
    unless left.size == right.size do return false
    for (left, right) in left.zip right do
      match left, right with
      | none, none => pure ()
      | some left, some right => unless ← compare left right do return false
      | _, _ => return false
  | _, _ => return false
  let leftRoles := left.dependencyRoles
  let rightRoles := right.dependencyRoles
  unless leftRoles.size == rightRoles.size &&
      (leftRoles.zip rightRoles).all (fun (left, right) =>
        sameNativeFieldRole left right) do return false
  let leftDependencies := left.sourceDependencies
  let rightDependencies := right.sourceDependencies
  unless leftDependencies.size == rightDependencies.size do return false
  for (left, right) in leftDependencies.zip rightDependencies do
    unless ← compare left right do return false
  match left.admittedInterface?, right.admittedInterface? with
  | none, none => pure true
  | some left, some right => compare left right
  | _, _ => pure false

-- Each cache entry records a completed comparison of these two complete immutable
-- objects. PtrMap retains both keys and distinguishes hash collisions by pointer equality.
-- In particular, sharing on either side never authorizes a different pair of views.
private unsafe def ValueBinding.exactlyMatchesCached (left right : ValueBinding) :
    StateM (PtrMap ValueBinding (PtrMap ValueBinding Bool)) Bool := do
  if ptrEq left right then return true
  if let some paired := (← get).find? left then
    if let some result := paired.find? right then return result
  let result ← ValueBinding.compareViews ValueBinding.exactlyMatchesCached left right
  modify fun cache =>
    cache.insert left (((cache.find? left).getD mkPtrMap).insert right result)
  return result

private unsafe def ValueBinding.exactlyMatchesUnsafe (left right : ValueBinding) : Bool :=
  (ValueBinding.exactlyMatchesCached left right).run' mkPtrMap

-- A nonrecursive public wrapper lets Lean export the private implementation's
-- compiled signature. A partial wrapper compiles an auxiliary declaration
-- without the original implemented_by attribute.
private partial def ValueBinding.exactlyMatchesReference (left right : ValueBinding) : Bool :=
  Id.run <| ValueBinding.compareViews
    (fun left right => pure (ValueBinding.exactlyMatchesReference left right)) left right

/-- Exact complete source views for retaining an already admitted relation.
Identity alone is insufficient: every source table, dependent view and native relation agrees. -/
@[implemented_by ValueBinding.exactlyMatchesUnsafe]
def ValueBinding.exactlyMatches (left right : ValueBinding) : Bool :=
  ValueBinding.exactlyMatchesReference left right

private def sameInterfaceParameters (left right : Option (Array (Option ValueBinding))) : Bool :=
  match left, right with
  | none, none => true
  | some left, some right =>
    left.size == right.size && (left.zip right).all (fun (left, right) =>
      match left, right with
      | none, none => true
      | some left, some right => left.exactlyMatches right
      | _, _ => false)
  | _, _ => false

/-- Preserve an existing certified native interface only across the same full consuming view.
This cannot create an interface or authorize a different dependent parameter occurrence. -/
private def retainAdmittedInterface (original current : ValueBinding) : ValueBinding :=
  match original.admittedInterface? with
  | none => current
  | some native =>
    if original.value == current.value &&
        original.associationIds.toList.isPrefixOf current.associationIds.toList &&
        sameNativeFieldRole original.role current.role &&
        sameInterfaceParameters original.sourceParameters? current.sourceParameters? &&
        original.dependencyRoles.size == current.dependencyRoles.size &&
        (original.dependencyRoles.zip current.dependencyRoles).all (fun (left, right) =>
          sameNativeFieldRole left right) &&
        original.sourceDependencies.size == current.sourceDependencies.size &&
        (original.sourceDependencies.zip current.sourceDependencies).all (fun (left, right) =>
          left.exactlyMatches right) then
      current.attachNativeInterface native
    else current

/-- Keep the original node and all admitted type dependencies at a consuming source role.
Runtime occurrences are resolved only by typed source binders; no term annotation is retained. -/
opaque ValueBinding.withRole (binding : ValueBinding) (role : SourceLayout)
    (sourceDependencies : Array ValueBinding := #[])
    (parameters : Option (Array (Option ValueBinding)) := none) : Except String ValueBinding := do
  if role.kind == .proof then throw "a source proof has no computational value binding"
  let parameters ← match parameters with
    | some parameters =>
      unless parameters.size == role.source.context.entries.size do
        throw "a consuming role requires its complete source parameter table"
      pure (some parameters)
    | none =>
      unless role.source.context.exactlyMatches binding.role.source.context do
        throw "a consuming role changed its source context without original parameter positions"
      pure (match binding with | .atRole _ _ parameters _ _ => parameters | _ => none)
  let underlying := match binding with
    | .atRole underlying previousRole previousParameters dependencies _ =>
      if dependencies.isEmpty && sameNativeFieldRole previousRole role &&
          sameInterfaceParameters previousParameters parameters then underlying
      else binding
    | _ => binding
  let current := .atRole underlying role parameters sourceDependencies
    (roleVisibility underlying role parameters sourceDependencies)
  return retainAdmittedInterface binding current

private def selectedReferences (indices : Array Nat) (values : Array (Option ValueBinding)) :
    Except String (Array ValueBinding) := do
  let mut selected := #[]
  for index in indices do
    let some value := values[index]?
      | throw "a result dependency is outside its complete reference table"
    if let some value := value then selected := selected.push value
  return selected

structure ContainerSlot where
  path : Array InputPathStep
  binding : ValueBinding
  /-- Computational field position, or an independent retained reference. -/
  fieldIndex : Option Nat

/-- A supplying connection's actual export at one original inert packet position.
This retains transport ownership and captures without inventing a native mathematical value. -/
structure PacketExport where
  private mk ::
  path : Array InputPathStep
  originScope : RuntimeId .scope
  originPath : Array InputPathStep
  owner : ConnectionGeneration
  token : String
  captures : Array ValueBinding

opaque PacketExport.fromConnection (connection : Connection) (originScope : RuntimeId .scope)
    (originPath path : Array InputPathStep)
    (token : String) (captures : Array ValueBinding) : Except String PacketExport := do
  unless originScope.worker == connection.generation.worker do
    throw "an inert packet export changed its original reply worker"
  if token.isEmpty then throw "an inert packet export requires its actual nonempty token"
  return ⟨path, originScope, originPath, connection.generation, token, captures⟩

/-- Move the same admitted export beneath one outer literal packet position. -/
opaque PacketExport.prefixed (exported : PacketExport) (nativePrefix : Array InputPathStep) :
    PacketExport :=
  { exported with path := nativePrefix ++ exported.path }

/-- The complete admitted packet before native field associations enrich its storage view.
Its original reference leaves remain separate from that later source-ordered field table. -/
structure OriginalPacket where
  private mk ::
  template : Json
  slots : Array ContainerSlot
  exports : Array PacketExport

/-- Literal packet structure, typed substitution slots and any actual field/callable bindings.
`none` fields denotes a descriptor without native field data; `some #[]` is an actual empty
record. A source record schema alone does not create computational field identities. -/
structure ValueContainer where
  private mk ::
  template : Json
  slots : Array ContainerSlot
  fields : Option (Array ValueBinding)
  callable : Option ValueBinding
  exports : Array PacketExport
  callableData : Bool
  originalPacket : Option OriginalPacket

/-- Replace only a previously located JSON position.
Reference: Lean.Json array/object operations and CasContract.Port's InputPathStep grammar. -/
private def replacePosition (json : Json) (path : List InputPathStep) (replacement : Json) :
    Except String Json := do
  match path, json with
  | [], _ => return replacement
  | .index index :: rest, .arr values =>
    let some value := values[index]? | throw "the container position is outside its array"
    return .arr (values.set! index (← replacePosition value rest replacement))
  | .field name :: rest, .obj fields =>
    let value ← json.getObjVal? name
    let value ← replacePosition value rest replacement
    return Json.mkObj (fields.toList.map fun (key, entry) =>
      (key, if key == name then value else entry))
  | _, _ => throw "the container position does not follow the retained JSON structure"

/-- A retained literal cannot carry ambient reference or native-token authority.
Reference: CasContract.Port.validateResultRefs and the runtime immediate-control JSON walk. -/
partial def checkLiteral (json : Json) : Except String Unit := do
  if let .ok tag := json.getObjValAs? String "ctor" then
    if #["scopeRef", "inputRef", "resultRef", "opaqueData", "deferredData"].contains tag then
      throw "the container has an unbound reference, native token or deferred control"
  match json with
  | .arr entries => for entry in entries do checkLiteral entry
  | .obj entries => for (_, entry) in entries.toList do checkLiteral entry
  | _ => pure ()

private def makeContainer (template : Json) (slots : Array ContainerSlot)
    (fields : Option (Array ValueBinding)) (callable : Option ValueBinding)
    (exports : Array PacketExport := #[]) :
    Except String ValueContainer := do
  let mut paths : Array (List InputPathStep) := #[]
  let mut template := template
  for slot in slots do
    if let some index := slot.fieldIndex then
      let some stored := fields
        | throw "a descriptor slot cannot claim an unavailable native field"
      let some field := stored[index]?
        | throw "the container slot is outside its source field table"
      unless slot.binding.value == field.value &&
          slot.binding.associationIds == field.associationIds do
        throw "the container slot does not retain its declared source field"
    let path := slot.path.toList
    if paths.any (fun previous => previous.isPrefixOf path || path.isPrefixOf previous) then
      throw "container reference positions overlap"
    template ← replacePosition template path .null
    paths := paths.push path
  for exported in exports do
    let path := exported.path.toList
    if paths.any (fun previous => previous.isPrefixOf path || path.isPrefixOf previous) then
      throw "inert packet export positions overlap another retained slot"
    template ← replacePosition template path .null
    paths := paths.push path
  checkLiteral template
  if let some binding := callable then
    unless binding.role.kind == .function do
      throw "the container callable has no prepared function interface"
  return ⟨template, slots, fields, callable, exports, false, none⟩

/-- Authenticate the original complete reply packet retained by this exact native result.
Native field associations may extend an original binding, but a sibling association cannot
replace it. The caller supplies the immutable packet captured before field staging. -/
def ValueContainer.retainsOriginalPacket (container expected : ValueContainer) : Bool :=
  match container.originalPacket with
  | none => false
  | some original =>
    original.template == expected.template && original.slots.size == expected.slots.size &&
      ((original.slots.zip expected.slots).all fun (actual, retained) =>
        actual.path == retained.path && actual.fieldIndex == retained.fieldIndex &&
          actual.binding.value == retained.binding.value &&
          retained.binding.associationIds.toList.isPrefixOf actual.binding.associationIds.toList) &&
      original.exports.size == expected.exports.size &&
      ((original.exports.zip expected.exports).all fun (actual, retained) =>
        actual.path == retained.path && actual.originScope == retained.originScope &&
          actual.originPath == retained.originPath && actual.owner == retained.owner &&
          actual.token == retained.token && actual.captures.size == retained.captures.size &&
          ((actual.captures.zip retained.captures).all fun (actual, retained) =>
            actual.value == retained.value &&
              retained.associationIds.toList.isPrefixOf actual.associationIds.toList))

/-- Both direct and original packet export owners constrain every later transport. -/
def ValueContainer.packetExports (container : ValueContainer) : Array PacketExport :=
  container.exports ++ (container.originalPacket.map (·.exports)).getD #[]

/-- Substitute freshly encoded references without rebuilding literal data from a source term. -/
opaque ValueContainer.fill (container : ValueContainer) (replacements : Array Json) :
    Except String Json := do
  unless replacements.size == container.slots.size do
    throw "container substitution does not match its exact reference arity"
  let mut packet := container.template
  for slot in container.slots, replacement in replacements do
    packet ← replacePosition packet slot.path.toList replacement
  unless container.exports.isEmpty do
    throw "an inert export packet requires its actual receiving owner before encoding"
  return packet

/-- Expose inert tokens only to their actual owning receiver. Foreign receivers retain
the whole typed map through the existing scoped interface. -/
opaque ValueContainer.fillForOwner (container : ValueContainer)
    (receiver : ConnectionGeneration) (replacements : Array Json) : Except String Json := do
  unless replacements.size == container.slots.size do
    throw "container substitution does not match its exact reference arity"
  unless container.packetExports.all (·.owner == receiver) do
    throw "an inert packet export belongs to another receiving connection"
  let mut packet := container.template
  for slot in container.slots, replacement in replacements do
    packet ← replacePosition packet slot.path.toList replacement
  for exported in container.exports do
    packet ← replacePosition packet exported.path.toList
      (ComputationalValue.opaque exported.token).encode
  return packet

/-- A transient compiler-checking view of complete descriptors. Opaque positions receive
temporary scoped indices, never mathematical values or transmitted tokens. Repeated views
share only the same original reply scope and absolute position, with unchanged authority. -/
opaque ValueContainer.nativeFraming (packets : Array ValueContainer) :
    Except String (Array Json × Array ValueBinding × Array PacketExport) := do
  let bindings := packets.flatMap (·.slots.map (·.binding))
  let mut originals : Array PacketExport := #[]
  for packet in packets do
    for exported in packet.exports do
      if let some original := originals.find? (fun original =>
          original.originScope == exported.originScope && original.originPath == exported.originPath) then
        unless original.owner == exported.owner && original.token == exported.token &&
            original.captures.size == exported.captures.size &&
            (original.captures.zip exported.captures).all (fun (first, second) =>
              first.value == second.value && first.associationIds == second.associationIds) do
          throw "one original opaque packet position changed its owner, token or captures"
      else
        originals := originals.push exported
  let mut framed := #[]
  let mut offset := 0
  for packet in packets do
    let mut value := packet.template
    for slot in packet.slots, index in [:packet.slots.size] do
      value ← replacePosition value slot.path.toList (ScopedReference.scope (offset + index)).encode
    for exported in packet.exports do
      let some index := originals.findIdx? (fun original =>
          original.originScope == exported.originScope && original.originPath == exported.originPath)
        | throw "the native framing view lost an original opaque packet position"
      value ← replacePosition value exported.path.toList
        (ScopedReference.scope (bindings.size + index)).encode
    framed := framed.push value
    offset := offset + packet.slots.size
  return (framed, bindings, originals)

inductive ValueData
  | portable (bytes : ByteArray)
  | product (fields : Array ValueBinding)
  | container (value : ValueContainer)
  | closure (program : RuntimeId .program) (captures : Array ValueBinding)
  | ownedToken (owner : ConnectionGeneration) (token : String) (captures : Array ValueBinding)

/-- The actual stored record table, distinct from a descriptor's native source schema.
Closures and native tokens keep their existing lazy interfaces outside this table. -/
def ValueData.storedFields? : ValueData → Option (Array ValueBinding)
  | .product fields => some fields
  | .container value => value.fields
  | _ => none

/-- Payload construction stamps native exports from the actual supplying connection. -/
structure ValuePayload where
  private mk ::
  data : ValueData

def ValuePayload.portable (bytes : ByteArray) : ValuePayload := ⟨.portable bytes⟩

def ValuePayload.product (fields : Array ValueBinding) : ValuePayload := ⟨.product fields⟩

opaque ValuePayload.container (template : Json) (slots : Array ContainerSlot)
    (fields : Array ValueBinding) (callable : Option ValueBinding) : Except String ValuePayload := do
  return ⟨.container (← makeContainer template slots (some fields) callable)⟩

/-- Retain a named source value and its actual packet inputs without fabricating its fields.
The public packet grammar is unchanged; no native projection or callable export is supplied. -/
opaque ValuePayload.descriptor (template : Json) (slots : Array ContainerSlot)
    (exports : Array PacketExport := #[]) :
    Except String ValuePayload := do
  return ⟨.container (← makeContainer template slots none none exports)⟩

/-- Store validated inert callable data, optionally with its independently retained native
continuation. The packet's framing does not execute it or provide mathematical evidence. -/
opaque ValuePayload.callablePacket (packet : CallablePacket) (slots : Array ContainerSlot)
    (callable : Option ValueBinding := none) (exports : Array PacketExport := #[])
    (original : Option ValueContainer := none) : Except String ValuePayload := do
  let container ← makeContainer packet.value slots none callable exports
  let originalPacket ← match original with
    | none => pure none
    | some original =>
      unless original.fields.isNone && original.callable.isNone &&
          original.originalPacket.isNone do
        throw "a callable result requires its original pre-staging descriptor"
      pure (some ⟨original.template, original.slots, original.exports⟩)
  return ⟨.container { container with callableData := true, originalPacket }⟩

/-- Retain an accepted operational continuation together with the original complete inert
packet. The wrapper keeps every actual export owner and capture, but is not itself portable
callable data: its native function interface is encoded through the ordinary scoped path. -/
opaque ValuePayload.retainedCallable (original : ValueContainer) (callable : ValueBinding) :
    Except String ValuePayload := do
  unless original.fields.isNone && original.callable.isNone &&
      original.originalPacket.isNone do
    throw "a retained callable requires its original pre-staging complete descriptor"
  let container ← makeContainer original.template original.slots none (some callable)
    original.exports
  return ⟨.container { container with
    originalPacket := some ⟨original.template, original.slots, original.exports⟩ }⟩

/-- Attach source-ordered native fields to the original complete returned descriptor while
preserving its pre-staging packet and exact reference leaves. This creates no new field value. -/
opaque ValuePayload.completeContainer (original : ValueContainer)
    (slots : Array ContainerSlot) (fields : Array ValueBinding) : Except String ValuePayload := do
  unless original.fields.isNone && original.callable.isNone do
    throw "a complete result requires its original pre-staging descriptor"
  let exports := original.exports.filter fun owned =>
    !slots.any (fun slot => slot.path.toList.isPrefixOf owned.path.toList)
  let container ← makeContainer original.template slots (some fields) none exports
  return ⟨.container { container with
    originalPacket := some ⟨original.template, original.slots, original.exports⟩ }⟩

def ValuePayload.closure (program : RuntimeId .program)
    (captures : Array ValueBinding) : ValuePayload := ⟨.closure program captures⟩

opaque ValuePayload.ownedExport (connection : Connection) (token : String)
    (captures : Array ValueBinding) : ValuePayload :=
  ⟨.ownedToken connection.generation token captures⟩

/-- Actual argument references and this result role's native formal dependency slots. -/
structure ApplicationOrigin where
  private mk ::
  layout : ApplicationLayout
  parameters : Array (Option ValueBinding)
  arguments : Array (Option ValueBinding)
  path : Array Name
  dependencies : Array Nat
  contextDependencies : Array Nat
  callable : Option ValueBinding

/-- Keep all formal slots and actual references; proof slots have no payload.
Reuse: ApplicationLayout's native telescope and existing ValueBinding identities. -/
opaque ApplicationOrigin.ofArguments (layout : ApplicationLayout)
    (parameters arguments : Array (Option ValueBinding)) (callable : Option ValueBinding) :
    Except String ApplicationOrigin := do
  unless parameters.size == layout.result.source.context.entries.size do
    throw "application provenance requires its complete original context table"
  unless arguments.size == layout.arguments.size do
    throw "application provenance requires the complete argument table"
  for argument in arguments, prepared in layout.arguments do
    if prepared.wireIndex.isNone && argument.isSome then
      throw "a formal proof has no application provenance payload"
  return ⟨layout, parameters, arguments, #[], layout.resultDependencies,
    layout.resultContextDependencies, callable⟩

/-- Keep the original arguments while selecting this source field's own dependencies. -/
opaque ApplicationOrigin.forSource (origin : ApplicationOrigin) (parent source : SourceLayout) :
    MetaM ApplicationOrigin := do
  let path := origin.path ++ (← parent.projectionPathTo source)
  let dependencies ← origin.layout.dependenciesAt path
  return { origin with
    path
    dependencies := dependencies.arguments
    contextDependencies := dependencies.context }

/-- Continue the same source application through an actual record's native field.
The stored result identity licenses access through later source bindings; no source replay occurs. -/
opaque ApplicationOrigin.forProjection (origin : ApplicationOrigin) (projection : Name) :
    MetaM ApplicationOrigin := do
  let path := origin.path.push projection
  let dependencies ← origin.layout.dependenciesAt path
  return { origin with
    path
    dependencies := dependencies.arguments
    contextDependencies := dependencies.context }

private def ApplicationInstantiation.origin (value : ApplicationInstantiation) : ApplicationOrigin :=
  ⟨value.association.layout, value.applicationParameters, value.arguments,
    value.association.path, value.association.dependencies, value.association.contextDependencies,
    value.callable⟩

private def sameNativeApplication (left right : ApplicationOrigin) : Bool :=
  left.path == right.path && left.dependencies == right.dependencies &&
    left.contextDependencies == right.contextDependencies &&
    sameInterfaceParameters (some left.parameters) (some right.parameters) &&
    sameInterfaceParameters (some left.arguments) (some right.arguments) &&
    (match left.callable, right.callable with
      | none, none => true
      | some left, some right => left.exactlyMatches right
      | _, _ => false) &&
    sameNativeFieldRole left.layout.result right.layout.result &&
    left.layout.resultDependencies == right.layout.resultDependencies &&
    left.layout.resultContextDependencies == right.layout.resultContextDependencies &&
    sameNativeSource left.layout.resultTypeFamily right.layout.resultTypeFamily &&
    sameNativeSource left.layout.resultTermFamily right.layout.resultTermFamily &&
    sameNativeSource left.layout.nativeInputTermFamily right.layout.nativeInputTermFamily &&
    left.layout.arguments.size == right.layout.arguments.size &&
    (left.layout.arguments.zip right.layout.arguments).all (fun (left, right) =>
      left.sourceIndex == right.sourceIndex && left.wireIndex == right.wireIndex &&
        left.binderInfo == right.binderInfo &&
        left.precedingDependencies == right.precedingDependencies &&
        sameNativeFieldRole left.source right.source &&
        sameNativeSource left.typeFamily right.typeFamily)

/-- Exact original input-result routing licenses this native interface at one consuming role.
Only request preparation constructs the witness, after original input admission and routing. -/
structure AdmittedInputInterface where
  private mk ::
  program : RuntimeId .program
  occurrence : RuntimeId .occurrence
  role : SourceLayout
  parameters : Array (Option ValueBinding)
  application : ApplicationOrigin
  selected : ValueBinding
  native : ValueBinding

/-- One original producing record prefix, before its current field is supplied.
An inherited descendant keeps that same declared field family and prior proof/data slots. -/
structure NativeFieldPrefixFrame where
  private mk ::
  association : RecordAssociation
  field : FieldLayout
  preceding : Array (Option ValueBinding)
  view : Option FieldDependencyView := none

def NativeFieldPrefixFrame.precedingDependencies (frame : NativeFieldPrefixFrame) : Array Nat :=
  (frame.view.map (·.precedingDependencies)).getD frame.field.precedingDependencies

/-- The source-ordered predecessor witnesses available at one original native field.
There is deliberately no runtime value for the unassembled current parent. -/
structure NativeFieldPrefix where
  private mk ::
  native : SourceLayout
  frames : Array NativeFieldPrefixFrame

def NativeFieldPrefix.references (nativePrefix : NativeFieldPrefix) : Array ValueBinding :=
  nativePrefix.frames.flatMap (fun frame => frame.preceding.filterMap id)

def NativeFieldPrefix.dependencies (nativePrefix : NativeFieldPrefix) :
    Except String (Array ValueBinding) := do
  let mut values := #[]
  for frame in nativePrefix.frames do
    values := values ++ (← selectedReferences frame.precedingDependencies frame.preceding)
  return values


/-- A complete captured prefix remains an immutable part of its producing type evidence.
Joining another checked frame may extend the prefix, but cannot erase an original frame,
replace a predecessor occurrence, or change its native declaration view. -/
private def NativeFieldPrefix.retainsCapture (current captured : NativeFieldPrefix) : Bool :=
  let sameTerm := fun (left right : ClosedTerm) =>
    left.context.exactlyMatches right.context && left.expression.equal right.expression &&
      left.type.equal right.type && left.universeParams == right.universeParams &&
      left.nativeDeclarations.exactlyMatches right.nativeDeclarations
  let sameField := fun (left right : FieldLayout) =>
    left.address == right.address && left.projection == right.projection &&
      left.sourceIndex == right.sourceIndex && left.wireIndex == right.wireIndex &&
      left.precedingDependencies == right.precedingDependencies &&
      left.kind == right.kind && sameTerm left.source right.source &&
      sameTerm left.typeFamily right.typeFamily &&
      SourceSelectionScope.exactlyMatches sameTerm left.selections right.selections
  let sameFrame := fun (left right : NativeFieldPrefixFrame) =>
    left.association.id == right.association.id &&
      left.association.program == right.association.program &&
      left.association.occurrence == right.association.occurrence &&
      left.association.bindings == right.association.bindings &&
      sameNativeFieldRole left.association.layout.source right.association.layout.source &&
      left.association.layout.fields.size == right.association.layout.fields.size &&
      (left.association.layout.fields.zip right.association.layout.fields).all
        (fun (left, right) => sameField left.field right.field &&
          sameNativeFieldRole left.layout right.layout) &&
      sameField left.field right.field &&
      (match left.view, right.view with
        | none, none => true
        | some left, some right => left.path == right.path &&
          left.precedingDependencies == right.precedingDependencies &&
          sameTerm left.typeFamily right.typeFamily
        | _, _ => false) &&
      left.preceding.size == right.preceding.size &&
      (left.preceding.zip right.preceding).all (fun (left, right) =>
        match left, right with
        | none, none => true
        | some left, some right => left.value == right.value &&
          left.associationIds == right.associationIds &&
          sameNativeFieldRole left.role right.role
        | _, _ => false)
  sameNativeFieldRole current.native captured.native &&
    captured.frames.all (fun frame => current.frames.any (sameFrame frame))

/-- The snapshot can describe only the original fresh field producer; it cannot change
another role, request occurrence, declaration position, or computational/proof slot. -/
def NativeFieldPrefix.requireOrigin (nativePrefix : NativeFieldPrefix)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (source : SourceLayout) : Except String Unit := do
  unless sameNativeFieldRole nativePrefix.native source do
    throw "a producing field prefix changed its exact native source or address"
  for frame in nativePrefix.frames do
    unless frame.association.program == program && frame.association.occurrence == occurrence &&
        frame.field.sourceIndex == frame.preceding.size do
      throw "a producing field prefix changed its original occurrence or native telescope"
    for actual in frame.preceding, index in [:frame.preceding.size] do
      let some prepared := frame.association.layout.fields[index]?
        | throw "a producing field prefix is outside its original native record"
      unless prepared.field.sourceIndex == index &&
          prepared.field.wireIndex.isSome == actual.isSome do
        throw "a producing field prefix changed a native proof or computational slot"
      if let some actual := actual then
        unless sameNativeFieldRole prepared.layout actual.role do
          throw "a producing field prefix changed an earlier original native field view"

/-- A native producer's complete type-reference capture for one exact source role.
The constructor is private: references are derived from that role's typed source positions. -/
structure SourceDependencyCapture where
  private mk ::
  source : SourceLayout
  parameters : Array (Option ValueBinding)
  references : Array ValueBinding
  fieldPrefix : Option NativeFieldPrefix := none
  /-- An inherited prefix belongs to this exact retained parent and native projection path. -/
  projectedFrom : Option (ValueBinding × Array Name) := none

structure ValueOrigin where
  occurrence : RuntimeId .occurrence
  program : RuntimeId .program
  role : SourceLayout
  parameters : Array (Option ValueBinding)
  application : Option ApplicationOrigin := none
  access : Option ValueBinding := none
  accessPath : Array Name := #[]
  sourceDependencies : Option SourceDependencyCapture := none
  fieldPrefix : Option NativeFieldPrefix := none
  inputInterface : Option AdmittedInputInterface := none

/-- Precise native captures replace conservative whole-context/argument ownership only
for their exact original source and complete parameter positions. Raw origins retain the
existing conservative rule. Independently supplied field-prefix dependencies always remain. -/
def ValueOrigin.typeDependencies (origin : ValueOrigin) : Except String (Array ValueBinding) := do
  let mut references ← match origin.sourceDependencies with
    | some captured =>
      unless sameNativeFieldRole captured.source origin.role &&
          captured.parameters.size == origin.parameters.size do
        throw "a type dependency capture changed its complete original source role"
      if let some (parent, path) := captured.projectedFrom then
        let some actual := origin.access
          | throw "a projected type capture lost its original actual parent"
        unless !path.isEmpty && origin.accessPath == path &&
            parent.value == actual.value && parent.associationIds == actual.associationIds &&
            sameNativeFieldRole parent.role actual.role do
          throw "a projected type capture changed its original parent or native path"
      if let some original := captured.fieldPrefix then
        let some current := origin.fieldPrefix
          | throw "a type dependency capture lost its original native field prefix"
        unless current.retainsCapture original do
          throw "a type dependency capture changed its original native field prefix"
      for original in captured.parameters, current in origin.parameters do
        match original, current with
        | none, none => pure ()
        | some original, some current =>
          unless original.value == current.value &&
              original.associationIds == current.associationIds &&
              sameNativeFieldRole original.role current.role do
            throw "a type dependency capture changed an original parameter occurrence"
        | _, _ => throw "a type dependency capture changed an original formal/runtime position"
      pure captured.references
    | none => do
      let (contextDependencies, contextParameters) := match origin.application with
        | none => (origin.role.contextDependencies, origin.parameters)
        | some application => (application.contextDependencies, application.parameters)
      let mut references ← selectedReferences contextDependencies contextParameters
      if let some application := origin.application then
        references := references ++
          (← selectedReferences application.dependencies application.arguments)
      pure references
  if let some nativePrefix := origin.fieldPrefix then
    references := references ++ (← nativePrefix.dependencies)
  return references

/-- Authenticate a prepared forwarding witness against its unchanged complete request.
A public role update or another equal-valued input cannot reuse this native interface. -/
opaque ValueOrigin.admittedInputInterface (origin : ValueOrigin) :
    Except String (Option AdmittedInputInterface) := do
  let some original := origin.inputInterface | return none
  let some application := origin.application
    | throw "an admitted native interface lost its original application"
  unless original.program == origin.program && original.occurrence == origin.occurrence &&
      sameNativeFieldRole original.role origin.role &&
      sameInterfaceParameters (some original.parameters) (some origin.parameters) &&
      sameNativeApplication original.application application do
    throw "an admitted native interface changed its original consuming request"
  unless original.selected.value == original.native.value &&
      original.native.associationIds.toList.isPrefixOf original.selected.associationIds.toList &&
      original.native.exactlyMatches original.selected.nativeInterface do
    throw "an admitted native interface changed its exact original input"
  return some original

/-- Direct field frames retain their original producer occurrence. An inherited frame
must also occur in the sealed capture of this exact actual projection; any added frame
still belongs to the fresh producer. No frame may borrow another equal-source parent. -/
opaque ValueOrigin.checkFieldPrefix (origin : ValueOrigin) : Except String Unit := do
  discard <| origin.typeDependencies
  let some current := origin.fieldPrefix | return ()
  let inherited := origin.sourceDependencies.bind fun captured =>
    if captured.projectedFrom.isSome then captured.fieldPrefix else none
  match inherited with
  | none => current.requireOrigin origin.program origin.occurrence origin.role
  | some inherited => do
    for frame in current.frames do
      let selected : NativeFieldPrefix := { current with frames := #[frame] }
      if inherited.retainsCapture selected then continue
      selected.requireOrigin origin.program origin.occurrence origin.role

/-- Visibility keeps the complete context, stored callable and argument reference planes. -/
def ValueOrigin.references (origin : ValueOrigin) : Array ValueBinding :=
  origin.sourceDependencies.toArray.flatMap (·.references) ++
    origin.inputInterface.toArray.flatMap (fun original => #[original.selected, original.native]) ++
    (origin.fieldPrefix.map (·.references)).getD #[] ++ origin.parameters.filterMap id ++
    (match origin.access with | none => #[] | some value => #[value]) ++
    match origin.application with
    | none => #[]
    | some application =>
      application.parameters.filterMap id ++
      (match application.callable with | none => #[] | some callable => #[callable]) ++
        application.arguments.filterMap id

/-- A tentative immutable node; whole-reply admission and receipt publication are separate. -/
structure ValueNode where
  private mk ::
  id : RuntimeId .value
  origin : ValueOrigin
  payload : ValuePayload
  owners : Array ConnectionGeneration

private def ValueData.references : ValueData → Array ValueBinding
  | .portable _ => #[]
  | .product fields => fields
  | .container value => value.slots.map (·.binding) ++
      (value.originalPacket.map (fun packet => packet.slots.map (·.binding))).getD #[] ++
      value.packetExports.flatMap (·.captures) ++ value.fields.getD #[] ++
      match value.callable with | none => #[] | some binding => #[binding]
  | .closure _ captures | .ownedToken _ _ captures => captures

def ValueNode.references (node : ValueNode) : Array ValueBinding :=
  node.origin.references ++ node.payload.data.references

/-- Persistent storage uses Lean's immutable HashMap; the live ledger holds no copy.
Reference: Lean v4.33.0 Std/Data/HashMap/Basic.lean, `HashMap.insert` and `getElem?`. -/
structure ValueGraph where
  private mk ::
  worker : String
  private nodes : Std.HashMap (RuntimeId .value) ValueNode
  private associations : Std.HashSet (RuntimeId .association)
  private projections : Std.HashMap (RuntimeId .value) (Array ValueBinding)
  private projectionViews : Std.HashMap (RuntimeId .value) (Array ValueBinding)
  private revision : Option (RuntimeId .revision)

def ValueGraph.empty (supply : IdentitySupply) : ValueGraph := ⟨supply.worker, {}, {}, {}, {}, none⟩

/-- Every value or association append has a fresh revision.
Reference: IdentitySupply monotone allocation and persistent HashMap/HashSet insertion. -/
def ValueGraph.sameRevision (left right : ValueGraph) : Bool :=
  left.worker == right.worker && left.revision == right.revision

def ValueGraph.find (graph : ValueGraph) (id : RuntimeId .value) : Option ValueNode :=
  graph.nodes[id]?

/-- Execute exact ordered obligations against the current immutable graph. A guarded body
is entered only on its original association's first visit, before any recursive traversal. -/
private partial def ValueGraph.checkVisibility (graph : ValueGraph)
    (checks : Array ValueVisibilityCheck) (visited : Std.HashSet (RuntimeId .association)) :
    Except String (Std.HashSet (RuntimeId .association)) := do
  let mut visited := visited
  for check in checks do
    match check with
    | .value identity =>
      unless (graph.find identity).isSome do
        throw "the value reference is outside the visible graph"
    | .association identity message =>
      unless graph.associations.contains identity do throw message
    | .worker worker message =>
      unless worker == graph.worker do throw message
    | .failure message => throw message
    | .firstVisit identity body =>
      unless visited.contains identity do
        visited ← graph.checkVisibility body visited
    | .remember identity => visited := visited.insert identity
  return visited

private def ValueGraph.checkBinding (graph : ValueGraph) (binding : ValueBinding)
    (visited : Std.HashSet (RuntimeId .association)) :
    Except String (Std.HashSet (RuntimeId .association)) :=
  graph.checkVisibility binding.visibility.checks visited

private def ValueGraph.require (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueNode := do
  discard <| graph.checkBinding binding {}
  let some node := graph.find binding.value
    | throw "the value reference is outside the visible graph"
  return node

/-- The displayed source role has one authoritative complete parameter telescope.
Each constructor supplies its own retained table, or explicitly preserves its immediate
underlying context. No historical role or source expression is searched for a supplier. -/
partial def ValueGraph.bindingContext (graph : ValueGraph) (binding : ValueBinding) :
    Except String (ContextTelescope × Array (Option ValueBinding)) := do
  discard <| graph.require binding
  let context := binding.role.source.context
  let parameters ← match binding with
    | .inNativeInterface underlying _ _ => pure (← graph.bindingContext underlying).2
    | .direct value _ =>
      let some node := graph.find value | throw "the source binding is outside its actual graph"
      unless context.exactlyMatches node.origin.role.source.context do
        throw "a direct binding changed its original producing source context"
      pure node.origin.parameters
    | .atRole _ _ (some parameters) _ _ => pure parameters
    | .inApplication _ _ _ parameters .. => pure parameters
    | .atRole underlying _ none _ _ | .inField _ underlying .. | .inProjection _ underlying ..
    | .inTelescope underlying .. =>
      let (original, parameters) ← graph.bindingContext underlying
      unless context.exactlyMatches original do
        throw "a source role lost its exact original parameter correspondence"
      pure parameters
  unless parameters.size == context.entries.size do
    throw "a source role lost its complete original parameter table"
  return (context, parameters)

/-- Read only a projection relation published in this immutable graph. Later consuming
aliases may extend its exact parent chain; divergent chains cannot select each other's fields.
Intermediate projection views use their recorded basis, never native declarations or values.
The returned baseline keeps its own owner closure; the parent supplies visibility only. -/
opaque ValueGraph.projected? (graph : ValueGraph) (parent : ValueBinding) (path : Array Name) :
    Except String (Option ValueBinding) := do
  discard <| graph.require parent
  let parent := parent.projectionParent
  discard <| graph.require parent
  let mut selected : Option (Nat × ValueBinding) := none
  for retained in graph.projections[parent.value]?.getD #[] do
    let .inProjection _ _ _ original selectedPath basis _ _ _ := retained
      | throw "the retained projection index has no actual projection relation"
    let original := original.projectionParent
    unless original.value == parent.value && selectedPath == path &&
        original.associationIds.toList.isPrefixOf parent.associationIds.toList do continue
    if let some (length, _) := selected then
      if original.associationIds.size ≤ length then continue
    discard <| graph.require retained
    discard <| graph.require basis
    selected := some (original.associationIds.size, basis)
  return selected.map (·.2)

/-- Read an already published access under its exact original parent and complete association
chain. The original field baseline remains separate: an earlier or sibling consuming parent
cannot supply this view, and role aliases alone do not change its reference identity.
Reuse: bindProjection's sealed native path and immutable association membership. -/
opaque ValueGraph.projectedAccess? (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : Except String (Option ValueBinding) := do
  discard <| graph.require parent
  for retained in graph.projectionViews[parent.value]?.getD #[] do
    let .inProjection _ _ _ original selectedPath _ _ _ _ := retained
      | throw "the retained access index has no actual projection relation"
    unless original.value == parent.value && original.associationIds == parent.associationIds &&
        selectedPath == path do continue
    discard <| graph.require retained
    return some retained
  return none

/-- Read source application provenance only from the visible binding and its immutable node. -/
opaque ValueGraph.applicationOrigin (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option ApplicationOrigin) := do
  let node ← graph.require binding
  if let some application := binding.applications.back? then return some application.origin
  return node.origin.application

/-- Recover only the baseline recorded by this exact access, including a directly staged reply.
An origin fallback is permitted only for its actual retained parent and native path. -/
partial def ValueGraph.projectionBasis (graph : ValueGraph) (binding parent : ValueBinding)
    (path : Array Name) : Except String (Option ValueBinding) := do
  let node ← graph.require binding
  discard <| graph.require parent
  if let some basis := binding.projectionBasis parent path then return some basis
  for (selected, suffix) in binding.projectionAccesses.reverse do
    if suffix.isEmpty || suffix.size ≥ path.size then continue
    let initialPath := path.extract 0 (path.size - suffix.size)
    unless path.extract initialPath.size path.size == suffix do continue
    if (← graph.projectionBasis selected parent initialPath).isNone then continue
    if let some basis := binding.projectionBasis selected suffix then return some basis
  let some selected := node.origin.access | return none
  let produced ← (ValueBinding.direct node.id node.origin.role).withRole node.origin.role
    (← node.origin.typeDependencies) (some node.origin.parameters)
  if selected.value == parent.value && selected.associationIds == parent.associationIds &&
      node.origin.accessPath == path then return some produced
  let suffix := node.origin.accessPath
  if suffix.isEmpty || suffix.size ≥ path.size then return none
  let initialPath := path.extract 0 (path.size - suffix.size)
  if path.extract initialPath.size path.size == suffix &&
      (← graph.projectionBasis selected parent initialPath).isSome then return some produced
  return none

/-- The latest retained projection before any newer consuming application.
An application begins another source continuation, even when it returns the same actual node. -/
private def ValueBinding.latestProjection : ValueBinding →
    Option (SourceLayout × ValueBinding × Array Name)
  | .inNativeInterface binding _ _ => binding.latestProjection
  | .atRole binding .. | .inField _ binding .. | .inTelescope binding .. =>
    binding.latestProjection
  | .inProjection _ _ source parent path _ _ _ _ => some (source, parent, path)
  | .direct .. | .inApplication .. => none

/-- The latest actual projection retains its immutable source role, parent and native path.
Later role aliases cannot rewrite this source witness; a newer application starts a different
continuation. Reuse: projectionBasis and the immutable node's original access record. -/
opaque ValueGraph.projectionSelection (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option (SourceLayout × ValueBinding × Array Name)) := do
  let node ← graph.require binding
  let selected ← match binding.latestProjection with
    | some selected => pure (some selected)
    | none =>
      if !binding.applications.isEmpty then return none
      pure (node.origin.access.map fun parent =>
        (node.origin.role, parent, node.origin.accessPath))
  let some (source, parent, path) := selected | return none
  if path.isEmpty then throw "a retained projection producer lost its native field path"
  let some _ ← graph.projectionBasis binding parent path
    | throw "a retained projection producer lost its exact parent and field selection"
  return some (source, parent, path)

/-- Resume only the exact recorded projection producer, preserving the existing reader API. -/
opaque ValueGraph.projectionOrigin (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option (ValueBinding × Array Name)) := do
  return (← graph.projectionSelection binding).map fun (_, parent, path) => (parent, path)

private structure BindingOwners where
  instantiations : Std.HashSet (RuntimeId .association) := {}
  values : Std.HashSet (RuntimeId .value) := {}
  generations : Std.HashSet ConnectionGeneration := {}
  owners : Array ConnectionGeneration := #[]

private partial def ValueGraph.bindingOwners (graph : ValueGraph) (binding : ValueBinding)
    (state : BindingOwners) : Except String BindingOwners := do
  match binding with
  | .inNativeInterface underlying native _ =>
    graph.bindingOwners native (← graph.bindingOwners underlying state)
  | .direct value _ =>
    if state.values.contains value then return state
    let some node := graph.find value
      | throw "the value reference is outside the visible graph"
    let mut state := { state with values := state.values.insert value }
    for owner in node.owners do
      unless state.generations.contains owner do
        state := { state with
          generations := state.generations.insert owner
          owners := state.owners.push owner }
    return state
  | .atRole underlying _ _ dependencies _ => do
    let mut state ← graph.bindingOwners underlying state
    for dependency in dependencies do state ← graph.bindingOwners dependency state
    return state
  | .inTelescope underlying _ _ _ _ =>
    -- The original full telescope and selected parent establish source identity. They do
    -- not turn a portable projected component into an owner of its siblings.
    graph.bindingOwners underlying state
  | .inProjection id underlying _ _ _ _ fields dependencies _ =>
    if state.instantiations.contains id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert id }
    for field in fields do state ← graph.bindingOwners field state
    for dependency in dependencies do
      let references ← selectedReferences dependency.precedingDependencies dependency.preceding
      for previous in references do
        state ← graph.bindingOwners previous state
    return state
  | .inField id underlying _ _ field preceding view _ =>
    if state.instantiations.contains id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert id }
    for index in (view.map (·.precedingDependencies)).getD field.precedingDependencies do
      let some previous := preceding[index]?
        | throw "the dependent field is missing a preceding source position"
      if let some previous := previous then
        state ← graph.bindingOwners previous state
    return state
  | .inApplication underlying _ association _ _ _ _ _ fields _ =>
    if state.instantiations.contains association.id then return state
    let mut state ← graph.bindingOwners underlying
      { state with instantiations := state.instantiations.insert association.id }
    -- The underlying role already carries its checked precise or conservative native
    -- dependencies. Retained application tables remain provenance, not an extra demand.
    for field in fields do state ← graph.bindingOwners field state
    return state

/-- Derive dependencies from visible nodes, rather than accepting owner claims from a reply. -/
opaque ValueGraph.requiredOwners (graph : ValueGraph) (bindings : Array ValueBinding) :
    Except String (Array ConnectionGeneration) := do
  let mut visible : Std.HashSet (RuntimeId .association) := {}
  for binding in bindings do
    visible ← graph.checkBinding binding visible
  let mut state : BindingOwners := {}
  for binding in bindings do state ← graph.bindingOwners binding state
  return state.owners

/-- Retain the same node under an already prepared consuming role. -/
opaque ValueGraph.rebind (graph : ValueGraph) (binding : ValueBinding) (role : SourceLayout)
    (parameters : Option (Array (Option ValueBinding)) := none) : Except String ValueBinding := do
  discard <| graph.require binding
  binding.withRole role #[] parameters

private def ValueBinding.applicationFields : ValueBinding → Option (Array ValueBinding)
  | .inNativeInterface binding native _ =>
    if binding.role.kind == .record then binding.applicationFields else native.applicationFields
  | .direct .. => none
  | .atRole binding .. | .inField _ binding .. => binding.applicationFields
  | .inApplication _ _ _ _ _ _ _ _ fields _ => some fields
  | .inProjection _ _ _ _ _ _ fields _ _ => some fields
  | .inTelescope binding _ _ fields _ =>
    match fields with | some _ => fields | none => binding.applicationFields

/-- Projection selects the retained field view, independently of unrelated field owners. -/
opaque ValueGraph.project (graph : ValueGraph) (binding : ValueBinding) (index : Nat) :
    Except String ValueBinding := do
  let node ← graph.require binding
  match node.payload.data with
  | .product fields =>
    let fields := binding.applicationFields.getD fields
    let some field := fields[index]?
      | throw "the projection is outside the retained product"
    return field
  | .container value =>
    let some stored := value.fields
      | throw "the descriptor has no stored native fields"
    let fields := binding.applicationFields.getD stored
    let some field := fields[index]?
      | throw "the projection is outside the retained container"
    return field
  | _ => throw "the retained payload has no stored product fields"

/-- One pure traversal supplies both the stored frontier and the exact visited parent bindings.
The temporary parents are used only while preparing descendant dependency views. -/
private def projectionWalk (graph : ValueGraph) (parent : ValueBinding) (path : Array Name)
    (usePublished : Bool := true) :
    Except String (Option (ValueBinding × Array Name) × Array (ValueBinding × Array Name)) := do
  discard <| graph.requiredOwners #[parent]
  let mut value := parent
  let mut parents := #[]
  for projection in path, offset in [:path.size] do
    let remaining := path.extract offset path.size
    parents := parents.push (value, remaining)
    let some field := value.nativeRole.fields.find? (·.projection == projection)
      | throw "a native field path lost its actual record interface"
    let some index := field.wireIndex
      | throw "a computational field path selected a proof field"
    let some node := graph.find value.value
      | throw "the selected value is outside the visible graph"
    if usePublished && node.payload.data.storedFields?.isNone then
      if let some retained ← graph.projected? value #[projection] then
        value := retained
        continue
    match node.payload.data with
    | .closure .. | .ownedToken .. => return (some (value, remaining), parents)
    | .container container =>
      if container.fields.isNone then return (none, parents)
      value ← graph.project value index
    | .product .. => value ← graph.project value index
    | .portable .. => throw "the selected value has no native record access interface"
  return (some (value, #[]), parents)

/-- Follow an exact native path through stored or already published fields without execution.
The returned baseline and remaining lazy path keep the existing read-only query contract. -/
opaque ValueGraph.projectionFrontier (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : Except String (Option (ValueBinding × Array Name)) := do
  return (← projectionWalk graph parent path).1

/-- Carry only the original field-prefix requirements of this selected descendant.
The source paths and original associations select these views; no payload equality is used. -/
private def projectionFieldDependencies (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) (selected : ValueBinding) : MetaM (Array FieldInstantiation) := do
  let (_, parents) ← IO.ofExcept <| (projectionWalk graph parent path).mapError IO.userError
  let mut dependencies : Array FieldInstantiation := #[]
  for (parent, remaining) in parents do
    for field in parent.instantiations do
      if field.field.precedingDependencies.isEmpty then continue
      let path := field.projectionPath ++ remaining
      if (selected.instantiations ++ dependencies).any (fun previous =>
          previous.id == field.id && previous.projectionPath == path) then continue
      let view ← field.field.dependencyView path
      dependencies := dependencies.push { field with view := some view }
  return dependencies

/-- Read the exact stored/lazy frontier and the references required by its selected path.
The first reference is the frontier itself. Additional references come only from the original
preceding fields selected by derived dependency views; no whole stored parent is demanded.
`none` and the remaining path are exactly projectionWalk's results, with no descriptor fallback.
This query creates no value, association, completion or resource. -/
opaque ValueGraph.projectionReferences (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) :
    MetaM (Option (ValueBinding × Array Name × Array ValueBinding)) := do
  let (frontier, _) ← IO.ofExcept <| (projectionWalk graph parent path).mapError IO.userError
  let some (selected, remaining) := frontier | return none
  let dependencies ← projectionFieldDependencies graph parent path selected
  let mut references := #[selected]
  for dependency in dependencies do
    let required ← IO.ofExcept <|
      (selectedReferences dependency.precedingDependencies dependency.preceding).mapError
        IO.userError
    references := references ++ required
  return some (selected, remaining, references)

/-- Read a bound occurrence and its exact native projection path before any reduction.
The context supplies the stable identity; neither a defining expression nor a type chooses it. -/
partial def boundProjection? (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr) :
    MetaM (Option (BindingId × Array Name)) := do
  match expression with
  | .fvar _ =>
    let some binding := context.bindings.find? (·.expression == expression) | return none
    if bound.contains binding.id then return some (binding.id, #[])
    return none
  | .mdata _ body => boundProjection? context bound body
  | _ =>
    let some projection ← SourceProjection.ofExpr? expression | return none
    let some (binding, path) ← boundProjection? context bound projection.parent | return none
    return some (binding, path.push projection.declaration)

/-- Dependencies follow explicit bound variables and exact native projection suffixes.
An unbound selected source expands only its own complete typed payload. The same selection
identity is visited once; an already bound projection stops before its parent is traversed. -/
private partial def boundPaths (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (selections : SourceSelectionScope Expr) (visited : IO.Ref (Std.HashSet BindingId)) :
    MetaM (Array (BindingId × Array Name)) := do
  if let some selected ← boundProjection? context bound expression then return #[selected]
  match expression with
  | .fvar _ =>
    let some binding := context.bindings.find? (·.expression == expression) | return #[]
    if (← visited.get).contains binding.id then return #[]
    visited.modify (·.insert binding.id)
    if let some selected := selections[binding.id]? then
      let gathered ← IO.mkRef (#[] : Array (BindingId × Array Name))
      discard <| selected.mapM fun term => do
        let references ← boundPaths context bound term selections visited
        gathered.modify (· ++ references)
        return term
      return ← gathered.get
    if binding.role == .selectedStructure then
      throwError "the source lost its retained typed selection"
    if binding.role == .result then
      throwError "the source lost a retained runtime binding"
    if let some definition := (← getFVarLocalDecl expression).value? then
      return ← boundPaths context bound definition selections visited
    return #[]
  | .mdata _ body => boundPaths context bound body selections visited
  | .app function argument =>
    return (← boundPaths context bound function selections visited) ++
      (← boundPaths context bound argument selections visited)
  | .lam _ type body _ | .forallE _ type body _ =>
    return (← boundPaths context bound type selections visited) ++
      (← boundPaths context bound body selections visited)
  | .letE _ type value body _ =>
    return (← boundPaths context bound type selections visited) ++
      (← boundPaths context bound value selections visited) ++
      (← boundPaths context bound body selections visited)
  | .proj _ _ body => boundPaths context bound body selections visited
  | _ => pure #[]

/-- Resolve only explicit typed bindings in the actual graph. Stored projections retain their
own dependencies; a lazy frontier keeps its original callable without inventing a result. -/
opaque boundSourceReferences (graph : Option ValueGraph) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (selections : SourceSelectionScope Expr := {}) :
    MetaM (Array ValueBinding) := do
  let paths ← boundPaths context bound expression selections (← IO.mkRef {})
  let mut references := #[]
  for (binding, path) in paths do
    let some parent := bound[binding]?
      | throwError "the native source lost its original runtime binding"
    if path.isEmpty then
      references := references.push parent
      continue
    let some graph := graph
      | throwError "bound projection preparation requires the actual current value graph"
    let some (_, _, selected) ← graph.projectionReferences parent path
      | CasCatalogue.throwStratum .noImplementation
          "the bound source path has no retained native field interface"
    references := references ++ selected
  return references

/-- The type and definitions of selected context entries retain their own explicit bindings.
Unreferenced context entries remain inert provenance. -/
opaque boundContextReferences (graph : Option ValueGraph) (context : OpenContext)
    (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (selections : SourceSelectionScope Expr := {}) :
    MetaM (Array ValueBinding) := do
  let mut references ← boundSourceReferences graph context bound expression selections
  let dependencies ← computationalDependencies (context.bindings.map (·.expression)) expression
  for index in dependencies do
    let some binding := context.bindings[index]?
      | throwError "a native type dependency is outside its complete context"
    let declaration ← getFVarLocalDecl binding.expression
    references := references ++ (← boundSourceReferences graph context bound declaration.type selections)
    if let some value := declaration.value? true then
      references := references ++ (← boundSourceReferences graph context bound value selections)
  return references

/-- Native type ownership follows the same exact bound-variable dependencies. -/
opaque boundTypeReferences (graph : Option ValueGraph) (source : ClosedTerm)
    (bound : Std.HashMap BindingId ValueBinding)
    (selections : SourceSelectionScope ClosedTerm := {}) : MetaM (Array ValueBinding) := do
  source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    boundContextReferences graph context bound (← inferType expression)
      (← selections.inContext context)

/-- Seal the native type-reference traversal for the checked producer's complete context.
The captured parameter array is kept in original source order and rechecked when consumed. -/
opaque SourceDependencyCapture.capture (graph : Option ValueGraph) (source : SourceLayout)
    (bound : Std.HashMap BindingId ValueBinding) : MetaM SourceDependencyCapture := do
  let parameters := source.source.context.entries.map fun entry => bound[entry.id]?
  let references ← boundTypeReferences graph source.source bound source.selections
  if let some graph := graph then
    discard <| IO.ofExcept <| (graph.requiredOwners references).mapError IO.userError
  return { source, parameters, references }

/-- Follow stored callable slots to actual code/token data, retaining the complete outer value.
The append-only graph supplies existing references; no source expression reconstructs a callable.
Reuse: ValueGraph.require and Lean v4.33.0 Std.HashSet for exact reference traversal. -/
private partial def storedCallable (graph : ValueGraph) (binding : ValueBinding)
    (visited : Std.HashSet (RuntimeId .value)) : Except String ValueBinding := do
  if visited.contains binding.value then throw "the retained callable references form a cycle"
  let node ← graph.require binding
  match node.payload.data with
  | .closure .. | .ownedToken .. => return binding
  | .container value =>
    let some callable := value.callable
      | if value.callableData then return binding
        else throw "the container has no stored callable"
    storedCallable graph callable (visited.insert binding.value)
  | .portable _ | .product _ => throw "the retained payload has no callable code or token"

opaque ValueGraph.callable (graph : ValueGraph) (binding : ValueBinding) :
    Except String ValueBinding := storedCallable graph binding {}

/-- Stage one node without modifying the prior graph or creating a completion witness.
References must already be visible; ownership is derived from those exact nodes and the
actual supplying connection. Payload equality never participates in node allocation. -/
opaque ValueGraph.stage (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (payload : ValuePayload) : IO (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throw <| IO.userError "value staging belongs to a different worker"
  if origin.role.kind == .proof then
    throw <| IO.userError "a source proof has no computational payload"
  unless origin.parameters.size == origin.role.source.context.entries.size do
    throw <| IO.userError "value staging requires the complete producing context table"
  discard <| IO.ofExcept <|
    (graph.requiredOwners origin.references).mapError IO.userError
  discard <| IO.ofExcept <| origin.checkFieldPrefix.mapError IO.userError
  let nativeDependencies ← IO.ofExcept <| origin.typeDependencies.mapError IO.userError
  let dependencies := payload.data.references ++ nativeDependencies
  let mut owners ← IO.ofExcept <|
    (graph.requiredOwners dependencies).mapError IO.userError
  match payload.data with
  | .ownedToken owner _ _ =>
    unless owner.worker == graph.worker do
      throw <| IO.userError "the supplying connection belongs to a different worker"
    unless owners.contains owner do owners := owners.push owner
  | .container container =>
    for owned in container.packetExports do
      unless owned.owner.worker == graph.worker do
        throw <| IO.userError "the packet export belongs to a different worker"
      unless owners.contains owned.owner do owners := owners.push owned.owner
  | .closure program _ =>
    unless program.worker == graph.worker do
      throw <| IO.userError "the closure program belongs to a different worker"
  | .portable _ | .product _ => pure ()
  let id ← supply.fresh .value
  let node : ValueNode := ⟨id, origin, payload, owners⟩
  let revision ← supply.fresh .revision
  let mut graph := { graph with
    nodes := graph.nodes.insert id node
    revision := some revision }
  let mut binding ← IO.ofExcept <| ((ValueBinding.direct id origin.role).withRole origin.role
    nativeDependencies (some origin.parameters)).mapError IO.userError
  if let some nativePrefix := origin.fieldPrefix then
    -- This is original producer evidence on a newly allocated node. Existing references
    -- never pass this branch and retain their own immutable producing prefix.
    for frame in nativePrefix.frames do
      let association ← supply.fresh .association
      binding := ValueBinding.attachField association binding origin.role frame.association frame.field
        frame.preceding frame.view
      graph := { graph with
        associations := graph.associations.insert association
        revision := some (← supply.fresh .revision) }
  return (graph, binding)

/-- Availability reads current liveness without rewriting the immutable payload. -/
def ValueGraph.isAvailable (graph : ValueGraph) (owners : OwnerRegistry)
    (binding : ValueBinding) : BaseIO Bool := do
  if owners.worker != graph.worker then return false
  let .ok dependencies := graph.requiredOwners #[binding] | return false
  owners.allAlive dependencies

/-- A computational candidate indexed by its prepared layout, retaining its actual root. -/
structure CandidateResponse (source : SourceLayout) where
  private mk ::
  root : ValueBinding

/-- Check the retained operational shape and bind the prepared source role.
Source: execution contract v2 §2 and data model §5. Scope, lifecycle and whole-reply admission
are separate boundaries. Native exports retain lazy field access through their actual root. -/
opaque CandidateResponse.ofValue (source : SourceLayout) (graph : ValueGraph)
    (value : ValueBinding) : Except String (CandidateResponse source) := do
  let node ← graph.require value
  match source.kind, node.payload.data with
  | .proof, _ => throw "a source proof has no computational response"
  | .function, .closure _ _ | .function, .ownedToken _ _ _ => pure ()
  | .function, .container _ => discard <| graph.callable value
  | .function, _ => throw "the candidate has no retained callable payload"
  | .record, .product fields =>
    let expected := source.fields.filter (·.wireIndex.isSome)
    unless fields.size == expected.size do
      throw "the candidate record does not match its prepared field arity"
  | .record, .container container =>
    if let some fields := container.fields then
      let expected := source.fields.filter (·.wireIndex.isSome)
      unless fields.size == expected.size do
        throw "the candidate container does not match its prepared field arity"
  | .record, .closure _ _ | .record, .ownedToken _ _ _ => pure ()
  | .record, _ => throw "the candidate has no retained record interface"
  | .data, _ | .typeValue, _ => pure ()
  return ⟨← graph.rebind value source⟩

/-- Associate an existing result with a prepared application without replacing its node.
Stored fields are exact projections with their own prepared consuming associations.
Reuse: CandidateResponse, immutable graph membership and source-derived dependency selection. -/
opaque ValueGraph.bindApplication (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (value : ValueBinding) (fields : Array ValueBinding) :
    IO (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throw <| IO.userError "application binding belongs to a different worker"
  let some application := origin.application
    | throw <| IO.userError "application binding requires a prepared application origin"
  unless origin.parameters.size == origin.role.source.context.entries.size do
    throw <| IO.userError "application binding requires the complete source context table"
  let forwarded ← IO.ofExcept <| origin.admittedInputInterface.mapError IO.userError
  if let some original := forwarded then
    unless original.selected.value == value.value &&
        original.selected.associationIds.toList.isPrefixOf value.associationIds.toList do
      throw <| IO.userError "the application result changed its exact admitted interface input"
  let dependencies ← IO.ofExcept <| origin.typeDependencies.mapError IO.userError
  let value ← IO.ofExcept <|
    (value.withRole origin.role dependencies (some origin.parameters)).mapError IO.userError
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue origin.role graph value).mapError IO.userError
  let some node := graph.find candidate.root.value
    | throw <| IO.userError "the application result is outside the visible graph"
  let stored := if origin.role.kind == .record then
      (node.payload.data.storedFields?.getD #[]).size
    else 0
  unless fields.size == stored do
    throw <| IO.userError "the application result requires its complete stored field views"
  for field in fields, index in [:fields.size] do
    let original ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
    unless original.value == field.value &&
        original.associationIds.toList.isPrefixOf field.associationIds.toList do
      throw <| IO.userError "an application field view changed its original stored reference"
  discard <| IO.ofExcept <|
    (graph.requiredOwners (origin.references ++ fields)).mapError IO.userError
  let association : ApplicationAssociation := ⟨← supply.fresh .association,
    origin.program, origin.occurrence, application.layout, application.path, application.dependencies,
    application.contextDependencies⟩
  let binding := ValueBinding.attachApplication candidate.root origin.role association
    origin.parameters application.parameters application.arguments application.callable origin.access fields
  let binding := match forwarded with
    | some original => binding.attachNativeInterface original.native
    | none => retainAdmittedInterface candidate.root binding
  let revision ← supply.fresh .revision
  let graph := { graph with
    associations := graph.associations.insert association.id
    revision := some revision }
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (graph, binding)

/-- Attach an exact prepared projection to an existing node and its stored field views.
The parent is retained for visibility and source selection, not as a whole-record owner demand.
Reuse: bindApplication for original application data, CandidateResponse and immutable associations. -/
opaque ValueGraph.bindProjection (graph : ValueGraph) (supply : IdentitySupply)
    (origin : ValueOrigin) (value : ValueBinding) (fields : Array ValueBinding) :
    MetaM (ValueGraph × ValueBinding) := do
  unless supply.worker == graph.worker && origin.program.worker == graph.worker &&
      origin.occurrence.worker == graph.worker do
    throwError "projection binding belongs to a different worker"
  let some parent := origin.access
    | throwError "projection binding requires its selected parent"
  if origin.accessPath.isEmpty then
    throwError "projection binding requires its exact source path"
  discard <| IO.ofExcept <|
    (graph.requiredOwners origin.references).mapError IO.userError
  let dependencies ← IO.ofExcept <| origin.typeDependencies.mapError IO.userError
  let value ← IO.ofExcept <|
    (value.withRole origin.role dependencies (some origin.parameters)).mapError IO.userError
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue origin.role graph value).mapError IO.userError
  let some node := graph.find candidate.root.value
    | throwError "the projected value is outside the visible graph"
  let prior ← IO.ofExcept <|
    (graph.projected? parent origin.accessPath).mapError IO.userError
  if let some prior := prior then
    unless candidate.root.value == prior.value &&
        prior.associationIds.toList.isPrefixOf candidate.root.associationIds.toList do
      throwError "the projection changed its retained field reference"
  -- New consuming views may enrich the returned value, but an existing source field
  -- keeps its original stored/published baseline. Both sources constrain this candidate.
  let available ← IO.ofExcept <|
    (graph.projectionFrontier parent origin.accessPath).mapError IO.userError
  let baseline : ValueBinding ← match available with
    | some (selected, #[]) => do
      unless selected.value == candidate.root.value &&
          selected.associationIds.toList.isPrefixOf candidate.root.associationIds.toList do
        throwError "the projection changed its retained field reference"
      match prior with
      | none => pure selected
      | some prior =>
        if prior.associationIds.toList.isPrefixOf selected.associationIds.toList then
          pure selected
        else if selected.associationIds.toList.isPrefixOf prior.associationIds.toList then
          pure prior
        else throwError "the projection changed its retained field reference"
    | _ => pure (prior.getD candidate.root)
  -- The baseline index identifies the pre-access parent. A repeated projection of a
  -- stored record gives its descendants fresh consuming views; those views cannot
  -- become the original field of every sibling projection of that same parent.
  -- Keep the current-parent and prior-cache constraints above, then retain the exact
  -- stored field of the already recorded pre-access parent when its path is complete.
  -- A lazy path has no independently stored baseline and keeps the existing result.
  let originalParent := parent.projectionParent
  let baseline ← if originalParent.associationIds == parent.associationIds then pure baseline
    else do
      let (original, _) ← IO.ofExcept <|
        (projectionWalk graph originalParent origin.accessPath (usePublished := false)).mapError
          IO.userError
      match original with
      | some (selected, #[]) =>
        unless selected.value == baseline.value &&
            selected.associationIds.toList.isPrefixOf baseline.associationIds.toList do
          throwError "the projection changed its retained field reference"
        pure selected
      | _ => pure baseline
  let stored := if origin.role.kind == .record then
      (node.payload.data.storedFields?.getD #[]).size
    else 0
  unless fields.size == stored do
    throwError "projection binding requires its complete stored field views"
  for field in fields, index in [:fields.size] do
    let original ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
    unless original.value == field.value &&
        original.associationIds.toList.isPrefixOf field.associationIds.toList do
      throwError "a projection field view changed its original stored reference"
  let dependencies ← projectionFieldDependencies graph parent origin.accessPath candidate.root
  let (graph, value) ← if origin.application.isSome then
      graph.bindApplication supply origin candidate.root fields
    else pure (graph, candidate.root)
  let id ← supply.fresh .association
  let binding := ValueBinding.attachProjection id value origin.role parent origin.accessPath
    baseline fields dependencies
  let binding := retainAdmittedInterface candidate.root binding
  let projections := if prior.isSome then graph.projections else
    let key := parent.projectionParent.value
    graph.projections.insert key ((graph.projections[key]?.getD #[]).push binding)
  -- Preserve a distinct published access for each exact parent chain. The baseline cache
  -- above deliberately keeps its original binding, independently of these consuming views.
  let previousAccess ← IO.ofExcept <|
    (graph.projectedAccess? parent origin.accessPath).mapError IO.userError
  let projectionViews := if previousAccess.isSome then graph.projectionViews else
    graph.projectionViews.insert parent.value
      ((graph.projectionViews[parent.value]?.getD #[]).push binding)
  let graph := { graph with
    associations := graph.associations.insert id
    projections
    projectionViews
    revision := some (← supply.fresh .revision) }
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (graph, binding)

/-- Retain an original constructor slot at its source-prescribed result field. Every stored
descendant keeps the same node and original field baseline; only checked native source views
and association identities are added. Whole native admission remains the caller's next step. -/
opaque ValueGraph.bindTelescopeTransport (graph : ValueGraph) (supply : IdentitySupply)
    (transport : ConstructorProjectionTransport) (parameters : Array (Option ValueBinding))
    (selected : ValueBinding) :
    MetaM (ValueGraph × ValueBinding) := do
  unless graph.worker == supply.worker &&
      parameters.size == transport.plan.context.entries.size do
    throwError "constructor transport lost its complete original runtime telescope"
  discard <| IO.ofExcept <|
    (graph.requiredOwners (parameters.filterMap id ++ #[selected])).mapError
      IO.userError
  let some index := transport.plan.context.entries.findIdx? (·.id == transport.binding)
    | throwError "constructor transport lost its original native slot identity"
  let some parent := parameters[index]!
    | throwError "constructor transport has no actual supplier for its original native slot"
  let some (original, #[]) ← IO.ofExcept <|
      (graph.projectionFrontier parent transport.selected.path).mapError IO.userError
    | throwError "constructor transport requires an already stored original port selection"
  unless original.value == selected.value &&
      original.associationIds.toList.isPrefixOf selected.associationIds.toList do
    throwError "constructor transport selected another original port occurrence"
  let rec visit (graph : ValueGraph) (value : ValueBinding) (path : Array Name) (fuel : Nat) :
      MetaM (ValueGraph × ValueBinding) := do
    let .succ remaining := fuel
      | throwError "constructor transport encountered cyclic original field data"
    let target ← transport.targetAt path
    let source := value.role
    let some node := graph.find value.value
      | throwError "constructor transport lost a stored original port descendant"
    let mut graph := graph
    let mut fields := none
    if target.kind == .record && node.payload.data.storedFields?.isSome then
      let mut retained := #[]
      for field in target.fields do
        if let some index := field.wireIndex then
          let child ← IO.ofExcept <| (graph.project value index).mapError IO.userError
          let (next, child) ← visit graph child (path.push field.projection) remaining
          graph := next
          retained := retained.push child
      fields := some retained
    let mut targetParameters := #[]
    for entry in target.source.context.entries do
      let some index := transport.plan.context.entries.findIdx? (·.id == entry.id)
        | throwError "constructor transport lost an original target source binding"
      let some parameter := parameters[index]?
        | throwError "constructor transport lost an original parameter position"
      targetParameters := targetParameters.push parameter
    let role ← IO.ofExcept <|
      (value.withRole target #[] (some targetParameters)).mapError IO.userError
    let candidate ← IO.ofExcept <| (CandidateResponse.ofValue target graph role).mapError IO.userError
    let id ← supply.fresh .association
    let binder ← supply.fresh .sourceBinding
    let instantiation : TelescopeInstantiation :=
      ⟨id, ⟨binder.worker, binder.serial⟩, transport, source, selected, parameters, path⟩
    let binding := ValueBinding.attachTelescope candidate.root target instantiation fields
    let binding := retainAdmittedInterface candidate.root binding
    graph := { graph with
      associations := graph.associations.insert id
      revision := some (← supply.fresh .revision) }
    discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
    return (graph, binding)
  visit graph selected #[] (graph.nodes.size + 1)

/-- Ordered actual constructor selections; proof positions retain their formal slots.
This is record storage, not a whole-reply admission or correctness witness. -/
structure RecordPrefix where
  private mk ::
  association : RecordAssociation
  private identities : IdentitySupply
  private selections : Array (Option ValueBinding)
  private sourceDependencies : Array (Array ValueBinding)
  private parameters : Option (Array (Option ValueBinding))

private def RecordPrefix.skipProofs (record : RecordPrefix) : RecordPrefix := Id.run do
  let mut selections := record.selections
  while selections.size < record.association.layout.fields.size do
    let some field := record.association.layout.fields[selections.size]? | break
    if field.field.kind != .proof then break
    selections := selections.push none
  return { record with selections }

/-- Allocate a fresh association before recording any actual field selections.
Reuse: the worker IdentitySupply and complete source-prepared RecordLayout. -/
opaque RecordPrefix.begin (supply : IdentitySupply) (program : RuntimeId .program)
    (occurrence : RuntimeId .occurrence) (layout : RecordLayout)
    (sourceDependencies : Array (Array ValueBinding) := #[])
    (parameters : Option (Array (Option ValueBinding)) := none) : IO RecordPrefix := do
  unless program.worker == supply.worker && occurrence.worker == supply.worker do
    throw <| IO.userError "record preparation belongs to a different worker"
  let bindings ← layout.fields.mapM fun _ => do
    let id ← supply.fresh .sourceBinding
    return (⟨id.worker, id.serial⟩ : BindingId)
  let association : RecordAssociation :=
    ⟨← supply.fresh .association, program, occurrence, layout, bindings⟩
  unless sourceDependencies.isEmpty || sourceDependencies.size == layout.fields.size do
    throw <| IO.userError "a record requires its complete prepared field dependencies"
  if let some parameters := parameters then
    unless parameters.size == layout.source.source.context.entries.size do
      throw <| IO.userError "a record prefix requires its complete original source parameter table"
  return RecordPrefix.skipProofs ⟨association, supply, #[], sourceDependencies, parameters⟩

/-- Prepare each field's actual bound type dependencies before attaching field roles. -/
opaque RecordPrefix.prepare (supply : IdentitySupply) (program : RuntimeId .program)
    (occurrence : RuntimeId .occurrence) (layout : RecordLayout) (graph : ValueGraph)
    (bound : Std.HashMap BindingId ValueBinding) : MetaM RecordPrefix := do
  let dependencies ← layout.source.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let nativeType ← whnf (← inferType expression)
    let .const name levels := nativeType.getAppFn
      | throwError "a record prefix lost its original native declaration"
    let some information := getStructureInfo? (← getEnv) name
      | throwError "a record prefix requires its original native structure"
    let constructor := getStructureCtor (← getEnv) name
    unless nativeType.getAppArgs.size == constructor.numParams do
      throwError "a record prefix changed its complete native parameter telescope"
    let applied := mkAppN (mkConst constructor.name levels) nativeType.getAppArgs
    forallTelescope (← inferType applied) fun formals _ => do
      unless formals.size == layout.fields.size do
        throwError "a record prefix changed its complete native field telescope"
      let selections ← layout.source.selections.inContext context
      let mut dependencies := #[]
      for formal in formals, index in [:formals.size] do
        let some prepared := layout.fields[index]?
          | throwError "a record prefix lost an original native field position"
        unless prepared.field.sourceIndex == index &&
            information.getProjFn? index == some prepared.field.projection do
          throwError "a record prefix changed an original native field position"
        let references ← if prepared.field.wireIndex.isNone then pure #[]
          else boundContextReferences (some graph) context bound (← inferType formal) selections
        dependencies := dependencies.push references
      return dependencies
  let parameters := layout.source.source.context.entries.map fun entry => bound[entry.id]?
  RecordPrefix.begin supply program occurrence layout dependencies (some parameters)

/-- Bind this same node at the next field and retain every preceding actual selection.
Visibility checks include the whole prefix; owner requirements follow the declared dependencies.
Reuse: CandidateResponse's operational shape check and ValueGraph reference validation. -/
opaque RecordPrefix.bind (record : RecordPrefix) (graph : ValueGraph) (value : ValueBinding) :
    IO (ValueGraph × RecordPrefix × ValueBinding) := do
  let record := record.skipProofs
  let some prepared := record.association.layout.fields[record.selections.size]?
    | throw <| IO.userError "the complete record has no further computational field"
  let value ← IO.ofExcept <|
    (value.withRole prepared.layout
      (record.sourceDependencies[record.selections.size]?.getD #[]) record.parameters).mapError IO.userError
  let candidate ← IO.ofExcept <|
    (CandidateResponse.ofValue prepared.layout graph value).mapError IO.userError
  let id ← record.identities.fresh .association
  let binding := ValueBinding.attachField id
    candidate.root prepared.layout record.association prepared.field record.selections none
  let binding := retainAdmittedInterface candidate.root binding
  let revision ← record.identities.fresh .revision
  let graph := { graph with
    associations := graph.associations.insert id
    revision := some revision }
  discard <| IO.ofExcept <| (graph.requiredOwners #[binding]).mapError IO.userError
  return (graph, ({ record with selections := record.selections.push (some binding) }).skipProofs,
    binding)

/-- Finish only a complete ordered record; no component is installed in a transaction here. -/
opaque RecordPrefix.finish (record : RecordPrefix) : Except String ValuePayload := do
  let record := record.skipProofs
  unless record.selections.size == record.association.layout.fields.size do
    throw "the dependent record is missing a required computational field"
  return .product (record.selections.filterMap id)

/-- Snapshot only the current native field and its already selected original predecessors. -/
opaque RecordPrefix.currentField (record : RecordPrefix) : MetaM NativeFieldPrefix := do
  let record := record.skipProofs
  let some prepared := record.association.layout.fields[record.selections.size]?
    | throwError "the complete native record has no further field prefix"
  unless prepared.field.sourceIndex == record.selections.size &&
      prepared.field.wireIndex.isSome do
    throwError "the current native field lost its original proof/data order"
  return ⟨prepared.layout,
    #[⟨record.association, prepared.field, record.selections, none⟩]⟩

/-- Carry the same original predecessor slots along an already selected native descendant.
Inner fields remain formal unless their own actual prefix is joined separately. -/
opaque NativeFieldPrefix.descend (nativePrefix : NativeFieldPrefix) (projection : Name) :
    MetaM NativeFieldPrefix := do
  let some field := nativePrefix.native.fields.find? (·.projection == projection)
    | throwError "the producing field prefix selected an undeclared native descendant"
  unless field.wireIndex.isSome do
    throwError "a producing data prefix selected a formal proof descendant"
  let native ← field.toLayout
  let frames ← nativePrefix.frames.mapM fun frame => do
    let path := (frame.view.map (·.path)).getD #[]
    return { frame with view := some (← frame.field.dependencyView (path.push projection)) }
  return ⟨native, frames⟩

/-- Join independently retained native ancestor prefixes at their already selected common
field. This validates their source position; actual predecessor identities remain distinct. -/
opaque NativeFieldPrefix.join (nativePrefix other : NativeFieldPrefix) : MetaM NativeFieldPrefix := do
  unless sameNativeFieldRole nativePrefix.native other.native do
    throwError "native field prefixes selected different original result positions"
  return ⟨nativePrefix.native, nativePrefix.frames ++ other.frames⟩

/-- Open every actual predecessor at its original declaration position. The context retains
an opaque typed binder and its original source correspondence; only the bound table carries
the selected runtime occurrence. Proof positions remain formal entries in the same telescope. -/
opaque NativeFieldPrefix.withBoundType (nativePrefix : NativeFieldPrefix)
    (context : OpenContext) (graph : ValueGraph)
    (bound : Std.HashMap BindingId ValueBinding)
    (action : OpenContext → Expr → Std.HashMap BindingId ValueBinding → MetaM α) : MetaM α := do
  discard <| IO.ofExcept <| (graph.requiredOwners nativePrefix.references).mapError IO.userError
  let some first := nativePrefix.frames[0]?
    | throwError "a native field prefix has no original declaration frame"
  let mut root := first.association.layout.source
  for frame in nativePrefix.frames do
    if frame.association.layout.source.address.size < root.address.size then
      root := frame.association.layout.source
  discard <| root.projectionPathTo nativePrefix.native
  let frames := nativePrefix.frames.qsort fun left right =>
    left.association.layout.source.address.size < right.association.layout.source.address.size
  let inputIds := context.bindings.filterMap fun binding =>
    if bound.contains binding.id then some binding.id else none
  let mut positions : Array (Array Name × BindingId × SourceLayout × Option ValueBinding) := #[]
  for frame in frames do
    let parentPath ← root.projectionPathTo frame.association.layout.source
    unless frame.association.bindings.size == frame.association.layout.fields.size do
      throwError "a native field prefix lost its complete original binder table"
    for actual in frame.preceding, index in [:frame.preceding.size] do
      let some prepared := frame.association.layout.fields[index]?
        | throwError "a native field prefix lost its earlier declaration position"
      unless actual.isSome == prepared.field.wireIndex.isSome do
        throwError "a native field prefix changed an original proof/data position"
      if frame.precedingDependencies.contains index then
        if let some original := actual then
          let source ← context.inputProjectionSource
            (← prepared.layout.source.inContext context) inputIds
          if let some (binding, sourcePath) ← boundProjection? context bound source then
            let some parent := bound[binding]?
              | throwError "a native field prefix lost its independently supplied parent"
            let some (current, remaining) ← IO.ofExcept <|
                (graph.projectionFrontier parent sourcePath).mapError IO.userError
              | throwError "a supplied native parent has no retained field interface"
            if remaining.isEmpty then
              unless original.value == current.value &&
                  (original.associationIds.toList.isPrefixOf current.associationIds.toList ||
                    current.associationIds.toList.isPrefixOf original.associationIds.toList) do
                throwError "a native field prefix disagrees with its supplied parent occurrence"
            else
              unless (← IO.ofExcept <|
                  (graph.projectionBasis original parent sourcePath).mapError IO.userError).isSome do
                throwError "a native field prefix lost its supplied parent's exact projection ancestry"
      let path := parentPath.push prepared.field.projection
      if let some (_, _, _, earlier) := positions.find? (·.1 == path) then
        match earlier, actual with
        | none, none => pure ()
        | some earlier, some actual =>
          unless earlier.value == actual.value &&
              (earlier.associationIds.toList.isPrefixOf actual.associationIds.toList ||
               actual.associationIds.toList.isPrefixOf earlier.associationIds.toList) do
            throwError "native field prefixes disagree about an original earlier occurrence"
        | _, _ => throwError "native field prefixes disagree about an original formal position"
      else
        positions := positions.push
          (path, frame.association.bindings[index]!, prepared.layout, actual)
  let rec visit
      (positions : List (Array Name × BindingId × SourceLayout × Option ValueBinding))
      (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
      (replacements : Array (Array Name × Expr)) : MetaM α := do
    match positions with
    | [] =>
      action context (← root.fieldTypeInContext nativePrefix.native context replacements) bound
    | (path, id, layout, actual) :: rest =>
      let original ← layout.source.inContext context
      let type ← root.fieldTypeInContext layout context replacements
      let continueWith := fun (context : OpenContext) (binding : LocalBinding) => do
        let mut bound := bound
        if let some actual := actual then
          if let some retained := bound[id]? then
            unless retained.value == actual.value &&
                (retained.associationIds.toList.isPrefixOf actual.associationIds.toList ||
                 actual.associationIds.toList.isPrefixOf retained.associationIds.toList) do
              throwError "a native predecessor binder changed its original actual occurrence"
          else bound := bound.insert id actual
        else if bound.contains id then
          throwError "a native proof predecessor acquired a runtime occurrence"
        visit rest context bound (replacements.push (path, binding.expression))
      if let some binding := context.bindings.find? (·.id == id) then
        unless ← context.withOriginalSources #[← inferType binding.expression, type]
            (fun types => isDefEq types[0]! types[1]!) do
          throwError "a native predecessor binder changed its original declared type"
        let some source := binding.originalSource
          | throwError "a native predecessor binder lost its original source correspondence"
        unless source.equal original do
          throwError "a native predecessor binder changed its original source position"
        continueWith context binding
      else
        context.withLocalBinding id (if actual.isSome then .result else .hypothesis)
          `nativeField type continueWith (originalSource := some original)
  visit positions.toList context bound #[]

/-- Capture a dependent field's type in its sealed producer prefix, before the whole
record exists. The original role/context stay unchanged; exact predecessor binders live
only in the checked native scope and are retained by the same prefix association. -/
opaque SourceDependencyCapture.capturePrefix (graph : ValueGraph) (source : SourceLayout)
    (bound : Std.HashMap BindingId ValueBinding) (fieldPrefix : NativeFieldPrefix) :
    MetaM SourceDependencyCapture := do
  unless sameNativeFieldRole source fieldPrefix.native do
    throwError "a native type capture changed its original field role"
  let parameters := source.source.context.entries.map fun entry => bound[entry.id]?
  let references ← source.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    fieldPrefix.withBoundType context graph bound fun context type bound => do
      boundContextReferences (some graph) context bound type
        (← source.selections.inContext context)
  discard <| IO.ofExcept <| (graph.requiredOwners references).mapError IO.userError
  return { source, parameters, references, fieldPrefix := some fieldPrefix }

/-- Read the prefix at the actual producing node, or follow its explicitly retained
projection when that node has no own native prefix. This traverses only the selected
reference chain; native types and equal-valued nodes never select an ancestor. -/
private partial def producingNativePrefix (graph : ValueGraph) (binding : ValueBinding) :
    MetaM (Option NativeFieldPrefix) := do
  let node ← IO.ofExcept <| (graph.require binding).mapError IO.userError
  if let some nativePrefix := node.origin.fieldPrefix then
    discard <| IO.ofExcept <| node.origin.checkFieldPrefix.mapError IO.userError
    return some nativePrefix
  let selected ← IO.ofExcept <| (graph.projectionSelection binding).mapError IO.userError
  let some (_, parent, path) := selected | return none
  let some original ← producingNativePrefix graph parent | return none
  let mut nativePrefix := original
  for projection in path do nativePrefix ← nativePrefix.descend projection
  return some nativePrefix

/-- Capture a projection's dependent type from its actual parent's retained producer.
The old frame identities and occurrences remain unchanged. The resulting seal authenticates
only this parent and path; it cannot authorize a different fresh field producer. -/
opaque SourceDependencyCapture.captureProjection (graph : ValueGraph) (source : SourceLayout)
    (bound : Std.HashMap BindingId ValueBinding) (nativePrefix : NativeFieldPrefix)
    (parent : ValueBinding) (path : Array Name) : MetaM SourceDependencyCapture := do
  unless !path.isEmpty && (← parent.nativeRole.projectionPathTo source) == path do
    throwError "a projected type capture changed its actual parent's native field path"
  let some original ← producingNativePrefix graph parent
    | throwError "a projected type capture has no original producing prefix"
  let mut original := original
  for projection in path do original ← original.descend projection
  let nativePrefix ← source.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let selections ← source.selections.inContext context
    discard <| source.selected? context
    let transport := fun (nativePrefix : NativeFieldPrefix) => do
      let native ← nativePrefix.native.inContext context
      unless native.address == source.address && native.kind == source.kind &&
          native.source.context.exactlyMatches source.source.context &&
          native.source.expression.equal source.source.expression &&
          native.source.type.equal source.source.type &&
          native.source.universeParams == source.source.universeParams &&
          native.source.nativeDeclarations.exactlyMatches source.source.nativeDeclarations do
        throwError "a projected type capture changed its original native field role"
      let merged ← SourceSelectionScope.merge selections (← native.selections.inContext context)
      unless SourceSelectionScope.exactlyMatches Expr.equal selections merged do
        throwError "a projected type capture lost an original complete source selection"
      return ({ nativePrefix with native := source } : NativeFieldPrefix)
    let original ← transport original
    let nativePrefix ← transport nativePrefix
    unless original.retainsCapture nativePrefix && nativePrefix.retainsCapture original do
      throwError "a projected type capture changed its original complete native prefix"
    return nativePrefix
  let captured ← SourceDependencyCapture.capturePrefix graph source bound nativePrefix
  return { captured with projectedFrom := some (parent, path) }

/-- The original packet of retained portable data. Native exports and closures have none.
Reuse: the stored literal structure and ValueContainer.fill, as in receiver encoding. -/
partial def ValueGraph.packet? (graph : ValueGraph) (binding : ValueBinding) :
    Except String (Option Json) := do
  let some node := graph.find binding.value | throw "the value is outside the visible graph"
  match node.payload.data with
  | .portable bytes =>
    let some text := String.fromUTF8? bytes | throw "the portable value is not UTF-8 packet data"
    return some (← Json.parse text)
  | .ownedToken .. | .closure .. => return none
  | .container container =>
    if !container.packetExports.isEmpty then return none
    if (binding.role.kind == .function || container.callable.isSome) &&
        !container.callableData then return none
    let mut replacements := #[]
    for slot in container.slots do
      let actual ← match slot.fieldIndex with
        | none => pure slot.binding
        | some index => graph.project binding index
      let some packet ← graph.packet? actual | return none
      replacements := replacements.push packet
    return some (← container.fill replacements)
  | .product fields =>
    let mut packets := #[]
    for index in [:fields.size] do
      let some packet ← graph.packet? (← graph.project binding index) | return none
      packets := packets.push packet
    if let #[packet] := packets then return some packet
    return some (.arr packets)

end CasRuntime
