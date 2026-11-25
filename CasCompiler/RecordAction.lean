module

public import CasCompiler.Program
public import CasCompiler.SelectedField

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- Availability belongs to the original family, independently of its data layout. -/
inductive RecordActionOwner
  | computation (reference : ComputationRef)
  | lift (id : LiftId)
  | limit (id : LimitId)

/-- A required invocation value at its original native field slot. -/
structure RecordActionInput where
  private mk ::
  sourceIndex : Nat
  projection : Name
  source : ClosedTerm

/-- A source-selected action and its declared invocation inputs. Native type dependencies
and additional released packet inputs remain separate: ordinary records use their sparse
FieldLayout dependencies; a published ordered packet retains its prescribed value inputs. -/
structure RecordAction where
  private mk ::
  owner : RecordActionOwner
  address : String
  familyAddress : String
  inputs : Array RecordActionInput
  /-- Exact outer native predecessor slots retained by this selected subfamily. -/
  predecessors : Array RecordActionInput := #[]

/-- Original registered family identity, shared by source ports and admission. -/
def computationAddress : ComputationRef → String
  | .operation id => id.raw
  | .functor id => id.raw
  | .method id => id.raw
  | .construction id => id.raw
  | .morphism id => id.raw

/-- The released ordinary-family address of an already validated native field path. -/
opaque nativeRecordActionAddress (owner : String) (path : Array FieldLayout) : String :=
  match path.back? with
  | some field =>
    if field.wireIndex == some 0 then owner
    else s!"{owner}#{field.projection.getString!}"
  | none => owner

/-- Ordinary registered families reuse the same native-field address rule. -/
opaque recordActionAddress (reference : ComputationRef) (path : Array FieldLayout) : String :=
  nativeRecordActionAddress (computationAddress reference) path

/-- Project the checked native field without reducing or replacing its parent. -/
private def project (parent : Expr) (field : FieldLayout) : MetaM Expr := do
  let some information := (← getEnv).getProjectionFnInfo? field.projection
    | throwError "a prepared record field lost its native projection declaration"
  return .proj (← getConstInfoCtor information.ctorName).induct information.i parent

/-- Follow the original source-ordered field path, retaining its exact parent. -/
private def parentAt (source : SourceLayout) (parent : Expr) (path : Array FieldLayout) :
    MetaM (SourceLayout × Expr × FieldLayout) := do
  let mut layout := source
  let mut parent := parent
  for requested in path, index in [:path.size] do
    let some field := layout.fields[requested.sourceIndex]?
      | throwError "a record action has a field outside its original source record"
    unless field.projection == requested.projection && field.address == requested.address do
      throwError "a record action changed its original source field path"
    if index + 1 == path.size then return (layout, parent, field)
    parent ← project parent field
    layout ← field.toLayout
  throwError "a record action requires its original selected field"

private def retainedInput (context : OpenContext) (selection : Option Name)
    (field : FieldLayout) (source : Expr) : MetaM RecordActionInput := do
  check source
  let source := match selection with
    | some selection => selectedField selection field.projection source
    | none => source
  return ⟨field.sourceIndex, field.projection, ← context.close source⟩

/-- Native dependencies select the actual earlier fields themselves, retaining a whole
callable when required. A type dependency does not authorize applying another function
to the current field's arguments. -/
private def nativeInputs (context : OpenContext) (layout : SourceLayout)
    (parent : Expr) (field : FieldLayout) : MetaM (Array RecordActionInput) := do
  let mut inputs := #[]
  for index in field.precedingDependencies do
    unless index < field.sourceIndex do
      throwError "a native field dependency is not an earlier source slot"
    let some preceding := layout.fields[index]?
      | throwError "a native field dependency is outside its original source record"
    if preceding.wireIndex.isNone then continue
    inputs := inputs.push (← retainedInput context none preceding (← project parent preceding))
  return inputs

/-- Prepare sparse native dependencies for an exact selected record field. The complete
source layout and actual parent stay fixed; no implementation availability is consulted. -/
opaque SourceLayout.actionInputs (source : SourceLayout) (context : OpenContext)
    (parent : Expr) (path : Array FieldLayout) : MetaM (Array RecordActionInput) := do
  let original ← source.source.inContext context
  unless ← isDefEq original parent do
    throwError "the record action changed its original native parent"
  let (layout, parent, field) ← parentAt source parent path
  nativeInputs context layout parent field

/-- The released lift packet consumes ordered earlier action results in addition to its
native type dependencies. Keep the original action-prefix positions and selection identity.
Source: cas-leaf-contracts api/wire-examples.md, prescribed lifts and separate factor. -/
private def orderedInputs (context : OpenContext) (selection : Option Name)
    (layout : SourceLayout) (parent : Expr) (count : Nat) (arguments : Array Expr) :
    MetaM (Array RecordActionInput) := do
  unless count ≤ layout.fields.size do
    throwError "a published record invocation exceeds its original field interface"
  let mut inputs := #[]
  for field in layout.fields.extract 0 count do
    if field.wireIndex.isNone then continue
    let projection ← project parent field
    let arity ← forallTelescope (← inferType projection) fun parameters _ => pure parameters.size
    unless arity ≤ arguments.size do
      throwError "a published record input lost its complete original action prefix"
    let value := mkAppN projection (arguments.extract 0 arity)
    inputs := inputs.push (← retainedInput context selection field value)
  return inputs

/-- Prepare the common record dispatch interface. The parent is the exact retained family
result; parameters and arguments are its complete original native source slots. Only checked
source terms are formed here. Runtime evaluates the resulting list after unique selection. -/
opaque RecordAction.prepare (boundary : ProgramBoundary) (universes : List Level)
    (context : OpenContext) (source : SourceLayout) (parent : Expr)
    (path : Array FieldLayout) (parameters arguments : Array Expr)
    (selection : Option Name) : MetaM RecordAction := do
  unless universes.length == boundary.universeParams.length do
    throwError "the record action changed its original universe telescope"
  let declared := mkAppN (← boundary.familyIn universes context) parameters
  unless ← isDefEq declared (← source.source.inContext context) do
    throwError "the record action changed its original applied source family"
  if let some reference := boundary.reference then
    let id := computationAddress reference
    if path.isEmpty then return ⟨.computation reference, id, id, #[], #[]⟩
    return ⟨.computation reference, recordActionAddress reference path, id,
      ← source.actionInputs context parent path, #[]⟩
  if let .limitUniversal family _ := boundary then
    let presentation := mkAppN
      (family.presentation.presentationFamily.instantiateLevelParams
        family.universeParams universes) parameters
    let original ← SourceLayout.ofTerm (← context.close presentation)
    let some universal := original.fields.find? (·.projection == family.projection)
      | throwError "the universal action lost its original presentation field"
    let predecessors ← nativeInputs context original presentation universal
    let inputs ← if path.isEmpty then pure #[]
      else source.actionInputs context parent path
    return ⟨.limit family.presentation.entry.id,
      nativeRecordActionAddress family.operation path, family.operation, inputs, predecessors⟩
  if let .creation family := boundary then
    unless path.isEmpty do
      throwError "a creation field must use its completed original native result"
    return ⟨.lift family.family.entry.id, family.operation, family.operation, #[], #[]⟩
  let .lift family := boundary
    | throwError "the selected source interface has no ordinary record action"
  let (layout, parent, field) ← parentAt source parent path
  let address := s!"{family.lift.raw}#{field.projection.getString!}"
  let inputs ← match family.port with
    | .computation => orderedInputs context selection layout parent field.sourceIndex arguments
    | .factor => do
      let some row := (← semanticState).lifts.find? (·.id == family.lift)
        | throwError "the selected factor lost its original lift declaration"
      let info ← checkedDeclaration row.evidence
      unless info.levelParams.length == universes.length do
        throwError "the selected factor lost its original evidence universe parameters"
      let evidence := mkAppN (mkConst row.evidence universes) parameters
      let computation ← LiftFamily.atEvidence row .computation evidence
      let computationLayout ← SourceLayout.ofTerm (← context.close computation)
      orderedInputs context selection computationLayout computation
        computationLayout.fields.size arguments
  return ⟨.lift family.lift, address, family.lift.raw, inputs, #[]⟩

end CasCompiler
