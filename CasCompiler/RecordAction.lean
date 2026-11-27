module

public import CasCompiler.Program
public import CasCompiler.SelectedField

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue


inductive RecordActionOwner
  | computation (reference : ComputationRef)
  | lift (id : LiftId)
  | limit (id : LimitId)


structure RecordActionInput where
  private mk ::
  sourceIndex : Nat
  projection : Name
  source : ClosedTerm
  selectedField : Option (SelectedSourceField ClosedTerm) := none




structure RecordAction where
  private mk ::
  owner : RecordActionOwner
  address : String
  familyAddress : String
  inputs : Array RecordActionInput

  predecessors : Array RecordActionInput := #[]


def computationAddress : ComputationRef → String
  | .operation id => id.raw
  | .functor id => id.raw
  | .method id => id.raw
  | .construction id => id.raw
  | .morphism id => id.raw


opaque nativeRecordActionAddress (owner : String) (path : Array FieldLayout) : String :=
  match path.back? with
  | some field =>
    if field.wireIndex == some 0 then owner
    else s!"{owner}#{field.projection.getString!}"
  | none => owner


opaque recordActionAddress (reference : ComputationRef) (path : Array FieldLayout) : String :=
  nativeRecordActionAddress (computationAddress reference) path


private def project (parent : Expr) (field : FieldLayout) : MetaM Expr := do
  let some information := (← getEnv).getProjectionFnInfo? field.projection
    | throwError "a prepared record field lost its native projection declaration"
  return .proj (← getConstInfoCtor information.ctorName).induct information.i parent


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
    (field : FieldLayout) (owner source : Expr) : MetaM RecordActionInput := do
  check source
  let selected ← selection.mapM fun construction => do
    let selected ← selectedFieldAt construction field.projection owner source
    let some field := selected.field
      | throwError "the ordered record input lost its complete native field selection"
    field.mapM context.close
  return ⟨field.sourceIndex, field.projection, ← context.close source, selected⟩




private def nativeInputs (context : OpenContext) (layout : SourceLayout)
    (parent : Expr) (field : FieldLayout) : MetaM (Array RecordActionInput) := do
  let mut inputs := #[]
  for index in field.precedingDependencies do
    unless index < field.sourceIndex do
      throwError "a native field dependency is not an earlier source slot"
    let some preceding := layout.fields[index]?
      | throwError "a native field dependency is outside its original source record"
    if preceding.wireIndex.isNone then continue
    inputs := inputs.push (← retainedInput context none preceding parent (← project parent preceding))
  return inputs



opaque SourceLayout.actionInputs (source : SourceLayout) (context : OpenContext)
    (parent : Expr) (path : Array FieldLayout) : MetaM (Array RecordActionInput) := do
  let original ← source.source.inContext context
  context.withOriginalSources #[original, parent] fun native => do
    unless ← isDefEq native[0]! native[1]! do
      throwError "the record action changed its original native parent"
  let (layout, parent, field) ← parentAt source parent path
  nativeInputs context layout parent field




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
    inputs := inputs.push (← retainedInput context selection field parent value)
  return inputs




opaque RecordAction.prepare (boundary : ProgramBoundary) (universes : List Level)
    (context : OpenContext) (source : SourceLayout) (parent : Expr)
    (path : Array FieldLayout) (parameters arguments : Array Expr)
    (selection : Option Name) : MetaM RecordAction := do
  unless universes.length == boundary.universeParams.length do
    throwError "the record action changed its original universe telescope"
  let declared := mkAppN (← boundary.familyIn universes context) parameters
  context.withOriginalSources #[declared, ← source.source.inContext context] fun native => do
    unless ← isDefEq native[0]! native[1]! do
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
      (selections := source.selections)
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
      let some selected ← source.selected? context
        | throwError "the selected factor lost its complete original source record"
      let some computation := selected.application.bind (·.owner)
        | throwError "the selected factor lost its actual original computation owner"
      let scope ← source.selections.inContext context
      let some original := scope.findAt? context computation
        | throwError "the factor's computation owner has no retained complete selection"
      let some application := original.application
        | throwError "the factor's original computation lost its selected family"
      let .lift computationFamily := application.family
        | throwError "the factor's original owner is not its selected lift computation"
      unless computationFamily.port == .computation &&
          reprStr computationFamily.entry == reprStr family.entry do
        throwError "the selected factor changed its complete original computation family"
      let computationLayout ← SourceLayout.ofTerm (← context.close computation)
        (selections := source.selections)
      orderedInputs context selection computationLayout computation
        computationLayout.fields.size arguments
  return ⟨.lift family.lift, address, family.lift.raw, inputs, #[]⟩

end CasCompiler
