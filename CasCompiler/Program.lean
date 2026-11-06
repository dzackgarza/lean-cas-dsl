module

public import LeanCategories.Catalogue.Registry.Computation
public import CasCompiler.Context
public import Lean.Meta.Structure

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The accepted whole-family source, before specialization or executable selection. -/
structure SourceProgram where
  private mk ::
  source : CheckedComputationDerivation

/-- One formal callable slot. Its ordinal and published reference are independent of its type. -/
structure PrerequisiteSlot where
  index : Nat
  source : CheckedComputationPrerequisite
  expression : Expr

/-- Read every published alternative through the upstream safety and axiom checks.
The upstream checked packet is retained intact, including rigid universes and equality.
Source: LeanCategories/Catalogue/Registry/Computation.lean at
8c35703b104aca1700b9fb40d1af4164ca31a55d. -/
opaque SourceProgram.forTarget (target : ComputationRef) : MetaM (Array SourceProgram) := do
  return (← checkedComputationDerivations target).map fun source => ⟨source⟩

/-- Open only the prerequisite prefix with fresh locals; keep the entire target family.
Lean's telescope and application operations retain dependent binder types and slot order. -/
def SourceProgram.withPrerequisites (program : SourceProgram)
    (action : Array PrerequisiteSlot → Expr → MetaM α) : MetaM α := do
  let source := program.source
  forallBoundedTelescope (← inferType source.template) (some source.prerequisites.size)
      fun locals _ => do
    unless locals.size == source.prerequisites.size do
      throwError "checked source program has an incomplete prerequisite telescope"
    let slots := source.prerequisites.mapIdx fun index prerequisite =>
      { index, source := prerequisite, expression := locals[index]! : PrerequisiteSlot }
    action slots (mkAppN source.template locals).headBeta

inductive ComputationalKind
  | proof | typeValue | function | record | data
  deriving BEq, Repr

inductive ComputationalAction
  | retain | project | apply
  deriving BEq, Repr

def ComputationalKind.actions : ComputationalKind → Array ComputationalAction
  | .proof => #[]
  | .function => #[.retain, .apply]
  | .record => #[.retain, .project]
  | .typeValue | .data => #[.retain]

/-- One exact source projection. Proof fields keep formal dependencies and have no wire slot. -/
structure FieldLayout where
  private mk ::
  address : Array Name
  projection : Name
  sourceIndex : Nat
  wireIndex : Option Nat
  precedingDependencies : Array Nat
  source : ClosedTerm
  typeFamily : ClosedTerm
  kind : ComputationalKind

/-- Mechanical layout of a fixed source value, with its complete dependent source type. -/
structure SourceLayout where
  private mk ::
  address : Array Name
  source : ClosedTerm
  kind : ComputationalKind
  fields : Array FieldLayout

private def computationalKind (type : Expr) : MetaM ComputationalKind := do
  if ← isProp type then return .proof
  let type ← whnf type
  if type.isForall then return .function
  if type.isSort then return .typeValue
  if let some name := type.getAppFn.constName? then
    if isStructure (← getEnv) name then return .record
  return .data

/-- Use Lean's source-ordered structure metadata and constructor telescope.
Reference: Lean/Structure.lean and Lean/Meta/Structure.lean at Lean v4.33.0.
Only propositions are erased; no subsingleton test enters field selection. -/
private def sourceLayout (source : ClosedTerm) (address : Array Name) : MetaM SourceLayout :=
  source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let type ← whnf (← inferType expression)
    let kind ← computationalKind type
    if kind != .record then return ⟨address, source, kind, #[]⟩
    let .const name levels := type.getAppFn
      | throwError "record layout requires its source structure declaration"
    let some info := getStructureInfo? (← getEnv) name
      | throwError "record layout requires source field metadata"
    let ctor := getStructureCtor (← getEnv) name
    let constructor := mkAppN (mkConst ctor.name levels)
      (type.getAppArgs.extract 0 ctor.numParams)
    forallTelescope (← inferType constructor) fun locals _ => do
      unless locals.size == info.fieldNames.size do
        throwError "record layout field metadata disagrees with its constructor"
      let mut fields : Array FieldLayout := #[]
      let mut wireIndex := 0
      for index in [:locals.size] do
        let some projection := info.getProjFn? index
          | throwError "record layout is missing a source projection"
        let fieldType ← inferType locals[index]!
        let dependencies := (Array.range index).filter fun previous =>
          fieldType.containsFVar locals[previous]!.fvarId!
        let typeFamily ← mkLambdaFVars (locals.extract 0 index) fieldType
          (usedOnly := false) (usedLetOnly := false)
        let value ← mkProjection expression info.fieldNames[index]!
        let fieldKind ← computationalKind (← inferType value)
        let fieldWireIndex := if fieldKind == .proof then none else some wireIndex
        fields := fields.push ⟨address.push projection, projection, index, fieldWireIndex,
          dependencies, ← context.close value, ← context.close typeFamily, fieldKind⟩
        if fieldKind != .proof then wireIndex := wireIndex + 1
      return ⟨address, source, kind, fields⟩

/-- Derive a fixed-value layout from the checked source, before any provider response. -/
opaque SourceLayout.ofTerm (source : ClosedTerm) : MetaM SourceLayout :=
  sourceLayout source #[]

/-- Inspect the same projected source value, retaining its full projection address. -/
opaque FieldLayout.toLayout (field : FieldLayout) : MetaM SourceLayout :=
  sourceLayout field.source field.address

/-- Prepare ordinary source application in the current complete context.
Arguments are checked source terms; computational candidates enter through the runtime. -/
opaque SourceLayout.applyIn (function : SourceLayout) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM SourceLayout := do
  unless function.kind == .function do
    throwError "source application requires a callable interface"
  let expression ← function.source.inContext context
  let arguments ← arguments.mapM (·.inContext context)
  sourceLayout (← context.close (mkAppN expression arguments)) function.address

end CasCompiler
