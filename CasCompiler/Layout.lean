module

public import CasCompiler.Context
public import Lean.Meta.Structure
public import Lean.Util.CollectFVars

@[expose] public section

namespace CasCompiler

open Lean Meta

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
  contextDependencies : Array Nat

/-- Close result-type dependencies through local types and definitions, in source order.
Reuse: Lean.collectFVars and LocalDecl.value?; the complete telescope stays in source.
Reference: Lean/Util/CollectFVars.lean and Lean/LocalContext.lean at v4.33.0. -/
private def contextDependencies (bindings : Array LocalBinding) (type : Expr) : MetaM (Array Nat) := do
  let mut variables := collectFVars {} type
  let mut needed : Array Nat := #[]
  for index in (List.range bindings.size).reverse do
    let binding := bindings[index]!
    if variables.fvarSet.contains binding.expression.fvarId! then
      needed := needed.push index
      let declaration ← getFVarLocalDecl binding.expression
      variables := collectFVars variables declaration.type
      if let some value := declaration.value? true then variables := collectFVars variables value
  return needed.reverse

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
    let originalType ← inferType expression
    let dependencies ← contextDependencies bindings originalType
    let type ← whnf originalType
    let kind ← computationalKind type
    if kind != .record then return ⟨address, source, kind, #[], dependencies⟩
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
      return ⟨address, source, kind, fields, dependencies⟩

/-- Derive a fixed-value layout from the checked source, before any provider response. -/
opaque SourceLayout.ofTerm (source : ClosedTerm) : MetaM SourceLayout :=
  sourceLayout source #[]

/-- Inspect the same projected source value, retaining its full projection address. -/
opaque FieldLayout.toLayout (field : FieldLayout) : MetaM SourceLayout :=
  sourceLayout field.source field.address

/-- A source constructor field and its complete prepared value interface. -/
structure RecordField where
  private mk ::
  field : FieldLayout
  layout : SourceLayout

/-- Prepare every constructor position, including formal proof-only positions.
Reuse: the source-ordered FieldLayout telescope and FieldLayout.toLayout above.
Runtime prefix references remain separate from these checked source expressions. -/
structure RecordLayout where
  private mk ::
  source : SourceLayout
  fields : Array RecordField

opaque RecordLayout.ofSource (source : SourceLayout) : MetaM RecordLayout := do
  unless source.kind == .record do
    throwError "record preparation requires a source record interface"
  let fields ← source.fields.mapM fun field => do
    return { field, layout := ← field.toLayout : RecordField }
  return ⟨source, fields⟩

/-- Reopen in the complete current scope while retaining the source projection address. -/
opaque SourceLayout.inContext (layout : SourceLayout) (context : OpenContext) : MetaM SourceLayout := do
  sourceLayout (← context.close (← layout.source.inContext context)) layout.address

/-- Prepare ordinary source application in the current complete context.
Arguments are checked source terms; computational candidates enter through the runtime. -/
opaque SourceLayout.applyIn (function : SourceLayout) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM SourceLayout := do
  sourceLayout (← context.close (← context.apply function.source arguments)) function.address

end CasCompiler
