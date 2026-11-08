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

/-- Close dependencies through the selected locals' native types and definitions, in order.
Reuse: Lean.collectFVars and LocalDecl.value?; callers retain their complete telescopes.
Reference: Lean/Util/CollectFVars.lean and Lean/LocalContext.lean at v4.33.0. -/
def localDependencies (locals : Array Expr) (type : Expr) : MetaM (Array Nat) := do
  let mut variables := collectFVars {} type
  let mut needed : Array Nat := #[]
  for index in (List.range locals.size).reverse do
    let expression := locals[index]!
    if variables.fvarSet.contains expression.fvarId! then
      needed := needed.push index
      let declaration ← getFVarLocalDecl expression
      variables := collectFVars variables declaration.type
      if let some value := declaration.value? true then variables := collectFVars variables value
  return needed.reverse

/-- Result-type dependency slots in the complete ordered source binding table. -/
def contextDependencies (bindings : Array LocalBinding) (type : Expr) : MetaM (Array Nat) :=
  localDependencies (bindings.map (·.expression)) type

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

/-- A complete native argument position, with proof erasure separated from formal dependency. -/
structure ArgumentLayout where
  private mk ::
  sourceIndex : Nat
  wireIndex : Option Nat
  binderInfo : BinderInfo
  precedingDependencies : Array Nat
  source : SourceLayout
  typeFamily : ClosedTerm

/-- Dependencies refer to the original formal argument slots, before actual source substitution.
Complete native type families retain every binder, including proof-only and unused positions. -/
structure ApplicationLayout where
  private mk ::
  arguments : Array ArgumentLayout
  resultDependencies : Array Nat
  resultTypeFamily : ClosedTerm
  result : SourceLayout
  resultContextDependencies : Array Nat

/-- Prepare the native application and its original callable telescope together.
Reuse: SourceLayout.applyIn, Lean.forallBoundedTelescope, localDependencies and mkLambdaFVars.
No runtime data is substituted into a native source term or its type family. -/
opaque ApplicationLayout.ofSource (function : SourceLayout) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM (SourceLayout × ApplicationLayout) := do
  let result ← function.applyIn context arguments
  let actual ← arguments.mapM SourceLayout.ofTerm
  let callable ← context.apply function.source #[]
  let type ← inferType callable
  forallBoundedTelescope type (some arguments.size) fun locals resultType => do
    unless locals.size == arguments.size do
      throwError "application layout requires the complete supplied native argument prefix"
    let mut prepared : Array ArgumentLayout := #[]
    let mut wireIndex := 0
    for argument in locals, index in [:locals.size] do
      let domain ← inferType argument
      let previous := locals.extract 0 index
      let dependencies ← localDependencies previous domain
      let family ← mkLambdaFVars previous domain (usedOnly := false) (usedLetOnly := false)
      let erased ← isProp domain
      let some source := actual[index]?
        | throwError "application layout lost a supplied native source argument"
      prepared := prepared.push ⟨index, if erased then none else some wireIndex,
        (← getFVarLocalDecl argument).binderInfo, dependencies, source,
        ← context.close family⟩
      if !erased then wireIndex := wireIndex + 1
    let dependencies ← localDependencies locals resultType
    let family ← mkLambdaFVars locals resultType (usedOnly := false) (usedLetOnly := false)
    let contextDependencies ← localDependencies (context.bindings.map (·.expression)) resultType
    return (result, ⟨prepared, dependencies, ← context.close family, result,
      contextDependencies⟩)

/-- Native projection metadata selects the original record, including class-valued records.
Reuse: Lean.ProjectionFunctionInfo, ConstructorVal.induct and Expr.proj at Lean v4.33.0.
Explicit projections avoid selecting a replacement local class instance. -/
private def projectSource (expression : Expr) (path : Array Name) : MetaM Expr := do
  let mut selected := expression
  for projection in path do
    let some info := (← getEnv).getProjectionFnInfo? projection
      | throwError "the application result address contains a nonprojection declaration"
    let constructor ← getConstInfoCtor info.ctorName
    selected := mkProj constructor.induct info.i selected
    check selected
  return selected

/-- Source-context and argument planes remain distinct from returned record-prefix fields. -/
structure ResultDependencies where
  context : Array Nat
  arguments : Array Nat

/-- Reflect constructor field domains under abstract preceding fields, as sourceLayout does.
If source arguments determine the record shape, retain that shape's formal dependencies.
Reference: Lean.forallBoundedTelescope, ConstructorVal and the native FieldLayout algorithm. -/
private partial def fieldDependencies (type actual : Expr) (path : List Name)
    (context arguments : Array Expr) (shapeContext shapeArguments : Array Nat) :
    MetaM ResultDependencies := do
  match path with
  | [] =>
    let contextDependencies ← localDependencies context type
    let argumentDependencies ← localDependencies arguments type
    return {
      context := (Array.range context.size).filter fun index =>
        shapeContext.contains index || contextDependencies.contains index
      arguments := (Array.range arguments.size).filter fun index =>
        shapeArguments.contains index || argumentDependencies.contains index }
  | projection :: rest =>
    let some info := (← getEnv).getProjectionFnInfo? projection
      | throwError "the application result address contains a nonprojection declaration"
    let constructor ← getConstInfoCtor info.ctorName
    let reduced ← whnf type
    let (type, shapeContext, shapeArguments) ←
      if reduced.getAppFn.constName? == some constructor.induct then
        pure (reduced, shapeContext, shapeArguments)
      else do
        let actualType ← whnf (← inferType actual)
        unless actualType.getAppFn.constName? == some constructor.induct do
          throwError "the source field has a different native record interface"
        pure (actualType, shapeContext ++ (← localDependencies context reduced),
          shapeArguments ++ (← localDependencies arguments reduced))
    let .const _ levels := type.getAppFn
      | throwError "the source field requires its native structure parameters"
    let applied := mkAppN (mkConst constructor.name levels)
      (type.getAppArgs.extract 0 constructor.numParams)
    forallBoundedTelescope (← inferType applied) (some (info.i + 1)) fun fields _ => do
      let some selected := fields[info.i]?
        | throwError "the native constructor lost a prepared result field"
      let actual ← projectSource actual #[projection]
      fieldDependencies (← inferType selected) actual rest context arguments
        shapeContext shapeArguments

/-- Check a descendant source role in its complete current context.
Stable source transport retains the parent across later bindings and lexical shadowing. -/
opaque SourceLayout.projectionPathTo (parent source : SourceLayout) : MetaM (Array Name) := do
  unless parent.address.toList.isPrefixOf source.address.toList do
    throwError "the source role is outside the prepared application result"
  let path := source.address.extract parent.address.size source.address.size
  source.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let expected ← projectSource (← parent.source.inContext context) path
    unless ← isDefEq expected expression do
      throwError "the source role is not its prepared application result projection"
    return path

/-- Native dependency slots at a relative projection path in the original application.
Preceding fields stay abstract. Both dependency planes keep their original source ordering. -/
opaque ApplicationLayout.dependenciesAt (layout : ApplicationLayout) (path : Array Name) :
    MetaM ResultDependencies :=
  layout.result.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    discard <| projectSource expression path
    let family ← layout.resultTypeFamily.inContext context
    lambdaTelescope family fun arguments type => do
      unless arguments.size == layout.arguments.size do
        throwError "the application result family lost a formal argument"
      fieldDependencies type expression path.toList (bindings.map (·.expression)) arguments #[] #[]

/-- Select an exact source descendant while preserving the original dependency planes. -/
opaque ApplicationLayout.dependenciesFor (layout : ApplicationLayout) (source : SourceLayout) :
    MetaM ResultDependencies := do
  layout.dependenciesAt (← layout.result.projectionPathTo source)

end CasCompiler
