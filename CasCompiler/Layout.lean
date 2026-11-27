module

import CasContract.Failure
import Lean.Meta.WHNF
public import CasCompiler.Context
public import CasCompiler.SelectionScope
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

partial def projectionBody? : Expr → Option Expr
  | .mdata _ body => projectionBody? body
  | expression => some expression


structure SourceProjection where
  private mk ::
  declaration : Name
  parent : Expr
  info : ProjectionFunctionInfo




opaque SourceProjection.ofExpr? (source : Expr) : MetaM (Option SourceProjection) := do
  let some expression := projectionBody? source | return none
  match expression with
  | .proj owner index parent =>
    let some structureInfo := getStructureInfo? (← getEnv) owner | return none
    let some declaration := structureInfo.getProjFn? index | return none
    let some info := (← getEnv).getProjectionFnInfo? declaration | return none
    return some ⟨declaration, parent, info⟩
  | _ =>
    let .const declaration _ := expression.getAppFn | return none
    let some info := (← getEnv).getProjectionFnInfo? declaration | return none
    let arguments := expression.getAppArgs
    unless arguments.size == info.numParams + 1 do return none
    return some ⟨declaration, arguments[info.numParams]!, info⟩


inductive InputProjectionTarget where
  | argument (index : Nat)
  | context (binding : BindingId)


structure InputProjection where
  private mk ::
  target : InputProjectionTarget
  path : Array Name




private def contextProjectionInputs (bindings : Array LocalBinding)
    (contextInputs : Array BindingId) : MetaM (Std.HashMap FVarId InputProjectionTarget) := do
  let mut available : Std.HashMap BindingId Expr := {}
  for binding in bindings do
    available := available.insert binding.id binding.expression
  let mut inputs : Std.HashMap FVarId InputProjectionTarget := {}
  for binding in contextInputs do
    let some expression := available[binding]?
      | throwError "a fixed context input is outside its original source telescope"
    let .fvar id := expression
      | throwError "a fixed context input has no original source local"
    if inputs.contains id then
      throwError "a fixed context input repeats an original source binding"
    if ← isProp (← inferType expression) then
      throwError "a proof context binding has no fixed computational input"
    inputs := inputs.insert id (.context binding)
  return inputs






private partial def inputProjectionHead (inputs : Std.HashMap FVarId InputProjectionTarget)
    (source : Expr) : MetaM Expr := do
  let some expression := projectionBody? source | return source
  if let some projection ← SourceProjection.ofExpr? expression then
    let parent ← inputProjectionHead inputs projection.parent
    if parent.getAppFn.constName? == some projection.info.ctorName then
      if let some field ← projectCore? parent projection.info.i then
        return ← inputProjectionHead inputs field
    let constructor ← getConstInfoCtor projection.info.ctorName
    return mkProj constructor.induct projection.info.i parent
  match expression with
  | .fvar id =>
    if inputs.contains id then return expression
    match (← getFVarLocalDecl expression).value? with
    | some value => inputProjectionHead inputs value
    | none => pure expression
  | .letE _ _ value body _ => inputProjectionHead inputs (body.instantiate1 value)
  | .app .. =>
    let function ← inputProjectionHead inputs expression.getAppFn
    let applied := mkAppN function expression.getAppArgs
    let arguments := applied.getAppArgs
    if let .const name _ := applied.getAppFn then
      if let some info := (← getEnv).getProjectionFnInfo? name then
        let arity := info.numParams + 1
        if arguments.size == arity then
          return ← inputProjectionHead inputs applied
        if arguments.size > arity then
          let field ← inputProjectionHead inputs
            (mkAppN applied.getAppFn (arguments.extract 0 arity))
          let remaining := arguments.extract arity arguments.size
          if field.isLambda then
            return ← inputProjectionHead inputs (field.betaRev remaining.reverse
              (useZeta := false) (preserveMData := true))
          return mkAppN field remaining
    if function.isLambda then
      inputProjectionHead inputs (function.betaRev expression.getAppRevArgs
        (useZeta := false) (preserveMData := true))
    else pure applied
  | .const name levels =>
    if ((← getEnv).getProjectionFnInfo? name).isSome then return expression
    if ← isMatcher name then return expression
    let some (.defnInfo declaration) := (← getEnv).find? name | return expression
    inputProjectionHead inputs
      (declaration.value.instantiateLevelParams declaration.levelParams levels)
  | _ => pure expression




private def inputProjectionEta? (inputs : Std.HashMap FVarId InputProjectionTarget)
    (source : Expr) : MetaM (Option Expr) := do
  let .const name _ := source.getAppFn | return none
  let environment ← getEnv
  let some (.ctorInfo constructor) := environment.find? name | return none
  unless (getStructureInfo? environment constructor.induct).isSome do return none
  let mut arguments := source.getAppArgs
  unless arguments.size == constructor.numParams + constructor.numFields do return none
  for index in [constructor.numParams:arguments.size] do
    let field ← inputProjectionHead inputs arguments[index]!


    let field ← match ← SourceProjection.ofExpr? field with
      | none => pure field
      | some projection => do
        let parentType ← whnf (← inferType projection.parent)
        let projectionCtor ← getConstInfoCtor projection.info.ctorName
        unless parentType.getAppFn.constName? == some projectionCtor.induct &&
            parentType.getAppArgs.size == projection.info.numParams do return field
        mkAppOptM projection.declaration
          ((parentType.getAppArgs.push projection.parent).map some)
    arguments := arguments.set! index field
  etaStruct? (mkAppN source.getAppFn arguments) (· == constructor.induct)




private partial def inputProjection (inputs : Std.HashMap FVarId InputProjectionTarget) (source : Expr)
    (path : List Name) : MetaM (Option InputProjection) := do
  let source ← inputProjectionHead inputs source
  if let .fvar id := source then
    let some target := inputs[id]? | return none
    return some ⟨target, path.toArray⟩
  if let some projection ← SourceProjection.ofExpr? source then
    return ← inputProjection inputs projection.parent (projection.declaration :: path)
  if path.isEmpty then
    if let some retained ← inputProjectionEta? inputs source then
      return ← inputProjection inputs retained []
    return none
  let projection :: rest := path | return none
  let some info := (← getEnv).getProjectionFnInfo? projection
    | throwError "the fixed result address contains a nonprojection declaration"
  unless source.getAppFn.constName? == some info.ctorName do return none
  let some field ← projectCore? source info.i | return none
  inputProjection inputs field rest

private def sourceProjectionInputs (bindings : Array LocalBinding) :
    Std.HashMap FVarId InputProjectionTarget := Id.run do
  let mut inputs := {}
  for binding in bindings do
    inputs := inputs.insert binding.expression.fvarId! (.context binding.id)
  return inputs

private def retainContextProjection (retained : Std.HashMap BindingId InputProjection)
    (projection : InputProjection) : MetaM InputProjection := do
  let .context binding := projection.target
    | throwError "an original source context projection acquired an argument position"
  let some parent := retained[binding]?
    | throwError "a source projection is outside its original ordered binding table"
  return { parent with path := parent.path ++ projection.path }





private def declaredInputProjections (bindings : Array LocalBinding) :
    MetaM (Std.HashMap BindingId InputProjection) := do
  let inputs := sourceProjectionInputs bindings
  let mut retained := {}
  for binding in bindings do
    let mut projection : InputProjection := ⟨.context binding.id, #[]⟩
    if let some definition := (← getFVarLocalDecl binding.expression).value? true then
      if let some source ← inputProjection inputs definition [] then
        projection ← retainContextProjection retained source
    retained := retained.insert binding.id projection
  return retained


opaque OpenContext.inputProjections (context : OpenContext) :
    MetaM (Std.HashMap BindingId InputProjection) :=
  declaredInputProjections context.bindings

private def declaredSourceProjection (bindings : Array LocalBinding) (source : Expr) :
    MetaM (Option InputProjection) := do
  let some projection ← inputProjection (sourceProjectionInputs bindings) source []
    | return none
  return some (← retainContextProjection (← declaredInputProjections bindings) projection)


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

  private recordAncestors : Array ClosedTerm
  selections : SourceSelectionScope ClosedTerm := {}




structure FieldDependencyView where
  private mk ::
  path : Array Name
  typeFamily : ClosedTerm
  precedingDependencies : Array Nat


structure SourceLayout where
  private mk ::
  address : Array Name
  source : ClosedTerm
  kind : ComputationalKind
  fields : Array FieldLayout
  contextDependencies : Array Nat

  inputProjection : Option InputProjection

  private recordAncestors : Array ClosedTerm
  selections : SourceSelectionScope ClosedTerm := {}
  selectionBinding : Option BindingId := none



def SourceLayout.selected? (layout : SourceLayout) (context : OpenContext) :
    MetaM (Option (SourceSelection Expr)) := do
  let some id := layout.selectionBinding | return none
  let some binding := context.bindings.find? (·.id == id)
    | throwError "the displayed role's selected source is outside its complete context"
  let selections ← layout.selections.inContext context
  let some selected := selections[id]?
    | throwError "the displayed role lost its original selected source binding"
  unless selected.formalBindings.isEmpty do
    throwError "the displayed role retains an unapplied source selection template"
  let original ← layout.source.inContext context
  context.withOriginalSources #[binding.expression, original, selected.value] fun sources => do
    let expected ← inferType sources[0]!
    unless ← isDefEq expected (← inferType sources[1]!) <&&>
        isDefEq expected (← inferType sources[2]!) do
      throwError "the displayed role changed its selected source's complete native type"
  return some selected




opaque localDependencies (locals : Array Expr) (type : Expr) :
    MetaM (Array Nat) := do
  let mut freeVariables := collectFVars {} type
  let mut needed : Array Nat := #[]
  for index in (List.range locals.size).reverse do
    let expression := locals[index]!
    if freeVariables.fvarSet.contains expression.fvarId! then
      needed := needed.push index
      let declaration ← getFVarLocalDecl expression
      freeVariables := collectFVars freeVariables declaration.type
      if let some value := declaration.value? true then
        freeVariables := collectFVars freeVariables value
  return needed.reverse



opaque computationalDependencies (locals : Array Expr) (type : Expr) : MetaM (Array Nat) :=
  localDependencies locals type


def contextDependencies (bindings : Array LocalBinding) (type : Expr) : MetaM (Array Nat) :=
  localDependencies (bindings.map (·.expression)) type




def selectedContextDependencies (context : OpenContext)
    (selections : SourceSelectionScope Expr) (expression : Expr) : MetaM (Array Nat) := do
  let mut pending ← contextDependencies context.bindings expression
  let mut visited : Std.HashSet Nat := {}
  while !pending.isEmpty do
    let some index := pending.back?
      | throwError "the source dependency queue lost its next original position"
    pending := pending.pop
    if visited.contains index then continue
    visited := visited.insert index
    let some binding := context.bindings[index]?
      | throwError "a selected source dependency is outside its complete context"
    match selections[binding.id]? with
    | none =>
      if binding.role == .selectedStructure then
        throwError "the source policy lost a complete typed selection"
    | some selected =>
      let additional ← IO.mkRef (#[] : Array Nat)
      discard <| selected.mapM fun term => do
        let dependencies ← contextDependencies context.bindings term
        additional.modify (· ++ dependencies)
        return term
      pending := pending ++ (← additional.get)
  return (Array.range context.bindings.size).filter visited.contains

private def computationalKind (type : Expr) : MetaM ComputationalKind := do
  if ← isProp type then return .proof
  let type ← whnf type
  if type.isForall then return .function
  if type.isSort then return .typeValue
  if let some name := type.getAppFn.constName? then
    if isStructure (← getEnv) name then return .record
  return .data






private def sourceLayout (source : ClosedTerm) (address : Array Name)
    (recordAncestors : Array ClosedTerm)
    (selections : SourceSelectionScope ClosedTerm := {})
    (selectionBinding : Option BindingId := none) : MetaM SourceLayout :=
  source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let selections ← selections.inContext context
    for (id, _) in selections do
      unless bindings.any (·.id == id) do
        throwError "a source layout selection is outside its complete typed context"
    let selections ← selections.close context
    if let some id := selectionBinding then
      unless selections.contains id do
        throwError "a source layout lost its explicit original selection binding"
    let inputProjection ← declaredSourceProjection bindings expression
    let originalType ← inferType expression
    let dependencies ← computationalDependencies (bindings.map (·.expression)) originalType
    let type ← whnf originalType
    let kind ← computationalKind type
    if kind != .record then return ⟨address, source, kind, #[], dependencies, inputProjection, recordAncestors, selections, selectionBinding⟩
    for ancestor in recordAncestors do
      if ← isDefEq type (← ancestor.inContext context) then
        CasCatalogue.throwStratum .noImplementation
          "the result requires a recursive public record schema"
    let recordPath := recordAncestors.push (← context.close type)
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
        let dependencies ← computationalDependencies (locals.extract 0 index) fieldType
        let typeFamily ← mkLambdaFVars (locals.extract 0 index) fieldType
          (usedOnly := false) (usedLetOnly := false)
        let value ← mkProjection expression info.fieldNames[index]!
        let fieldKind ← computationalKind (← inferType value)
        let fieldWireIndex := if fieldKind == .proof then none else some wireIndex
        fields := fields.push ⟨address.push projection, projection, index, fieldWireIndex,
          dependencies, ← context.close value, ← context.close typeFamily, fieldKind, recordPath, selections⟩
        if fieldKind != .proof then wireIndex := wireIndex + 1
      return ⟨address, source, kind, fields, dependencies, inputProjection, recordAncestors, selections, selectionBinding⟩


opaque SourceLayout.ofTerm (source : ClosedTerm)
    (selections : SourceSelectionScope ClosedTerm := {})
    (selectionBinding : Option BindingId := none) : MetaM SourceLayout :=
  sourceLayout source #[] #[] selections selectionBinding


opaque FieldLayout.toLayout (field : FieldLayout) : MetaM SourceLayout :=
  sourceLayout field.source field.address field.recordAncestors field.selections


structure RecordField where
  private mk ::
  field : FieldLayout
  layout : SourceLayout




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


opaque SourceLayout.inContext (layout : SourceLayout) (context : OpenContext) : MetaM SourceLayout := do
  let selections ← (← layout.selections.inContext context).close context
  sourceLayout (← context.close (← layout.source.inContext context)) layout.address
    layout.recordAncestors selections layout.selectionBinding


opaque SourceLayout.withSelections (layout : SourceLayout)
    (selections : SourceSelectionScope ClosedTerm) : MetaM SourceLayout :=
  layout.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let merged ← SourceSelectionScope.merge (← layout.selections.inContext context)
      (← selections.inContext context)
    sourceLayout layout.source layout.address layout.recordAncestors (← merged.close context)
      layout.selectionBinding



opaque SourceLayout.applyIn (function : SourceLayout) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM SourceLayout := do
  let selections ← (← function.selections.inContext context).close context
  sourceLayout (← context.close (← context.apply function.source arguments)) function.address #[] selections


structure ArgumentLayout where
  private mk ::
  sourceIndex : Nat
  wireIndex : Option Nat
  binderInfo : BinderInfo
  precedingDependencies : Array Nat
  source : SourceLayout
  typeFamily : ClosedTerm



structure ApplicationLayout where
  private mk ::
  arguments : Array ArgumentLayout
  resultDependencies : Array Nat
  resultTypeFamily : ClosedTerm
  resultTermFamily : ClosedTerm


  private nativeInputTermFamily : ClosedTerm
  result : SourceLayout
  resultContextDependencies : Array Nat


opaque ApplicationLayout.withSelections (layout : ApplicationLayout) (context : OpenContext)
    (selections : SourceSelectionScope ClosedTerm) : MetaM ApplicationLayout := do
  let result ← (← layout.result.inContext context).withSelections selections
  let arguments ← layout.arguments.mapM fun argument => do
    let source ← (← argument.source.inContext context).withSelections selections
    return { argument with source }
  return { layout with result, arguments }




opaque ApplicationLayout.ofSource (function : SourceLayout) (context : OpenContext)
    (arguments : Array ClosedTerm) (nativeInputFamily : Option ClosedTerm := none)
    (selections : SourceSelectionScope ClosedTerm := {}) :
    MetaM (SourceLayout × ApplicationLayout) := do
  let function ← (← function.inContext context).withSelections selections


  let retainWholeFamily := arguments.isEmpty &&
    (nativeInputFamily.isSome || function.kind != .function)
  let result ← if retainWholeFamily then function.inContext context
    else function.applyIn context arguments
  let actual ← arguments.mapM fun argument => do
    SourceLayout.ofTerm (← context.close (← argument.inContext context)) function.selections
  let callable ← if retainWholeFamily then function.source.inContext context
    else context.apply function.source #[]
  let inputCallable ← match nativeInputFamily with
    | none => pure callable
    | some native => do
      let native ← native.inContext context
      unless callable.equal native do
        throwError "native input analysis changed the original family body"
      pure native
  let type ← inferType callable
  forallBoundedTelescope type (some arguments.size) fun locals resultType => do
    unless locals.size == arguments.size do
      throwError "application layout requires the complete supplied native argument prefix"
    let mut prepared : Array ArgumentLayout := #[]
    let mut wireIndex := 0
    for argument in locals, index in [:locals.size] do
      let domain ← inferType argument
      let previous := locals.extract 0 index
      let dependencies ← computationalDependencies previous domain
      let family ← mkLambdaFVars previous domain (usedOnly := false) (usedLetOnly := false)
      let erased ← isProp domain
      let some source := actual[index]?
        | throwError "application layout lost a supplied native source argument"
      prepared := prepared.push ⟨index, if erased then none else some wireIndex,
        (← getFVarLocalDecl argument).binderInfo, dependencies, source,
        ← context.close family⟩
      if !erased then wireIndex := wireIndex + 1
    let dependencies ← computationalDependencies locals resultType
    let family ← mkLambdaFVars locals resultType (usedOnly := false) (usedLetOnly := false)
    let termFamily ← context.close (← mkLambdaFVars locals (mkAppN callable locals)
      (usedOnly := false) (usedLetOnly := false))
    let nativeInputTermFamily ← if nativeInputFamily.isNone then pure termFamily else do
      context.close (← mkLambdaFVars locals (mkAppN inputCallable locals)
        (usedOnly := false) (usedLetOnly := false))
    let contextDependencies ← computationalDependencies (context.bindings.map (·.expression)) resultType
    return (result, ⟨prepared, dependencies, ← context.close family, termFamily,
      nativeInputTermFamily, result,
      contextDependencies⟩)




private def projectSource (expression : Expr) (path : Array Name) : MetaM Expr := do
  let mut selected := expression
  for projection in path do
    let some info := (← getEnv).getProjectionFnInfo? projection
      | throwError "the application result address contains a nonprojection declaration"
    let constructor ← getConstInfoCtor info.ctorName
    selected := mkProj constructor.induct info.i selected
    check selected
  return selected





opaque ApplicationLayout.inputProjectionAt (layout : ApplicationLayout) (path : Array Name)
    (contextInputs : Array BindingId := #[]) :
    MetaM (Option InputProjection) :=
  layout.result.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    discard <| projectSource expression path
    let family ← layout.nativeInputTermFamily.inContext context
    lambdaBoundedTelescope family layout.arguments.size fun locals result => do
      unless locals.size == layout.arguments.size do
        throwError "the application result term family lost a formal argument"
      let mut inputs ← contextProjectionInputs bindings contextInputs
      for argument in locals, index in [:locals.size] do
        inputs := inputs.insert argument.fvarId! (.argument index)
      inputProjection inputs result path.toList





opaque sourceInputProjection? (source : Expr) (locals : Array Expr)
    (path : Array Name := #[]) : MetaM (Option (Nat × Array Name)) := do
  let mut inputs : Std.HashMap FVarId InputProjectionTarget := {}
  for input in locals, index in [:locals.size] do
    let .fvar id := input
      | throwError "an open source input is not its original local variable"
    if inputs.contains id || (← isProof input) then
      throwError "an open source input repeats a binding or selects a proof"
    inputs := inputs.insert id (.argument index)
  discard <| projectSource source path
  let some selected ← inputProjection inputs source path.toList | return none
  let .argument index := selected.target
    | throwError "an open source input selected an unavailable context binding"
  return some (index, selected.path)




opaque ClosedTerm.inputProjectionAt (source : ClosedTerm) (path : Array Name)
    (contextInputs : Array BindingId := #[]) : MetaM (Option InputProjection) :=
  source.withOpen fun bindings expression => do
    discard <| projectSource expression path
    inputProjection (← contextProjectionInputs bindings contextInputs) expression path.toList



opaque OpenContext.inputProjectionSource (context : OpenContext) (expression : Expr)
    (contextInputs : Array BindingId) : MetaM Expr := do
  inputProjectionHead (← contextProjectionInputs context.bindings contextInputs) expression





opaque ClosedTerm.inputProjectionSource (source : ClosedTerm) : MetaM ClosedTerm :=
  source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let mut inputs : Std.HashMap FVarId InputProjectionTarget := {}
    for binding in bindings do
      let .fvar id := binding.expression
        | throwError "a source head context binding has no original source local"
      inputs := inputs.insert id (.context binding.id)
    let expression ← inputProjectionHead inputs expression
    context.close expression




structure InputExpression where
  private mk ::
  private family : ClosedTerm
  argumentCount : Nat

opaque InputExpression.context (expression : InputExpression) : ContextTelescope :=
  expression.family.context




inductive InputArgumentRef where
  | slot (index : Nat)
  | expression (source : InputExpression)



structure InputApplicationStep where
  selection : Array Name
  arguments : Array InputArgumentRef




inductive InputProjectionResult where
  | projection (route : InputProjection)
  | callable (route : InputProjection) (remainingSteps : Array InputApplicationStep)

private def captureInputExpression (context : OpenContext) (locals : Array Expr)
    (source : Expr) : MetaM InputExpression := do
  let family ← mkLambdaFVars locals source (usedOnly := false) (usedLetOnly := false)
  return ⟨← context.close family, locals.size⟩



private def InputExpression.inInputContext (expression : InputExpression)
    (context : OpenContext) (locals : Array Expr) : MetaM Expr := do
  unless expression.argumentCount ≤ locals.size do
    throwError "a suspended source expression lost its original formal prefix"
  let family ← expression.family.inContext context
  return family.betaRev (locals.extract 0 expression.argumentCount).reverse
    (useZeta := false) (preserveMData := true)

private def continueInputProjection (route : InputProjection)
    (steps : List InputApplicationStep) : InputProjectionResult :=
  match steps with
  | [] => .projection route
  | step :: rest =>
    let route := { route with path := route.path ++ step.selection }
    if step.arguments.isEmpty then continueInputProjection route rest
    else .callable route (({ step with selection := #[] } :: rest).toArray)

private def prependInputSelection (projection : Name) (steps : List InputApplicationStep) :
    List InputApplicationStep :=
  match steps with
  | [] => [{ selection := #[projection], arguments := #[] }]
  | step :: rest => { step with selection := #[projection] ++ step.selection } :: rest




private def inputProjectionLambda? (source : Expr) : MetaM (Option Expr) := do
  let .const name _ := source.getAppFn | return none
  let some info := (← getEnv).getProjectionFnInfo? name | return none
  unless source.getAppArgs.size < info.numParams + 1 do return none
  let .forallE name domain _ binderInfo ← inferType source | return none
  withLocalDecl name binderInfo domain fun argument => do
    return some (← mkLambdaFVars #[argument] (mkApp source argument)
      (usedOnly := false) (usedLetOnly := false))

mutual





private partial def traceInputApplications (context : OpenContext)
    (inputs : Std.HashMap FVarId InputProjectionTarget) (locals : Array Expr)
    (source : Expr) (steps : List InputApplicationStep) :
    MetaM (Option InputProjectionResult) := do
  match steps with
  | [] => traceInputSource context inputs locals source []
  | step :: rest =>
    let mut selected := source
    for projection in step.selection do
      let some info := (← getEnv).getProjectionFnInfo? projection
        | throwError "the composed input route contains a nonprojection declaration"
      let constructor ← getConstInfoCtor info.ctorName
      selected := mkProj constructor.induct info.i selected
    if step.arguments.isEmpty then
      return ← traceInputApplications context inputs locals selected rest
    let head ← inputProjectionHead inputs selected
    let pending := { step with selection := #[] } :: rest
    if let some route ← inputProjection inputs head [] then
      return some (continueInputProjection route pending)
    let head ← if head.isLambda then pure head
      else pure ((← inputProjectionLambda? head).getD head)
    let .lam name domain body binderInfo := head
      | return ← traceInputSource context inputs locals head pending
    let some argument := step.arguments[0]?
      | throwError "a pending source application lost its next formal argument"
    let remaining : List InputApplicationStep :=
      { selection := #[], arguments := step.arguments.extract 1 step.arguments.size } :: rest
    match argument with
    | .expression expression =>
      let value ← expression.inInputContext context locals
      traceInputApplications context inputs locals (body.instantiate1 value) remaining
    | .slot index =>
      if let some argument := locals[index]? then
        return ← traceInputApplications context inputs locals (body.instantiate1 argument) remaining
      unless index == locals.size do
        throwError "a composed source application lost its complete formal argument prefix"
      withLocalDecl name binderInfo domain fun argument =>
        traceInputApplications context (inputs.insert argument.fvarId! (.argument index))
          (locals.push argument) (body.instantiate1 argument) remaining




private partial def traceInputSource (context : OpenContext)
    (inputs : Std.HashMap FVarId InputProjectionTarget) (locals : Array Expr)
    (source : Expr) (steps : List InputApplicationStep) :
    MetaM (Option InputProjectionResult) := do
  let source ← inputProjectionHead inputs source
  if let some route ← inputProjection inputs source [] then
    return some (continueInputProjection route steps)
  if let some projection ← SourceProjection.ofExpr? source then
    return ← traceInputSource context inputs locals projection.parent
      (prependInputSelection projection.declaration steps)



  let callable ← if source.isLambda then pure (some source)
    else inputProjectionLambda? source
  if let some callable := callable then
    if let some next := steps.head? then
      if next.selection.isEmpty then
        return ← traceInputApplications context inputs locals callable steps
    return none
  if source.isApp then
    let arguments ← source.getAppArgs.mapM fun argument => do
      return InputArgumentRef.expression (← captureInputExpression context locals argument)
    return ← traceInputSource context inputs locals source.getAppFn
      ({ selection := #[], arguments } :: steps)
  return none

end

private def inputApplicationSteps (argumentCount : Nat)
    (steps : Array (Array Name × Nat)) (path : Array Name) : Array InputApplicationStep := Id.run do
  let mut offset := argumentCount
  let mut result := #[]
  for (selection, count) in steps do
    let arguments := (Array.range count).map fun index => InputArgumentRef.slot (offset + index)
    result := result.push { selection, arguments }
    offset := offset + count
  if !path.isEmpty then result := result.push { selection := path, arguments := #[] }
  return result





opaque InputExpression.inputProjectionThrough (expression : InputExpression)
    (steps : Array (Array Name × Nat)) (path : Array Name)
    (contextInputs : Array BindingId := #[]) : MetaM (Option InputProjectionResult) :=
  expression.family.withOpen fun bindings family => do
    let context ← ContextTelescope.capture bindings
    lambdaBoundedTelescope family expression.argumentCount fun locals result => do
      unless locals.size == expression.argumentCount do
        throwError "a suspended source expression lost a formal argument"
      let mut inputs ← contextProjectionInputs bindings contextInputs
      for argument in locals, index in [:locals.size] do
        inputs := inputs.insert argument.fvarId! (.argument index)
      traceInputApplications context inputs locals result
        (inputApplicationSteps locals.size steps path).toList








opaque ApplicationLayout.inputProjectionThrough (first : ApplicationLayout)
    (steps : Array (Array Name × Nat)) (path : Array Name)
    (contextInputs : Array BindingId := #[]) :
    MetaM (Option InputProjectionResult) :=
  first.result.source.withOpen fun bindings result => do
    let context ← ContextTelescope.capture bindings
    if steps.isEmpty then discard <| projectSource result path


    let family ← context.close (← first.nativeInputTermFamily.inContext context)
    let expression : InputExpression := ⟨family, first.arguments.size⟩
    expression.inputProjectionThrough steps path contextInputs


structure ResultDependencies where
  context : Array Nat
  arguments : Array Nat




private def originalDependencies (context arguments introduced : Array Expr) (type : Expr) :
    MetaM ResultDependencies := do
  let required ← computationalDependencies (context ++ arguments ++ introduced) type
  return {
    context := (Array.range context.size).filter required.contains
    arguments := (Array.range arguments.size).filter fun index =>
      required.contains (context.size + index) }




private partial def withFieldTypeAt (type actual : Expr) (path : List Name)
    (context arguments : Array Expr) (introduced : Array Expr) (shape : ResultDependencies)
    (visit : Array Expr → Expr → ResultDependencies → MetaM α) : MetaM α := do
  match path with
  | [] => visit introduced type shape
  | projection :: rest =>
    let some info := (← getEnv).getProjectionFnInfo? projection
      | throwError "the application result address contains a nonprojection declaration"
    let constructor ← getConstInfoCtor info.ctorName
    let reduced ← whnf type
    let (type, shape) ←
      if reduced.getAppFn.constName? == some constructor.induct then
        pure (reduced, shape)
      else do
        let actualType ← whnf (← inferType actual)
        unless actualType.getAppFn.constName? == some constructor.induct do
          throwError "the source field has a different native record interface"
        let dependencies ← originalDependencies context arguments introduced reduced
        pure (actualType, {
          context := shape.context ++ dependencies.context
          arguments := shape.arguments ++ dependencies.arguments })
    let .const _ levels := type.getAppFn
      | throwError "the source field requires its native structure parameters"
    let applied := mkAppN (mkConst constructor.name levels)
      (type.getAppArgs.extract 0 constructor.numParams)
    forallBoundedTelescope (← inferType applied) (some (info.i + 1)) fun fields _ => do
      let some selected := fields[info.i]?
        | throwError "the native constructor lost a prepared result field"
      let actual ← projectSource actual #[projection]
      withFieldTypeAt (← inferType selected) actual rest context arguments
        (introduced ++ fields.extract 0 info.i) shape visit

private def fieldDependencies (type actual : Expr) (path : List Name)
    (context arguments : Array Expr) (shapeContext shapeArguments : Array Nat) :
    MetaM ResultDependencies :=
  withFieldTypeAt type actual path context arguments #[] ⟨shapeContext, shapeArguments⟩
    fun introduced type shape => do
      let dependencies ← originalDependencies context arguments introduced type
      return {
        context := (Array.range context.size).filter fun index =>
          shape.context.contains index || dependencies.context.contains index
        arguments := (Array.range arguments.size).filter fun index =>
          shape.arguments.contains index || dependencies.arguments.contains index }




opaque FieldLayout.dependencyView (field : FieldLayout) (path : Array Name) :
    MetaM FieldDependencyView :=
  field.typeFamily.withOpen fun bindings family => do
    let context ← ContextTelescope.capture bindings
    let actual ← field.source.inContext context
    lambdaBoundedTelescope family field.sourceIndex fun preceding type => do
      unless preceding.size == field.sourceIndex do
        throwError "a dependent field lost its original native prefix"
      withFieldTypeAt type actual path.toList #[] preceding #[] ⟨#[], #[]⟩
        fun introduced type shape => do
          let locals := preceding ++ introduced
          let dependencies ← computationalDependencies locals type
          let required := (Array.range preceding.size).filter fun index =>
            shape.arguments.contains index || dependencies.contains index
          let family ← mkLambdaFVars locals type (usedOnly := false) (usedLetOnly := false)
          return ⟨path, ← context.close family, required⟩



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


opaque ApplicationLayout.dependenciesFor (layout : ApplicationLayout) (source : SourceLayout) :
    MetaM ResultDependencies := do
  layout.dependenciesAt (← layout.result.projectionPathTo source)




opaque ApplicationLayout.forProjection (layout : ApplicationLayout) (projection : Name) :
    MetaM ApplicationLayout := do
  let some field := layout.result.fields.find? (·.projection == projection)
    | throwError "the application selected a field outside its original native result"
  unless field.wireIndex.isSome do
    throwError "a formal proof field has no computational application result"
  let result ← field.toLayout
  let (resultTermFamily, resultTypeFamily) ← layout.resultTermFamily.withOpen
      fun bindings family => do
    let context ← ContextTelescope.capture bindings
    lambdaTelescope family fun arguments value => do
      unless arguments.size == layout.arguments.size do
        throwError "the native result projection lost its original declaration telescope"
      let selected ← projectSource value #[projection]
      let term ← mkLambdaFVars arguments selected (usedOnly := false) (usedLetOnly := false)
      let type ← mkLambdaFVars arguments (← inferType selected)
        (usedOnly := false) (usedLetOnly := false)
      return (← context.close term, ← context.close type)
  let nativeInputTermFamily ← layout.nativeInputTermFamily.withOpen fun bindings family => do
    let context ← ContextTelescope.capture bindings
    lambdaTelescope family fun arguments value => do
      let selected ← projectSource value #[projection]
      context.close (← mkLambdaFVars arguments selected
        (usedOnly := false) (usedLetOnly := false))
  let dependencies ← layout.dependenciesAt #[projection]
  return { layout with
    result := result
    resultTermFamily := resultTermFamily
    resultTypeFamily := resultTypeFamily
    nativeInputTermFamily := nativeInputTermFamily
    resultDependencies := dependencies.arguments,
    resultContextDependencies := dependencies.context }

end CasCompiler
