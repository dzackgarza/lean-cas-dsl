module

import CasContract.Failure
import Lean.Meta.WHNF
public import CasCompiler.Context
public import CasCompiler.SelectedField
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

/-- Fixed source inputs retain their original argument or captured-context plane. -/
inductive InputProjectionTarget where
  | argument (index : Nat)
  | context (binding : BindingId)

/-- A fixed result selects this original source input and its native projection path. -/
structure InputProjection where
  private mk ::
  target : InputProjectionTarget
  path : Array Name

deriving instance BEq for InputProjectionTarget
instance : BEq InputProjection where
  beq left right := left.target == right.target && left.path == right.path

/-- Bind only retained original context slots to their freshly reopened source locals.
Reuse: ContextTelescope's stable BindingId correspondence and the route's exact FVarId map.
Runtime supplies the IDs with actual parameter values; no source or payload comparison binds them. -/
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

/-- Expose source definitions, beta/let substitutions and constructor projections only.
Reuse: Expr.betaRev with preserved metadata and Meta.projectCore? from Lean v4.33.0.
Recursors, quotient eliminators, matchers and opaque declarations remain computation boundaries;
full whnf and smart unfolding would also perform mathematical reductions. Retained context
locals are input boundaries even when they have native definitions; unretained lets may unfold. -/
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

/-- Recognize native structure eta after source-only normalization of its constructor fields.
Reuse: Lean v4.33.0 Meta.etaStruct?, which requires each ordered field to project the SAME
source parent. Actual arguments and runtime payloads never participate in this contraction. -/
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
    -- Use the registered projection's original structure parameters for etaStruct?'s
    -- parameter check; a field's own type may have a different parameter telescope.
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

/-- Follow a validated result path through source constructors to an original source slot.
An abstract input may have a polymorphic record type: once its exact binder is reached,
the remaining actual-source path is retained without substituting any actual input. -/
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

/-- Record source aliases in original declaration order, before any actual runtime values.
Reuse the fixed-input traversal above with every original local held opaque. Only a retained
input route composes with its earlier declaration's exact BindingId/path. An unrouteable
constructor, application or marked source definition keeps its own named occurrence. -/
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

/-- Capture the complete source-position map before associating any runtime values.
Formal-only bindings retain entries; no expression or payload comparison selects their IDs. -/
opaque OpenContext.inputProjections (context : OpenContext) :
    MetaM (Std.HashMap BindingId InputProjection) :=
  declaredInputProjections context.bindings

private def declaredSourceProjection (bindings : Array LocalBinding) (source : Expr) :
    MetaM (Option InputProjection) := do
  let some projection ← inputProjection (sourceProjectionInputs bindings) source []
    | return none
  return some (← retainContextProjection (← declaredInputProjections bindings) projection)

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
  /-- Native ancestor record types, closed over their complete stable source context. -/
  private recordAncestors : Array ClosedTerm

/-- A descendant's type under the original field prefix and its native inner field binders.
Only original prefix positions have actual values in this view. The original FieldLayout
stays unchanged; this is the checked dependency interface of its selected descendant. -/
structure FieldDependencyView where
  private mk ::
  path : Array Name
  typeFamily : ClosedTerm
  precedingDependencies : Array Nat

/-- Mechanical layout of a fixed source value, with its complete dependent source type. -/
structure SourceLayout where
  private mk ::
  address : Array Name
  source : ClosedTerm
  kind : ComputationalKind
  fields : Array FieldLayout
  contextDependencies : Array Nat
  /-- Original source binding/projection, retained before any runtime association. -/
  inputProjection : Option InputProjection
  /-- The stored-record path above this layout; callable application starts a new path. -/
  private recordAncestors : Array ClosedTerm

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
Only propositions are erased; no subsingleton test enters field selection.
Reuse the path-local repeated-type guard from RoutedResultPlan.compileSlots at fef6be1;
closed types preserve its meaning across fresh source contexts and later projections. -/
private def sourceLayout (source : ClosedTerm) (address : Array Name)
    (recordAncestors : Array ClosedTerm) : MetaM SourceLayout :=
  source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    let inputProjection ← declaredSourceProjection bindings expression
    let originalType ← inferType expression
    let dependencies ← contextDependencies bindings originalType
    let type ← whnf originalType
    let kind ← computationalKind type
    if kind != .record then
      return ⟨address, source, kind, #[], dependencies, inputProjection, recordAncestors⟩
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
        let dependencies ← localDependencies (locals.extract 0 index) fieldType
        let typeFamily ← mkLambdaFVars (locals.extract 0 index) fieldType
          (usedOnly := false) (usedLetOnly := false)
        let value ← mkProjection expression info.fieldNames[index]!
        let fieldKind ← computationalKind (← inferType value)
        let fieldWireIndex := if fieldKind == .proof then none else some wireIndex
        fields := fields.push ⟨address.push projection, projection, index, fieldWireIndex,
          dependencies, ← context.close value, ← context.close typeFamily, fieldKind, recordPath⟩
        if fieldKind != .proof then wireIndex := wireIndex + 1
      return ⟨address, source, kind, fields, dependencies, inputProjection, recordAncestors⟩

/-- Derive a fixed-value layout from the checked source, before any provider response. -/
opaque SourceLayout.ofTerm (source : ClosedTerm) : MetaM SourceLayout :=
  sourceLayout source #[] #[]

/-- Inspect the same projected source value, retaining its full projection address. -/
opaque FieldLayout.toLayout (field : FieldLayout) : MetaM SourceLayout :=
  sourceLayout field.source field.address field.recordAncestors

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
  sourceLayout (← context.close (← layout.source.inContext context)) layout.address layout.recordAncestors

/-- Prepare ordinary source application in the current complete context.
Arguments are checked source terms; computational candidates enter through the runtime. -/
opaque SourceLayout.applyIn (function : SourceLayout) (context : OpenContext)
    (arguments : Array ClosedTerm) : MetaM SourceLayout := do
  sourceLayout (← context.close (← context.apply function.source arguments)) function.address #[]

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
  resultTermFamily : ClosedTerm
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
    let termFamily ← mkLambdaFVars locals (mkAppN callable locals)
      (usedOnly := false) (usedLetOnly := false)
    let contextDependencies ← localDependencies (context.bindings.map (·.expression)) resultType
    return (result, ⟨prepared, dependencies, ← context.close family, ← context.close termFamily, result,
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

/-- Read a fixed input route from the original symbolic result before actual substitution.
The actual result validates the requested field path; exact fresh binder identities supply
argument ordinals and selected original context BindingIds. No equality comparison between
inputs selects a computational occurrence. Context IDs name only retained parameter slots. -/
opaque ApplicationLayout.inputProjectionAt (layout : ApplicationLayout) (path : Array Name)
    (contextInputs : Array BindingId := #[]) :
    MetaM (Option InputProjection) :=
  layout.result.source.withOpen fun bindings expression => do
    let context ← ContextTelescope.capture bindings
    discard <| projectSource expression path
    let family ← layout.resultTermFamily.inContext context
    lambdaBoundedTelescope family layout.arguments.size fun locals result => do
      unless locals.size == layout.arguments.size do
        throwError "the application result term family lost a formal argument"
      let mut inputs ← contextProjectionInputs bindings contextInputs
      for argument in locals, index in [:locals.size] do
        inputs := inputs.insert argument.fvarId! (.argument index)
      inputProjection inputs result path.toList

/-- Read an exact context reference or native projection from a closed source term.
The selected context binders remain identities even when they have definitions. This reuses
the same source-only traversal as application routing without inventing an application slot. -/
opaque ClosedTerm.inputProjectionAt (source : ClosedTerm) (path : Array Name)
    (contextInputs : Array BindingId := #[]) : MetaM (Option InputProjection) :=
  source.withOpen fun bindings expression => do
    discard <| projectSource expression path
    inputProjection (← contextProjectionInputs bindings contextInputs) expression path.toList

/-- A native source expression suspended over its exact opened formal prefix.
The original context remains a separate stable BindingId plane. No actual values or actual
argument expressions enter this family, and unused or proof formals remain abstracted. -/
structure InputExpression where
  private mk ::
  private family : ClosedTerm
  argumentCount : Nat

opaque InputExpression.context (expression : InputExpression) : ContextTelescope :=
  expression.family.context

/-- A pending argument is an exact existing formal slot or an unforced native source expression.
An unrouteable expression still occupies its formal position; it is never a fabricated value
or a missing runtime input. -/
inductive InputArgumentRef where
  | slot (index : Nat)
  | expression (source : InputExpression)

/-- Ordered native selection followed by a complete application prefix, including proof slots.
A zero-argument step retains a projection after the last pending application. -/
structure InputApplicationStep where
  selection : Array Name
  arguments : Array InputArgumentRef

/-- A final fixed result or an exact input callable before its entire remaining operation suffix.
Leading selections are included in the route. Remaining steps include the final result path,
so their consumer resumes with an empty additional path. -/
inductive InputProjectionResult where
  | projection (route : InputProjection)
  | callable (route : InputProjection) (remainingSteps : Array InputApplicationStep)

private def captureInputExpression (context : OpenContext) (locals : Array Expr)
    (source : Expr) : MetaM InputExpression := do
  let family ← mkLambdaFVars locals source (usedOnly := false) (usedLetOnly := false)
  return ⟨← context.close family, locals.size⟩

/-- Reopen only a source expression captured in this compiler traversal. Substitution here is
between original symbolic source terms, never between runtime operands or their native roles. -/
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

/-- Expose one binder of a partially applied registered projection, without unfolding its
declaration into a recursor. Its own native telescope supplies the symbolic argument domain.
Reuse: ProjectionFunctionInfo and the exact projection constant already present in the source. -/
private def inputProjectionLambda? (source : Expr) : MetaM (Option Expr) := do
  let .const name _ := source.getAppFn | return none
  let some info := (← getEnv).getProjectionFnInfo? name | return none
  unless source.getAppArgs.size < info.numParams + 1 do return none
  let .forallE name domain _ binderInfo ← inferType source | return none
  withLocalDecl name binderInfo domain fun argument => do
    return some (← mkLambdaFVars #[argument] (mkApp source argument)
      (usedOnly := false) (usedLetOnly := false))

mutual

/-- Compose native source lambdas with a complete pending argument sequence. Supplied formal
slots open fresh locals; a native body argument remains source syntax until it is selected.
Every returned continuation records its argument sources explicitly, rather than assuming that
they form a suffix of the current runtime table. -/
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

/-- Inspect the native application/projection spine while keeping every body argument closed
and unforced. A source boundary or recursor cannot turn into an input callable. Native lambdas
may consume source syntax; retained callables return a continuation for their exact binding. -/
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
  -- A native callable can progress only by consuming an existing pending application.
  -- Inspect it before splitting its own application spine: decomposing an unsaturated
  -- projection would manufacture arguments that merely reconstruct the same callable.
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

/-- Inspect a selected suspended expression in its original context and exact formal prefix.
Later application slots are appended only to the temporary argument plane. An unknown source
expression returns none when selected; callers never force it merely to fill an argument slot.
Reuse: ClosedTerm, the same safe native head reducer, and exact FVarId input routing. -/
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

/-- Trace retained partial applications and native source-body applications in the first
application's original symbolic scope. Supplied argument counts include every proof position.
Argument targets and continuation slots index the temporary flattened argument table; captured
source expressions seal exactly its opened prefix. Stable context BindingIds remain separate.
Neither prepared layouts nor dependency ordinals change. No actual input expression or value
is substituted to discover a route, and native mathematical computation remains a boundary.
Reuse: inputProjectionAt, ClosedTerm and InputExpression.inputProjectionThrough. -/
opaque ApplicationLayout.inputProjectionThrough (first : ApplicationLayout)
    (steps : Array (Array Name × Nat)) (path : Array Name)
    (contextInputs : Array BindingId := #[]) :
    MetaM (Option InputProjectionResult) := do
  if steps.isEmpty then
    first.result.source.withOpen fun _ expression =>
      discard <| projectSource expression path
  let expression : InputExpression := ⟨first.resultTermFamily, first.arguments.size⟩
  expression.inputProjectionThrough steps path contextInputs

/-- Source-context and argument planes remain distinct from returned record-prefix fields. -/
structure ResultDependencies where
  context : Array Nat
  arguments : Array Nat

/-- Reflect constructor field domains under abstract preceding fields, as sourceLayout does.
If source arguments determine the record shape, retain that shape's formal dependencies.
Reference: Lean.forallBoundedTelescope, ConstructorVal and the native FieldLayout algorithm. -/
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
        pure (actualType, {
          context := shape.context ++ (← localDependencies context reduced)
          arguments := shape.arguments ++ (← localDependencies arguments reduced) })
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
    fun _ type shape => do
      let contextDependencies ← localDependencies context type
      let argumentDependencies ← localDependencies arguments type
      return {
        context := (Array.range context.size).filter fun index =>
          shape.context.contains index || contextDependencies.contains index
        arguments := (Array.range arguments.size).filter fun index =>
          shape.arguments.contains index || argumentDependencies.contains index }

/-- Derive a selected descendant's original-prefix dependencies from the declared field family.
Inner constructor prefixes remain abstract, so an unrelated sibling cannot become an owner.
Reuse: the same native projection/telescope traversal as ApplicationLayout.dependenciesAt. -/
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
          let dependencies ← localDependencies locals type
          let required := (Array.range preceding.size).filter fun index =>
            shape.arguments.contains index || dependencies.contains index
          let family ← mkLambdaFVars locals type (usedOnly := false) (usedLetOnly := false)
          return ⟨path, ← context.close family, required⟩

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
