/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.StructuredProjection
public import CasCatalogue.ComputationalData
public import CasCatalogue.FunctorActionData
public import CasCatalogue.DeclaredApplication

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.RoutedResultPlan

/-- A data input is an occurrence in the selected declaration, not an expression
lookup. Parameter positions count explicit non-propositional arguments only. -/
inductive Input where
  | receiver
  | parameter (actionIndex dataIndex : Nat)
  deriving BEq, Inhabited

structure Parameter where
  actionIndex : Nat
  declarationIndex : Nat
  dataIndex : Nat
  formal : Expr
  expectedType : Expr

/-- A parameter's public role is retained by its original typed producer. The
schema never guesses a category from a carrier or a computational descriptor. -/
inductive ParameterRole where
  | object (context : CategoryContext)
  | map (context : CategoryContext) (source target : Expr)
  | value

structure ParameterInterface where
  actionIndex : Nat
  dataIndex : Nat
  formal : Expr
  expectedType : Expr
  role : ParameterRole

/-- A categorical role is supplied by an independently selected complete
interface. Scalar record fields do not acquire a category from their carrier. -/
inductive Role where
  | object (context : CategoryContext)
  | map (context : CategoryContext) (sourceSlot targetSlot : Nat)
  | value

/-- Retained fields keep their original root and public projection plan. A
returned leaf is the only place where a prospective consumer may allocate a
future. Complete records are assembled through the existing public codec. -/
inductive Node where
  | retained (input : Input) (projection : ComputationalData.RecordProjectionPlan)
  | returned
  | record (codec : ComputationalData.RecordFieldCodec) (fields : Array Nat)

structure Slot where
  formal : Expr
  expectedType : Expr
  replyPath : ComputationalData.RecordFieldPath
  role : Role
  node : Node

/-- The full public role is inherited from one exact input position. The role
path is fixed before closing symbolic roots; it never selects a category by a
closed carrier or a computational packet. Scalars retain their declared type. -/
inductive ProjectionParameterRole where
  | object (input : Input) (path : ComputationalData.RecordFieldPath)
  | map (input : Input) (path : ComputationalData.RecordFieldPath)
  | value

/-- Only an exact public input projection or an independently fixed portable
literal can supply a newly selected projection action's computational parameter. -/
inductive ProjectionParameterSource where
  | retained (input : Input) (projection : ComputationalData.RecordProjectionPlan)
  | literal (data : Json)

structure ProjectionParameter where
  declarationIndex : Nat
  dataIndex : Nat
  formal : Expr
  expectedType : Expr
  role : ProjectionParameterRole
  source : ProjectionParameterSource

/-- A registered field action, including every explicit computational parameter
origin, selected while the original declaration roots are still distinct. -/
structure ProjectionActionPlan where
  edge : EdgeRef
  declarationApplication : Expr
  application : Expr
  parent : Expr
  field : Expr
  step : ComputationalData.RecordFieldStep
  sourceContext : CategoryContext
  targetContext : CategoryContext
  parameters : Array ProjectionParameter

/-- An unused presentation does not require a computational comparison action.
Missing data origins and formal ambiguity are retained as different outcomes;
neither may select a different action when a field is later observed. -/
inductive ProjectionActionFailure where
  | missing (message : String)
  | ambiguous (message : String)

structure ProjectionActionSelection where
  parentSlot : Nat
  fieldSlot : Nat
  replyPath : ComputationalData.RecordFieldPath
  action : Except ProjectionActionFailure ProjectionActionPlan

def ProjectionActionFailure.raise {α : Type} (failure : ProjectionActionFailure) :
    TermElabM α := do
  match failure with
  | .missing message => throwStratum .noImplementation m!"{message}"
  | .ambiguous message => throwSemanticAmbiguity m!"{message}"

/-- Children precede their record and both endpoints precede a map. Distinct
positions stay distinct even when their closed formal values happen to agree. -/
structure Plan where
  method : MethodId
  application : Expr
  prefixActions : Array (EdgeRef × Expr)
  receiver : Expr
  argument : Expr
  formal : Expr
  sourceContext : CategoryContext
  resultContext : CategoryContext
  parameters : Array Parameter
  slots : Array Slot
  output : Nat
  projectionActions : Array ProjectionActionSelection := #[]

private inductive InputKind where
  | object | callable | data

private structure SymbolicInput where
  formal : Expr
  input : Option Input
  kind : InputKind := .data

private inductive ProjectionAccess where
  | exposed | internal | missing
  deriving BEq

private partial def scalarRecordSchema : ComputationalData.PointSchema → Bool
  | .literal _ shape | .constrainedData shape => scalarRecordSchema shape
  | .recordFields .. => true
  | _ => false

/-- Mathematical implementation fields are not automatically public data
positions. Ordinary object and callable packets are atomic; only their published
record codecs expose children. A generic scalar record uses its selected schema. -/
private def publicPathInterface (root : SymbolicInput)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM (Except ProjectionAccess (Expr × InputKind)) := do
  let mut current := root.formal
  let mut kind := root.kind
  for step in path do
    if kind matches .callable then return .error .internal
    let codec ← ComputationalData.recordFieldCodec current
    unless codec == step.codec do
      throwError "a retained routed projection changed its selected public codec"
    match codec with
    | .arrow =>
        unless step.count == 3 && step.index < 3 do return .error .missing
        kind := if step.index == 2 then .callable else .object
    | .arrowRefinement | .core =>
        unless step.count == 1 && step.index == 0 do return .error .missing
        kind := .object
    | .ordered =>
        if kind matches .object then return .error .internal
        let some schema ← ComputationalData.pointSchema (← inferType current)
          | return .error .missing
        unless scalarRecordSchema schema do return .error .internal
        kind := .data
    current ← withTransparency .all <| mkProjection current step.field
  return .ok (current, kind)

private def publicPathAccess (root : SymbolicInput)
    (path : ComputationalData.RecordFieldPath) : TermElabM ProjectionAccess := do
  match ← publicPathInterface root path with
  | .ok _ => return .exposed
  | .error access => return access

private partial def projectionAccess (root : SymbolicInput) :
    ComputationalData.RecordProjectionPlan → TermElabM ProjectionAccess
  | .input path => publicPathAccess root path
  | .record _ fields => do
      let mut missing := false
      for field in fields do
        match ← projectionAccess root field with
        | .internal => return .internal
        | .missing => missing := true
        | .exposed => pure ()
      return if missing then .missing else .exposed

private partial def projectionUsesInput : ComputationalData.RecordProjectionPlan → Bool
  | .input _ => true
  | .record _ fields => fields.any projectionUsesInput

/-- All roots are fresh telescope binders. A proof-only empty record does not
establish a source occurrence, and an implicit argument has no invented wire slot. -/
private def retainedNode? (inputs : Array SymbolicInput) (formal : Expr) :
    TermElabM (Option Node) := do
  let mut candidates : Array (Option Input × ComputationalData.RecordProjectionPlan) := #[]
  for input in inputs do
    if let some projection ← ComputationalData.recordProjectionPlan? input.formal formal then
      if projectionUsesInput projection then
        match ← projectionAccess input projection with
        | .exposed => candidates := candidates.push (input.input, projection)
        | .internal => pure ()
        | .missing =>
            throwStratum .noImplementation
              "a retained routed field requires its complete public input projection schema"
  match candidates with
  | #[] => return none
  | #[(some input, projection)] => return some (.retained input projection)
  | #[(none, _)] =>
      throwStratum .noImplementation
        "the routed result retains a declaration parameter with no transmitted data slot"
  | _ =>
      throwError "a symbolic routed result field has several distinct retained input roots"

private def appendSlot (slots : Array Slot) (slot : Slot) : Nat × Array Slot :=
  (slots.size, slots.push slot)

private def fieldSlot (slots : Array Slot) (index : Nat) : TermElabM Slot := do
  let some slot := slots[index]?
    | throwError "the routed result schema refers to an absent earlier field"
  return slot

private def slotContext (role : Role) : Option CategoryContext :=
  match role with
  | .object context | .map context .. => some context
  | .value => none

/-- A whole sort-valued object and an existing atomic scalar codec have no
independent represented fields. Composite scalar codecs are deliberately not
classified as atomic. Their fields need a complete selected schema. -/
private def atomicData (type : Expr) : TermElabM Bool := do
  if (← withTransparency .all <| whnf type).isSort then return true
  match ← ComputationalData.pointSchema type with
  | some (.plain _) => return true
  | _ => return false

/-- The Core codec exposes one object at the source category of its independently
selected constructor. The full bundle, including its dictionary, is recovered
through that accepted constructor while symbolic parameters remain in scope. -/
private def coreBaseContext (context : CategoryContext) : TermElabM CategoryContext := do
  let .construct id #[.category expression] := context.expression
    | throwStratum .noImplementation
        "the complete Core record requires its selected constructor category interface"
  let some constructor := (← registryState).constructor? id
    | throwError "the selected Core category constructor is absent"
  unless constructor.semantics == `CasCatalogue.Constructors.core do
    throwStratum .noImplementation
      "the complete Core record has no selected Core constructor interface"
  let declaration ← mkConstWithFreshMVarLevels constructor.semantics
  let (fields, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let application := mkAppN declaration fields
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq application context.bundle) do
    CategoryContext.exposeStructureParameters application
  unless ← withTransparency .all <| isDefEq application context.bundle do
    throwStratum .noImplementation
      "the routed record lacks its complete symbolic Core constructor interface"
  let explicit ← ((fields.zip infos).filterMap fun (field, info) =>
    if info.isExplicit then some field else none).mapM instantiateMVars
  let #[bundle] := explicit
    | throwStratum .noImplementation
        "the accepted Core constructor has no single complete source-category parameter"
  if bundle.hasMVar || bundle.hasLevelMVar then
    throwStratum .noImplementation
      "the routed Core record has unresolved symbolic category parameters"
  return { expression, bundle }

/-- Compile positions at a fresh output record, and provenance at the selected
action on fresh input binders. These are separate symbolic boundaries: equal
output fields cannot collapse their endpoint positions, and equal actual inputs
cannot select another retained supplier. -/
private partial def compileSlots (inputs : Array SymbolicInput)
    (shapeRoot selectedResult field : Expr) (role : Role)
    (slots : Array Slot) (seen : Array Expr := #[]) :
    TermElabM (Nat × Array Slot) := do
  let some replyPath ← ComputationalData.recordFieldPath? shapeRoot field
    | throwError "the routed result schema lost its declared output field path"
  let formal := field.replaceFVars #[shapeRoot] #[selectedResult]
  let expectedType ← instantiateMVars (← inferType formal)
  let make := fun node => ({ formal, expectedType, replyPath, role, node } : Slot)
  match role with
  | .object context => CategoryContext.checkObject context formal
  | .map context sourceSlot targetSlot =>
      let source ← fieldSlot slots sourceSlot
      let target ← fieldSlot slots targetSlot
      CategoryContext.checkMorphism context formal source.formal target.formal
  | .value => pure ()
  if let some node ← retainedNode? inputs formal then
    return appendSlot slots (make node)
  if role matches .map .. then
    return appendSlot slots (make .returned)
  if let .object context := role then
    if let some arrow ← StructuredProjection.arrow? field context then
      if arrow.subobject then
        let (child, slots) ← compileSlots inputs shapeRoot selectedResult arrow.arrow
          (.object arrow.arrowContext) slots seen
        return appendSlot slots (make (.record .arrowRefinement #[child]))
      let (source, slots) ← compileSlots inputs shapeRoot selectedResult arrow.source
        (.object arrow.base) slots seen
      let (target, slots) ← compileSlots inputs shapeRoot selectedResult arrow.target
        (.object arrow.base) slots seen
      let (hom, slots) ← compileSlots inputs shapeRoot selectedResult arrow.hom
        (.map arrow.base source target) slots seen
      return appendSlot slots (make (.record .arrow #[source, target, hom]))
    let codec ← ComputationalData.recordFieldCodec field
    if codec == .core then
      let base ← coreBaseContext context
      let some underlying ← ComputationalData.recordProjection ``CategoryTheory.Core.of field
        | throwError "the complete Core record omitted its declared object field"
      let (child, slots) ← compileSlots inputs shapeRoot selectedResult underlying
        (.object base) slots seen
      return appendSlot slots (make (.record .core #[child]))
    if codec == .arrow || codec == .arrowRefinement then
      throwStratum .noImplementation
        "the routed Arrow object requires its complete selected constructor category"
    -- The public object interface permits an opaque packet. Implementation
    -- fields of GroupCat, RingCat, and other bundled mathematical structures
    -- are not public output ports merely because Lean represents them by records.
    return appendSlot slots (make .returned)
  if ← atomicData expectedType then
    return appendSlot slots (make .returned)
  let shape ← withTransparency .all <| whnf (← inferType field)
  if seen.contains shape then
    throwStratum .noImplementation
      "the routed result requires a recursive public record schema"
  if let some name := shape.getAppFn.constName? then
    if let some info := getStructureInfo? (← getEnv) name then
      let codec ← ComputationalData.recordFieldCodec field
      if codec == .arrow || codec == .arrowRefinement then
        throwStratum .noImplementation
          "the nested routed record requires its complete declared categorical field role"
      let mut children := #[]
      let mut slots := slots
      for name in info.fieldNames do
        let projection ← withTransparency .all <| mkProjection field name
        unless ← isProp (← inferType projection) do
          let (child, next) ← compileSlots inputs shapeRoot selectedResult projection
            .value slots (seen.push shape)
          children := children.push child
          slots := next
      return appendSlot slots (make (.record codec children))
  throwStratum .noImplementation
    "the routed result requires a complete public schema for its non-atomic data fields"

private def instantiateContext (context : CategoryContext) (binders values : Array Expr) :
    CategoryContext :=
  { context with bundle := context.bundle.replaceFVars binders values }

private def instantiateRole (role : Role) (binders values : Array Expr) : Role :=
  match role with
  | .object context => .object (instantiateContext context binders values)
  | .map context source target => .map (instantiateContext context binders values) source target
  | .value => .value

private def instantiateSlot (slot : Slot) (binders values : Array Expr) : Slot :=
  { slot with
    formal := slot.formal.replaceFVars binders values
    expectedType := slot.expectedType.replaceFVars binders values
    role := instantiateRole slot.role binders values }

private def sameProjectionStep (left right : ComputationalData.RecordFieldStep) : Bool :=
  left.structureName == right.structureName && left.field == right.field &&
    left.index == right.index && left.count == right.count && left.codec == right.codec

private def sameProjectionPath
    (left right : ComputationalData.RecordFieldPath) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) => sameProjectionStep a b

private partial def projectionInputPaths : ComputationalData.RecordProjectionPlan →
    Array ComputationalData.RecordFieldPath
  | .input path => #[path]
  | .record _ fields => fields.flatMap projectionInputPaths

private def commonProjectionPath
    (paths : Array ComputationalData.RecordFieldPath) : ComputationalData.RecordFieldPath := Id.run do
  let some first := paths[0]? | return #[]
  let mut shared := first
  for path in paths.extract 1 paths.size do
    let mut count := 0
    for (a, b) in shared.zip path do
      if sameProjectionStep a b then count := count + 1 else break
    shared := shared.extract 0 count
  return shared

/-- A direct field inherits its selected public role. A record assembled from
fields may retain the complete category of their one common public record
ancestor only when its full type is unchanged. This is a positioned role source,
not a search for another equal-typed object or a category dictionary. -/
private def projectionParameterRole (root : SymbolicInput) (input : Input)
    (projection : ComputationalData.RecordProjectionPlan) (formal : Expr) :
    TermElabM (Except ProjectionActionFailure ProjectionParameterRole) := do
  let path := match projection with
    | .input path => path
    | .record .. => commonProjectionPath (projectionInputPaths projection)
  let selected ← publicPathInterface root path
  let .ok (ancestor, kind) := selected
    | return .error (.missing
        "the projection action parameter lacks its selected complete public input role")
  if projection matches .input _ then
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType formal) (← inferType ancestor) <&&> isDefEq formal ancestor) do
      throwError "the projection parameter changed its exact symbolic input field"
  if kind matches .data then return .ok .value
  if let .record codec _ := projection then
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType formal) (← inferType ancestor)) do
      return .error (.missing
        "the projection action's assembled parameter requires an independent complete categorical role")
    unless codec == (← ComputationalData.recordFieldCodec ancestor) do
      return .error (.missing
        "the projection action's assembled parameter changed its selected public categorical codec")
    if kind matches .callable then
      return .error (.missing
        "a complete callable parameter has no public record assembly interface")
  match kind with
  | .object => return .ok (.object input path)
  | .callable => return .ok (.map input path)
  | .data => return .ok .value

/-- Portable fallback is confined to the existing proof-free scalar codec and
its complete independently fixed type. A closed bundled object, callable,
category dictionary or opaque value is not a literal merely because it can be
reduced in Lean. -/
private def portableProjectionParameter? (formal expectedType : Expr) :
    TermElabM (Option Json) := do
  unless FunctorActionData.closedParameter formal &&
      FunctorActionData.closedParameter expectedType &&
      (← ComputationalData.plainType expectedType) do return none
  let .ok data ← Codec.encode formal | return none
  let .ok decoded ← Codec.decode expectedType data | return none
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType decoded) expectedType <&&> isDefEq decoded formal) do
    throwError "the portable projection parameter failed its existing codec round trip"
  return some data

private def projectionParameterOrigin (inputs : Array SymbolicInput)
    (formal expectedType : Expr) :
    TermElabM (Except ProjectionActionFailure
      (ProjectionParameterRole × ProjectionParameterSource)) := do
  let mut candidates : Array (SymbolicInput × ComputationalData.RecordProjectionPlan) := #[]
  for input in inputs do
    if let some projection ← ComputationalData.recordProjectionPlan? input.formal formal then
      if projectionUsesInput projection then
        match ← projectionAccess input projection with
        | .exposed => candidates := candidates.push (input, projection)
        | .internal => pure ()
        | .missing => return .error (.missing
            "a projection action parameter requires its complete public input projection schema")
  match candidates with
  | #[(root, projection)] =>
    let some input := root.input
      | return .error (.missing
          "a projection action parameter has no transmitted original data slot")
    match ← projectionParameterRole root input projection formal with
    | .ok role => return .ok (role, .retained input projection)
    | .error failure => return .error failure
  | #[] =>
    if let some data ← portableProjectionParameter? formal expectedType then
      return .ok (.value, .literal data)
    return .error (.missing
      "a projection action parameter has no retained original input or independent portable literal")
  | _ => throwError
      "a symbolic projection parameter has several distinct retained input origins"

private def projectionParameters (inputs : Array SymbolicInput)
    (application : Expr) : TermElabM (Except ProjectionActionFailure (Array ProjectionParameter)) := do
  forallTelescopeReducing (← inferType application.getAppFn) fun binders _ => do
    let values := application.getAppArgs
    unless binders.size == values.size do
      throwError "the selected projection action omitted a complete declaration argument"
    let mut parameters : Array ProjectionParameter := #[]
    for declarationIndex in [:binders.size] do
      let some binder := binders[declarationIndex]?
        | throwError "the projection parameter schema lost a declaration binder"
      let some formal := values[declarationIndex]?
        | throwError "the projection parameter schema lost its selected argument"
      let expectedType := (← inferType binder).replaceFVars binders values
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType formal) expectedType) do
        throwError "the selected projection parameter changed its complete telescope type"
      let info ← binder.fvarId!.getBinderInfo
      if info.isExplicit && !(← isProp expectedType) then
        match ← projectionParameterOrigin inputs formal expectedType with
        | .ok (role, source) =>
          parameters := parameters.push {
            declarationIndex, dataIndex := parameters.size, formal, expectedType, role, source }
        | .error failure => return .error failure
    return .ok parameters

/-- The registered functor is selected on a fresh record, at the entire supplied
source and target bundles. Parameter data origins are compiled only after this
mathematical selection; missing computational data cannot break a formal tie. -/
private def selectProjectionActionAt (inputs : Array SymbolicInput)
    (parent : Expr) (source target : CategoryContext)
    (step : ComputationalData.RecordFieldStep) :
    TermElabM (Except ProjectionActionFailure ProjectionActionPlan) := do
  CategoryContext.checkObject source parent
  let field ← withTransparency .all <| mkProjection parent step.field
  CategoryContext.checkObject target field
  let state ← registryState
  let mut candidates : Array (Except ProjectionActionFailure ProjectionActionPlan) := #[]
  for row in state.functors do
    let candidate : Option (Except ProjectionActionFailure ProjectionActionPlan) ← withoutModifyingState do
      let application ← instantiateFresh row.declaration
      let action ← Semantic.asFunctor application
      let (domain, codomain) ← functorCategoryBundles action
      unless ← withoutModifyingState (withTransparency .all <| isDefEq domain source.bundle) do
        CategoryContext.exposeStructureParameters application
      unless ← withTransparency .all <|
          isDefEq domain source.bundle <&&> isDefEq codomain target.bundle do return none
      let accepted ← withLocalDeclD `recordReceiver (← inferType parent) fun symbolic => do
        let image ← Semantic.objOf action symbolic
        let some path ← ComputationalData.recordFieldPath? symbolic image | return false
        pure (sameProjectionPath path #[step])
      unless accepted do return none
      let application ← instantiateMVars application
      let action ← instantiateMVars action
      if application.hasMVar || application.hasLevelMVar || application.hasLooseBVars ||
          action.hasMVar || action.hasLevelMVar || action.hasLooseBVars then
        return some (.error (.missing
          "the registered projection action lacks its complete independently selected declaration parameters"))
      unless (← isTypeCorrect application) && (← isTypeCorrect action) do
        throwError "the selected projection action lost its complete typed application"
      match ← projectionParameters inputs application with
      | .ok parameters => return some (.ok {
          edge := .functor row.id, declarationApplication := application, application := action,
          parent, field, step, sourceContext := source, targetContext := target, parameters })
      | .error failure => return some (.error failure)
    if let some candidate := candidate then candidates := candidates.push candidate
  match candidates with
  | #[selected] => return selected
  | #[] => return .error (.missing
      "the selected public field has no registered projection action for its complete comparison")
  | _ => return .error (.ambiguous
      "several registered actions transport the same independently selected public field")

private def compileProjectionActions (inputs : Array SymbolicInput) (slots : Array Slot) :
    TermElabM (Array ProjectionActionSelection) := do
  let mut result := #[]
  for fieldSlot in [:slots.size] do
    let some selected := slots[fieldSlot]?
      | throwError "the projection action schema lost its selected field position"
    let .object target := selected.role | continue
    let some step := selected.replyPath.back? | continue
    let parentPath := selected.replyPath.extract 0 (selected.replyPath.size - 1)
    let parents := (slots.mapIdx fun index slot => (index, slot)).filter
      fun (_, slot) => sameProjectionPath slot.replyPath parentPath
    let #[(parentSlot, parent)] := parents
      | throwError "a public projection action lost its unique declared parent field"
    let .object source := parent.role
      | throwError "a categorical projection action lost its complete parent object role"
    let action ← selectProjectionActionAt inputs parent.formal source target step
    result := result.push { parentSlot, fieldSlot, replyPath := selected.replyPath, action }
  return result

private def instantiateProjectionAction (plan : ProjectionActionPlan)
    (binders values : Array Expr) : ProjectionActionPlan :=
  { plan with
    declarationApplication := plan.declarationApplication.replaceFVars binders values
    application := plan.application.replaceFVars binders values
    parent := plan.parent.replaceFVars binders values
    field := plan.field.replaceFVars binders values
    sourceContext := instantiateContext plan.sourceContext binders values
    targetContext := instantiateContext plan.targetContext binders values
    parameters := plan.parameters.map fun parameter => { parameter with
      formal := parameter.formal.replaceFVars binders values
      expectedType := parameter.expectedType.replaceFVars binders values } }

/-- Standalone public fields use the same fresh selector. Their only retained
computational root is the exact original parent. A nonportable category parameter
with no public data position remains unavailable rather than being recovered
from another equal closed object. -/
def selectProjectionAction (parent : Expr) (source target : CategoryContext)
    (step : ComputationalData.RecordFieldStep) :
    TermElabM (Except ProjectionActionFailure ProjectionActionPlan) := do
  withLocalDeclD `recordReceiver (← inferType parent) fun symbolic => do
    let selected ← selectProjectionActionAt
      #[{ formal := symbolic, input := some .receiver, kind := .object }]
      symbolic source target step
    return selected.map fun action => instantiateProjectionAction action #[symbolic] #[parent]

/-- Parent and field positions are authoritative even when their complete
closed expressions agree with other slots. Missing unused selections stay inert. -/
def Plan.projectionAction (plan : Plan) (parentSlot fieldSlot : Nat) :
    TermElabM ProjectionActionPlan := do
  let candidates := plan.projectionActions.filter fun selected =>
    selected.parentSlot == parentSlot && selected.fieldSlot == fieldSlot
  let #[selected] := candidates
    | throwError "the result comparison lost its uniquely selected projection action position"
  let some field := plan.slots[fieldSlot]?
    | throwError "the result comparison lost its original field slot"
  let some parent := plan.slots[parentSlot]?
    | throwError "the result comparison lost its original parent slot"
  unless sameProjectionPath selected.replyPath field.replyPath &&
      sameProjectionPath parent.replyPath
        (field.replyPath.extract 0 (field.replyPath.size - 1)) do
    throwError "the result comparison changed its original projection declaration path"
  match selected.action with
  | .ok action => return action
  | .error failure => failure.raise

private def completeApplication (declaration : Name) (action : Expr) : TermElabM Expr := do
  let some (selected, _) ← DeclaredApplication.complete? declaration action true
    | throwStratum .noImplementation
        "the routed schema requires the complete already selected declaration application"
  unless selected.getAppFn.constName? == some declaration do
    throwStratum .noImplementation
      "the routed schema requires the complete already selected declaration application"
  return selected

private inductive ActionShape where
  | named (edge : EdgeRef) (declarationApplication : Expr)
  | constructed (constructor : ConstructorId) (inner : ActionShape)

private def classifierAction (application : Expr) : TermElabM Expr := do
  let mut classifier := application
  let type ← whnf (← inferType classifier)
  if type.isAppOf ``LeanCategories.PropertyClassifier then
    classifier ← mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[classifier]
  else if type.isAppOf ``LeanCategories.StructureClassifier then
    classifier ← mkAppM ``LeanCategories.StructureClassifier.toClassifier #[classifier]
  Semantic.asFunctor (← mkAppM ``LeanCategories.Classifier.forget #[classifier])

private partial def ActionShape.declaration : ActionShape → Expr
  | .named _ application => application
  | .constructed _ inner => inner.declaration

/-- Only the already selected public constructor actions surround the named
declaration. No matching at a receiver chooses a replacement action. -/
private partial def ActionShape.action (shape : ActionShape) (declaration : Expr) :
    TermElabM Expr := do
  match shape with
  | .named (.functor _) _ => Semantic.asFunctor declaration
  | .named (.classifierForget _) _ => classifierAction declaration
  | .named _ _ => throwError "a routed declaration has no named action role"
  | .constructed constructor inner =>
      let some action := ((← registryState).constructor? constructor).bind (·.functorialAction)
        | throwError "the selected constructor has no registered action"
      Semantic.applyConstructorFunctor action (← inner.action declaration)

private partial def actionShape (state : RegistryState) (edge : EdgeRef) (actual : Expr) :
    TermElabM ActionShape := do
  let shape ← match edge with
    | .functor id => do
        let some entry := state.functor? id
          | throwError "the routed schema names an absent selected functor"
        pure (ActionShape.named edge (← completeApplication entry.declaration actual))
    | .classifierForget id => do
        let some entry := state.classifier? id
          | throwError "the routed schema names an absent selected classifier"
        let some (application, _) ← DeclaredApplication.completeProjected? entry.declaration
            (← Semantic.asFunctor actual) classifierAction
            (FunctorActionData.directActionDeclaration? state actual)
          | throwStratum .noImplementation
              "the routed schema requires the classifier's complete selected declaration"
        unless application.getAppFn.constName? == some entry.declaration do
          throwError "the routed schema changed its selected classifier declaration"
        pure (ActionShape.named edge application)
    | .constructMap constructor inner => do
        let some action := (state.constructor? constructor).bind (·.functorialAction)
          | throwError "the routed schema names a constructor without its registered action"
        let application ← completeApplication action actual
        let infos ← forallTelescopeReducing (← inferType application.getAppFn) fun fields _ =>
          fields.mapM (·.fvarId!.getBinderInfo)
        unless infos.size == application.getAppNumArgs do
          throwError "the constructed route action omitted a complete declaration argument"
        let explicit := (application.getAppArgs.zip infos).filterMap fun (argument, info) =>
          if info.isExplicit then some argument else none
        let #[innerAction] := explicit
          | throwStratum .noImplementation
              "the routed constructor action requires its declared symbolic parameter schema"
        pure (ActionShape.constructed constructor (← actionShape state inner innerAction))
  let rebuilt ← shape.action shape.declaration
  let expected ← Semantic.asFunctor actual
  unless ← withTransparency .all <|
      isDefEq (← inferType rebuilt) (← inferType expected) <&&> isDefEq rebuilt expected do
    throwError "the routed symbolic schema changed its complete selected action"
  return shape

private structure SymbolicActions where
  binders : Array Expr := #[]
  values : Array Expr := #[]
  parameters : Array Parameter := #[]
  inputs : Array SymbolicInput := #[]
  actions : Array Expr := #[]

private def parameterKind (parameter : Parameter)
    (interfaces : Array ParameterInterface) : TermElabM InputKind := do
  let candidates := interfaces.filter fun selected =>
    selected.actionIndex == parameter.actionIndex && selected.dataIndex == parameter.dataIndex
  match candidates with
  | #[] => return .data
  | #[selected] =>
      unless selected.formal == parameter.formal do
        throwError "a routed parameter interface changed its exact declaration occurrence"
      unless ← withTransparency .all <| isDefEq selected.expectedType parameter.expectedType do
        throwError "a routed parameter interface changed its complete declared type"
      match selected.role with
      | .object context =>
          CategoryContext.checkObject context parameter.formal
          return .object
      | .map context source target =>
          CategoryContext.checkMorphism context parameter.formal source target
          return .callable
      | .value => return .data
  | _ => throwError "a routed parameter occurrence has several supplied public roles"

private def declarationSlots (actionIndex : Nat) (binders values : Array Expr)
    (interfaces : Array ParameterInterface := #[]) :
    TermElabM (Array Parameter × Array SymbolicInput) := do
  unless binders.size == values.size do
    throwError "the routed schema requires every selected declaration argument"
  let mut parameters : Array Parameter := #[]
  let mut inputs : Array SymbolicInput := #[]
  for declarationIndex in [:binders.size] do
    let binder := binders[declarationIndex]!
    let value := values[declarationIndex]!
    let expectedType := (← inferType binder).replaceFVars binders values
    unless ← withTransparency .all <| isDefEq (← inferType value) expectedType do
      throwError "a routed declaration parameter changed its full telescope type"
    let info ← binder.fvarId!.getBinderInfo
    if info.isExplicit && !(← isProp (← inferType binder)) then
      let dataIndex := parameters.size
      let parameter : Parameter := {
        actionIndex, declarationIndex, dataIndex, formal := value, expectedType }
      let kind ← parameterKind parameter interfaces
      parameters := parameters.push parameter
      inputs := inputs.push {
        formal := binder, input := some (.parameter actionIndex dataIndex), kind }
    else
      inputs := inputs.push { formal := binder, input := none }
  return (parameters, inputs)

/-- Each action has independent ordered parameter occurrences. Compatibility of
the resulting symbolic categories is checked separately; equal closed values do
not merge roots that happened to agree in the original invocation. -/
private partial def withSymbolicActions (shapes : Array ActionShape) (index : Nat)
    (captured : SymbolicActions) (interfaces : Array ParameterInterface)
    (consume : SymbolicActions → TermElabM Plan) :
    TermElabM Plan := do
  let some shape := shapes[index]? | return ← consume captured
  let application := shape.declaration
  forallTelescopeReducing (← inferType application.getAppFn) fun binders _ => do
    let values := application.getAppArgs
    let (parameters, inputs) ← declarationSlots index binders values interfaces
    let action ← shape.action (mkAppN application.getAppFn binders)
    withSymbolicActions shapes (index + 1) {
      binders := captured.binders ++ binders
      values := captured.values ++ values
      parameters := captured.parameters ++ parameters
      inputs := captured.inputs ++ inputs
      actions := captured.actions.push action } interfaces consume

private def coreConstructor : TermElabM (ConstructorId × Name) := do
  let #[constructor] := (← registryState).constructors.filter
      (·.semantics == `CasCatalogue.Constructors.core)
    | throwError "the accepted core constructor is absent or ambiguous"
  return (constructor.id, constructor.semantics)

private def methodSourceContext (method : MethodEntry) (context : CategoryContext) :
    TermElabM CategoryContext := do
  match method.shape with
  | .isoInvariant => CategoryContext.construct context (← coreConstructor).1
  | _ => return context

/-- Recover an underlying bundle only through the already accepted complete
Core constructor. Neither the carrier alone nor a computational packet supplies
its category dictionary. This is the inverse of `methodArgument`'s typed wrapper. -/
private def underlyingMethodContext (method : MethodEntry) (source : CategoryContext) :
    TermElabM CategoryContext := do
  match method.shape with
  | .isoInvariant =>
      let constructor ← coreConstructor
      coreBaseContext {
        expression := .construct constructor.1 #[.category source.expression]
        bundle := source.bundle }
  | _ => return source

private def checkBoundary (actual expected : Expr) (symbolic : Bool) : TermElabM Unit := do
  unless ← withoutModifyingState (withTransparency .all <| isDefEq actual expected) do
    if symbolic then
      throwStratum .noImplementation
        "the routed result requires a retained relation between its dependent symbolic category parameters"
    else
      throwError "the routed result schema changed a complete selected category boundary"

private def resultOf (method : MethodEntry) (prefixActions : Array EdgeRef)
    (actions : Array Expr) (receiver : Expr)
    (sourceContext : CategoryContext) (symbolic : Bool) : TermElabM (Expr × Expr) := do
  unless actions.size == prefixActions.size + 1 do
    throwError "the routed result schema omitted a selected action"
  let state ← registryState
  let mut value := receiver
  let mut context := sourceContext
  for (edge, action) in prefixActions.zip (actions.extract 0 prefixActions.size) do
    let (source, target) ← functorCategoryBundles action
    checkBoundary context.bundle source symbolic
    value ← Semantic.objOf action value
    let some expression := state.selectedEdgeTarget? edge
      | throwError "the routed schema lost a selected target category expression"
    context := { expression, bundle := target }
  let methodAction := actions.back!
  let (source, _) ← functorCategoryBundles methodAction
  checkBoundary (← methodSourceContext method context).bundle source symbolic
  let argument ← methodArgument method value
  return (argument, ← Semantic.objOf methodAction argument)

private def selectedShapes (method : MethodEntry) (F : Expr)
    (prefixActions : Array (EdgeRef × Expr)) : TermElabM (Expr × Array ActionShape × Array Expr) := do
  let state ← registryState
  let some entry := state.functor? method.functor
    | throwError "the routed result schema names an absent selected functor"
  let application ← completeApplication entry.declaration F
  let mut shapes := #[]
  let mut actions := #[]
  for (edge, action) in prefixActions do
    shapes := shapes.push (← actionShape state edge action)
    actions := actions.push (← Semantic.asFunctor action)
  shapes := shapes.push (← actionShape state (.functor method.functor) application)
  actions := actions.push (← Semantic.asFunctor application)
  return (application, shapes, actions)

-- Read only declaration slots; no receiver or result schema is needed here.
private def slotsForShapes (shapes : Array ActionShape) : TermElabM (Array Parameter) := do
  let mut result := #[]
  for index in [:shapes.size] do
    let some shape := shapes[index]?
      | throwError "the routed parameter schema lost a selected action"
    let application := shape.declaration
    let (parameters, _) ← forallTelescopeReducing (← inferType application.getAppFn)
      fun binders _ => declarationSlots index binders application.getAppArgs
    result := result ++ parameters
  return result

/-- Capture ordered parameter occurrences before choosing a computational
boundary. Action indices address the selected route steps followed by the final
method. Constructed actions use their exact retained inner declaration, as the
existing edge descriptor does. This does not compile a result schema or demand
an input computation, so an unsupported unselected boundary stays inert. -/
def parameterSlots (method : MethodEntry) (F : Expr)
    (prefixActions : Array (EdgeRef × Expr) := #[]) : TermElabM (Array Parameter) := do
  let (_, shapes, _) ← selectedShapes method F prefixActions
  slotsForShapes shapes

/-- Select one immutable schema from the full registered functor application.
The entire declaration telescope is freshened positionally, including dependent
instances and proof arguments. Only explicit nonproof arguments supply public
data roots. Closing the plan substitutes those same slots, never equal expressions.

An unsupported composite result reports its missing public interface here. It is
never replaced by a whole future that would discard known receiver/parameter
fields. No computational data, dispatch, cache or backend participates. -/
def select (method : MethodEntry) (F receiver : Expr)
    (sourceContext resultContext : CategoryContext)
    (prefixActions : Array (EdgeRef × Expr) := #[])
    (parameterInterfaces : Array ParameterInterface := #[]) : TermElabM Plan := do
  let (application, shapes, actions) ← selectedShapes method F prefixActions
  let parameters ← slotsForShapes shapes
  for selected in parameterInterfaces do
    let some parameter := parameters.find? fun parameter =>
        parameter.actionIndex == selected.actionIndex && parameter.dataIndex == selected.dataIndex
      | throwError "a routed parameter interface addresses an absent declared data slot"
    discard <| parameterKind parameter parameterInterfaces
  let methodAction := actions.back!
  let (_, targetBundle) ← functorCategoryBundles methodAction
  CategoryContext.checkObject sourceContext receiver
  unless ← withTransparency .all <| isDefEq resultContext.bundle targetBundle do
    throwError "the routed result schema changed the complete result category"
  let (argument, result) ← resultOf method (prefixActions.map (·.1)) actions receiver sourceContext false
  CategoryContext.checkObject resultContext result
  withSymbolicActions shapes 0 {} parameterInterfaces fun captured => do
    let some first := captured.actions[0]?
      | throwError "the symbolic routed schema omitted its method action"
    let (initial, _) ← functorCategoryBundles first
    let symbolicSource ← if prefixActions.isEmpty then
        underlyingMethodContext method { sourceContext with bundle := initial }
      else pure { sourceContext with bundle := initial }
    let type ← CategoryContext.carrier symbolicSource
    unless ← withTransparency .all <| isDefEq
        (type.replaceFVars captured.binders captured.values)
        (← inferType receiver) do
      throwError "the symbolic routed receiver lost its original complete type"
    checkBoundary (symbolicSource.bundle.replaceFVars captured.binders captured.values)
      sourceContext.bundle false
    withLocalDeclD `receiver type fun symbolicReceiver => do
      let (_, symbolicResult) ← resultOf method (prefixActions.map (·.1))
        captured.actions symbolicReceiver symbolicSource true
      let (_, symbolicTarget) ← functorCategoryBundles captured.actions.back!
      let symbolicContext := { resultContext with bundle := symbolicTarget }
      CategoryContext.checkObject symbolicContext symbolicResult
      let inputs := captured.inputs.push {
        formal := symbolicReceiver, input := some .receiver, kind := .object }
      withLocalDeclD `resultShape (← inferType symbolicResult) fun shape => do
        let (output, slots) ← compileSlots inputs shape symbolicResult shape
          (.object symbolicContext) #[]
        let projectionActions ← compileProjectionActions inputs slots
        let binders := captured.binders.push symbolicReceiver
        let values := captured.values.push receiver
        let closed := symbolicResult.replaceFVars binders values
        unless ← withTransparency .all <|
            isDefEq (← inferType closed) (← inferType result) <&&> isDefEq closed result do
          throwError "closing the routed schema changed its selected result"
        let slots := slots.map fun slot => instantiateSlot slot binders values
        let projectionActions := projectionActions.map fun selected => { selected with
          action := selected.action.map fun action => instantiateProjectionAction action binders values }
        for selected in projectionActions do
          if let .ok action := selected.action then
            unless (← isTypeCorrect action.declarationApplication) &&
                (← isTypeCorrect action.application) do
              throwError "a closed projection action lost its complete declaration type"
            for parameter in action.parameters do
              unless ← withTransparency .all <|
                  isDefEq (← inferType parameter.formal) parameter.expectedType do
                throwError "a closed projection parameter lost its complete declared type"
        for slot in slots do
          unless ← isTypeCorrect slot.formal do
            throwError "a closed routed result field lost its complete declared type"
          unless ← withTransparency .all <| isDefEq (← inferType slot.formal) slot.expectedType do
            throwError "a closed routed result field changed its original expected type"
          if let some context := slotContext slot.role then
            unless ← isTypeCorrect context.bundle do
              throwError "a routed result field lost its complete category dictionary"
        return {
          method := method.id, application, prefixActions, receiver, argument, formal := result,
          sourceContext, resultContext, parameters := captured.parameters, slots, output,
          projectionActions }

def Plan.inputFormal (plan : Plan) (input : Input) : TermElabM Expr := do
  match input with
  | .receiver => return plan.receiver
  | .parameter actionIndex index =>
      let some parameter := plan.parameters.find?
          (fun parameter => parameter.actionIndex == actionIndex && parameter.dataIndex == index)
        | throwError "the routed result schema references an absent data parameter"
      return parameter.formal

/-- Expose a map's already assembled endpoint packets. An opaque callable is
permitted; the complete endpoints do not come from that callable's reply bytes. -/
def Slot.endpoints? (slot : Slot) (earlier : Array DataOwnership.Data) :
    Option (DataOwnership.Data × DataOwnership.Data) := do
  let .map _ source target := slot.role | none
  return (← earlier[source]?, ← earlier[target]?)

/-- Assemble the selected prospective shape or another typed instance. Callers
provide exact original input occurrences and allocate only genuinely returned
leaves. No result reference, owner or session is manufactured by this helper. -/
def Plan.foldData (plan : Plan)
    (inputs : Input → TermElabM DataOwnership.Data)
    (returned : Nat → Slot → Array DataOwnership.Data → TermElabM DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Array DataOwnership.Data) := do
  let mut values : Array DataOwnership.Data := #[]
  for index in [:plan.slots.size] do
    let some slot := plan.slots[index]?
      | throwError "the routed result schema lost a declared field"
    let data ← match slot.node with
      | .retained input projection =>
          let formal ← plan.inputFormal input
          let some data ← projection.apply? formal (← inputs input) objects
            | throwStratum .noImplementation
                "the retained routed input does not expose its complete public projection"
          pure data
      | .returned => returned index slot values
      | .record codec children => do
          let mut fields := #[]
          for child in children do
            let some field := values[child]?
              | throwError "a routed record refers to a field before it is available"
            fields := fields.push field
          let some data := codec.assemble? fields
            | throwError "the routed record schema disagrees with its public codec"
          pure data
    values := values.push data
  return values

def Plan.outputData? (plan : Plan) (values : Array DataOwnership.Data) :
    Option DataOwnership.Data :=
  values[plan.output]?

/-- Read every declared slot from one complete actual reply. Projection retains
the exact supplying sessions at each position. This only supplies data to the
consumer: it must still compare retained nodes to their original scoped inputs,
validate ordinary returned fields, and validate each map at `Slot.endpoints?`.
An opaque whole record cannot hide required field or endpoint slots. -/
def Plan.projectData? (plan : Plan) (reply : DataOwnership.Data)
    (objects : ComputationalData.InterfaceObjects := #[]) :
    TermElabM (Option (Array DataOwnership.Data)) := do
  let mut values := #[]
  for slot in plan.slots do
    let projection := ComputationalData.RecordProjectionPlan.input slot.replyPath
    let some field ← projection.apply? plan.formal reply objects | return none
    values := values.push field
  return some values

end CasCatalogue.RoutedResultPlan
