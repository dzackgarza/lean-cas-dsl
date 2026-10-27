/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.StructuredProjection
public import CasCatalogue.ComputationalData
public import CasCatalogue.FunctorActionData
public import CasCatalogue.DeclaredApplication
public import Mathlib.CategoryTheory.NatIso

-- This module publishes executable schema APIs and their result types. Their
-- implementation bodies stay private so the public wrappers can use the
-- private symbolic compiler without exporting its internal input types.
public section
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

/-- An output may expose a field produced by an earlier action of the same
fused invocation. Its actual packet belongs to this reply occurrence, not to
another evaluation of an equal formal expression. -/
structure ReturnedOrigin where
  actionIndex : Nat
  replyPath : ComputationalData.RecordFieldPath

structure Slot where
  formal : Expr
  expectedType : Expr
  replyPath : ComputationalData.RecordFieldPath
  role : Role
  node : Node
  producedBy : Option ReturnedOrigin := none

/-- The full public role is inherited from one exact input position. The role
path is fixed before closing symbolic roots; it never selects a category by a
closed carrier or a computational packet. Scalars retain their declared type. -/
inductive ProjectionParameterRole where
  | object (input : Input) (path : ComputationalData.RecordFieldPath)
  | map (input : Input) (path : ComputationalData.RecordFieldPath)
  /-- A composed parameter keeps the complete role of its selected local
  producer, even when its data assembles several original input occurrences. -/
  | objectAt (context : CategoryContext)
  | mapAt (context : CategoryContext) (source target : Expr)
  | value

/-- Only an exact public input projection or an independently fixed portable
literal can supply a newly selected projection action's computational parameter. -/
inductive ProjectionParameterSource where
  | retained (input : Input) (projection : ComputationalData.RecordProjectionPlan)
  /-- The exact output occurrence of a preceding selected route action. The
  index never addresses the enclosing method's own result. -/
  | intermediate (actionIndex : Nat) (projection : ComputationalData.RecordProjectionPlan)
  | record (codec : ComputationalData.RecordFieldCodec)
      (fields : Array ProjectionParameterSource)
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
structure ProjectionActionStep where
  edge : EdgeRef
  declarationApplication : Expr
  application : Expr
  sourceContext : CategoryContext
  targetContext : CategoryContext
  parameters : Array ProjectionParameter

/-- One exact accepted comparison occurrence in the alignment to the public
projection. `data` retains the declared direction; only `inverse` orients this
occurrence in the selected path. Parameters and action segments are positional
inside this occurrence, even when another occurrence has equal expressions. -/
structure ProjectionAlignmentStep where
  witness : RouteComparison
  inverse : Bool
  data : Semantic.RouteComparisonData
  parameters : Array ProjectionParameter
  before : Array ProjectionActionStep
  left : Array ProjectionActionStep
  right : Array ProjectionActionStep
  after : Array ProjectionActionStep

structure ProjectionActionPlan where
  route : Route
  steps : Array ProjectionActionStep
  /-- The complete public field functor, including its morphism action. -/
  projection : Expr
  /-- The exact composite of the selected registered step applications. -/
  application : Expr
  parent : Expr
  field : Expr
  step : ComputationalData.RecordFieldStep
  sourceContext : CategoryContext
  targetContext : CategoryContext
  comparisons : Array (RouteComparison × Expr) := #[]
  alignment : Array ProjectionAlignmentStep := #[]
  /-- The ordered accepted comparison from `application` to `projection`.
  Absence means the two complete functors are definitionally equal. -/
  alignmentComparison : Option Expr := none

/-- Parameter positions remain local to their exact route step. Flattening is
only an inventory operation, never a way to recover or merge an occurrence. -/
def ProjectionActionPlan.parameters (plan : ProjectionActionPlan) : Array ProjectionParameter :=
  plan.steps.flatMap (·.parameters) ++ plan.alignment.flatMap fun selected =>
    selected.parameters ++
      (selected.before ++ selected.left ++ selected.right ++ selected.after).flatMap (·.parameters)

/-- Specialize the existing naturality theorem at the exact retained map.
Execution of the three component maps produces the theorem's left side; its
right side is the canonical public projection's map, with complete dictionaries
and endpoints retained. This introduces no new categorical law. -/
def ProjectionActionPlan.mapAlignment (plan : ProjectionActionPlan)
    (morphism : Expr) : TermElabM (Option Expr) := do
  let some comparison := plan.alignmentComparison
    | do
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq plan.application plan.projection) do
        throwError "the projection plan omitted its nonidentity accepted alignment"
      return none
  Semantic.checkRouteComparison comparison plan.application plan.projection
  let proof ← mkAppM ``CategoryTheory.NatIso.naturality_1 #[comparison, morphism]
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Eq 3 && (← withTransparency .all <|
      isDefEq type.getAppArgs[2]! (← Semantic.mapOf plan.projection morphism)) do
    throwError "the projection naturality theorem changed the complete canonical map"
  unless ← isTypeCorrect proof do
    throwError "the projection naturality theorem lost its exact typed occurrence"
  return some (← instantiateMVars proof)

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

/-- A missing intermediate field is computed only by its already selected
registered action. Map image endpoints address distinct slots in this stage's
fresh public result schema, even when their later formal values coincide. -/
inductive FieldActionKind where
  | object
  | map (sourceSlot targetSlot : Nat)

structure FieldCompletionAction where
  steps : Array ProjectionActionStep
  input : Expr
  inputType : Expr
  inputRole : ProjectionParameterRole
  source : ProjectionParameterSource
  kind : FieldActionKind

/-- Completion reads original positions, assembles the existing public codec,
or invokes a complete registered field action. An opaque missing field has no
invented derivation merely because the enclosing stage has a known result type. -/
inductive FieldCompletion where
  | retained (source : ProjectionParameterSource)
  | record (codec : ComputationalData.RecordFieldCodec) (fields : Array Nat)
  | action (selected : FieldCompletionAction)
  | unavailable (failure : ProjectionActionFailure)

/-- One independently compiled action boundary, kept after composing its
provenance into the final result. Final-reply positions exposed by `producedPaths`
take priority over this completion table; the table supplies only missing data. -/
structure IntermediateStage where
  actionIndex : Nat
  edge : EdgeRef
  application : Expr
  receiver : Expr
  formal : Expr
  sourceContext : CategoryContext
  resultContext : CategoryContext
  parameters : Array Parameter
  slots : Array Slot
  output : Nat
  completions : Array FieldCompletion
  projectionActions : Array ProjectionActionSelection := #[]

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
  stages : Array IntermediateStage := #[]

private inductive InputKind where
  | object | callable | data

/-- Formal dependency and computational provenance are separate. Every action
is compiled in its own well-typed declaration telescope; only this positional
tree is substituted at the next receiver. A returned leaf keeps its preceding
action and public output path, rather than becoming an equal-valued input. -/
private inductive Origin where
  | retained (input : Input) (projection : ComputationalData.RecordProjectionPlan)
  | returned (actionIndex : Nat) (path : ComputationalData.RecordFieldPath)
  | record (codec : ComputationalData.RecordFieldCodec) (fields : Array Origin)

private structure SymbolicInput where
  formal : Expr
  input : Option Input
  kind : InputKind := .data
  origin : Option Origin := none

/-- Restrict a public projection without inspecting values or suppliers. The
path was selected at the complete typed output schema of the preceding action. -/
private partial def projectionAtPath (projection : ComputationalData.RecordProjectionPlan)
    (path : ComputationalData.RecordFieldPath) :
    TermElabM ComputationalData.RecordProjectionPlan := do
  if path.isEmpty then return projection
  match projection with
  | .input initial => return .input (initial ++ path)
  | .record codec fields =>
      let some step := path[0]?
        | throwError "a composed projection lost its first public field"
      unless step.codec == codec && step.count == fields.size do
        throwError "a composed projection changed its selected public record schema"
      let some child := fields[step.index]?
        | throwError "a composed projection addresses an absent public field"
      projectionAtPath child (path.extract 1 path.size)

private partial def originAtPath (origin : Origin)
    (path : ComputationalData.RecordFieldPath) : TermElabM Origin := do
  if path.isEmpty then return origin
  match origin with
  | .retained input projection =>
      return .retained input (← projectionAtPath projection path)
  | .returned actionIndex initial =>
      return .returned actionIndex (initial ++ path)
  | .record codec fields =>
      let some step := path[0]?
        | throwError "a composed origin lost its first public field"
      unless step.codec == codec && step.count == fields.size do
        throwError "a composed origin changed its selected public record schema"
      let some child := fields[step.index]?
        | throwError "a composed origin addresses an absent public field"
      originAtPath child (path.extract 1 path.size)

private partial def projectOrigin (origin : Origin) :
    ComputationalData.RecordProjectionPlan → TermElabM Origin
  | .input path => originAtPath origin path
  | .record codec fields => do
      return .record codec (← fields.mapM (projectOrigin origin))

/-- A complete record can retain one original root only when every child uses
that same ordinal root. Equal expressions and equal packets play no role. -/
private partial def retainedOrigin? : Origin →
    Option (Input × ComputationalData.RecordProjectionPlan)
  | .retained input projection => some (input, projection)
  | .returned .. => none
  | .record codec fields => do
      let first ← fields[0]?
      let (input, _) ← retainedOrigin? first
      let projections ← fields.mapM fun child => do
        let (selected, projection) ← retainedOrigin? child
        if selected == input then some projection else none
      return (input, .record codec projections)

private partial def Origin.parameterSource : Origin → ProjectionParameterSource
  | .retained input projection => .retained input projection
  | .returned actionIndex path => .intermediate actionIndex (.input path)
  | .record codec fields => .record codec (fields.map Origin.parameterSource)

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
private def selectedOrigin? (inputs : Array SymbolicInput) (formal : Expr) :
    TermElabM (Option Origin) := do
  let mut candidates : Array (SymbolicInput × ComputationalData.RecordProjectionPlan) := #[]
  for input in inputs do
    if let some projection ← ComputationalData.recordProjectionPlan? input.formal formal then
      if projectionUsesInput projection then
        match ← projectionAccess input projection with
        | .exposed => candidates := candidates.push (input, projection)
        | .internal => pure ()
        | .missing =>
            throwStratum .noImplementation
              "a retained routed field requires its complete public input projection schema"
  match candidates with
  | #[] => return none
  | #[(root, projection)] =>
      if let some origin := root.origin then
        return some (← projectOrigin origin projection)
      let some input := root.input
        | throwStratum .noImplementation
            "the routed result retains a declaration parameter with no transmitted data slot"
      return some (.retained input projection)
  | _ =>
      throwError "a symbolic routed result field has several distinct retained input roots"

private def retainedNode? (inputs : Array SymbolicInput) (formal : Expr) :
    TermElabM (Option Node) := do
  let some origin ← selectedOrigin? inputs formal | return none
  let some (input, projection) := retainedOrigin? origin | return none
  return some (.retained input projection)

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

/-- A later action may retain a preceding returned field. Keep that exact
producer, which is published on the eventual slot as `producedBy`, even though
the fused reply still represents the field as returned data. -/
private def compileOrigins (inputs : Array SymbolicInput) (actionIndex : Nat)
    (slots : Array Slot) : TermElabM (Array Origin) := do
  let mut origins := #[]
  for slot in slots do
    let origin ← match ← selectedOrigin? inputs slot.formal with
      | some origin => pure origin
      | none => match slot.node with
        | .retained input projection => pure (.retained input projection)
        | .returned => pure (.returned actionIndex slot.replyPath)
        | .record codec fields => do
            let children ← fields.mapM fun index => do
              let some child := origins[index]?
                | throwError "a composed result origin precedes its declared field dependencies"
              return child
            pure (.record codec children)
    origins := origins.push origin
  return origins

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

private def instantiateProjectionParameterRole (role : ProjectionParameterRole)
    (binders values : Array Expr) : ProjectionParameterRole :=
  match role with
  | .objectAt context => .objectAt (instantiateContext context binders values)
  | .mapAt context source target =>
      .mapAt (instantiateContext context binders values)
        (source.replaceFVars binders values) (target.replaceFVars binders values)
  | _ => role

private def sameProjectionStep (left right : ComputationalData.RecordFieldStep) : Bool :=
  left.structureName == right.structureName && left.field == right.field &&
    left.index == right.index && left.count == right.count && left.codec == right.codec

private def sameProjectionPath
    (left right : ComputationalData.RecordFieldPath) : Bool :=
  left.size == right.size && (left.zip right).all fun (a, b) => sameProjectionStep a b

/-- Locate an earlier produced field in this invocation's own final reply.
The result contains every distinct public reply position, never a preferred
equal-valued supplier. A parent slot and its child can describe the same reply
path; only that identical positional description is coalesced. -/
def Plan.producedPaths (plan : Plan) (actionIndex : Nat)
    (path : ComputationalData.RecordFieldPath) :
    Array ComputationalData.RecordFieldPath := Id.run do
  let mut result := #[]
  for slot in plan.slots do
    let some origin := slot.producedBy | continue
    unless origin.actionIndex == actionIndex && origin.replyPath.size <= path.size &&
        sameProjectionPath origin.replyPath (path.extract 0 origin.replyPath.size) do continue
    let selected := slot.replyPath ++ path.extract origin.replyPath.size path.size
    unless result.any (sameProjectionPath · selected) do result := result.push selected
  return result

/-- Select an action boundary by its original ordinal. The final method follows
all prefix actions; a stage's slots and completion table share one fixed public
schema. This lookup never reconstructs a stage from an equal formal result. -/
def Plan.stage (plan : Plan) (actionIndex : Nat) : TermElabM IntermediateStage := do
  unless plan.stages.size == plan.prefixActions.size + 1 do
    throwError "the routed result plan omitted an original action boundary"
  let some selected := plan.stages[actionIndex]?
    | throwError "the routed result plan addresses an absent action boundary"
  unless selected.actionIndex == actionIndex &&
      selected.completions.size == selected.slots.size && selected.output < selected.slots.size do
    throwError "the routed action boundary changed its positional completion schema"
  return selected

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

private partial def projectionParameterOrigin (inputs : Array SymbolicInput)
    (formal expectedType : Expr) (seen : Array Expr := #[]) :
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
    -- A released scalar record can assemble fields from several original
    -- positions. Each child is selected separately; sharing a declaration
    -- value or a supplier never collapses those positions. Categorical records
    -- still need the complete role of an independently selected producer.
    unless seen.contains expectedType do
      if let some schema ← ComputationalData.pointSchema expectedType then
        if scalarRecordSchema schema then
          let type ← withTransparency .all <| whnf expectedType
          if let some name := type.getAppFn.constName? then
            if let some info := getStructureInfo? (← getEnv) name then
              let mut fields := #[]
              for name in info.fieldNames do
                let child ← withTransparency .all <| mkProjection formal name
                let childType ← inferType child
                unless ← isProp childType do
                  match ← projectionParameterOrigin inputs child childType (seen.push expectedType) with
                  | .ok (.value, source) => fields := fields.push source
                  | .ok _ => return .error (.missing
                      "the assembled scalar parameter requires an independent role for a categorical child")
                  | .error failure => return .error failure
              return .ok (.value, .record (← ComputationalData.recordFieldCodec formal) fields)
    return .error (.missing
      "a projection action parameter has no retained original input or independent portable literal")
  | _ => throwError
      "a symbolic projection parameter has several distinct retained input origins"

/-- A symbolic trial already retains the literal declaration application
created by the accepted edge. Check that whole occurrence without closing its
local telescope. The existing closed matcher remains responsible for aliases. -/
private def completeSelectedApplication (declaration : Name) (value : Expr)
    (project : Expr → TermElabM Expr) (literal? : Option Expr) : TermElabM Expr := do
  if let some literal := literal? then
    if literal.getAppFn.constName? == some declaration &&
        !literal.hasMVar && !literal.hasLevelMVar && !literal.hasLooseBVars then
      let arity ← forallTelescopeReducing (← inferType literal.getAppFn)
        fun binders _ => pure binders.size
      unless literal.getAppNumArgs == arity && (← isTypeCorrect literal) do
        throwError "the symbolic action lost its complete literal declaration application"
      let compared ← project literal
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq (← inferType compared) (← inferType value) <&&> isDefEq compared value) do
        throwError "the literal declaration changed its complete selected action"
      return literal
  let some (selected, _) ← DeclaredApplication.completeProjected? declaration value project literal?
    | throwStratum .noImplementation
        "the routed schema requires the complete already selected declaration application"
  unless selected.getAppFn.constName? == some declaration do
    throwError "the routed schema changed its selected declaration"
  return selected

private def completeApplication (declaration : Name) (action : Expr) : TermElabM Expr := do
  let mut literal := action.consumeMData
  while literal.isAppOfArity ``id 2 || literal.isAppOf ``CategoryTheory.Cat.Hom.toFunctor do
    literal := literal.appArg!.consumeMData
  completeSelectedApplication declaration action (fun selected => do Semantic.asFunctor selected)
    (some literal)

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

private partial def ActionShape.edge : ActionShape → EdgeRef
  | .named edge _ => edge
  | .constructed constructor inner => .constructMap constructor inner.edge

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
        let application ← completeSelectedApplication entry.declaration
          (← Semantic.asFunctor actual) classifierAction
          (FunctorActionData.directActionDeclaration? state actual)
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

/-- Recheck the complete named, classifier or constructor-induced application
without asking a runtime consumer to reconstruct its declaration schema. -/
def ProjectionActionStep.checkedDeclaration (selected : ProjectionActionStep) : TermElabM Expr := do
  let shape ← actionShape (← registryState) selected.edge selected.application
  let declared := shape.declaration
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType declared) (← inferType selected.declarationApplication) <&&>
        isDefEq declared selected.declarationApplication) do
    throwError "the selected projection step changed its complete declaration application"
  let (source, target) ← functorCategoryBundles (← Semantic.asFunctor selected.application)
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq source selected.sourceContext.bundle <&&>
        isDefEq target selected.targetContext.bundle) do
    throwError "the selected projection step changed its complete category boundaries"
  return declared

/-- Validate the retained original cell and each position in its four action
segments. The original and constructor-mapped endpoints remain separate; this
check never reconstructs a declaration from a generated comparison proof. -/
def ProjectionAlignmentStep.checkedDeclaration (selected : ProjectionAlignmentStep) :
    TermElabM Expr := do
  let state ← registryState
  let some cell := state.cells.find? (·.id == selected.witness.cell)
    | throwError "the projection alignment lost its accepted cell declaration"
  unless cell.invertible do
    throwError "the projection alignment lost its accepted invertible interface"
  let declared ← completeSelectedApplication cell.declaration selected.data.declarationApplication
    (fun application => pure application) (some selected.data.declarationApplication)
  let (baseLeft, baseRight) ← Semantic.comparisonApplicationEndpoints
    selected.data.baseLeftApplications selected.data.baseRightApplications
  Semantic.checkRouteComparison declared baseLeft baseRight
  let checkSegment (refs : Array EdgeRef) (applications : Array Expr)
      (steps : Array ProjectionActionStep) : TermElabM Unit := do
    unless refs.size == applications.size && refs.size == steps.size do
      throwError "the projection alignment changed an original action segment's positions"
    for ((ref, application), step) in (refs.zip applications).zip steps do
      unless ref == step.edge do
        throwError "the projection alignment changed a selected action identity"
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq application step.application) do
        throwError "the projection alignment changed a complete retained action application"
      discard <| step.checkedDeclaration
  checkSegment selected.witness.before selected.data.beforeApplications selected.before
  checkSegment (RouteComparison.mapRefs selected.witness.constructors cell.left)
    selected.data.leftApplications selected.left
  checkSegment (RouteComparison.mapRefs selected.witness.constructors cell.right)
    selected.data.rightApplications selected.right
  checkSegment selected.witness.after selected.data.afterApplications selected.after
  let (componentLeft, componentRight) ← Semantic.comparisonApplicationEndpoints
    selected.data.leftApplications selected.data.rightApplications
  Semantic.checkRouteComparison selected.data.componentComparison componentLeft componentRight
  let (left, right) ← Semantic.comparisonApplicationEndpoints
    (selected.data.beforeApplications ++ selected.data.leftApplications ++ selected.data.afterApplications)
    (selected.data.beforeApplications ++ selected.data.rightApplications ++ selected.data.afterApplications)
  Semantic.checkRouteComparison selected.data.comparison left right
  return declared

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

/-- The public record interface fixes the whole mathematical projection. An
object-function match alone cannot justify transporting presentation maps. -/
private def declaredProjection (parent : Expr) (source target : CategoryContext)
    (step : ComputationalData.RecordFieldStep) : TermElabM Expr := do
  let projection ← match step.codec with
    | .core => do
        unless step.index == 0 && step.count == 1 do
          throwError "the Core projection changed its selected public field"
        let base ← coreBaseContext source
        mkAppOptM ``CategoryTheory.Core.inclusion
          #[some (← CategoryContext.carrier base), some (← CategoryContext.dictionary base)]
    | .arrowRefinement =>
        unless step.index == 0 && step.count == 1 do
          throwError "the refined Arrow projection changed its selected public field"
        StructuredProjection.projectionFunctorOfBundle source.bundle "inclusion"
    | .arrow => do
        unless step.count == 3 do
          throwError "the Arrow projection changed its complete public field schema"
        let label ← match step.index with
          | 0 => pure "source"
          | 1 => pure "target"
          | _ => throwError "the selected Arrow field is not an object projection"
        StructuredProjection.projectionFunctorOfBundle source.bundle label
    | .ordered => throwStratum .noImplementation
        "the scalar record codec does not declare a categorical projection functor"
  let (domain, codomain) ← functorCategoryBundles projection
  unless ← withTransparency .all <|
      isDefEq domain source.bundle <&&> isDefEq codomain target.bundle do
    throwError "the public projection changed its complete declared categories"
  let accepted ← withLocalDeclD `projectionReceiver (← inferType parent) fun symbolic => do
    let image ← Semantic.objOf projection symbolic
    let some path ← ComputationalData.recordFieldPath? symbolic image | return false
    pure (sameProjectionPath path #[step])
  unless accepted do
    throwError "the declared projection functor changed its selected public field"
  return ← instantiateMVars projection

private def appendProjectionRoute (routes : Array Route) (route : Route) : Array Route :=
  if routes.any (fun previous => previous.refs == route.refs &&
      previous.source.syntacticEq route.source && previous.target.syntacticEq route.target) then
    routes
  else routes.push route

/-- Read an exact accepted action reference, without promoting a nonstructural
action into the inheritance graph. Comparison endpoints may themselves name
composites of such actions. -/
private partial def projectionEdge (state : RegistryState) (ref : EdgeRef) :
    TermElabM StructuralEdge := do
  match ref with
  | .functor id =>
      let some row := state.functor? id
        | throwError "a projection comparison names an absent registered functor"
      return { source := row.source, target := row.target, expression := row.expression, ref }
  | .classifierForget id =>
      let some row := state.classifier? id
        | throwError "a projection comparison names an absent registered classifier"
      return { source := .classifierTotal id, target := row.host,
        expression := .classifierForget id row.host, ref }
  | .constructMap constructor inner =>
      let some row := state.constructor? constructor
        | throwError "a projection comparison names an absent registered constructor"
      unless row.functorialAction.isSome do
        throwError "a projection comparison constructor has no accepted functor action"
      let edge ← projectionEdge state inner
      return { source := .construct constructor #[.category edge.source],
        target := .construct constructor #[.category edge.target],
        expression := .constructMap constructor edge.expression, ref }

private def projectionRoute (state : RegistryState) (source target : CategoryExpr)
    (refs : Array EdgeRef) : TermElabM Route := do
  let steps ← refs.mapM (projectionEdge state)
  let mut previous := source
  for edge in steps do
    unless previous.syntacticEq edge.source do
      throwError "an accepted projection comparison changed its declared route boundary"
    previous := edge.target
  unless previous.syntacticEq target do
    throwError "an accepted projection comparison changed its declared route target"
  return { source, target, steps }

/-- Reuse complete structural closure, including classifier and constructor
actions. A named registered action can also be the terminal operation of such a
route; this preserves direct nonstructural declarations without treating them
as inheritance edges. Constructor contexts act on those same complete routes. -/
private partial def projectionRoutes (state : RegistryState) (source target : CategoryExpr) :
    TermElabM (Array Route) := do
  let mut routes ← match state.completeRoutes source target with
    | .ok routes => pure routes
    | .error error => throwResolutionError state error
  for row in state.functors do
    let terminal : StructuralEdge := {
      source := row.source, target := row.target, expression := row.expression,
      ref := .functor row.id }
    routes := appendProjectionRoute routes {
      source := row.source, target := row.target, steps := #[terminal] }
    unless row.target.syntacticEq target do continue
    let prefixes ← match state.completeRoutes source row.source with
      | .ok routes => pure routes
      | .error error => throwResolutionError state error
    for initial in prefixes do
      routes := appendProjectionRoute routes {
        source, target, steps := initial.steps.push terminal }
  -- A comparison explicitly declares both complete route expressions. Retain
  -- those expressions, including nonstructural action segments, and their
  -- complete structural whiskering contexts. No structural flag is changed.
  for cell in state.cells do
    unless cell.invertible && cell.left != cell.right do continue
    let left ← projectionRoute state cell.source cell.target cell.left
    let right ← projectionRoute state cell.source cell.target cell.right
    routes := appendProjectionRoute (appendProjectionRoute routes left) right
    let prefixes ← match state.completeRoutes source cell.source with
      | .ok routes => pure routes
      | .error error => throwResolutionError state error
    let suffixes ← match state.completeRoutes cell.target target with
      | .ok routes => pure routes
      | .error error => throwResolutionError state error
    for initial in prefixes do
      for final in suffixes do
        for segment in #[left, right] do
          routes := appendProjectionRoute routes {
            source, target, steps := initial.steps ++ segment.steps ++ final.steps }
  match source, target with
  | .construct constructor #[.category innerSource],
      .construct targetConstructor #[.category innerTarget] =>
      if constructor == targetConstructor &&
          ((state.constructor? constructor).bind (·.functorialAction)).isSome then
        for inner in (← projectionRoutes state innerSource innerTarget) do
          let steps := inner.steps.map fun edge => ({
            source := .construct constructor #[.category edge.source]
            target := .construct constructor #[.category edge.target]
            expression := .constructMap constructor edge.expression
            ref := .constructMap constructor edge.ref } : StructuralEdge)
          routes := appendProjectionRoute routes {
            source := .construct constructor #[.category inner.source]
            target := .construct constructor #[.category inner.target], steps }
  | _, _ => pure ()
  return routes

private def comparisonRouteRefs (state : RegistryState) (witness : RouteComparison) :
    TermElabM (Array EdgeRef × Array EdgeRef) := do
  let some cell := state.cells.find? (·.id == witness.cell)
    | throwError "the selected projection comparison names an absent accepted cell"
  return (witness.before ++ RouteComparison.mapRefs witness.constructors cell.left ++ witness.after,
    witness.before ++ RouteComparison.mapRefs witness.constructors cell.right ++ witness.after)

private structure ProjectionCandidate where
  route : Route
  application : Expr
  applications : Array Expr
  canonical : Bool

private instance : Inhabited ProjectionCandidate :=
  ⟨{ route := { source := .atom default, target := .atom default, steps := #[] },
    application := default, applications := #[], canonical := false }⟩

private structure ProjectionComparison where
  witness : RouteComparison
  data : Semantic.RouteComparisonData
  left : Nat
  right : Nat

/-- Missing mathematical inputs stay unavailable; a failed internal type check
is not reclassified as a missing computational registration. Proof and instance
closure uses the existing complete-declaration machinery. -/
private def closeProjectionValue (value : Expr) : TermElabM (Option Expr) := do
  try
    let closed ← DirectConstruction.close {
      value, arguments := (← getMVars value).map mkMVar, explicit := #[] }
    return some closed.value
  catch error =>
    let value ← instantiateMVars value
    if Exception.interpretationKind error == .invalid &&
        (value.hasMVar || value.hasLevelMVar) then return none
    throw error

private def closeProjectionValues (values : Array Expr) : TermElabM (Option (Array Expr)) := do
  let mut closed := #[]
  for value in values do
    let some value ← closeProjectionValue value | return none
    closed := closed.push value
  return some closed

private def closeProjectionComparison (data : Semantic.RouteComparisonData) :
    TermElabM (Option Semantic.RouteComparisonData) := do
  let some comparison ← closeProjectionValue data.comparison | return none
  let some componentComparison ← closeProjectionValue data.componentComparison | return none
  let some declarationApplication ← closeProjectionValue data.declarationApplication | return none
  let some baseLeftApplications ← closeProjectionValues data.baseLeftApplications | return none
  let some baseRightApplications ← closeProjectionValues data.baseRightApplications | return none
  let some leftApplications ← closeProjectionValues data.leftApplications | return none
  let some rightApplications ← closeProjectionValues data.rightApplications | return none
  let some beforeApplications ← closeProjectionValues data.beforeApplications | return none
  let some afterApplications ← closeProjectionValues data.afterApplications | return none
  return some {
    comparison, componentComparison, declarationApplication, baseLeftApplications, baseRightApplications,
    leftApplications, rightApplications, beforeApplications, afterApplications }

private def compileProjectionSteps (inputs : Array SymbolicInput) (state : RegistryState)
    (refs : Array EdgeRef) (applications : Array Expr) :
    TermElabM (Except ProjectionActionFailure (Array ProjectionActionStep)) := do
  unless refs.size == applications.size do
    throwError "the projection route lost an original step application"
  let mut steps := #[]
  for (ref, application) in refs.zip applications do
    let edge ← projectionEdge state ref
    let shape ← actionShape state ref application
    let declared := shape.declaration
    let parameters ← match ← projectionParameters inputs declared with
      | .ok parameters => pure parameters
      | .error failure => return .error failure
    let (domain, codomain) ← functorCategoryBundles (← Semantic.asFunctor application)
    steps := steps.push {
      edge := ref, declarationApplication := declared, application,
      sourceContext := { expression := edge.source, bundle := domain },
      targetContext := { expression := edge.target, bundle := codomain }, parameters }
  return .ok steps

/-- All simple paths in the finite accepted comparison class. A second path is
an unresolved comparison choice; neither length nor declaration order selects
it. The visited positions ensure termination without an arbitrary route cap. -/
private partial def projectionAlignmentPaths (comparisons : Array ProjectionComparison)
    (targets : Array Nat) (current : Nat) (visited : Array Nat) :
    Array (Array (Nat × Bool)) := Id.run do
  if targets.contains current then return #[#[]]
  let mut result := #[]
  for index in [:comparisons.size] do
    let some comparison := comparisons[index]? | continue
    let next := if comparison.left == current then some (comparison.right, false)
      else if comparison.right == current then some (comparison.left, true) else none
    let some (next, inverse) := next | continue
    if visited.contains next then continue
    for remaining in projectionAlignmentPaths comparisons targets next (visited.push next) do
      result := result.push (#[(index, inverse)] ++ remaining)
  return result

private def compileProjectionAlignment (inputs : Array SymbolicInput) (state : RegistryState)
    (selected : ProjectionComparison) (inverse : Bool) :
    TermElabM (Except ProjectionActionFailure ProjectionAlignmentStep) := do
  let some cell := state.cells.find? (·.id == selected.witness.cell)
    | throwError "the selected projection alignment lost its original cell declaration"
  unless selected.data.declarationApplication.getAppFn.constName? == some cell.declaration do
    throwError "the projection alignment changed its original complete cell application"
  let parameters ← match ← projectionParameters inputs selected.data.declarationApplication with
    | .ok parameters => pure parameters
    | .error failure => return .error failure
  let before ← match ← compileProjectionSteps inputs state selected.witness.before
      selected.data.beforeApplications with
    | .ok steps => pure steps
    | .error failure => return .error failure
  let left ← match ← compileProjectionSteps inputs state
      (RouteComparison.mapRefs selected.witness.constructors cell.left)
      selected.data.leftApplications with
    | .ok steps => pure steps
    | .error failure => return .error failure
  let right ← match ← compileProjectionSteps inputs state
      (RouteComparison.mapRefs selected.witness.constructors cell.right)
      selected.data.rightApplications with
    | .ok steps => pure steps
    | .error failure => return .error failure
  let after ← match ← compileProjectionSteps inputs state selected.witness.after
      selected.data.afterApplications with
    | .ok steps => pure steps
    | .error failure => return .error failure
  return .ok {
    witness := selected.witness, inverse, data := selected.data,
    parameters, before, left, right, after }

/-- The independently declared whole projection anchors formal selection. A
non-definitional implementation enters only through accepted comparisons to
that anchor. Exact application constraints are solved before any computational
parameter origins are compiled; all chosen occurrences then leave this local
elaboration state fully closed. -/
private def selectProjectionActionAt (inputs : Array SymbolicInput)
    (parent : Expr) (source target : CategoryContext)
    (step : ComputationalData.RecordFieldStep) :
    TermElabM (Except ProjectionActionFailure ProjectionActionPlan) := withoutModifyingState do
  CategoryContext.checkObject source parent
  let field ← withTransparency .all <| mkProjection parent step.field
  CategoryContext.checkObject target field
  let projection ← declaredProjection parent source target step
  let state ← registryState
  let routes ← projectionRoutes state source.expression target.expression
  let mut candidates : Array ProjectionCandidate := #[]
  for route in routes do
    let saved ← Term.saveState
    let candidate : Option ProjectionCandidate ← do
      if route.refs.isEmpty then
        unless route.source.syntacticEq source.expression &&
            route.target.syntacticEq target.expression do return none
      let (action, applications) ← if route.refs.isEmpty then do
          let identity ← mkAppOptM ``CategoryTheory.Functor.id
            #[some (← CategoryContext.carrier source), some (← CategoryContext.dictionary source)]
          pure (identity, #[])
        else Semantic.routeFunctorWithApplications state route.refs
      let (domain, codomain) ← functorCategoryBundles action
      unless ← withoutModifyingState (withTransparency .all <| isDefEq domain source.bundle) do
        for application in applications do
          CategoryContext.exposeStructureParameters application
      unless ← withTransparency .all <|
          isDefEq domain source.bundle <&&> isDefEq codomain target.bundle do return none
      let canonical ← withoutModifyingState (withTransparency .all <| isDefEq action projection)
      if canonical then
        unless ← withTransparency .all <| isDefEq action projection do
          throwError "the complete projection anchor changed during its formal selection"
      return some { route, application := action, applications, canonical }
    match candidate with
    | some candidate => candidates := candidates.push candidate
    | none => saved.restore true
  let classes := state.classify candidates (fun _ => "public-field-projection") (·.route)
  let cls ← match classes.filter (fun cls => cls.members.any (·.canonical)) with
    | #[cls] => pure cls
    | #[] => return .error (.missing
        "the public field has no registered route or accepted comparison to its complete projection functor")
    | _ => return .error (.ambiguous
        "several unconnected registered routes implement the complete public projection")
  unless cls.ambiguities.isEmpty do
    return .error (.ambiguous "several accepted cells compare the same projection routes")
  let #[sourceCandidate] := cls.sources
    | return .error (.ambiguous
        "the accepted projection comparisons have no unique designated source route")
  let #[sourceIndex] := (Array.range cls.members.size).filter
      (fun index => cls.members[index]!.route.refs == sourceCandidate.route.refs)
    | throwError "the projection class lost its exact designated source position"
  -- All comparisons constrain the original candidate applications in this
  -- shared local state. A later comparison can determine an earlier dependent
  -- parameter; no independently fresh replacement application is substituted.
  let mut comparisons : Array ProjectionComparison := #[]
  for witness in cls.comparisonWitnesses do
    let (leftRefs, rightRefs) ← comparisonRouteRefs state witness
    let #[left] := (Array.range cls.members.size).filter
        (fun index => cls.members[index]!.route.refs == leftRefs)
      | throwError "the projection comparison lost its exact selected left route"
    let #[right] := (Array.range cls.members.size).filter
        (fun index => cls.members[index]!.route.refs == rightRefs)
      | throwError "the projection comparison lost its exact selected right route"
    let data ← Semantic.routeComparisonWithData state witness
    Semantic.checkRouteComparison data.comparison
      cls.members[left]!.application cls.members[right]!.application
    comparisons := comparisons.push { witness, data, left, right }
  let mut members : Array ProjectionCandidate := #[]
  for candidate in cls.members do
    let some application ← closeProjectionValue candidate.application
      | return .error (.missing
          "the projection route requires further independently selected mathematical parameters")
    let some applications ← closeProjectionValues candidate.applications
      | return .error (.missing
          "the projection route lacks its complete original declaration applications")
    members := members.push { candidate with application, applications }
  let mut closedComparisons : Array ProjectionComparison := #[]
  for selected in comparisons do
    let some data ← closeProjectionComparison selected.data
      | return .error (.missing
          "the accepted projection comparison requires further complete declaration parameters")
    Semantic.checkRouteComparison data.comparison
      members[selected.left]!.application members[selected.right]!.application
    closedComparisons := closedComparisons.push { selected with data }
  let selected := members[sourceIndex]!
  let steps ← match ← compileProjectionSteps inputs state selected.route.refs selected.applications with
    | .ok steps => pure steps
    | .error failure => return .error failure
  let mut alignment := #[]
  let mut alignmentComparison : Option Expr := none
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq selected.application projection) do
    let targets ← (Array.range members.size).filterM fun index =>
      withoutModifyingState (withTransparency .all <| isDefEq members[index]!.application projection)
    let paths := projectionAlignmentPaths closedComparisons targets sourceIndex #[sourceIndex]
    let path ← match paths with
      | #[path] => pure path
      | #[] => throwError "the accepted projection class lost its path to the canonical anchor"
      | _ => return .error (.ambiguous
          "several accepted comparison paths align the selected route with the public projection")
    for (index, inverse) in path do
      let some selectedComparison := closedComparisons[index]?
        | throwError "the projection alignment lost its exact accepted comparison position"
      let compiled ← match ← compileProjectionAlignment inputs state selectedComparison inverse with
        | .ok compiled => pure compiled
        | .error failure => return .error failure
      alignment := alignment.push compiled
      let comparison ← if inverse then
          mkAppM ``CategoryTheory.Iso.symm #[selectedComparison.data.comparison]
        else pure selectedComparison.data.comparison
      alignmentComparison ← match alignmentComparison with
        | none => pure (some comparison)
        | some previous => pure (some (← mkAppM ``CategoryTheory.Iso.trans #[previous, comparison]))
    let some comparison := alignmentComparison
      | throwError "the non-definitional projection alignment omitted its accepted comparison"
    Semantic.checkRouteComparison comparison selected.application projection
    let some comparison ← closeProjectionValue comparison
      | throwError "the projection alignment lost an already selected complete parameter"
    alignmentComparison := some comparison
  return .ok {
    route := selected.route, steps, projection, application := selected.application, parent, field, step,
    sourceContext := source, targetContext := target,
    comparisons := closedComparisons.map fun selected => (selected.witness, selected.data.comparison),
    alignment, alignmentComparison }

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

private def instantiateProjectionParameter (parameter : ProjectionParameter)
    (binders values : Array Expr) : ProjectionParameter :=
  { parameter with
    formal := parameter.formal.replaceFVars binders values
    expectedType := parameter.expectedType.replaceFVars binders values
    role := instantiateProjectionParameterRole parameter.role binders values }

private def instantiateProjectionStep (step : ProjectionActionStep)
    (binders values : Array Expr) : ProjectionActionStep :=
  { step with
    declarationApplication := step.declarationApplication.replaceFVars binders values
    application := step.application.replaceFVars binders values
    sourceContext := instantiateContext step.sourceContext binders values
    targetContext := instantiateContext step.targetContext binders values
    parameters := step.parameters.map fun parameter =>
      instantiateProjectionParameter parameter binders values }

private def instantiateProjectionComparison (data : Semantic.RouteComparisonData)
    (binders values : Array Expr) : Semantic.RouteComparisonData :=
  let close (value : Expr) := value.replaceFVars binders values
  { comparison := close data.comparison
    componentComparison := close data.componentComparison
    declarationApplication := close data.declarationApplication
    baseLeftApplications := data.baseLeftApplications.map close
    baseRightApplications := data.baseRightApplications.map close
    leftApplications := data.leftApplications.map close
    rightApplications := data.rightApplications.map close
    beforeApplications := data.beforeApplications.map close
    afterApplications := data.afterApplications.map close }

private def instantiateProjectionAlignment (selected : ProjectionAlignmentStep)
    (binders values : Array Expr) : ProjectionAlignmentStep :=
  { selected with
    data := instantiateProjectionComparison selected.data binders values
    parameters := selected.parameters.map fun parameter =>
      instantiateProjectionParameter parameter binders values
    before := selected.before.map fun step => instantiateProjectionStep step binders values
    left := selected.left.map fun step => instantiateProjectionStep step binders values
    right := selected.right.map fun step => instantiateProjectionStep step binders values
    after := selected.after.map fun step => instantiateProjectionStep step binders values }

private def instantiateProjectionAction (plan : ProjectionActionPlan)
    (binders values : Array Expr) : ProjectionActionPlan :=
  { plan with
    steps := plan.steps.map fun step => instantiateProjectionStep step binders values
    projection := plan.projection.replaceFVars binders values
    application := plan.application.replaceFVars binders values
    parent := plan.parent.replaceFVars binders values
    field := plan.field.replaceFVars binders values
    sourceContext := instantiateContext plan.sourceContext binders values
    targetContext := instantiateContext plan.targetContext binders values
    comparisons := plan.comparisons.map fun (witness, comparison) =>
      (witness, comparison.replaceFVars binders values)
    alignment := plan.alignment.map fun selected =>
      instantiateProjectionAlignment selected binders values
    alignmentComparison := plan.alignmentComparison.map fun comparison =>
      comparison.replaceFVars binders values }

/-- Read a role at an already selected public path. The enclosing producer
supplies the complete category; a field's carrier never selects a dictionary. -/
private def publicRoleAt (formal : Expr) (role : ParameterRole)
    (path : ComputationalData.RecordFieldPath) : TermElabM ParameterRole := do
  let mut current := formal
  let mut selected := role
  for step in path do
    let child ← withTransparency .all <| mkProjection current step.field
    let some info := getStructureInfo? (← getEnv) step.structureName
      | throwError "a projection parameter lost its selected public structure declaration"
    let mut count := 0
    let mut position : Option Nat := none
    for name in info.fieldNames do
      let item ← withTransparency .all <| mkProjection current name
      unless ← isProp (← inferType item) do
        if name == step.field then position := some count
        count := count + 1
    unless position == some step.index && count == step.count &&
        (← ComputationalData.recordFieldCodec current) == step.codec do
      throwError "a projection parameter changed its selected public field position"
    selected ← match selected with
      | .object context => do
          let codec ← ComputationalData.recordFieldCodec current
          if codec == .core then
            unless step.index == 0 && step.count == 1 do
              throwError "the Core parameter changed its public object position"
            pure (.object (← coreBaseContext context))
          else
            let some arrow ← StructuredProjection.arrow? current context
              | throwError "the projection parameter lost its complete public categorical role"
            if arrow.subobject then
              unless step.index == 0 && step.count == 1 do
                throwError "the refined Arrow parameter changed its public field position"
              pure (.object arrow.arrowContext)
            else
              unless step.count == 3 do
                throwError "the Arrow parameter changed its complete public field schema"
              match step.index with
              | 0 | 1 => pure (.object arrow.base)
              | 2 => pure (.map arrow.base arrow.source arrow.target)
              | _ => throwError "the Arrow parameter addresses an absent public field"
      | .map .. => throwError "a whole callable has no public implementation-field projection"
      | .value => pure .value
    current := child
  return selected

private def localInputRole (input : Input) (sourceContext : CategoryContext)
    (interfaces : Array ParameterInterface) : TermElabM ParameterRole := do
  match input with
  | .receiver => return .object sourceContext
  | .parameter actionIndex dataIndex =>
      match interfaces.filter (fun selected =>
          selected.actionIndex == actionIndex && selected.dataIndex == dataIndex) with
      | #[] => return .value
      | #[selected] => return selected.role
      | _ => throwError "a projection parameter has several original complete producer roles"

private def closeProjectionRole (role : ProjectionParameterRole) (formal : Expr)
    (inputs : Array SymbolicInput) (sourceContext : CategoryContext)
    (interfaces : Array ParameterInterface) : TermElabM ProjectionParameterRole := do
  let selected ← match role with
    | .object input path => pure (some (input, path, false))
    | .map input path => pure (some (input, path, true))
    | _ => pure none
  let some (input, path, callable) := selected | return role
  let #[root] := inputs.filter (·.input == some input)
    | throwError "the composed projection parameter lost its exact local producer position"
  let selected ← publicRoleAt root.formal
    (← localInputRole input sourceContext interfaces) path
  match selected with
  | .object context =>
      if callable then throwError "the composed parameter changed its whole-map producer role"
      CategoryContext.checkObject context formal
      return .objectAt context
  | .map context source target =>
      unless callable do throwError "the composed parameter changed its object producer role"
      CategoryContext.checkMorphism context formal source target
      return .mapAt context source target
  | .value => throwError "the composed parameter lost its independently selected categorical role"

private partial def checkProjectionSourceBefore (actionIndex : Nat) :
    ProjectionParameterSource → TermElabM ProjectionParameterSource
  | .intermediate preceding projection => do
      unless preceding < actionIndex do
        throwError "a projection parameter depends on its own or a later method result"
      pure (.intermediate preceding projection)
  | .record codec fields => do
      return .record codec (← fields.mapM (checkProjectionSourceBefore actionIndex))
  | source => pure source

private partial def rebaseProjectionSource (origin : Origin) (actionIndex : Nat) :
    ProjectionParameterSource → TermElabM ProjectionParameterSource
  | .retained .receiver projection => do
      let source := (← projectOrigin origin projection).parameterSource
      checkProjectionSourceBefore actionIndex source
  | .record codec fields => do
      return .record codec (← fields.mapM (rebaseProjectionSource origin actionIndex))
  | source => checkProjectionSourceBefore actionIndex source

private def rebaseProjectionAction (plan : ProjectionActionPlan)
    (origin : Origin) (actionIndex : Nat) (inputs : Array SymbolicInput)
    (sourceContext : CategoryContext) (interfaces : Array ParameterInterface) :
    TermElabM ProjectionActionPlan := do
  let rebaseParameter (parameter : ProjectionParameter) : TermElabM ProjectionParameter := do
    return { parameter with
      role := (← closeProjectionRole parameter.role parameter.formal inputs sourceContext interfaces)
      source := (← rebaseProjectionSource origin actionIndex parameter.source) }
  let rebaseStep (step : ProjectionActionStep) : TermElabM ProjectionActionStep := do
    let parameters ← step.parameters.mapM rebaseParameter
    return { step with parameters }
  let steps ← plan.steps.mapM rebaseStep
  let alignment ← plan.alignment.mapM fun selected => do
    return { selected with
      parameters := (← selected.parameters.mapM rebaseParameter)
      before := (← selected.before.mapM rebaseStep)
      left := (← selected.left.mapM rebaseStep)
      right := (← selected.right.mapM rebaseStep)
      after := (← selected.after.mapM rebaseStep) }
  return { plan with steps, alignment }

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

/-- Constructor wrappers retain their original inner action occurrence. The
compiler may factor a field through one of these complete actions; it never
chooses a functor by agreeing only at a particular receiver. -/
private partial def completionActions (shape : ActionShape) (declaration : Expr) :
    TermElabM (Array (EdgeRef × Expr)) := do
  let current := (shape.edge, ← shape.action declaration)
  match shape with
  | .named .. => return #[current]
  | .constructed _ inner => return #[current] ++ (← completionActions inner declaration)

private def completionActionLiteral (action : Expr) : Expr := Id.run do
  let mut selected := action.consumeMData.headBeta
  while selected.isAppOfArity ``id 2 ||
      selected.isAppOf ``CategoryTheory.Cat.Hom.toFunctor do
    selected := selected.appArg!.consumeMData.headBeta
  return selected

private partial def completionActionSteps (inputs : Array SymbolicInput)
    (state : RegistryState) (selected : Array (EdgeRef × Expr)) (action : Expr) :
    TermElabM (Except ProjectionActionFailure (Array ProjectionActionStep)) := do
  if let some declaration := FunctorActionData.directActionDeclaration? state action then
    -- The actual field's literal declaration retains its own parameter
    -- occurrences, including parameters ignored by the mathematical functor.
    let candidates :=
      (state.functors.filter (fun row =>
        declaration.getAppFn.constName? == some row.declaration)).map (fun row => EdgeRef.functor row.id) ++
      (state.classifiers.filter (fun row =>
        declaration.getAppFn.constName? == some row.declaration)).map (fun row => EdgeRef.classifierForget row.id)
    match candidates with
    | #[edge] => return ← compileProjectionSteps inputs state #[edge] #[action]
    | #[] => return .error (.missing "the intermediate field action is not registered")
    | _ => return .error (.ambiguous
        "the intermediate field's complete declaration has several accepted action bindings")
  -- Match constructor wrappers while all original binders are fresh. Full
  -- definitional equality verifies the action later; it cannot choose a
  -- different computational parameter occurrence here.
  let literal := completionActionLiteral action
  let known := selected.filter fun (_, application) =>
    completionActionLiteral application == literal
  match known with
  | #[(edge, _)] => return ← compileProjectionSteps inputs state #[edge] #[action]
  | #[] => pure ()
  | _ => return .error (.ambiguous
      "several selected complete action occurrences factor one intermediate field")
  if literal.isAppOfArity ``CategoryTheory.Functor.comp 8 then
    let arguments := literal.getAppArgs
    let first ← match ← completionActionSteps inputs state selected arguments[6]! with
      | .ok steps => pure steps
      | .error failure => return .error failure
    let second ← match ← completionActionSteps inputs state selected arguments[7]! with
      | .ok steps => pure steps
      | .error failure => return .error failure
    return .ok (first ++ second)
  return .error (.missing
    "the missing intermediate field has no retained complete registered action")

/-- Reduce administrative/public record projections only until the next whole
object or map action is exposed. Its operand is still a fresh local input field;
the selected action's body is not evaluated to guess an equal-valued source. -/
private def completionActionApplication? (formal : Expr) :
    MetaM (Option (Bool × Expr × Expr)) := do
  let isMap := fun (value : Expr) => value.isAppOfArity ``CategoryTheory.Functor.map 8 ||
    value.isAppOfArity ``Prefunctor.map 8
  let value ← withTransparency .all <| whnfHeadPred formal fun value =>
    pure ((FunctorActionData.objectAction? value).isNone && !isMap value)
  if let some (action, input) := FunctorActionData.objectAction? value then
    return some (false, action, input)
  if value.isAppOfArity ``CategoryTheory.Functor.map 8 then
    return some (true, value.getAppArgs[4]!, value.appArg!)
  if value.isAppOfArity ``Prefunctor.map 8 then
    let prefunctor := value.getAppArgs[4]!.consumeMData
    if prefunctor.isAppOfArity ``CategoryTheory.Functor.toPrefunctor 5 then
      return some (true, prefunctor.appArg!, value.appArg!)
  return none

private def compileFieldAction (inputs : Array SymbolicInput) (state : RegistryState)
    (selected : Array (EdgeRef × Expr)) (slots : Array Slot) (slot : Slot) :
    TermElabM FieldCompletion := do
  let some (morphism, application, input) ← completionActionApplication? slot.formal
    | return .unavailable (.missing
        "the missing intermediate field has no declared object or map action on a retained input")
  let steps ← match ← completionActionSteps inputs state selected application with
    | .ok steps => pure steps
    | .error failure => return .unavailable failure
  let some first := steps[0]?
    | throwError "a field completion lost its original action step"
  let some last := steps.back?
    | throwError "a field completion lost its final action step"
  let composite ← Semantic.compositeOfApplications (steps.map (·.application))
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType composite) (← inferType application) <&&>
        isDefEq composite application) do
    throwError "the intermediate field changed its complete selected composite"
  let inputType ← inferType input
  let (inputRole, source) ← match ← projectionParameterOrigin inputs input inputType with
    | .ok selected => pure selected
    | .error failure => return .unavailable failure
  match slot.role, morphism with
  | .object context, false =>
      unless inputRole matches .object .. do
        return .unavailable (.missing "an intermediate object action lost its public input object role")
      CategoryContext.checkObject first.sourceContext input
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq context.bundle last.targetContext.bundle <&&>
            isDefEq slot.formal (← Semantic.objOf composite input)) do
        return .unavailable (.missing
          "the intermediate object field requires its accepted complete action alignment")
      return .action { steps, input, inputType, inputRole, source, kind := .object }
  | .map context sourceSlot targetSlot, true =>
      unless inputRole matches .map .. do
        return .unavailable (.missing "an intermediate map action lost its complete callable input role")
      let sourceField ← fieldSlot slots sourceSlot
      let targetField ← fieldSlot slots targetSlot
      unless ← withoutModifyingState (withTransparency .all <|
          isDefEq context.bundle last.targetContext.bundle <&&>
            isDefEq slot.formal (← Semantic.mapOf composite input)) do
        return .unavailable (.missing
          "the intermediate map field requires its accepted complete action alignment")
      CategoryContext.checkMorphism context slot.formal sourceField.formal targetField.formal
      return .action { steps, input, inputType, inputRole, source,
        kind := .map sourceSlot targetSlot }
  | _, _ => return .unavailable (.missing
      "the intermediate field action has a different independently declared public role")

private def compileCompletions (inputs : Array SymbolicInput) (actionIndex : Nat)
    (shape : ActionShape) (declaration : Expr) (slots : Array Slot) (origins : Array Origin) :
    TermElabM (Array FieldCompletion) := do
  unless slots.size == origins.size do
    throwError "the intermediate completion lost its positional source inventory"
  let state ← registryState
  let selected ← completionActions shape declaration
  (slots.zip origins).mapM fun (slot, origin) => do
    match origin with
    | .retained .. => return .retained origin.parameterSource
    | .returned preceding _ =>
        if preceding < actionIndex then return .retained origin.parameterSource
        unless preceding == actionIndex do
          throwError "an intermediate field depends on a later producer"
    | .record .. => pure ()
    match slot.node with
    | .retained input projection => return .retained (.retained input projection)
    | .record codec fields => return .record codec fields
    | .returned => compileFieldAction inputs state selected slots slot

private def instantiateFieldAction (selected : FieldCompletionAction)
    (binders values : Array Expr) : FieldCompletionAction :=
  { selected with
    steps := selected.steps.map fun step => instantiateProjectionStep step binders values
    input := selected.input.replaceFVars binders values
    inputType := selected.inputType.replaceFVars binders values
    inputRole := instantiateProjectionParameterRole selected.inputRole binders values }

private def closeCompletion (selected : FieldCompletion) (binders values : Array Expr)
    (origin : Origin) (actionIndex : Nat) (inputs : Array SymbolicInput)
    (sourceContext : CategoryContext) (interfaces : Array ParameterInterface) :
    TermElabM FieldCompletion := do
  match selected with
  | .retained source => return .retained (← checkProjectionSourceBefore actionIndex source)
  | .record .. | .unavailable .. => return selected
  | .action selected =>
    let selected := instantiateFieldAction selected binders values
    let steps ← selected.steps.mapM fun step => do
      let parameters ← step.parameters.mapM fun parameter => do
        return { parameter with
          role := (← closeProjectionRole parameter.role parameter.formal inputs sourceContext interfaces)
          source := (← rebaseProjectionSource origin actionIndex parameter.source) }
      return { step with parameters }
    let inputRole ← closeProjectionRole selected.inputRole selected.input inputs sourceContext interfaces
    let source ← rebaseProjectionSource origin actionIndex selected.source
    return .action { selected with steps, inputRole, source }

private structure StageSchema extends IntermediateStage where
  origin : Origin

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

private def checkBoundary (actual expected : Expr) : TermElabM Unit := do
  unless ← withoutModifyingState (withTransparency .all <| isDefEq actual expected) do
    throwError "the routed result schema changed a complete selected category boundary"

private def resultOf (method : MethodEntry) (prefixActions : Array EdgeRef)
    (actions : Array Expr) (receiver : Expr)
    (sourceContext : CategoryContext) : TermElabM (Expr × Expr) := do
  unless actions.size == prefixActions.size + 1 do
    throwError "the routed result schema omitted a selected action"
  let state ← registryState
  let mut value := receiver
  let mut context := sourceContext
  for (edge, action) in prefixActions.zip (actions.extract 0 prefixActions.size) do
    let (source, target) ← functorCategoryBundles action
    checkBoundary context.bundle source
    value ← Semantic.objOf action value
    let some expression := state.selectedEdgeTarget? edge
      | throwError "the routed schema lost a selected target category expression"
    context := { expression, bundle := target }
  let methodAction := actions.back!
  let (source, _) ← functorCategoryBundles methodAction
  checkBoundary (← methodSourceContext method context).bundle source
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

/-- Compile one action in its own dependent telescope. The incoming provenance
tree is substituted only at its receiver; it never identifies declaration
binders or imposes false independence on a complete selected category boundary. -/
private def compileStage (actionIndex : Nat) (shape : ActionShape)
    (receiver : Expr) (sourceContext targetContext : CategoryContext)
    (origin : Origin) (interfaces : Array ParameterInterface)
    (method? : Option MethodEntry) : TermElabM StageSchema := do
  let application := shape.declaration
  let actualAction ← shape.action application
  let (actualSource, actualTarget) ← functorCategoryBundles actualAction
  let acceptedContext ← match method? with
    | some method => methodSourceContext method sourceContext
    | none => pure sourceContext
  checkBoundary acceptedContext.bundle actualSource
  checkBoundary targetContext.bundle actualTarget
  let argument ← match method? with
    | some method => methodArgument method receiver
    | none => pure receiver
  let expected ← Semantic.objOf actualAction argument
  CategoryContext.checkObject targetContext expected
  forallTelescopeReducing (← inferType application.getAppFn) fun declarationBinders _ => do
    let declarationValues := application.getAppArgs
    let (parameters, declarationInputs) ← declarationSlots actionIndex
      declarationBinders declarationValues interfaces
    let symbolicAction ← shape.action (mkAppN application.getAppFn declarationBinders)
    let (initial, symbolicTarget) ← functorCategoryBundles symbolicAction
    let symbolicSource ← match method? with
      | some method => underlyingMethodContext method { sourceContext with bundle := initial }
      | none => pure { sourceContext with bundle := initial }
    let type ← CategoryContext.carrier symbolicSource
    unless ← withTransparency .all <| isDefEq
        (type.replaceFVars declarationBinders declarationValues) (← inferType receiver) do
      throwError "the symbolic action receiver lost its complete selected type"
    checkBoundary (symbolicSource.bundle.replaceFVars declarationBinders declarationValues)
      sourceContext.bundle
    withLocalDeclD `receiver type fun symbolicReceiver => do
      let symbolicArgument ← match method? with
        | some method => methodArgument method symbolicReceiver
        | none => pure symbolicReceiver
      let symbolicResult ← Semantic.objOf symbolicAction symbolicArgument
      let symbolicContext := { targetContext with bundle := symbolicTarget }
      CategoryContext.checkObject symbolicContext symbolicResult
      let inputs := declarationInputs.push {
        formal := symbolicReceiver, input := some .receiver, kind := .object,
        origin := some origin }
      withLocalDeclD `resultShape (← inferType symbolicResult) fun outputShape => do
        let (output, symbolicSlots) ← compileSlots inputs outputShape symbolicResult outputShape
          (.object symbolicContext) #[]
        let origins ← compileOrigins inputs actionIndex symbolicSlots
        let some outputOrigin := origins[output]?
          | throwError "the composed action lost its selected output provenance"
        let symbolicSlots := (symbolicSlots.zip origins).map fun (slot, origin) =>
          { slot with producedBy := match origin with
            | .returned actionIndex replyPath => some { actionIndex, replyPath }
            | _ => none }
        let selectedActions ← compileProjectionActions inputs symbolicSlots
        let symbolicCompletions ← compileCompletions inputs actionIndex shape
          (mkAppN application.getAppFn declarationBinders) symbolicSlots origins
        let binders := declarationBinders.push symbolicReceiver
        let values := declarationValues.push receiver
        let formal := symbolicResult.replaceFVars binders values
        unless ← withTransparency .all <|
            isDefEq (← inferType formal) (← inferType expected) <&&> isDefEq formal expected do
          throwError "closing one routed action changed its complete selected result"
        let slots := symbolicSlots.map fun slot => instantiateSlot slot binders values
        let closedInputs := inputs.map fun input => { input with
          formal := input.formal.replaceFVars binders values }
        let completions ← symbolicCompletions.mapM fun selected =>
          closeCompletion selected binders values origin actionIndex closedInputs
            sourceContext interfaces
        let projectionActions ← selectedActions.mapM fun selected => do
          let action ← match selected.action with
            | .error failure => pure (.error failure)
            | .ok action => do
                let closed := instantiateProjectionAction action binders values
                pure (.ok (← rebaseProjectionAction closed origin actionIndex
                  closedInputs sourceContext interfaces))
          return { selected with action }
        for selected in projectionActions do
          if let .ok action := selected.action then
            unless (← isTypeCorrect action.projection) &&
                (← isTypeCorrect action.application) do
              throwError "a closed projection action lost its complete functor type"
            for step in action.steps do
              discard <| step.checkedDeclaration
            for selected in action.alignment do
              discard <| selected.checkedDeclaration
            if let some comparison := action.alignmentComparison then
              Semantic.checkRouteComparison comparison action.application action.projection
            for (_, comparison) in action.comparisons do
              unless ← isTypeCorrect comparison do
                throwError "a closed projection action lost an accepted comparison"
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
        for (slot, completion) in slots.zip completions do
          if let .action selected := completion then
            unless ← isTypeCorrect selected.input do
              throwError "a closed field completion lost its original input type"
            unless ← withTransparency .all <|
                isDefEq (← inferType selected.input) selected.inputType do
              throwError "a closed field completion changed its declared input type"
            for step in selected.steps do
              discard <| step.checkedDeclaration
              for parameter in step.parameters do
                unless ← withTransparency .all <|
                    isDefEq (← inferType parameter.formal) parameter.expectedType do
                  throwError "a closed field completion lost a complete action parameter"
            let some first := selected.steps[0]?
              | throwError "a closed field completion omitted its original action"
            let some last := selected.steps.back?
              | throwError "a closed field completion omitted its final action"
            match selected.kind, selected.inputRole, slot.role with
            | .object, .objectAt inputContext, .object resultContext =>
                checkBoundary inputContext.bundle first.sourceContext.bundle
                checkBoundary resultContext.bundle last.targetContext.bundle
                CategoryContext.checkObject inputContext selected.input
            | .map source target, .mapAt inputContext originalSource originalTarget,
                .map resultContext sourceSlot targetSlot =>
                unless source == sourceSlot && target == targetSlot && source != target do
                  throwError "a field completion merged distinct declared map endpoint positions"
                checkBoundary inputContext.bundle first.sourceContext.bundle
                checkBoundary resultContext.bundle last.targetContext.bundle
                CategoryContext.checkMorphism inputContext selected.input originalSource originalTarget
            | _, _, _ =>
                throwError "a closed field completion changed its complete input or output role"
        return {
          actionIndex, edge := shape.edge, application := actualAction, receiver, formal,
          sourceContext, resultContext := targetContext,
          parameters, slots, output, completions, origin := outputOrigin, projectionActions }

/-- Compose independently compiled field transformations at the exact selected
category boundaries. Equal closed parameters never merge their supplier slots.
The only compositional substitution is the preceding field provenance at the
next receiver; dependent category parameters remain in their own valid context.
No computational data, dispatch, cache or backend participates. -/
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
  let (argument, result) ← resultOf method (prefixActions.map (·.1)) actions receiver sourceContext
  CategoryContext.checkObject resultContext result
  let state ← registryState
  let mut current := receiver
  let mut context := sourceContext
  let mut origin := Origin.retained .receiver (.input #[])
  let mut capturedParameters := #[]
  let mut stages := #[]
  let mut completed : Option StageSchema := none
  for index in [:shapes.size] do
    let some shape := shapes[index]?
      | throwError "the composed schema lost a selected action shape"
    let some action := actions[index]?
      | throwError "the composed schema lost a complete selected application"
    let (_, bundle) ← functorCategoryBundles action
    let finalAction := index == prefixActions.size
    let target ← if finalAction then pure resultContext else do
      let some (edge, _) := prefixActions[index]?
        | throwError "the composed schema lost a preceding selected route step"
      let some expression := state.selectedEdgeTarget? edge
        | throwError "the composed schema lost a complete selected target expression"
      pure ({ expression, bundle } : CategoryContext)
    let stage ← compileStage index shape current context target origin parameterInterfaces
      (if finalAction then some method else none)
    current := stage.formal
    context := target
    origin := stage.origin
    capturedParameters := capturedParameters ++ stage.parameters
    stages := stages.push stage.toIntermediateStage
    completed := some stage
  let some completed := completed
    | throwError "the composed schema omitted its selected method action"
  unless ← withTransparency .all <|
      isDefEq (← inferType current) (← inferType result) <&&> isDefEq current result do
    throwError "composing the selected field schemas changed the complete formal result"
  return {
    method := method.id, application, prefixActions, receiver, argument, formal := result,
    sourceContext, resultContext, parameters := capturedParameters,
    slots := completed.slots, output := completed.output,
    projectionActions := completed.projectionActions, stages }

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
