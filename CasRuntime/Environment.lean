module

public import CasRuntime.Value
public import CasCompiler.SelectedMorphism
import CasCompiler.SourceTypeOrigin

public section

namespace CasRuntime

open Lean Meta CasCompiler

initialize registerTraceClass `cas.environment

/-- An actual value associated with an explicitly identified source binder. -/
structure RuntimeParameter where
  private mk ::
  source : BindingId
  value : ValueBinding
  private origin : ValueOrigin
  private graph : ValueGraph

/-- Read the actual producing provenance and retain its visible graph for stored field checks.
Reuse: ValueGraph.requiredOwners and ValueGraph.find; no payload copy enters this table. -/
opaque RuntimeParameter.ofValue (graph : ValueGraph) (source : BindingId) (value : ValueBinding) :
    Except String RuntimeParameter := do
  discard <| graph.requiredOwners #[value]
  let some node := graph.find value.value
    | throw "the runtime parameter is outside the visible graph"
  return ⟨source, value, node.origin, graph⟩

/-- An actual operand at an explicit position in the complete source argument list. -/
structure RuntimeArgument where
  private mk ::
  index : Nat
  value : ValueBinding
  private origin : ValueOrigin
  private graph : ValueGraph
  private marks : Array ValueBinding

/-- Retain operand provenance from the visible graph before native application preparation.
Reuse: the same graph visibility and immutable producing-origin checks as RuntimeParameter. -/
opaque RuntimeArgument.ofValue (graph : ValueGraph) (index : Nat) (value : ValueBinding)
    (marks : Array ValueBinding := #[]) :
    Except String RuntimeArgument := do
  discard <| graph.requiredOwners #[value]
  let some node := graph.find value.value
    | throw "the runtime argument is outside the visible graph"
  return ⟨index, value, node.origin, graph, marks⟩

/-- Resolve only marks in this argument's complete retained native source.
The captured argument snapshot is authoritative, never the current global mark array. -/
opaque RuntimeArgument.sourceMarks (argument : RuntimeArgument) (source : ClosedTerm) :
    Except String (Array (Nat × ValueBinding)) :=
  retainedSourceMarks (argument.marks.mapIdx fun key value => (key, value)) source

/-- The complete semantic telescope and its separate ordered runtime-binding table.
Formal-only entries retain their source definitions, hypotheses and selected instances.
Source: data model section 2, ContextTelescope and its runtime-binding table. -/
structure RuntimeEnvironment where
  private mk ::
  worker : String
  context : ContextTelescope
  values : Array (Option ValueBinding)
  private inputProjections : Std.HashMap BindingId InputProjection
  sourceMarks : Array (Nat × ValueBinding)
  /-- The current immutable graph supplied at preparation after actual operands are lowered. -/
  private sourceGraph : Option ValueGraph

def RuntimeEnvironment.references (environment : RuntimeEnvironment) : Array ValueBinding :=
  environment.values.filterMap id ++ environment.sourceMarks.map (·.2)

/-- Extend inert source provenance with exact captured references from the same preparation.
No historical graph is chosen from a parameter; callers supply the current graph explicitly. -/
opaque RuntimeEnvironment.withSourceMarks (environment : RuntimeEnvironment)
    (marks : Array (Nat × ValueBinding)) (graph : Option ValueGraph := none) :
    MetaM RuntimeEnvironment := do
  let marks ← IO.ofExcept <| (mergeSourceMarks environment.sourceMarks marks).mapError IO.userError
  let sourceGraph := match graph with
    | some current => some current
    | none => environment.sourceGraph
  if let some graph := sourceGraph then
    unless graph.worker == environment.worker do
      throwError "marked source preparation belongs to a different worker"
    discard <| IO.ofExcept <| (graph.requiredOwners (marks.map (·.2))).mapError IO.userError
  return { environment with sourceMarks := marks, sourceGraph }

def RuntimeEnvironment.lookup (environment : RuntimeEnvironment) (source : BindingId) :
    Except String (Option ValueBinding) := do
  for (entry, value) in environment.context.entries.zip environment.values do
    if entry.id == source then return value
  throw "the runtime binding identity is outside its source telescope"

private def RuntimeEnvironment.bindingMap (environment : RuntimeEnvironment) :
    Std.HashMap BindingId ValueBinding := Id.run do
  let mut supplied := {}
  for (entry, value) in environment.context.entries.zip environment.values do
    if let some value := value then supplied := supplied.insert entry.id value
  return supplied

/-- The same actual occurrence, seen at either end of one association chain: a later projection
extends the original's chain, and a record field holding a binding extends the binding's own
chain (a lift record's source object). A different value is never the same reference. -/
private def sameReference (original current : ValueBinding) : Bool :=
  original.value == current.value &&
    (original.associationIds.toList.isPrefixOf current.associationIds.toList ||
      current.associationIds.toList.isPrefixOf original.associationIds.toList)

/-- A supplied operand retains a source binding's value when it is that node and carries every
association of the binding. A view of the node without one of them (the value before a consuming
application) is not the bound value. -/
private def retainsReference (bound operand : ValueBinding) : Bool :=
  bound.value == operand.value &&
    bound.associationIds.toList.isPrefixOf operand.associationIds.toList

private def checkNativeType (context : OpenContext) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin) : MetaM Unit := do
  let original ← value.role.source.inContext context
  unless ← isDefEq (← inferType original) expected do
    trace[cas.environment] "{original} : {← inferType original}, expected {expected}"
    throwError "the runtime value has an incompatible complete source type"
  let producing ← origin.role.source.inContext context
  unless ← isDefEq (← inferType producing) expected do
    trace[cas.environment] "{producing} : {← inferType producing}, expected {expected}"
    throwError "the producing runtime value has an incompatible complete source type"

/-- The tag of the failure "the source binding `id` has no runtime value". A session uses it to
report the statement as the gap of that definition. -/
def missingValueTag (id : BindingId) : Name :=
  .num (.str `CasRuntime.missingValue id.session) id.serial

/-- Whether the failure is a missing runtime value of the source binding `id`. -/
def missingValueOf (error : Exception) (id : BindingId) : Bool :=
  error.toMessageData.hasTag (· == missingValueTag id)

/-- Expose only the existing native input-routing head and exact declared arrow endpoints.
Reclose each step over the original telescope; selected source boundaries and retained lets
remain intact, including distinct closed definitions with convertible values. -/
private partial def dependencySource (source : ClosedTerm) : MetaM ClosedTerm := do
  let source ← source.inputProjectionSource
  source.withOpen fun bindings stated => do
    let declared ← declaredEndpoint stated
    let context ← ContextTelescope.capture bindings
    if declared != stated then return ← dependencySource (← context.close declared)
    if let some projection ← SourceProjection.ofExpr? stated then
      let parent ← dependencySource (← context.close projection.parent)
      let parent ← parent.inContext context
      if parent != projection.parent then
        let constructor ← getConstInfoCtor projection.info.ctorName
        return ← dependencySource (← context.close (mkProj constructor.induct projection.info.i parent))
    return source

/-- A let is an alias only when its own source selects an earlier binder or native field.
Closed or computed definitions keep their distinct binding identities. -/
private partial def dependencyReference (context : OpenContext) (inputs : Array BindingId)
    (source : ClosedTerm) (path : Array Name := #[]) :
    MetaM (Option (BindingId × Array Name)) := do
  let source ← dependencySource source
  let some selected ← source.inputProjectionAt path inputs | return none
  let .context id := selected.target
    | throwError "a context dependency selected a nonexistent application argument"
  let some binding := context.bindings.find? (·.id == id)
    | throwError "a dependent source reference is outside its context"
  if let some definition := (← getFVarLocalDecl binding.expression).value? then
    if definition.hasFVar then
      if let some original ← dependencyReference context inputs
          (← context.close definition) selected.path then
        return some original
  return some (id, selected.path)

/-- Align the original field's abstract prefix slots with their positions in the expected
native type. Equality of runtime values or convertible source binders never selects a slot.
Slot domains recover earlier transitive dependencies. Fixed fragments may validate against
closed, unmarked native content only after excluding every prefix and introduced binder;
the original captured context references remain independently required. -/
private partial def dependencyTerms (sameContextReference : Expr → Expr → MetaM Bool)
    (locals : Array Expr) (formal expected : Expr)
    (binders : Array (Expr × Expr) := #[])
    (capturedReference : Option (Bool → Expr → Expr → MetaM (Option Bool)) := none)
    (sourceView : Option (Expr → MetaM Expr) := none) (capturedReduction : Bool := true)
    (allowClosedExpected : Bool := true) :
    MetaM (Option (Array (Nat × Expr))) := do
  let allowClosedExpected := allowClosedExpected && (match expected with
    | .mdata .. => false
    | _ => true)
  let expectedHasMetadata := (expected.find? fun
    | .mdata .. => true
    | _ => false).isSome
  let originalFormal := formal
  let originalExpected := expected
  let blocksReduction := fun (expression : Expr) => match expression with
    | .mdata data _ => (markedKey? data).isNone &&
      (data.contains `CasCompiler.source.kind || data.contains `CasCompiler.selection)
    | _ => false
  let capturedReduction := capturedReduction &&
    !(blocksReduction formal) && !(blocksReduction expected)
  -- Existing shape matching ignores metadata; the additional source comparison must not
  -- enter a selected/marked boundary, including during recursive type normalization.
  let sameContextReference :=
    if (projectionBody? formal).isSome && (projectionBody? expected).isSome then
      sameContextReference
    else fun _ _ => pure false
  let formal := formal.consumeMData
  let expected := expected.consumeMData
  if let some compare := capturedReference then
    if let some same ← compare capturedReduction originalFormal originalExpected then
      unless same do
        throwError "the runtime value has a different marked source type dependency"
      return some #[]
    -- Type metadata may be inert, but a retained mark inside it cannot disappear before
    -- its own structural position has been compared. No marked body is normalized here.
    match originalFormal, originalExpected with
    | .mdata _ body, .mdata _ other =>
      return ← dependencyTerms sameContextReference locals body other binders
        capturedReference sourceView capturedReduction allowClosedExpected
    | .mdata _ body, _ =>
      return ← dependencyTerms sameContextReference locals body originalExpected binders
        capturedReference sourceView capturedReduction allowClosedExpected
    | _, .mdata _ body =>
      return ← dependencyTerms sameContextReference locals originalFormal body binders
        capturedReference sourceView capturedReduction allowClosedExpected
    | _, _ => pure ()
  if let some index := locals.findIdx? (· == formal) then
    if expected.hasLooseBVars then return none
    let proof ← isProof formal
    let freeVariables := collectFVars {} expected
    if !proof && binders.any (fun (_, bound) => freeVariables.fvarSet.contains bound.fvarId!) then
      return none
    let some preceding ← dependencyTerms sameContextReference (locals.extract 0 index)
        (← inferType formal) (← inferType expected) binders
        capturedReference sourceView capturedReduction allowClosedExpected | return none
    if proof then return some preceding
    return some (preceding.push (index, originalExpected))
  if let some (_, bound) := binders.find? (fun (source, _) => source == formal) then
    return if bound == expected then some #[] else none
  if formal == expected && (capturedReference.isNone ||
      (!hasSourceMarks originalFormal && !hasSourceMarks originalExpected)) then return some #[]
  let merge (left right : MetaM (Option (Array (Nat × Expr)))) :
      MetaM (Option (Array (Nat × Expr))) := do
    let some left ← left | return none
    let some right ← right | return none
    return some (left ++ right)
  let matched ← match formal, expected with
    | .sort _, .sort _ => pure (some #[])
    | .const name _, .const other _ =>
      if name == other then pure (some #[]) else pure none
    | .app f a, .app g b =>
      merge (dependencyTerms sameContextReference locals f g binders
        capturedReference sourceView capturedReduction allowClosedExpected)
        (dependencyTerms sameContextReference locals a b binders
          capturedReference sourceView capturedReduction allowClosedExpected)
    | .forallE name a b info, .forallE other c d otherInfo
    | .lam name a b info, .lam other c d otherInfo => do
      let some domains ← dependencyTerms sameContextReference locals a c binders
          capturedReference sourceView capturedReduction allowClosedExpected | return none
      withLocalDecl name info a fun source =>
        withLocalDecl other otherInfo c fun target => do
          let some bodies ← dependencyTerms sameContextReference locals
              (b.instantiate1 source) (d.instantiate1 target) (binders.push (source, target))
              capturedReference sourceView capturedReduction allowClosedExpected
            | return none
          return some (domains ++ bodies)
    | .proj owner index parent, .proj other otherIndex otherParent =>
      if owner == other && index == otherIndex then
        dependencyTerms sameContextReference locals parent otherParent binders
          capturedReference sourceView capturedReduction allowClosedExpected
      else pure none
    | _, _ => pure none
  if matched.isSome then return matched
  if ← sameContextReference originalFormal originalExpected then return some #[]
  -- This comparison contributes no dependency route. The expected fragment has no source
  -- reference to replace, and the formal fragment contains no slot whose identity could be
  -- recovered by conversion. Retained marks remain barriers even around closed native data.
  let formalVars := collectFVars {} formal
  let hasAbstract := locals.any (fun parameter => formalVars.fvarSet.contains parameter.fvarId!) ||
    binders.any (fun (source, _) => formalVars.fvarSet.contains source.fvarId!)
  if allowClosedExpected && !expectedHasMetadata && !expected.hasFVar &&
      !expected.hasLooseBVars && !formal.hasLooseBVars && !hasAbstract then
    let converts ← withoutModifyingState do
      withConfig (fun config => { config with zetaDelta := true }) (isDefEq formal expected)
    if converts then return some #[]
  let normalize := fun (original expression : Expr) => do
    if let some view := sourceView then
      if capturedReduction && !original.hasLooseBVars then view original else pure original
    else if expression.hasLooseBVars then pure expression
    else withConfig (fun config => { config with zetaDelta := false }) (whnf expression)
  let normalizedFormal ← normalize originalFormal formal
  let normalizedExpected ← normalize originalExpected expected
  if normalizedFormal == formal && normalizedExpected == expected then return none
  dependencyTerms sameContextReference locals normalizedFormal normalizedExpected binders
    capturedReference sourceView capturedReduction (allowClosedExpected && !expectedHasMetadata)

/-- Read only actual fields of this exact current context value. A lazy frontier requires a
published graph relation or recorded access; dependency checking never computes a missing field. -/
private def storedDependency (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) : MetaM (Option ValueBinding) := do
  let mut value := parent
  for projection in path do
    let some field := value.role.fields.find? (·.projection == projection)
      | throwError "a consuming dependent reference is outside its native record"
    let some index := field.wireIndex
      | throwError "a consuming runtime dependency selected a proof field"
    let some node := graph.find value.value
      | throwError "a consuming dependent reference is outside its actual graph"
    if node.payload.data.storedFields?.isNone then
      let some retained ← IO.ofExcept <|
          (graph.projected? value #[projection]).mapError IO.userError
        | return none
      value := retained
      continue
    value ← IO.ofExcept <| (graph.project value index).mapError IO.userError
  return some value

/-- The one native edge being completed by this actual projection result. Its candidate is
fixed before recursive validation; ordinary capture and result checks never receive it. -/
private structure PendingResultProjection where
  parent : ValueBinding
  projection : Name
  result : ValueBinding

/-- Read the original graph before crossing one prepared, still unpublished projection edge.
Every existing stored field and cached path constrains the result. After crossing that edge,
only the candidate's actual stored or previously published descendants may supply a value.
No source expression or type equality selects a runtime parent. -/
private partial def pendingDependency (graph : ValueGraph) (parent : ValueBinding)
    (path : Array Name) (pending : Option PendingResultProjection) :
    MetaM (Option ValueBinding) := do
  if path.isEmpty then return some parent
  let cached ← IO.ofExcept <| (graph.projected? parent path).mapError IO.userError
  let some projection := path[0]?
    | throwError "a pending dependent reference lost its native projection"
  let some field := parent.role.fields.find? (·.projection == projection)
    | throwError "a consuming dependent reference is outside its native record"
  let some index := field.wireIndex
    | throwError "a consuming runtime dependency selected a proof field"
  let some node := graph.find parent.value
    | throwError "a consuming dependent reference is outside its actual graph"
  let existing ← IO.ofExcept <|
    (graph.projected? parent #[projection]).mapError IO.userError
  let step ← if node.payload.data.storedFields?.isSome then do
      let stored ← IO.ofExcept <| (graph.project parent index).mapError IO.userError
      if let some existing := existing then
        unless sameReference stored existing do
          throwError "the runtime value has a different consuming dependent reference \
            in its retained projection"
      pure (some stored)
    else pure existing
  let rest := path.extract 1 path.size
  let selected ← match step with
    | some next => pendingDependency graph next rest pending
    | none => match pending with
      | some access =>
        if projection == access.projection && sameReference parent access.parent then
          pendingDependency graph access.result rest none
        else pure none
      | none => pure none
  if let some cached := cached then
    if let some selected := selected then
      unless sameReference cached selected do
        throwError "the runtime value has a different consuming dependent reference \
          in its retained projection"
    return some cached
  return selected

/-- Follow only the candidate's recorded access chain to the selected source occurrence.
The graph contributes immutable producing access, while association prefixes permit aliases. -/
private partial def hasDependencyAccess (graph : ValueGraph) (value parent : ValueBinding)
    (path : Array Name) : Bool := Id.run do
  if path.isEmpty then return sameReference parent value
  let mut accesses := value.projectionAccesses
  if let some node := graph.find value.value then
    if let some original := node.origin.access then
      accesses := accesses.push (original, node.origin.accessPath)
  for (original, suffix) in accesses do
    if suffix.isEmpty || suffix.size > path.size then continue
    let prefixSize := path.size - suffix.size
    if path.extract prefixSize path.size == suffix &&
        hasDependencyAccess graph original parent (path.extract 0 prefixSize) then return true
  return false

/-- An exact source-path parent and declared field. A prepared projection supplies its
original operand path; recursive stored-result validation extends that same path. -/
private structure ResultFieldPrefix where
  parent : ValueBinding
  layout : RecordLayout
  field : FieldLayout
  «view» : Option FieldDependencyView := none

/-- Follow only the next declared source field of this same prepared prefix witness. The
view narrows its original slots to that descendant; introduced native locals stay abstract. -/
private def ResultFieldPrefix.descend (current : ResultFieldPrefix) (projection : Name) :
    MetaM ResultFieldPrefix := do
  let path := ((current.view.map (·.path)).getD #[]).push projection
  return { current with «view» := some (← current.field.dependencyView path) }

/-- Read only an exact current prefix local and its native projection spine. -/
private partial def prefixProjection (locals : Array Expr) (term : Expr) :
    MetaM (Option (Nat × Array Name)) := do
  if let some index := locals.findIdx? (· == term) then return some (index, #[])
  let some projection ← SourceProjection.ofExpr? term | return none
  let some (index, path) ← prefixProjection locals projection.parent | return none
  return some (index, path.push projection.declaration)

/-- Align an original dependency with the current field's abstract native prefix positions.
All occurrences must resolve to a current prefix route, an explicit context reference, or closed
source. An unrelated unresolved family cannot borrow another occurrence's prefix witness. -/
private def currentPrefixRoutes (context : OpenContext) (inputs : Array BindingId)
    (graph : ValueGraph) (original : FieldInstantiation) (slot : Nat)
    (current : ResultFieldPrefix) : MetaM (Option (Array (ValueBinding × Array Name) × Bool)) := do
  let family ← original.typeFamily.inContext context
  let currentFamily ← ((current.view.map (·.typeFamily)).getD
    current.field.typeFamily).inContext context
  let inspect := fun locals type => do
    unless locals.size ≥ original.preceding.size do
      throwError "a consuming runtime dependency lost its complete native prefix"
    let inspectCurrent := fun currentLocals currentType => do
      unless currentLocals.size ≥ current.field.sourceIndex do
        throwError "the current result field lost its complete native prefix"
      let prefixLocals := currentLocals.extract 0 current.field.sourceIndex
      let some terms ← dependencyTerms (fun _ _ => pure false) locals type currentType | return none
      let selected := terms.filterMap fun (index, term) => if index == slot then some term else none
      if selected.isEmpty then return none
      let mut routes := #[]
      let mut complete := true
      for term in selected do
        if let some (index, path) ← prefixProjection prefixLocals term then
          let some prepared := current.layout.fields[index]?
            | throwError "a current result dependency is outside its declared prefix"
          unless prepared.field.wireIndex.isSome do
            complete := false
            continue
          let some value ← storedDependency graph current.parent #[prepared.field.projection]
            | throwError "the runtime value is missing a required original dependent prefix field"
          routes := routes.push (value, path)
        else
          let freeVars := collectFVars {} term
          if currentLocals.any (fun parameter => freeVars.fvarSet.contains parameter.fvarId!) then
            complete := false
            continue
          let source ← dependencySource (← context.close term)
          let term ← source.inContext context
          if term.hasFVar && (← dependencyReference context inputs source).isNone then
            complete := false
      if routes.isEmpty then return none
      return some (routes, complete)
    if current.view.isSome then lambdaTelescope currentFamily inspectCurrent
    else lambdaBoundedTelescope currentFamily current.field.sourceIndex inspectCurrent
  if original.view.isSome then lambdaTelescope family inspect
  else lambdaBoundedTelescope family original.preceding.size inspect

/-- Read the existing native projection grammar without reducing across a source boundary. -/
private partial def capturedTypePosition (context : OpenContext)
    (positions : Std.HashMap BindingId InputProjection) (source : Expr) :
    MetaM (Option (BindingId × Array Name)) := do
  let some source := projectionBody? source | return none
  if source.isFVar then
    let some binding := context.bindings.find? (·.expression == source) | return none
    let some selected := positions[binding.id]? | return none
    let .context original := selected.target | return none
    return some (original, selected.path)
  let some projection ← SourceProjection.ofExpr? source | return none
  let some (binding, path) ← capturedTypePosition context positions projection.parent | return none
  return some (binding, path.push projection.declaration)

/-- Resolve an exact native source address to its already supplied occurrence and suffix.
A named alias joins by its captured BindingId/path, never by a convertible native value. -/
private def capturedTypeReferences (context : OpenContext)
    (inputProjections : Std.HashMap BindingId InputProjection) (inputs : Array BindingId)
    (supplied : Std.HashMap BindingId ValueBinding) (marks : Array (Nat × ValueBinding))
    (expression : Expr) (reduce : Bool) : MetaM (Array (ValueBinding × Array Name)) := do
  let captured := context.bindings.map (·.expression)
  if expression.hasLooseBVars || expression.hasExprMVar || expression.hasLevelMVar ||
      (expression.abstract captured).hasFVar then return #[]
  let expression ← if reduce then context.inputProjectionSource expression inputs
    else pure expression
  if let some (key, path) ← markedProjection? expression then
    let some (_, parent) := marks.find? (·.1 == key)
      | throwError "the runtime value has an unresolved consuming dependent type"
    return #[(parent, path)]
  let reference ← if reduce then
      dependencyReference context inputs (← context.close expression)
    else capturedTypePosition context inputProjections expression
  let some reference := reference | return #[]
  let mut references := #[]
  for binding in context.bindings do
    let some value := supplied[binding.id]? | continue
    let some selected := inputProjections[binding.id]? | continue
    let .context source := selected.target | continue
    unless source == reference.1 && selected.path.toList.isPrefixOf reference.2.toList do continue
    references := references.push (value, reference.2.extract selected.path.size reference.2.size)
  return references

/-- Check actual captured type positions before native conversion can erase their marks.
Published access relations permit a field alias; equality of payloads or native values does not. -/
private def sameCapturedTypeReference (graph : ValueGraph)
    (left right : ValueBinding × Array Name) : MetaM Bool := do
  if sameReference left.1 right.1 && left.2 == right.2 then return true
  let leftValue ← storedDependency graph left.1 left.2
  let rightValue ← storedDependency graph right.1 right.2
  match leftValue, rightValue with
  | some first, some second => return sameReference first second
  | some first, none => return hasDependencyAccess graph first right.1 right.2
  | none, some second => return hasDependencyAccess graph second left.1 left.2
  | none, none => return false

private def checkDependencies (context : OpenContext)
    (inputProjections : Std.HashMap BindingId InputProjection)
    (supplied : Std.HashMap BindingId ValueBinding) (marks : Array (Nat × ValueBinding))
    (graph : ValueGraph)
    (graphFor : BindingId → MetaM ValueGraph) (expected : Expr)
    (value : ValueBinding) (origin : ValueOrigin)
    (currentPrefixes : Array ResultFieldPrefix := #[])
    (pending : Option PendingResultProjection := none) : MetaM Unit := do
  for index in origin.role.contextDependencies do
    let some dependency := origin.role.source.context.entries[index]?
      | throwError "a producing runtime dependency is outside its source telescope"
    let some original := origin.parameters[index]?
      | throwError "a producing runtime dependency is outside its complete reference table"
    if let some original := original then
      let some current := supplied[dependency.id]?
        | throwError (MessageData.tagged (missingValueTag dependency.id)
            m!"the runtime value is missing a retained dependent reference")
      unless sameReference original current do
        throwError "the runtime value has a different retained dependent reference"
  let mut inputs := #[]
  for binding in context.bindings do
    unless ← isProp (← inferType binding.expression) do inputs := inputs.push binding.id
  -- Only already captured context terms can use this correspondence. Fresh field-prefix
  -- and binder locals remain the responsibility of dependencyTerms' ordered slot matches.
  let captured := context.bindings.map (·.expression)
  let fixedContextReference := fun (expression : Expr) => do
    if expression.hasLooseBVars || expression.hasExprMVar || expression.hasLevelMVar ||
        (expression.abstract captured).hasFVar then return none
    dependencyReference context inputs (← context.close expression)
  let sameContextReference := fun (formal expected : Expr) => do
    let some original ← fixedContextReference formal | return false
    let some current ← fixedContextReference expected | return false
    return original == current
  -- Actual source bindings remain opaque. Formal definitions have no runtime supplier;
  -- the existing source-only view may follow them until their captured occurrence mark.
  let retainedInputs := inputs.filter (supplied.contains ·)
  let sourceView := fun (expression : Expr) =>
    context.inputProjectionSource expression retainedInputs
  let compareCaptured := fun (reduce : Bool) (formal current : Expr) => do
    let originalSource ← if reduce then sourceView formal else pure formal
    let currentSource ← if reduce then sourceView current else pure current
    let originalMarked ← markedProjection? originalSource
    let currentMarked ← markedProjection? currentSource
    if originalMarked.isNone && currentMarked.isNone then return none
    -- A closed native fragment introduces no competing runtime supplier. Let the
    -- existing structural/closed-fragment checks validate its native conversion;
    -- do not resolve a descriptive producer mark merely to decide that comparison.
    let currentHasMetadata := (currentSource.find? fun
      | .mdata .. => true
      | _ => false).isSome
    if !currentSource.hasFVar && !currentSource.hasLooseBVars &&
        !currentSource.hasExprMVar && !currentSource.hasLevelMVar &&
        !currentHasMetadata then return none
    let left ←
      capturedTypeReferences context inputProjections retainedInputs supplied marks
        originalSource reduce
    let right ←
      capturedTypeReferences context inputProjections retainedInputs supplied marks
        currentSource reduce
    if left.isEmpty || right.isEmpty then
      -- A closed native type contributes no competing runtime supplier. Any real source
      -- local/mark must instead resolve to its explicitly retained position.
      let unresolved := fun (expression : Expr) => expression.hasFVar || hasSourceMarks expression
      return some (!(if left.isEmpty then unresolved originalSource else unresolved currentSource))
    for first in left do
      for second in right do
        unless ← sameCapturedTypeReference graph first second do return some false
    return some true
  let typeReferences := fun (expression : Expr) => do
    try markedContextReferences (some graph) context marks expression
    catch error =>
      if error.toMessageData.hasTag (· == `CasRuntime.missingSourceMark) then
        throwError "the runtime value has an unresolved consuming dependent type"
      throw error
  let expectedMarks ← typeReferences expected
  let typeHasMarks := fun (expression : Expr) => do
    if hasSourceMarks expression then return true
    let dependencies ← computationalDependencies (context.bindings.map (·.expression)) expression
    for index in dependencies do
      let some binding := context.bindings[index]?
        | throwError "a native type dependency is outside its complete context"
      let declaration ← getFVarLocalDecl binding.expression
      if hasSourceMarks declaration.type ||
          (declaration.value? true).any hasSourceMarks then return true
    return false
  let typeSources := #[value.role.source, origin.role.source] ++
    value.markedTypeRoles.map (·.source)
  for source in typeSources do
    let originalType ← inferType (← source.inContext context)
    if !expectedMarks.isEmpty || (← typeHasMarks originalType) then
      let some _ ← dependencyTerms sameContextReference #[] originalType expected #[]
          (some compareCaptured) (some sourceView)
        | throwError "the runtime value has a different marked source type dependency"
  if value.instantiations.all (·.precedingDependencies.isEmpty) then return ()
  let dependencies ← computationalDependencies (context.bindings.map (·.expression)) expected
  let markedDependencies ← markedSourceReferences (some graph) context marks expected
  let mut references : Array (LocalBinding × (BindingId × Array Name)) := #[]
  for index in dependencies do
    let some dependency := context.bindings[index]?
      | throwError "a consuming runtime dependency is outside its current source telescope"
    if let some reference ← dependencyReference context inputs
        (← context.close dependency.expression) then
      references := references.push (dependency, reference)
  let hasDependencies := !references.isEmpty || !markedDependencies.isEmpty
  for instantiation in value.instantiations do
    if instantiation.precedingDependencies.isEmpty then continue
    let family ← instantiation.typeFamily.inContext context
    let inspect := fun locals type => do
      unless locals.size ≥ instantiation.preceding.size do
        throwError "a consuming runtime dependency lost its complete native prefix"
      dependencyTerms sameContextReference locals type expected
    let terms ← if instantiation.view.isSome then lambdaTelescope family inspect
      else lambdaBoundedTelescope family instantiation.preceding.size inspect
    for index in instantiation.precedingDependencies do
      let some previous := instantiation.preceding[index]?
        | throwError "a consuming runtime dependency is outside its complete field prefix"
      if let some original := previous then
        unless (instantiation.association.layout.fields[index]?).isSome do
          throwError "a consuming runtime dependency is outside its source record"
        let some terms := terms
          | if !hasDependencies then continue
            throwError "the runtime value has an unresolved consuming dependent type"
        let selected := terms.filterMap fun (slot, term) => if slot == index then some term else none
        if selected.isEmpty && hasDependencies then
          throwError "the runtime value has an unresolved consuming dependent slot"
        let mut unresolved : Option Expr := none
        for term in selected do
          let source ← dependencySource (← context.close term)
          let term ← source.inContext context
          if let some (key, path) ← markedProjection? term then
            let some (_, parent) := marks.find? (·.1 == key)
              | throwError "a consuming dependent type lost its captured occurrence mark"
            let current ← if !currentPrefixes.isEmpty && pending.isSome then
                pendingDependency graph parent path pending
              else storedDependency graph parent path
            match current with
            | some current =>
              unless sameReference original current do
                throwError "the runtime value has a different marked dependent reference ({term})"
            | none =>
              unless hasDependencyAccess graph original parent path do
                throwError "the runtime value has an unresolved marked dependent reference ({term})"
            continue
          let some reference ← dependencyReference context inputs source
            | if term.hasFVar && unresolved.isNone then unresolved := some term
              continue
          let mut matched := false
          for (dependency, selectedReference) in references do
            if selectedReference != reference then continue
            matched := true
            let some current := supplied[dependency.id]?
              | throwError (MessageData.tagged (missingValueTag dependency.id)
                  m!"the runtime value is missing a consuming dependent reference \
                    ({dependency.expression})")
            unless sameReference original current do
              throwError "the runtime value has a different consuming dependent reference \
                ({dependency.expression})"
          if !reference.2.isEmpty then
            let fieldMatched := matched
            for (dependency, selectedReference) in references do
              unless selectedReference == (reference.1, #[]) do continue
              let some parent := supplied[dependency.id]?
                | if fieldMatched then continue
                  throwError (MessageData.tagged (missingValueTag dependency.id)
                    m!"the runtime value is missing a consuming dependent reference \
                      ({dependency.expression})")
              let current ← if !currentPrefixes.isEmpty && pending.isSome then
                  pendingDependency (← graphFor dependency.id) parent reference.2 pending
                else storedDependency (← graphFor dependency.id) parent reference.2
              match current with
              | some current =>
                unless sameReference original current do
                  dbg_trace "[dependent.identity] field={instantiation.field.projection} slot={index} source={repr reference.1} path={repr reference.2} parent={repr parent.value} parentAssociations={repr parent.associationIds} original={repr original.value} originalAssociations={repr original.associationIds} current={repr current.value} currentAssociations={repr current.associationIds}"
                  -- Failure-only inspection of the exact field occurrence. Native checks,
                  -- input routing and the rejection below are unchanged.
                  try
                    withoutModifyingState do
                      let rec shape (locals : Array Expr) (fuel : Nat) (expression : Expr) :
                          String :=
                        match fuel with
                        | 0 =>
                          match expression.getAppFn with
                          | .const name _ => s!"{name}"
                          | .fvar id => s!"fvar({id.name})"
                          | .forallE .. => "forall"
                          | .lam .. => "lambda"
                          | .mdata .. => "metadata"
                          | .proj name field _ => s!"projection({name},{field})"
                          | _ => "..."
                        | remaining + 1 =>
                          match expression with
                          | .fvar id =>
                            match locals.findIdx? (· == expression) with
                            | some position => s!"prefix({position})"
                            | none =>
                              match context.bindings.find? (·.expression == expression) with
                              | some binding => s!"context({reprStr binding.id})"
                              | none => s!"fvar({id.name})"
                          | .bvar position => s!"bound({position})"
                          | .sort levelValue => s!"sort({reprStr levelValue})"
                          | .const name levels => s!"constant({name},{levels.length})"
                          | .lit literal => s!"literal({reprStr literal})"
                          | .mvar id => s!"metavariable({id.name})"
                          | .mdata _ body => s!"metadata({shape locals remaining body})"
                          | .proj name field body =>
                            s!"projection({name},{field},{shape locals remaining body})"
                          | .app .. =>
                            let arguments := expression.getAppArgs
                            let shown := (arguments.extract 0 4).map
                              (shape locals remaining)
                            s!"application({shape locals remaining expression.getAppFn};arity={arguments.size};{String.intercalate "," shown.toList})"
                          | .forallE name domain body info =>
                            s!"forall({name},{reprStr info};{shape locals remaining domain};{shape locals remaining body})"
                          | .lam name domain body info =>
                            s!"lambda({name},{reprStr info};{shape locals remaining domain};{shape locals remaining body})"
                          | .letE name domain assigned body _ =>
                            s!"let({name};{shape locals remaining domain};{shape locals remaining assigned};{shape locals remaining body})"
                      dbg_trace "[dependent.detail] candidate={repr value.value} associationCount={value.associationIds.size} associations={repr (value.associationIds.extract 0 8)} kind={repr value.role.kind} fieldView={repr instantiation.projectionPath} precedingCount={instantiation.preceding.size} required={repr instantiation.precedingDependencies} currentPrefixCount={currentPrefixes.size}"
                      let payloadKind (binding : ValueBinding) : Option String :=
                        (graph.find binding.value).map fun node =>
                          match node.payload.data with
                          | .portable _ => "portable"
                          | .product fields => s!"product({fields.size})"
                          | .container packet => s!"container(fields={packet.fields.map (·.size)})"
                          | .closure program captures =>
                            s!"closure({reprStr program};captures={captures.size})"
                          | .ownedToken _ _ captures => s!"owned(captures={captures.size})"
                      dbg_trace "[dependent.detail] candidatePayload={payloadKind value} prefixPayload={payloadKind original} suppliedPayload={payloadKind current}"
                      dbg_trace "[dependent.detail] candidateSource={shape #[] 4 value.role.source.expression}"
                      dbg_trace "[dependent.detail] producingSource={shape #[] 4 origin.role.source.expression}"
                      dbg_trace "[dependent.detail] prefixSource={shape #[] 4 original.role.source.expression}"
                      dbg_trace "[dependent.detail] prefixProducer={(graph.find original.value).map (fun node => shape #[] 4 node.origin.role.source.expression)}"
                      dbg_trace "[dependent.detail] suppliedSource={shape #[] 4 current.role.source.expression}"
                      dbg_trace "[dependent.detail] fieldSource={shape #[] 4 instantiation.field.source.expression}"
                      dbg_trace "[dependent.detail] recordSource={shape #[] 4 instantiation.association.layout.source.source.expression}"
                      dbg_trace "[dependent.detail] expected={shape #[] 5 expected}"
                      dbg_trace "[dependent.detail] selectedCount={selected.size} selected={repr ((selected.extract 0 6).map (shape #[] 5))}"
                      let inspectFailure := fun locals body => do
                        dbg_trace "[dependent.detail] formalPrefixCount={locals.size} formalType={shape locals 5 body}"
                        for parameter in locals, position in [:locals.size] do
                          if position < instantiation.preceding.size && position < 8 then
                            dbg_trace "[dependent.detail] prefixSlot={position} type={shape locals 4 (← inferType parameter)} original={repr (((instantiation.preceding[position]?).bind id).map (·.value))}"
                      if instantiation.view.isSome then
                        lambdaTelescope family inspectFailure
                      else
                        lambdaBoundedTelescope family instantiation.preceding.size inspectFailure
                  catch _ => pure ()
                  throwError (MessageData.tagged
                    `CasRuntime.RuntimeEnvironment.dependentReferenceMismatch
                    m!"the runtime value has a different consuming dependent reference ({term})")
              | none =>
                unless hasDependencyAccess graph original parent reference.2 do
                  throwError "the runtime value has an unresolved consuming dependent reference ({term})"
              matched := true
          unless matched do
            let some dependency := context.bindings.find? (·.id == reference.1)
              | throwError "a consuming dependent reference is outside its source telescope"
            throwError (MessageData.tagged (missingValueTag dependency.id)
              m!"the runtime value is missing a consuming dependent reference ({dependency.expression})")
        let mut covered := false
        for current in currentPrefixes do
          if let some (routes, complete) ← currentPrefixRoutes context inputs graph instantiation index current then
            covered := covered || complete
            for (parent, path) in routes do
              match ← storedDependency graph parent path with
              | some actual =>
                unless sameReference original actual do
                  throwError "the runtime value has a different consuming dependent reference \
                    in its current result prefix; field={instantiation.field.projection}; \
                    slot={index}; currentField={current.field.projection}; \
                    path={reprStr path}; parent={reprStr parent.value}; \
                    original={reprStr original.value}; originalAssociations={reprStr original.associationIds}; \
                    actual={reprStr actual.value}; actualAssociations={reprStr actual.associationIds}; \
                    originalSource={(graph.find original.value).map (·.origin.role.source.expression)}; \
                    actualSource={(graph.find actual.value).map (·.origin.role.source.expression)}; \
                    originalRecord={instantiation.association.layout.source.source.expression}; \
                    currentRecord={current.layout.source.source.expression}; \
                    preceding={reprStr (instantiation.preceding.map (·.map (·.value)))}"
              | none =>
                unless hasDependencyAccess graph original parent path do
                  throwError "the runtime value has an unresolved consuming dependent reference \
                    in its current result prefix"
        if !covered then
          if let some term := unresolved then
            throwError "the runtime value has an unresolved consuming dependent reference ({term})"

/-- Associate existing nodes by stable source identity, native type and retained type dependencies.
Check the complete table before comparing each actual producing dependency with its current
binding. Reuse: ClosedTerm.inContext, Lean.Meta.isDefEq and SourceLayout.contextDependencies.
Consuming field dependencies align their native prefix slots with the expected type, then check
the selected source binding or projection against its retained reference.
Later consuming roles may extend the original reference's complete instantiation chain.
Whole-reply admission remains a separate check. -/
opaque RuntimeEnvironment.capture (worker : String) (context : OpenContext)
    (parameters : Array RuntimeParameter)
    (sourceMarks : Array (Nat × ValueBinding) := #[])
    (sourceGraph : Option ValueGraph := none) : MetaM RuntimeEnvironment := do
  if worker.isEmpty then throwError "runtime association requires an actual worker identity"
  let inputProjections ← context.inputProjections
  let mut sourceMarks := sourceMarks
  for parameter in parameters do
    sourceMarks ← IO.ofExcept <|
      (mergeSourceMarks sourceMarks parameter.origin.sourceMarks).mapError IO.userError
    sourceMarks ← IO.ofExcept <|
      (mergeSourceMarks sourceMarks parameter.value.sourceMarks).mapError IO.userError
  if let some graph := sourceGraph then
    unless graph.worker == worker do
      throwError "marked source preparation belongs to a different worker"
    discard <| IO.ofExcept <|
      (graph.requiredOwners (sourceMarks.map (·.2))).mapError IO.userError
  let mut supplied : Std.HashMap BindingId ValueBinding := {}
  for parameter in parameters do
    if supplied.contains parameter.source then
      throwError "a source binder has duplicate runtime associations"
    unless parameter.value.value.worker == worker do
      throwError "a runtime source binding belongs to a different worker"
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a runtime association names a source binder outside the complete telescope"
    let expected ← inferType source.expression
    if ← isProp expected then
      throwError "a source proof has no runtime value association"
    checkNativeType context expected parameter.value parameter.origin
    let role ← SourceLayout.ofTerm (← context.close source.expression)
    let marks ← IO.ofExcept <| (retainedSourceMarks sourceMarks role.source).mapError IO.userError
    let dependencies ← markedTypeReferences sourceGraph role.source marks
    let .ok value := parameter.value.withRole role marks dependencies
      | throwError "the source binder has no computational runtime role"
    supplied := supplied.insert parameter.source value
  for parameter in parameters do
    let some source := context.bindings.find? (·.id == parameter.source)
      | throwError "a consuming runtime binding is outside its source telescope"
    let graphFor := fun id => do
      let some parameter := parameters.find? (·.source == id)
        | throwError "a retained dependent reference lost its supplying graph"
      pure parameter.graph
    checkDependencies context inputProjections supplied sourceMarks
      (sourceGraph.getD parameter.graph) graphFor
      (← inferType source.expression) parameter.value parameter.origin
  let values := context.bindings.map fun binding => supplied[binding.id]?
  return ⟨worker, context.telescope, values, inputProjections, sourceMarks, sourceGraph⟩

/-- Whether a source parent already has an explicit runtime occurrence.
Formal selected instances have none; runtime-bound class values keep the same exact identity
as other values. Reuse: stable binding lookup, retained-value marks and native projections. -/
partial def RuntimeEnvironment.hasRetainedSource (environment : RuntimeEnvironment)
    (context : OpenContext) (specified : Expr) : MetaM Bool := do
  if let .mdata data body := specified then
    if (markedKey? data).isSome then return true
    if data.contains `CasCompiler.source.objectOrigin then
      let some (_, original) ← sourceObjectOrigin? specified
        | throwError "the source object lost its retained original parameter"
      return ← environment.hasRetainedSource context original
    if (data.find `CasCompiler.source.kind).isSome ||
        (data.find `CasCompiler.selection).isSome then return false
    return ← environment.hasRetainedSource context body
  if let .letE _ _ value body _ := specified then
    return ← environment.hasRetainedSource context (body.instantiate1 value)
  if specified.isFVar then
    let some binding := context.bindings.find? (·.expression == specified)
      | throwError "the source argument is outside the complete runtime telescope"
    match environment.lookup binding.id with
    | .ok (some _) => return true
    | .ok none =>
      if let some definition := (← specified.fvarId!.getDecl).value? then
        return ← environment.hasRetainedSource context definition
      return false
    | .error reason => throwError "the source argument is outside its telescope: {reason}"
  if let some projection ← SourceProjection.ofExpr? specified then
    return ← environment.hasRetainedSource context projection.parent
  return false

/-- Check an operand's retained source selection. Projection names describe the already
selected path; the parent comes only from that value's association or producing origin.
Native conversion may check other expressions, but never chooses a projected parent. -/
private partial def RuntimeEnvironment.retainsSourceReference (environment : RuntimeEnvironment)
    (context : OpenContext) (graph : ValueGraph) (marks : Array ValueBinding)
    (specified : Expr) (value : ValueBinding) (requireAnchor : Bool := false)
    (anchored : Bool := false) : MetaM Bool := do
  if let .mdata data body := specified then
    if let some key := markedKey? data then
      let some selected := marks[key]?
        | throwError "the source argument lost its retained occurrence mark"
      let .ok _ := graph.requiredOwners #[selected]
        | throwError "the source argument's marked occurrence is outside the visible graph"
      unless retainsReference selected value do return false
      -- A mark adds an identity constraint; it cannot replace a variable or field constraint.
      return ← environment.retainsSourceReference context graph marks body value requireAnchor true
    if data.contains `CasCompiler.source.objectOrigin then
      let some (_, original) ← sourceObjectOrigin? specified
        | throwError "the source object lost its retained original parameter"
      return ← environment.retainsSourceReference context graph marks original value requireAnchor anchored
    if (data.find `CasCompiler.source.kind).isNone &&
        (data.find `CasCompiler.selection).isNone then
      return ← environment.retainsSourceReference context graph marks body value requireAnchor anchored
  if specified.isFVar then
    let some binding := context.bindings.find? (·.expression == specified)
      | throwError "the source argument is outside the complete runtime telescope"
    match environment.lookup binding.id with
    | .ok (some retained) => return retainsReference retained value
    | .ok none =>
      let some definition := (← specified.fvarId!.getDecl).value?
        | throwError "the source argument has no retained runtime binding"
      return ← environment.retainsSourceReference context graph marks definition value requireAnchor anchored
    | .error reason => throwError "the source argument is outside its telescope: {reason}"
  let projection ← SourceProjection.ofExpr? specified
  let runtimeProjection ← match projection with
    | none => pure false
    | some projection =>
      if !projection.info.fromClass then pure true
      else environment.hasRetainedSource context projection.parent
  if runtimeProjection then
    let some node := graph.find value.value
      | throwError "the runtime argument is outside the visible graph"
    let mut selected := value.projectionAccesses
    if let some parent := node.origin.access then
      selected := selected.push (parent, node.origin.accessPath)
    for (parent, path) in selected do
      if path.isEmpty then continue
      let mut original := specified
      let mut matchedPath := true
      for projection in path.reverse do
        let some step ← SourceProjection.ofExpr? original
          | matchedPath := false; break
        unless step.declaration == projection do
          matchedPath := false
          break
        original := step.parent
      if matchedPath then
        if ← environment.retainsSourceReference context graph marks original parent true then return true
    return false
  if requireAnchor && !anchored then return false
  let original ← value.role.source.inContext context
  return ← isDefEq original specified

/-- Bind the supplied operand to its actual source argument, rather than a same-typed value.
Source variables use their stable-ID runtime association. A projection retains the exact path
and selected parent. Reuse: complete type/dependency checks and native projection metadata. -/
opaque RuntimeEnvironment.checkArgument (environment : RuntimeEnvironment) (source : ClosedTerm)
    (argument : RuntimeArgument) : MetaM ValueBinding := do
  unless argument.value.value.worker == environment.worker do
    throwError "the runtime argument belongs to a different worker"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let specified ← source.inContext context
    let expected ← inferType specified
    if ← isProp expected then throwError "a formal proof argument has no runtime value binding"
    checkNativeType context expected argument.value argument.origin
    let marks ← IO.ofExcept <| (argument.sourceMarks source).mapError IO.userError
    let marks ← IO.ofExcept <|
      (mergeSourceMarks environment.sourceMarks marks).mapError IO.userError
    let marks ← IO.ofExcept <|
      (mergeSourceMarks marks argument.value.sourceMarks).mapError IO.userError
    let marks ← IO.ofExcept <|
      (mergeSourceMarks marks argument.origin.sourceMarks).mapError IO.userError
    checkDependencies context environment.inputProjections environment.bindingMap marks
      argument.graph (fun _ => pure argument.graph)
      expected argument.value argument.origin
    unless ← environment.retainsSourceReference context argument.graph argument.marks
        specified argument.value do
      trace[cas.environment] "argument {argument.index}: {specified}; retained source {← argument.value.role.source.inContext context}"
      throwError (MessageData.tagged `CasRuntime.RuntimeEnvironment.sourceReferenceMismatch
        "the runtime argument does not retain its specified source value")
    let role ← SourceLayout.ofTerm (← context.close specified)
    let selectedMarks ← IO.ofExcept <| (retainedSourceMarks marks role.source).mapError IO.userError
    let dependencies ← markedTypeReferences (some argument.graph) role.source selectedMarks
    let .ok value := argument.value.withRole role selectedMarks dependencies
      | throwError "the source argument has no computational runtime role"
    return value

/-- Check a retained candidate at the prepared result's complete native type and actual indexes.
Reuse: the source-binding type/dependency checks and CandidateResponse's operational shape check.
The graph supplies the immutable producing provenance; liveness and publication are later gates. -/
private partial def checkResultValue (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding)
    (currentPrefixes : Array ResultFieldPrefix := #[])
    (pending : Option PendingResultProjection := none) : MetaM (CandidateResponse source) := do
  unless graph.worker == environment.worker do
    throwError "the prepared result belongs to a different worker"
  let .ok _ := graph.requiredOwners (environment.references.push value)
    | throwError "the prepared result or its runtime context is outside the visible graph"
  let some node := graph.find value.value
    | throwError "the prepared result is outside the visible graph"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let expected ← inferType (← source.source.inContext context)
    checkNativeType context expected value node.origin
    let marks ← IO.ofExcept <|
      (mergeSourceMarks environment.sourceMarks value.sourceMarks).mapError IO.userError
    let marks ← IO.ofExcept <|
      (mergeSourceMarks marks node.origin.sourceMarks).mapError IO.userError
    checkDependencies context environment.inputProjections environment.bindingMap marks graph
      (fun _ => pure graph) expected value node.origin currentPrefixes pending
    let selectedMarks ← IO.ofExcept <|
      (retainedSourceMarks marks source.source).mapError IO.userError
    let dependencies ← markedTypeReferences (some graph) source.source selectedMarks
    let value ← IO.ofExcept <|
      (value.withRole source selectedMarks dependencies).mapError IO.userError
    let candidate ← match CandidateResponse.ofValue source graph value with
      | .ok candidate => pure candidate
      | .error reason =>
        throwError "the prepared result has an incompatible computational interface: {reason} \
          at {← source.source.inContext context}"
    let stored := node.payload.data.storedFields?.isSome
    if source.kind == .record && stored then
      let layout ← RecordLayout.ofSource source
      for prepared in layout.fields do
        if let some index := prepared.field.wireIndex then
          let field ← IO.ofExcept <| (graph.project candidate.root index).mapError IO.userError
          let prefixes ← currentPrefixes.mapM (·.descend prepared.field.projection)
          discard <| checkResultValue environment graph prepared.layout field
            (prefixes.push ⟨candidate.root, layout, prepared.field, none⟩) pending
    return candidate

/-- Validate the complete stored result through its source-derived native field layouts.
Reuse: RecordLayout, graph projection and the same native type/dependency check at every node.
Exported records retain their lazy interface; stored records validate all retained children. -/
opaque RuntimeEnvironment.checkResult (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding) : MetaM (CandidateResponse source) :=
  checkResultValue environment graph source value

/-- Exact original parent/field witnesses along an already chosen path. Ancestors must be
stored or published; this helper neither evaluates an input nor chooses from candidate history. -/
private def projectionPrefixes (graph : ValueGraph) (operand : ValueBinding)
    (path : Array Name) : MetaM (Array ResultFieldPrefix × FieldLayout) := do
  let mut parent := operand
  let mut parentSource := operand.role
  let mut prefixes : Array ResultFieldPrefix := #[]
  let mut selectedField : Option FieldLayout := none
  for projection in path, index in [:path.size] do
    let layout ← RecordLayout.ofSource parentSource
    let some declared := layout.fields.find? (·.field.projection == projection)
      | throwError "the pending projection is outside its original native parent"
    unless declared.field.wireIndex.isSome do
      throwError "a composed projection passed through a proof field"
    let some actualField := parent.role.fields.find? (·.projection == projection)
      | throwError "the retained projection parent lost its declared field"
    unless actualField.sourceIndex == declared.field.sourceIndex &&
        actualField.wireIndex == declared.field.wireIndex do
      throwError "the retained projection parent changed its native field position"
    prefixes ← prefixes.mapM (·.descend projection)
    prefixes := prefixes.push ⟨parent, layout, declared.field, none⟩
    selectedField := some declared.field
    if index + 1 < path.size then
      let selected ← IO.ofExcept <|
        (graph.projectionFrontier parent #[projection]).mapError IO.userError
      let some (selected, remaining) := selected
        | throwError "a composed projection lost its retained intermediate parent"
      unless remaining.isEmpty do
        throwError "a composed projection cannot manufacture an intermediate parent"
      parent := selected
      parentSource := declared.layout
  let some field := selectedField
    | throwError "a retained projection requires its original native field path"
  return (prefixes, field)

/-- Follow only the actual operand's latest projection and its original selected parents.
Each link must retain its exact native source and complete stored selection before inherited
prefixes descend through that link. Newer applications stop the retained projection chain. -/
private partial def retainedOperandPrefixes (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (operand : ValueBinding) : MetaM (Array ResultFieldPrefix) := do
  let selected ← IO.ofExcept <| (graph.projectionSelection operand).mapError IO.userError
  let some (originalSource, parent, path) := selected
    | return #[]
  let (prefixes, field) ← projectionPrefixes graph parent path
  let nativeSource ← field.toLayout
  let originalMatches ← originalSource.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let mut previous : Option Nat := none
    for entry in nativeSource.source.context.entries do
      let some index := bindings.findIdx? (·.id == entry.id) | return false
      if let some prior := previous then
        if index ≤ prior then return false
      previous := some index
    return (← originalSource.source.inContext context) ==
      (← nativeSource.source.inContext context)
  unless originalMatches do return #[]
  let authentic ← environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let mut inputs := #[]
    for binding in bindings do
      unless ← isProp (← inferType binding.expression) do inputs := inputs.push binding.id
    if let some (id, aliasPath) ← dependencyReference context inputs source.source then
      let some supplied := environment.bindingMap[id]? | return false
      match ← storedDependency graph supplied aliasPath with
      | some actual => return retainsReference actual operand
      | none => return false
    let stated ← source.source.inContext context
    let original ← originalSource.source.inContext context
    return stated == original
  unless authentic do return #[]
  let retained ← IO.ofExcept <|
    (graph.projectionFrontier parent path).mapError IO.userError
  let some (baseline, remaining) := retained
    | throwError "the retained operand lost its original selected field"
  unless remaining.isEmpty && retainsReference baseline operand do
    throwError "the retained operand changed its original selected field"
  let mut inherited ← retainedOperandPrefixes environment graph parent.role parent
  for projection in path do inherited ← inherited.mapM (·.descend projection)
  return inherited ++ prefixes

/-- Validate the native result of this exact pending field demand, including all stored
descendants. Only the declared field of the retained operand can be temporarily unavailable;
existing selections keep their node and association chain. The witness is read-only and lives
only during this complete check, before any projection association is published. -/
opaque RuntimeEnvironment.checkProjectionResult (environment : RuntimeEnvironment)
    (graph : ValueGraph) (source : SourceLayout) (value operand : ValueBinding)
    (field : FieldLayout) : MetaM (CandidateResponse source) := do
  let path ← operand.role.projectionPathTo source
  unless !path.isEmpty && path.back? == some field.projection do
    throwError "the pending projection changed its exact native source field"
  let (current, declared) ← projectionPrefixes graph operand path
  unless field.sourceIndex == declared.sourceIndex && field.projection == declared.projection do
    throwError "the pending projection changed its original native field"
  let mut prefixes ← retainedOperandPrefixes environment graph operand.role operand
  for projection in path do prefixes ← prefixes.mapM (·.descend projection)
  prefixes := prefixes ++ current
  let pending : Option PendingResultProjection ← if path.size > 1 then do
      let selected ← IO.ofExcept <|
        (graph.projectionFrontier operand path).mapError IO.userError
      let some (retained, remaining) := selected
        | throwError "a composed projection lost its complete stored source path"
      unless remaining.isEmpty && retainsReference retained value do
        throwError "a composed projection changed its retained field reference"
      pure none
    else do
      if let some retained ← pendingDependency graph operand #[field.projection] none then
        unless retainsReference retained value do
          throwError "the projection changed its retained field reference"
      pure (some ⟨operand, field.projection, value⟩)
  -- Every prefix comes from this exact prepared path. All applicable original-slot routes
  -- must agree; neither a candidate ancestor nor a convertible source chooses a witness.
  checkResultValue environment graph source value prefixes pending

/-- Admit an already selected operand at its independently prepared input source. Only its
authenticated original projection chain or exact named alias may supply native prefixes.
Ordinary candidate output admission never consults this input-only witness. -/
opaque RuntimeEnvironment.checkOperand (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (operand : ValueBinding) : MetaM (CandidateResponse source) := do
  let prefixes ← retainedOperandPrefixes environment graph source operand
  checkResultValue environment graph source operand prefixes

/-- Stamp a produced node with its complete ordered actual context references.
Reuse: SourceLayout.inContext transports the checked role by stable source identities.
Result-type dependency selection is mechanical source metadata, not candidate decoding. -/
opaque RuntimeEnvironment.origin (environment : RuntimeEnvironment)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (role : SourceLayout) : MetaM ValueOrigin := do
  unless program.worker == environment.worker && occurrence.worker == environment.worker do
    throwError "the producing runtime context belongs to a different worker"
  let role ← if role.source.context.exactlyMatches environment.context then pure role
    else environment.context.withOpen fun bindings => do
      let context ← ContextTelescope.capture bindings
      role.inContext context
  let marks ← IO.ofExcept <|
    (retainedSourceMarks environment.sourceMarks role.source).mapError IO.userError
  let dependencies ← markedTypeReferences environment.sourceGraph role.source marks
  return {
    program, occurrence, role, parameters := environment.values
    sourceMarks := marks, sourceDependencies := dependencies }

end CasRuntime
