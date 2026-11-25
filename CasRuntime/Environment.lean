module

public import CasRuntime.Value

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
  captureSourceMarks argument.marks source

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

/-- Resolve a native consuming-type slot through the source positions captured before
runtime association. Original context locals stay opaque; selected aliases use their
retained BindingId/path, and marked or computational boundaries remain unrouteable.
Reuse: ClosedTerm.inputProjectionAt and OpenContext.inputProjections. -/
private def dependencyReference (inputProjections : Std.HashMap BindingId InputProjection)
    (inputs : Array BindingId) (source : ClosedTerm) (path : Array Name := #[]) :
    MetaM (Option (BindingId × Array Name)) := do
  let some selected ← source.inputProjectionAt path inputs | return none
  let .context id := selected.target
    | throwError "a context dependency selected a nonexistent application argument"
  let some original := inputProjections[id]?
    | throwError "a dependent source reference is outside its captured source positions"
  let .context binding := original.target
    | throwError "a captured context dependency acquired an application argument"
  return some (binding, original.path ++ selected.path)

/-- Align the original field's abstract prefix slots with their positions in the expected
native type. Equality of runtime values or convertible source binders never selects a slot.
Slot domains recover earlier transitive dependencies. The complete native type check already
validates universes; head normalization exposes type aliases while current let binders stay frozen.
Fixed context subterms may agree through their previously captured source positions. -/
private partial def dependencyTerms (sameContextReference : Expr → Expr → MetaM Bool)
    (locals : Array Expr) (formal expected : Expr)
    (binders : Array (Expr × Expr) := #[])
    (capturedReference : Option (Bool → Expr → Expr → MetaM (Option Bool)) := none)
    (sourceView : Option (Expr → MetaM Expr) := none) (capturedReduction : Bool := true) :
    MetaM (Option (Array (Nat × Expr))) := do
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
        capturedReference sourceView capturedReduction
    | .mdata _ body, _ =>
      return ← dependencyTerms sameContextReference locals body originalExpected binders
        capturedReference sourceView capturedReduction
    | _, .mdata _ body =>
      return ← dependencyTerms sameContextReference locals originalFormal body binders
        capturedReference sourceView capturedReduction
    | _, _ => pure ()
  if let some index := locals.findIdx? (· == formal) then
    if expected.hasLooseBVars then return none
    let proof ← isProof formal
    let freeVariables := collectFVars {} expected
    if !proof && binders.any (fun (_, bound) => freeVariables.fvarSet.contains bound.fvarId!) then
      return none
    let some preceding ← dependencyTerms sameContextReference (locals.extract 0 index)
        (← inferType formal) (← inferType expected) binders
        capturedReference sourceView capturedReduction | return none
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
        capturedReference sourceView capturedReduction)
        (dependencyTerms sameContextReference locals a b binders
          capturedReference sourceView capturedReduction)
    | .forallE name a b info, .forallE other c d otherInfo
    | .lam name a b info, .lam other c d otherInfo => do
      let some domains ← dependencyTerms sameContextReference locals a c binders
          capturedReference sourceView capturedReduction | return none
      withLocalDecl name info a fun source =>
        withLocalDecl other otherInfo c fun target => do
          let some bodies ← dependencyTerms sameContextReference locals
              (b.instantiate1 source) (d.instantiate1 target) (binders.push (source, target))
              capturedReference sourceView capturedReduction
            | return none
          return some (domains ++ bodies)
    | .proj owner index parent, .proj other otherIndex otherParent =>
      if owner == other && index == otherIndex then
        dependencyTerms sameContextReference locals parent otherParent binders
          capturedReference sourceView capturedReduction
      else pure none
    | _, _ => pure none
  if matched.isSome then return matched
  if ← sameContextReference originalFormal originalExpected then return some #[]
  let normalize := fun (original expression : Expr) => do
    if let some view := sourceView then
      if capturedReduction && !original.hasLooseBVars then view original else pure original
    else if expression.hasLooseBVars then pure expression
    else withConfig (fun config => { config with zetaDelta := false }) (whnf expression)
  let normalizedFormal ← normalize originalFormal formal
  let normalizedExpected ← normalize originalExpected expected
  if normalizedFormal == formal && normalizedExpected == expected then return none
  dependencyTerms sameContextReference locals normalizedFormal normalizedExpected binders
    capturedReference sourceView capturedReduction

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
      | throwError "a native type lost its captured occurrence mark"
    return #[(parent, path)]
  let reference ← if reduce then
      dependencyReference inputProjections inputs (← context.close expression)
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
    (value : ValueBinding) (origin : ValueOrigin) : MetaM Unit := do
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
    dependencyReference inputProjections inputs (← context.close expression)
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
  let expectedMarks ← markedContextReferences (some graph) context marks expected
  let typeSources := #[value.role.source, origin.role.source] ++
    value.markedTypeRoles.map (·.source)
  for source in typeSources do
    let originalType ← inferType (← source.inContext context)
    let originalMarks ← markedContextReferences (some graph) context marks originalType
    if !originalMarks.isEmpty || !expectedMarks.isEmpty then
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
    if let some reference ← dependencyReference inputProjections inputs
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
        for term in selected do
          -- Source routing and its unresolved-reference check must inspect the same structural
          -- view. A constructor projection can discard a source local without selecting it.
          let endpoint ← (← context.close term).inputProjectionSource inputs
          let expression ← endpoint.inContext context
          if let some (key, path) ← markedProjection? expression then
            let some (_, parent) := marks.find? (·.1 == key)
              | throwError "a consuming dependent type lost its captured occurrence mark"
            let current ← storedDependency graph parent path
            match current with
            | some current =>
              unless sameReference original current do
                throwError "the runtime value has a different marked dependent reference ({term})"
            | none =>
              unless hasDependencyAccess graph original parent path do
                throwError "the runtime value has an unresolved marked dependent reference ({term})"
            continue
          let some reference ← dependencyReference inputProjections inputs endpoint
            | if expression.hasFVar then
                throwError "the runtime value has an unresolved consuming dependent reference \
                  ({expression})"
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
              let current ← storedDependency (← graphFor dependency.id) parent reference.2
              match current with
              | some current =>
                unless sameReference original current do
                  throwError "the runtime value has a different consuming dependent reference ({term})"
              | none =>
                unless hasDependencyAccess graph original parent reference.2 do
                  throwError "the runtime value has an unresolved consuming dependent reference ({term})"
              matched := true
          unless matched do
            let some dependency := context.bindings.find? (·.id == reference.1)
              | throwError "a consuming dependent reference is outside its source telescope"
            throwError (MessageData.tagged (missingValueTag dependency.id)
              m!"the runtime value is missing a consuming dependent reference ({dependency.expression})")

/-- Associate existing nodes by stable source identity, native type and retained type dependencies.
Check the complete table before comparing each actual producing dependency with its current
binding. Reuse: ClosedTerm.inContext, Lean.Meta.isDefEq and SourceLayout.contextDependencies.
Consuming field dependencies align their native prefix slots with the expected type, then
join the selected source term through the original captured BindingId/projection map.
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
    checkDependencies context inputProjections supplied sourceMarks parameter.graph graphFor
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
    if (data.find `CasCompiler.source.kind).isSome ||
        (data.find `CasCompiler.selection).isSome then return false
    return ← environment.hasRetainedSource context body
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
    checkDependencies context environment.inputProjections environment.bindingMap marks
      argument.graph (fun _ => pure argument.graph)
      expected argument.value argument.origin
    unless ← environment.retainsSourceReference context argument.graph argument.marks
        specified argument.value do
      trace[cas.environment] "argument {argument.index}: {specified}; retained source {← argument.value.role.source.inContext context}"
      throwError "the runtime argument does not retain its specified source value"
    let role ← SourceLayout.ofTerm (← context.close specified)
    let selectedMarks ← IO.ofExcept <| (retainedSourceMarks marks role.source).mapError IO.userError
    let dependencies ← markedTypeReferences environment.sourceGraph role.source selectedMarks
    let .ok value := argument.value.withRole role selectedMarks dependencies
      | throwError "the source argument has no computational runtime role"
    return value

/-- Check a retained candidate at the prepared result's complete native type and actual indexes.
Reuse: the source-binding type/dependency checks and CandidateResponse's operational shape check.
The graph supplies the immutable producing provenance; liveness and publication are later gates. -/
private partial def checkResultValue (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding) : MetaM (CandidateResponse source) := do
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
      (fun _ => pure graph) expected value node.origin
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
          discard <| checkResultValue environment graph prepared.layout field
    return candidate

/-- Validate the complete stored result through its source-derived native field layouts.
Reuse: RecordLayout, graph projection and the same native type/dependency check at every node.
Exported records retain their lazy interface; stored records validate all retained children. -/
opaque RuntimeEnvironment.checkResult (environment : RuntimeEnvironment) (graph : ValueGraph)
    (source : SourceLayout) (value : ValueBinding) : MetaM (CandidateResponse source) :=
  checkResultValue environment graph source value

/-- Stamp a produced node with its complete ordered actual context references.
Reuse: SourceLayout.inContext transports the checked role by stable source identities.
Result-type dependency selection is mechanical source metadata, not candidate decoding. -/
opaque RuntimeEnvironment.origin (environment : RuntimeEnvironment)
    (program : RuntimeId .program) (occurrence : RuntimeId .occurrence)
    (role : SourceLayout) : MetaM ValueOrigin := do
  unless program.worker == environment.worker && occurrence.worker == environment.worker do
    throwError "the producing runtime context belongs to a different worker"
  environment.context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    let role ← role.inContext context
    let marks ← IO.ofExcept <|
      (retainedSourceMarks environment.sourceMarks role.source).mapError IO.userError
    let dependencies ← markedTypeReferences environment.sourceGraph role.source marks
    return {
      program, occurrence, role, parameters := environment.values
      sourceMarks := marks, sourceDependencies := dependencies }

end CasRuntime
