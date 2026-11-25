module

public import CasRuntime.Closure
public import CasCompiler.Elaborate
public import CasCompiler.LimitSelection
public import CasCompiler.CreationSource
public import CasCompiler.SelectedField
public import CasCompiler.SelectedMorphism
public import CasCompiler.InputCoverage
public import CasRuntime.Transaction
public import CasRuntime.InputResult
public import CasRuntime.RoutedMethod
public import CasCompiler.CategoricalPointSource
public import CasCompiler.StructuralMap
public import CasRuntime.CallablePacket
public import CasRuntime.CategoricalPointPacket
public import LeanCategories.Catalogue.Registry.Semantic
public import CasCatalogue.InterpretationFailure

public section

namespace CasCompiler

open Lean Meta CasRuntime CasCatalogue

initialize registerTraceClass `cas.lower

/-- A selected leg whose exact source receiver is already an authenticated projection of
one completed cone. Only lowering that receiver constructs this demand. Runtime execution
receives the existing parent and association chain; it never finds a cone by row or diagram. -/
structure NativeLimitLegDemand where
  private mk ::
  selection : NativeLimitLegSelection
  receiver : ValueBinding
  cone : ValueBinding
  /-- Present only when the receiver itself supplied the authenticated native projection. -/
  apexSource : Option SourceLayout
  /-- The compiler-prepared native component at its original typed diagram index. -/
  component : ClosedTerm
  /-- The actual lowering frame, including nested callable captures and local binders. -/
  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  contextEnvironment : RuntimeEnvironment

/-- The active cell consumed by compiled source code. `run` interprets each emitted program.
A later demand is prepared from the actual references that an earlier program returned. -/
structure LowerEnvironment where
  ledger : OccurrenceLedger
  transaction : CellTransaction
  codes : IO.Ref (Std.HashMap (RuntimeId .program) ClosureCode)
  marks : IO.Ref (Array ValueBinding)
  sourceSnapshot : Option Json := none
  run : OperationalProgram ValueBinding → MetaM ValueBinding
  /-- Consume released leg data from the actual completed packet. The handler must keep the
  supplied cone, diagram, typed index and owners; it is not an arbitrary apply operation. -/
  limitLeg : NativeLimitLegDemand → MetaM ValueBinding := fun _ =>
    throwStratum .noImplementation "the completed cone requires its native leg-data continuation"

private structure Frame where
  environment : LowerEnvironment
  program : RuntimeId .program
  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  /-- A validated membership view of this frame's fixed context and binding table.
  Native associations may be reused within this fixed frame only after validating
  their references against the current graph and capturing the new source marks.
  Prepared invocation inputs still undergo their complete admission. -/
  retainedView : IO.Ref (Option RuntimeEnvironment)
  selection : Option Name := none

private abbrev LowerM := ReaderT Frame MetaM

private def supply : LowerM IdentitySupply :=
  return (← read).environment.ledger.owners.identities

private def parameters : LowerM (Array RuntimeParameter) := do
  let frame ← read
  let graph ← frame.environment.transaction.view
  let mut result := #[]
  for binding in frame.context.bindings do
    if let some value := frame.bound[binding.id]? then
      let .ok parameter := RuntimeParameter.ofValue graph binding.id value
        | throwError "internal: a retained source binding is outside the active graph"
      result := result.push parameter
  return result

private def sourceMarks (sources : Array ClosedTerm) : LowerM (Array (Nat × ValueBinding)) := do
  let frame ← read
  let actual ← frame.environment.marks.get
  let mut marks ← IO.ofExcept <|
    (captureContextSourceMarks actual frame.context.telescope).mapError IO.userError
  for source in sources do
    let selected ← IO.ofExcept <| (captureSourceMarks actual source).mapError IO.userError
    marks ← IO.ofExcept <| (mergeSourceMarks marks selected).mapError IO.userError
  return marks

private def runtimeEnvironment : LowerM RuntimeEnvironment := do
  let frame ← read
  RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
    (← sourceMarks #[]) (some (← frame.environment.transaction.view))
    (← frame.retainedView.get)

/-- Source-path selection only asks which original bindings are retained.
The frame's context and binding table do not change during lowering; recursive
execution opens its own frame. Reuse the checked lookup table for this question,
not as authority for admitting a later request. Origin formation revalidates
all references against its actual graph and extends the mark table separately. -/
private def retainedEnvironment : LowerM RuntimeEnvironment := do
  let frame ← read
  -- Even source-path inspection must not continue in a settled transaction.
  discard <| frame.environment.transaction.view
  if let some view ← frame.retainedView.get then return view
  let view ← runtimeEnvironment
  frame.retainedView.set (some view)
  return view

-- Temporary bounded source-cost inspection. The timer never changes or resets the budget.
private def sourceCostHead (expression : Expr) : String :=
  match expression.consumeMData.getAppFn.consumeMData with
  | .const name _ => s!"constant:{name}"
  | .proj name position parent =>
    s!"projection:{name}.{position};parent={reprStr parent.consumeMData.getAppFn.constName?}"
  | .fvar _ => "fvar"
  | .bvar _ => "bound"
  | .sort _ => "sort"
  | .forallE .. => "forall"
  | .lam .. => "lambda"
  | .letE .. => "let"
  | .lit _ => "literal"
  | .mvar _ => "metavariable"
  | .mdata .. => "metadata"
  | .app .. => "application"

private def traceExpensiveLower {α : Type} (phase : String) (expression : Expr)
    (contextSize : Nat) (action : LowerM α) : LowerM α := do
  let started ← IO.getNumHeartbeats
  try
    action
  finally
    -- Diagnostics must not replace the original success, failure or interrupt.
    try
      let finished ← IO.getNumHeartbeats
      let elapsed := finished - started
      if elapsed ≥ 10000000 then
        dbg_trace "[lower.cost] phase={phase} head={sourceCostHead expression} arguments={expression.getAppNumArgs} context={contextSize} rawTicks={elapsed} start={started} finish={finished}"
    catch _ => pure ()

-- Stamp an already checked source layout with the current actual runtime context.
-- Reusing native layout data never reuses an earlier occurrence or parameter table.
private def originFor (role : SourceLayout) : LowerM ValueOrigin := do
  let frame ← read
  let identities ← supply
  -- The complete native association of this fixed frame was checked by
  -- capture. Recheck every referenced identity in the actual current graph;
  -- do not reuse its graph snapshot as authority for a later origin.
  let checked ← retainedEnvironment
  let graph ← frame.environment.transaction.view
  discard <| IO.ofExcept <| (graph.requiredOwners checked.references).mapError IO.userError
  let environment ← traceExpensiveLower "origin.refresh" role.source.expression
      frame.context.bindings.size do
    checked.withSourceMarks (← sourceMarks #[role.source]) (some graph)
  traceExpensiveLower "origin.transport" role.source.expression frame.context.bindings.size do
    environment.origin frame.program (← identities.fresh .occurrence) role

private def origin (expression : Expr) : LowerM ValueOrigin := do
  let frame ← read
  traceExpensiveLower "origin.total" expression frame.context.bindings.size do
    let source ← traceExpensiveLower "origin.close" expression frame.context.bindings.size do
      frame.context.close expression
    let role ← traceExpensiveLower "origin.layout" expression frame.context.bindings.size do
      SourceLayout.ofTerm source
    originFor role

private def stage (expression : Expr) (payload : ValuePayload) : LowerM ValueBinding := do
  (← read).environment.transaction.stage (← origin expression) payload

private def demand (request : PreparedRequest) : LowerM ValueBinding := do
  let frame ← read
  let request := (request.withSelection frame.selection).withSourceSnapshot
    frame.environment.sourceSnapshot
  frame.environment.run do
    let response ← PFunctor.FreeM.lift (P := OperationalSignature) request
    pure response.root

/-- A published computation cannot be silently evaluated as an ordinary native definition.
This predicate selects no row or address; the reader must supply that original reference. -/
private def isRegisteredComputation (state : SemanticState) (declaration : Name) : Bool :=
  state.operations.any (·.declaration == declaration) ||
  state.functors.any (·.declaration == declaration) ||
  state.constructions.any (·.declaration == declaration) ||
  state.morphisms.any (·.declaration == declaration) ||
  state.objects.any (·.application == some declaration) ||
  state.binders.any (·.operation == declaration)

/-- Native fields of independently registered constant declarations may use their definitions.
Membership is the only result: it never chooses a descriptor ID, even for a unique row. -/
private def isRegisteredDescriptor (state : SemanticState) (declaration : Name) : Bool :=
  state.objects.any (·.declaration == declaration) ||
  state.categories.any (·.declaration == declaration) ||
  state.numerals.any (·.declaration == declaration) ||
  state.literals.any (·.denotation == declaration) ||
  state.graphLiterals.any (·.denotation == declaration) ||
  state.subsetLiterals.any (·.denotation == declaration) ||
  state.classifiers.any (·.declaration == declaration) ||
  state.cells.any (·.declaration == declaration) ||
  state.presentations.any (·.declaration == declaration) ||
  state.constructors.any (·.semantics == declaration)

/-- Reject loss of a public source selection before native reduction can erase its boundary.
Named limit/generator applications are included although their addresses have a distinct form. -/
private def requiresSourceAddress (state : SemanticState) (declaration : Name) : Bool :=
  isRegisteredComputation state declaration || isRegisteredDescriptor state declaration ||
  state.limits.any (·.declaration == declaration) ||
  state.objects.any (fun entry => entry.generator == some declaration ||
    entry.refines.any (·.identification == declaration))

/-- Open an already authorized native definition before substituting its original arguments.
Reuse: Lean's bare-constant unfolding and metadata-preserving beta substitution. Applying
`unfoldDefinition?` to the whole application erases returned source/retained-value metadata;
smart unfolding could also execute a match before the kernel reaches its explicit boundary. -/
private def unfoldSourceApplication? (expression : Expr) : MetaM (Option Expr) := do
  let .const _ _ := expression.getAppFn | return none
  let some body ← withOptions (fun options => options.setBool `smartUnfolding false) <|
      unfoldDefinition? expression.getAppFn
    | return none
  return some (body.betaRev expression.getAppRevArgs (preserveMData := true))

/-- Replace only the original full application's ordered argument positions, preserving
every source annotation on its head/spine. This does not search for equal subexpressions. -/
private def withApplicationArguments (expression : Expr) (arguments : Array Expr) :
    Except String Expr := do
  let rec rebuild (expression : Expr) (next : Nat) : Except String (Expr × Nat) := do
    match expression with
    | .mdata data body =>
      let (body, next) ← rebuild body next
      return (.mdata data body, next)
    | .app function _ =>
      let (function, next) ← rebuild function next
      let some argument := arguments[next]?
        | throw "a named source lost an original declaration argument"
      return (.app function argument, next + 1)
    | .const .. => return (expression, next)
    | _ => throw "a named source lost its original native declaration head"
  let (expression, consumed) ← rebuild expression 0
  unless consumed == arguments.size do
    throw "a named source changed its complete declaration argument arity"
  return expression

private def selectedReference? (data : MData) : Option (Name × ComputationRef) := do
  let declaration := data.getName `CasCompiler.source.declaration
  let id := data.getString `CasCompiler.source.id
  if declaration.isAnonymous || id.isEmpty then none
  let kind := data.getName `CasCompiler.source.kind
  if kind == ``OperationEntry then some (declaration, .operation ⟨id⟩)
  else if kind == ``MethodEntry then some (declaration, .method ⟨id⟩)
  else if kind == ``MorphismEntry then some (declaration, .morphism ⟨id⟩)
  else if kind == ``ConstructionEntry then some (declaration, .construction ⟨id⟩)
  else if kind == ``EdgeRef.functor then some (declaration, .functor ⟨id⟩)
  else none

private def selectedPointBoundary (data : MData) : Bool :=
  let kind := data.getName `CasCompiler.source.kind
  kind == ``CategoricalPointFamily || kind == ``SourceActionFamily ||
    kind == ``LimitFamily || kind == ``BinderEntry

/-- Ordinary descriptor producers retain their exact public row, just as computations do.
Their native value is the selected declaration's original application. -/
private def selectedDescriptor? (data : MData) : Option (Name × String) := do
  let declaration := data.getName `CasCompiler.source.declaration
  let id := data.getString `CasCompiler.source.id
  if declaration.isAnonymous || id.isEmpty then none
  let kind := data.getName `CasCompiler.source.kind
  if kind == ``ObjectEntry || kind == ``LiteralEntry || kind == ``GraphLiteralEntry ||
      kind == ``ClassifierEntry || kind == ``NamedCategoryEntry || kind == ``CellEntry ||
      kind == ``PresentationComparisonEntry || kind == ``ConstructorEntry then
    some (declaration, id)
  else none

/-- An independently declared native interface retains its selected owner and exact declaration.
Its record fields are structural source code, with no invented computation address. -/
private def selectedNativeInterface? (data : MData) : Option Name := do
  let kind := data.getName `CasCompiler.source.kind
  unless kind == ``ConstructorEntry.functorialAction || kind == ``ConstructorEntry.comparisonAction ||
      kind == ``ConstructorEntry.identityComparison ||
      kind == ``ConstructorEntry.compositionComparison || kind == ``ObjectEntry.refines do none
  let declaration := data.getName `CasCompiler.source.declaration
  if declaration.isAnonymous then none else some declaration

/-- A retained public selection must resolve by its original row and declaration. Missing or
changed fields are not an invitation to recover a different address from the native term. -/
private def checkSelectedAddress (data : MData) : MetaM Unit := do
  let kind := data.getName `CasCompiler.source.kind
  let computation := kind == ``OperationEntry || kind == ``MethodEntry ||
    kind == ``MorphismEntry || kind == ``ConstructionEntry || kind == ``EdgeRef.functor
  if computation then
    let some (declaration, reference) := selectedReference? data
      | throwError "the selected computation lost its original registered address"
    unless (← reference.declaration (← semanticState)) == declaration do
      throwError "the selected computation changed its original registered declaration"
    return ()
  unless kind == ``ObjectEntry || kind == ``LiteralEntry || kind == ``GraphLiteralEntry ||
      kind == ``ClassifierEntry || kind == ``EdgeRef.classifierForget ||
      kind == ``NumeralEntry || kind == ``SubsetLiteralEntry || kind == ``LimitEntry ||
      kind == ``ObjectEntry.generator || kind == ``ObjectEntry.application ||
      kind == ``NamedCategoryEntry || kind == ``CellEntry || kind == ``BinderEntry ||
      kind == ``PresentationComparisonEntry || kind == ``ConstructorEntry ||
      kind == ``ConstructorEntry.functorialAction || kind == ``ConstructorEntry.comparisonAction ||
      kind == ``ConstructorEntry.identityComparison ||
      kind == ``ConstructorEntry.compositionComparison || kind == ``ObjectEntry.refines do return ()
  let id := data.getString `CasCompiler.source.id
  let state ← semanticState
  let declarations : Option (Array Name) :=
    if kind == ``ObjectEntry then
      some ((state.objects.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``LiteralEntry then
      some ((state.literals.filter (·.id.raw == id)).map (·.denotation))
    else if kind == ``GraphLiteralEntry then
      some ((state.graphLiterals.filter (·.id.raw == id)).map (·.denotation))
    else if kind == ``ClassifierEntry || kind == ``EdgeRef.classifierForget then
      some ((state.classifiers.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``NumeralEntry then
      some ((state.numerals.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``SubsetLiteralEntry then
      some ((state.subsetLiterals.filter (·.id.raw == id)).map (·.denotation))
    else if kind == ``LimitEntry then
      some ((state.limits.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``ObjectEntry.generator then
      some ((state.objects.filter (·.id.raw == id)).filterMap (·.generator))
    else if kind == ``ObjectEntry.application then
      some ((state.objects.filter (·.id.raw == id)).filterMap (·.application))
    else if kind == ``BinderEntry then
      some ((state.binders.filter (·.id.raw == id)).map (·.operation))
    else if kind == ``NamedCategoryEntry then
      some ((state.categories.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``CellEntry then
      some ((state.cells.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``PresentationComparisonEntry then
      some ((state.presentations.filter (·.id.raw == id)).map (·.declaration))
    else if kind == ``ConstructorEntry then
      some ((state.constructors.filter (·.id.raw == id)).map (·.semantics))
    else if kind == ``ConstructorEntry.functorialAction then
      some ((state.constructors.filter (·.id.raw == id)).filterMap (·.functorialAction))
    else if kind == ``ConstructorEntry.comparisonAction then
      some ((state.constructors.filter (·.id.raw == id)).filterMap (·.comparisonAction))
    else if kind == ``ConstructorEntry.identityComparison then
      some ((state.constructors.filter (·.id.raw == id)).filterMap (·.identityComparison))
    else if kind == ``ConstructorEntry.compositionComparison then
      some ((state.constructors.filter (·.id.raw == id)).filterMap (·.compositionComparison))
    else if kind == ``ObjectEntry.refines then
      some ((state.objects.filter (·.id.raw == id)).filterMap
        (fun entry => entry.refines.map (·.identification)))
    else none
  if let some declarations := declarations then
    let #[declaration] := declarations
      | throwError "the selected descriptor lost its original registered address"
    unless data.getName `CasCompiler.source.declaration == declaration do
      throwError "the selected descriptor changed its original registered declaration"

/-- Expose only a selected native interface at the root of this exact projection chain.
The original source remains the retained role; this separate view inspects its constructor.
No expression search, registry recovery, or alternate declaration supplies the root. -/
private partial def nativeInterfaceSource? (expression : Expr) : MetaM (Option Expr) := do
  if let .mdata data head := expression.getAppFn then
    if let some declaration := selectedNativeInterface? data then
      checkSelectedAddress data
      let native := (mkAppN head expression.getAppArgs).consumeMData
      unless native.getAppFn.isConstOf declaration do
        throwError "the selected native interface lost its original declaration application"
      let some body ← unfoldSourceApplication? native
        | throwStratum .noImplementation m!"{declaration} has no native interface definition"
      return some body
  let some projection ← SourceProjection.ofExpr? expression | return none
  let some parent ← nativeInterfaceSource? projection.parent | return none
  let owner := (← getConstInfoCtor projection.info.ctorName).induct
  return some (.proj owner projection.info.i parent)

/-- A registered distinguished element that the reader evaluated at its point: a subset literal,
an object's generator, a numeral, or the apex of a registered limit or colimit at its maps. Its
address names the element; formation retains its actual application beside the native value.
A numeral is the image of `k` under a universal map
(NumeralEntry); computing that image is a leaf's job (constitution C22). -/
private def namedElement? (data : MData) : Option (Name × String) := do
  let declaration := data.getName `CasCompiler.source.declaration
  let id := data.getString `CasCompiler.source.id
  if declaration.isAnonymous || id.isEmpty then none
  let kind := data.getName `CasCompiler.source.kind
  if kind == ``SubsetLiteralEntry || kind == ``NumeralEntry || kind == ``LimitEntry then
    some (declaration, id)
  else if kind == ``ObjectEntry.generator then some (declaration, s!"{id}#generator")
  else none

/-- Closed scalar data in the released literal grammar, read by ScalarLiteral.check.
Reference: CasRuntime/Literal.lean decode; this is its inverse on literal constructor forms.
Only numerals, lists and constructor applications are read. No definition is unfolded. -/
private partial def literal? (expression : Expr) : MetaM (Option Json) := do
  let expression := (← instantiateMVars expression).consumeMData
  if expression.hasFVar || expression.hasMVar then return none
  if let some value := expression.rawNatLit? then return some (toJson value)
  if let .lit (.strVal value) := expression then return some (toJson value)
  -- Lean's native unit notation is a constructor alias (Init/Prelude.lean), with
  -- no arguments or computational fields. Overloaded OfNat/Neg projections are
  -- handled at their actual selected instance; their numeral index is not a value.
  if expression.isConstOf ``Unit.unit then return some (.arr #[])
  if expression.isAppOfArity ``Int.ofNat 1 then
    if let some value := expression.appArg!.rawNatLit? then return some (toJson (Int.ofNat value))
  if expression.isAppOfArity ``Int.negSucc 1 then
    if let some value := expression.appArg!.rawNatLit? then return some (toJson (Int.negSucc value))
  if let some (_, elements) := expression.listLit? then
    let mut packets := #[]
    for element in elements do
      let some packet ← literal? element | return none
      packets := packets.push packet
    return some (.arr packets)
  if expression.isAppOfArity ``Quot.mk 3 then return ← literal? expression.appArg!
  let .const name _ := expression.getAppFn | return none
  let some (.ctorInfo constructor) := (← getEnv).find? name | return none
  let arguments := expression.getAppArgs
  unless arguments.size == constructor.numParams + constructor.numFields do return none
  let some (.inductInfo info) := (← getEnv).find? constructor.induct | return none
  let mut packets := #[]
  for field in arguments.extract constructor.numParams arguments.size do
    if ← isProof field then continue
    let some packet ← literal? field | return none
    packets := packets.push packet
  if info.ctors.length == 1 && info.numIndices == 0 then
    if let #[packet] := packets then return some packet
    return some (.arr packets)
  return some (Json.mkObj [("ctor", toJson name.getString!), ("args", .arr packets)])

private partial def captured (frame : Frame) (graph : ValueGraph)
    (marks : Array (Nat × ValueBinding)) (expression : Expr)
    (found : Array ValueBinding) : MetaM (Array ValueBinding) := do
  match expression with
  | .mdata data body =>
    if (markedKey? data).isSome then return found
    captured frame graph marks body found
  | .fvar id =>
    match frame.context.bindings.find? (·.expression.fvarId! == id) with
    | some binding => match frame.bound[binding.id]? with
      | some value => return found.push value
      | none =>
        -- Only this exact source definition may expose an earlier captured reference.
        -- A directly retained value above remains authoritative, even for a definition.
        match (← id.getDecl).value? with
        | some value =>
          let selected ← markedSourceReferences (some graph) frame.context marks value
          captured frame graph marks value (found ++ selected)
        | none => return found
    | none => return found
  | .app function argument =>
    captured frame graph marks argument (← captured frame graph marks function found)
  | .lam _ type body _ | .forallE _ type body _ =>
    captured frame graph marks body (← captured frame graph marks type found)
  | .letE _ type value body _ =>
    captured frame graph marks body
      (← captured frame graph marks value (← captured frame graph marks type found))
  | .proj _ _ value => captured frame graph marks value found
  | _ => return found

/-- Retain a checked source term as code with its actual captured references.
Its fields and applications are lowered when a demand reaches them. -/
private def closureWith (expression : Expr) (build : ClosedTerm → ClosureCode)
    (retainedRole : Option Expr := none) (retainedValues : Array ValueBinding := #[]) :
    LowerM ValueBinding := do
  let frame ← read
  if let some original := retainedRole then
    unless ← isDefEq (← inferType original) (← inferType expression) do
      throwError "the delayed native continuation changed its original source interface"
  traceExpensiveLower "closure.total" expression frame.context.bindings.size do
    let program ← (← supply).fresh .program
    let source ← traceExpensiveLower "closure.close" expression frame.context.bindings.size do
      frame.context.close expression
    let captures ← traceExpensiveLower "closure.captures" expression
        frame.context.bindings.size do
      let marks ← sourceMarks #[source]
      let graph ← frame.environment.transaction.view
      let selected ← markedSourceReferences (some graph) frame.context marks expression
      captured frame graph marks expression selected
    let captures := captures ++ retainedValues
    let code := build source
    frame.environment.codes.modify (·.insert program code)
    traceExpensiveLower "closure.stage" expression frame.context.bindings.size do
      stage (retainedRole.getD expression) (.closure program captures)

private def closure (expression : Expr) : LowerM ValueBinding :=
  closureWith expression ClosureCode.term

mutual

/-- Lower one checked source term to its actual retained value.
Source: mathematical-input contract §2 and plan §2, lean-cas-dsl#10 comment 6664354269.
Variables read their retained bindings. Published computation families become prepared
primitive demands at their actual arguments. Fields and applications of retained values become
projection and application demands. Lambdas and selected instances retain code and captures.
Only retained source definitions and accepted derivation compositions expose their bodies.
Declared native interfaces retain their original fields. No operation is recognized by name. -/
private partial def lower (expression : Expr) : LowerM ValueBinding := do
  let expression ← instantiateMVars expression
  match expression with
  | .mdata data body =>
    if let some (.ofString selector) := data.find `CasCompiler.endpoint then
      let projection := if selector == "source" then ``CategoryTheory.Arrow.left
        else if selector == "target" then ``CategoryTheory.Arrow.right
        else Name.anonymous
      unless !projection.isAnonymous && body.getAppFn.isConstOf projection do
        throwError "the selected endpoint lost its declared projection"
      let arrow := body.getAppArgs.back!
      unless arrow.getAppFn.isConstOf ``CategoryTheory.Arrow.mk do
        throwError "the selected endpoint lost its actual arrow"
      let some endpoint := selectedEndpoint? expression
        | throwError "the selected endpoint lost its declared constructor argument"
      let frame ← read
      let environment ← retainedEnvironment
      -- This exact Arrow.mk argument may already name an actual input. Preserve that
      -- reference; otherwise the endpoint remains a descriptor of its selected arrow.
      if ← environment.hasRetainedSource frame.context endpoint then
        return ← lower (← argumentSource environment endpoint)
      let value ← lower arrow.getAppArgs.back!
      let template := Json.mkObj [("ctor", "morphismEndpoint"),
        ("args", .arr #[.null, toJson selector])]
      let slots : Array ContainerSlot :=
        #[{ path := #[.field "args", .index 0], binding := value, fieldIndex := none }]
      let fields ← selectedEndpointFields? (selector == "source") value
      if let some fields := fields then
        let role := (← origin expression).role
        if role.kind == .record then
          return ← stageRecord (← RecordLayout.ofSource role) fields (some (template, slots))
      let built ← match fields with
        | some fields => pure (ValuePayload.container template slots fields none)
        | none => pure (ValuePayload.descriptor template slots)
      let .ok payload := built
        | throwError "the selected endpoint has an invalid reference layout"
      return ← stage expression payload
    if let some (selection, field) := selectedField? data then
      let transaction := (← read).environment.transaction
      if data.getBool `CasCompiler.selection.owner then
        unless body.isAppOfArity ``Function.const 4 do
          throwError "the source field lost its exact typed owner envelope"
        let owner ← lower body.getAppArgs[3]!
        let .ok prior ← transaction.selectedAt selection field owner
          | throwStratum .unavailable "the selected owner's result is no longer available"
        if let some value := prior then return value
        let value ← if data.getBool `CasCompiler.selection.deferredCone then do
            let frame ← read
            let graph ← transaction.view
            let some original := graph.find owner.value
              | throwError "the deferred cone lost its original actual receiver"
            let source ← markValue frame.environment.marks owner
              (← original.origin.role.source.inContext frame.context)
            let some whole ← limitConeSource frame.context source
              | throwError "the deferred cone lost its original complete source plan"
            lower whole
          else lower body.getAppArgs[2]!
        let .ok () ← transaction.bindSelectedAt selection field owner value
          | throwError "the selected owner's field changed its computational occurrence"
        return value
      let .ok prior ← transaction.selected selection field
        | throwStratum .unavailable "the selected construction's result is no longer available"
      if let some value := prior then return value
      let value ← withReader (fun frame => { frame with selection := some selection }) (lower body)
      let .ok () ← transaction.bindSelected selection field value
        | throwError "the selected construction's field changed its computational occurrence"
      return value
    if let some key := markedKey? data then
      let some value := (← (← read).environment.marks.get)[key]?
        | throwError "internal: a retained source value lost its mark"
      return value
    checkSelectedAddress data
    if data.getName `CasCompiler.source.kind == ``CategoricalPointFamily then
      return ← categoricalPointFamily data body
    if data.getName `CasCompiler.source.kind == ``LimitFamily then
      return ← wholeLimitFamily data body
    if data.getName `CasCompiler.source.kind == ``LimitUniversalFamily then
      return ← universalLimitFamily data body
    if data.getName `CasCompiler.source.kind == ``CreationFamily then
      return ← creationFamily data body
    if data.getName `CasCompiler.source.kind == ``SourceActionFamily then
      return ← objectActionFamily data body
    if let some selected ← SourceActionFamily.native? expression then return ← lower selected
    if let some selected ← categoricalPointSource? expression then return ← lower selected
    if data.getName `CasCompiler.source.kind == ``BinderEntry then
      return ← closure expression
    if let some declaration := selectedNativeInterface? data then
      unless body.consumeMData.getAppFn.isConstOf declaration do
        throwError "the selected native interface lost its original declaration application"
      return ← nativeInterface expression
    if data.getBool `CasCompiler.source.derived then
      unless (selectedReference? data).isSome || (selectedDescriptor? data).isSome ||
          data.getName `CasCompiler.source.kind == ``EdgeRef.classifierForget do
        throwError "a derived source reference has no declared computation, descriptor or view role"
      return ← lower body
    -- The reader's selected address belongs to this original computation. Its arguments
    -- and nested source references keep their own selections when its head is exposed.
    -- A named element is sent as its descriptor at its explicit parameters, not as the
    -- unfolded definition of its point value.
    if data.getName `CasCompiler.source.kind == ``ObjectEntry.application then
      return ← objectApplicationFamily data body
    -- Admission retains its complete point family, including data-bearing evidence. Only a
    -- complete native input-result plan may reconstruct its computational record fields.
    if data.getName `CasCompiler.source.kind == ``ObjectEntry.admission then
      return ← admission expression data body
    -- A published computation of a selected lift is sent to its lift's ports, at the
    -- parameters of the lift's evidence; its definition is not unfolded (C22).
    if data.getName `CasCompiler.source.kind == ``RoutedMethodFamily then
      return ← routedMethodFamily data body
    if data.getName `CasCompiler.source.kind == ``LiftFamily then return ← liftFamily data body
    if data.getName `CasCompiler.source.kind == ``PresentationFamily then
      return ← presentationFamily data body
    if data.getName `CasCompiler.source.kind == ``PropertyEntry then
      return ← propertyObservation data body
    if data.contains `CasCompiler.source.leg then
      if let some selected ← NativeLimitLegSelection.ofExpr? expression then
        let receiver ← lower selected.construction.receiver
        let frame ← read
        let graph ← frame.environment.transaction.view
        let .ok projected := graph.projectionSelection receiver
          | throwError "the selected leg lost its receiver's actual projection parent"
        let mut retained : Option (ValueBinding × Option SourceLayout) := none
        if let some (source, cone, path) := projected then
          let apex := if selected.construction.source.colimit then
            ``CategoryTheory.Limits.Cocone.pt else ``CategoryTheory.Limits.Cone.pt
          if path == #[apex] then
            retained := some (cone, some source)
        if retained.isNone then
          -- The compiled source identity is only one part of this completion key.
          -- This exact receiver node and full association path distinguish separate calls.
          let field := if selected.construction.source.colimit then
            ``CategoryTheory.Limits.ColimitCocone.cocone else
            ``CategoryTheory.Limits.LimitCone.cone
          let .ok cone ← frame.environment.transaction.selectedAt
              selected.construction.source.construction field receiver
            | throwStratum .unavailable "the selected construction's result is no longer available"
          retained := cone.map (fun cone => (cone, none))
        if let some (cone, source) := retained then
          let coneSource ← markValue frame.environment.marks cone
            (← cone.role.source.inContext frame.context)
          let component ← frame.context.close
            (← selected.construction.legAt coneSource selected.index)
          return ← frame.environment.limitLeg {
            selection := selected, receiver, cone, apexSource := source, component
            context := frame.context, bound := frame.bound
            contextEnvironment := ← runtimeEnvironment }
        let some ownerNode := graph.find receiver.value
          | throwError "the delayed leg lost its original receiver"
        let owner ← markValue frame.environment.marks receiver
          (← ownerNode.origin.role.source.inContext frame.context)
        let some whole ← deferredLimitConeSource owner
          | throwError "the delayed leg lost its original complete cone source"
        let indexValue ← lower selected.index
        let index ← markValue frame.environment.marks indexValue selected.index
        let source ← selected.construction.legAt whole index
        let packet : Option ValueContainer ←
          if selected.construction.source.creation.isSome then
            pure none
          else do
            let some (declaration, address) := namedElement? data
              | throwError "the formal leg lost its original named source descriptor"
            let some element ← sourceApplication? declaration body
              | throwError "the formal leg lost its original complete presentation"
            let some (.ofNat ordinal) := data.find `CasCompiler.source.leg
              | throwError "the formal leg lost its original source ordinal"
            let arguments ← explicitArguments element
            pure (some (← descriptorPacket s!"{address}#leg"
              (arguments.push (mkNatLit ordinal))))
        let captures := (packet.map (·.slots.map (·.binding))).getD #[]
        return ← closureWith source (fun source => .formalLeg source packet)
          (some expression) captures
    if let some (declaration, address) := namedElement? data then
      let some element ← sourceApplication? declaration body
        | throwError "internal: the named element lost its original registered application"
      if data.getName `CasCompiler.source.kind == ``LimitEntry &&
          !data.contains `CasCompiler.source.leg then
        if let some formal ← formalLimitDescriptor expression then return formal
      let arguments ← explicitArguments element
      -- A defining leg of a registered limit is that limit's named leg at its maps and the
      -- ordinal of its shape object (SourceLimit.sourceLimitLeg?). The contract publishes no
      -- address that applies a leg to an element (api/wire-examples.md, "constructionLeg").
      if let some (.ofNat ordinal) := data.find `CasCompiler.source.leg then
        if (← origin expression).role.kind == .function then
          throwStratum .noImplementation
            m!"the leg {ordinal} of {address} is a map of sets; no published address applies it"
        return ← descriptor expression s!"{address}#leg" (arguments.push (mkNatLit ordinal))
      if (← origin expression).role.kind == .function then return ← closure expression
      -- A published element names its whole value at these arguments. Its native record
      -- schema does not supply computed fields, and projecting the same named source again
      -- is not executable field code. Its registered consumers retain the descriptor.
      return ← descriptor expression address arguments
    if let some (declaration, address) := selectedDescriptor? data then
      let application := body.consumeMData
      unless application.getAppFn.isConstOf declaration do
        throwError "the selected descriptor lost its original declaration application"
      return ← namedConstant expression address application
    match selectedReference? data with
    | some (declaration, _) =>
      let native := body.consumeMData
      unless native.getAppFn.isConstOf declaration do
        throwError "the selected computation lost its original declaration application"
      -- Formation supplied this exact application, before native projection or action.
      -- Only its head moves to the ordinary application boundary; arguments stay intact.
      application (mkAppN (.mdata data native.getAppFn) native.getAppArgs)
    | none => lower body
  | .fvar id =>
    let frame ← read
    let some binding := frame.context.bindings.find? (·.expression.fvarId! == id)
      | throwError "a source variable is outside its complete binding context"
    if let some value := frame.bound[binding.id]? then return value
    match (← id.getDecl).value? with
    | some value =>
      unless binding.role == .definition do
        throwStratum .noImplementation
          m!"the source binding {(← id.getDecl).userName} has no retained computational value"
      lower value
    | none =>
      -- Keep the existing one-string symbolic descriptor. Its opaque identity uses the
      -- same nonce:serial convention as RequestScope.wireId; display names stay in context.
      let packet := Json.mkObj [("ctor", "variable"),
        ("args", .arr #[toJson s!"{binding.id.session}:{binding.id.serial}"])]
      stage expression (.portable packet.compress.toUTF8)
  | .letE _ _ value body _ =>
    if (← isProof value) || (← isType value) then return ← lower (body.instantiate1 value)
    let bound ← lower value
    lower (body.instantiate1 (← markValue (← read).environment.marks bound value))
  | .lam .. => closure expression
  | _ =>
    if let some selected ← categoricalPointSource? expression then return ← lower selected
    let frame ← read
    if let some selected ← NativeStructuralMap.ofExpr? frame.context expression
        (frame.bound.toArray.map (·.1)) then
      return ← structuralMap selected
    -- Native whnf beta-reduces and then erases result metadata. Substitute this exact
    -- application first, preserving the selected boundary on its result or partial body.
    -- No declaration body, let binding or argument is evaluated by this structural step.
    if expression.getAppFn.isHeadBetaTargetFn false then
      let reduced := expression.getAppFn.betaRev expression.getAppRevArgs
        (preserveMData := true)
      if reduced != expression then return ← lower reduced
    -- Lean's head reduction drops metadata. A retained value at the head is applied as that
    -- same value, a retained record gives its field, and a selected family head is dispatched.
    if let .mdata data head := expression.getAppFn then
      checkSelectedAddress data
      if let some declaration := selectedNativeInterface? data then
        unless head.consumeMData.getAppFn.isConstOf declaration do
          throwError "the selected native interface lost its original declaration application"
        return ← nativeInterface (.mdata data (mkAppN head expression.getAppArgs))
      if data.getBool `CasCompiler.source.derived then
        return ← apply (← lower expression.getAppFn) expression.getAppArgs
      if let some (declaration, address) := selectedDescriptor? data then
        let application := (mkAppN head expression.getAppArgs).consumeMData
        unless application.getAppFn.isConstOf declaration do
          throwError "the selected descriptor lost its original declaration application"
        return ← namedConstant expression address application
      if data.getName `CasCompiler.source.kind == ``BinderEntry then
        let selected := Expr.mdata data (mkAppN head expression.getAppArgs)
        if let some prepared ← categoricalPointSource? selected then return ← lower prepared
        return ← closure selected
      if (markedKey? data).isSome || selectedPointBoundary data ||
          data.getName `CasCompiler.source.kind == ``RoutedMethodFamily then
        return ← apply (← lower expression.getAppFn) expression.getAppArgs
      if data.getName `CasCompiler.source.kind == ``ObjectEntry.application then
        return ← objectApplicationFamily data (mkAppN head expression.getAppArgs)
      if (selectedReference? data).isSome then return ← application expression
      if !data.contains `CasCompiler.source.kind &&
          !data.contains `CasCompiler.lower.value &&
          !data.contains `CasCompiler.selection &&
          !data.contains `CasCompiler.endpoint then
        return ← lower (mkAppN head expression.getAppArgs)
    if let .const declaration _ := expression.getAppFn then
      if requiresSourceAddress (← semanticState) declaration then
        let frame ← read
        dbg_trace "[lost-source] declaration={declaration} expression={repr expression}"
        dbg_trace "[lost-source] context={repr (frame.context.bindings.map (·.id))} retained={repr (frame.bound.toArray.map (·.1))}"
        throwError "the registered source declaration {declaration} lost its selected source address"
    -- Native type hints and the typed source-application witness are transparent
    -- identity wrappers. Substitute their original arguments before whnf can
    -- discard the returned selection metadata. This does not evaluate any
    -- registered declaration or the ignored witness.
    if expression.getAppFn.isConstOf ``id ||
        expression.getAppFn.isConstOf ``Function.const then
      if let some reduced ← unfoldSourceApplication? expression then
        return ← lower reduced
    -- Select a retained native field before head reduction can erase its actual parent.
    -- Both projection syntaxes retain their complete application suffix. Formal class fields
    -- remain definitions until their exact parent has a runtime reference.
    let arguments := expression.getAppArgs
    let nativeEnvironment ← getEnv
    let projectionSource := match expression.getAppFn with
      | .proj .. => expression.getAppFn
      | .const declaration _ =>
        match nativeEnvironment.getProjectionFnInfo? declaration with
        | some info =>
          if info.numParams < arguments.size then
            mkAppN expression.getAppFn (arguments.extract 0 (info.numParams + 1))
          else expression
        | none => expression
      | _ => expression
    if let some projection ← SourceProjection.ofExpr? projectionSource then
      let traced := (expression.find? (·.isConstOf `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
      if traced then dbg_trace "[inclusion.stage] lower projection {projection.declaration}: before environment"
      let frame ← read
      let environment ← retainedEnvironment
      if traced then dbg_trace "[inclusion.stage] lower projection {projection.declaration}: after environment"
      if ← environment.hasRetainedSource frame.context projection.parent then
        if traced then dbg_trace "[inclusion.stage] lower projection {projection.declaration}: retained parent"
        let (parent, path) ← projectionSourcePath environment projectionSource
        let selected ← projectPath (← lower parent) path
        return ← apply selected (arguments.extract projectionSource.getAppNumArgs arguments.size)
      -- An owned source field is a computation boundary even before its first result exists.
      -- Follow only this syntactic native spine; reduction must not erase its owner marker.
      let (parent, path) ← projectionSourcePath environment projectionSource
      if let .mdata data _ := parent then
        if (selectedField? data).isSome then
          let selected ← projectPath (← lower parent) path
          return ← apply selected (arguments.extract projectionSource.getAppNumArgs arguments.size)
      if let .mdata data _ := projection.parent.getAppFn then
        checkSelectedAddress data
        if (selectedNativeInterface? data).isSome then
          let owner := (← getConstInfoCtor projection.info.ctorName).induct
          let selected ← field owner projection.info.i projection.parent
            m!"{projection.declaration}"
          return ← apply selected (arguments.extract projectionSource.getAppNumArgs arguments.size)
        if (selectedReference? data).isSome || (namedElement? data).isSome ||
            selectedPointBoundary data ||
            data.getName `CasCompiler.source.kind == ``RoutedMethodFamily ||
            data.getName `CasCompiler.source.kind == ``ObjectEntry.application then
          -- A published source application owns its native record before projection.
          -- Native reduction must not erase that boundary or select a constructor field
          -- before the actual computation has supplied the record.
          let selected ← project (← lower projection.parent) projection.info.i
            m!"{projection.declaration}"
          return ← apply selected (arguments.extract projectionSource.getAppNumArgs arguments.size)
      if traced then dbg_trace "[inclusion.stage] lower projection {projection.declaration}: unretained parent"
    -- Select a native constructor field before head reduction can discard its retained-value
    -- or source-boundary metadata. This reads only the exact selected constructor argument.
    -- Reuse the metadata-preserving projection step from Layout.inputProjectionHead.
    let traceInclusion := (expression.find? (·.isConstOf
      `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
    if traceInclusion then dbg_trace "[inclusion.lower] before constructor projection"
    if let some projection ← SourceProjection.ofExpr? projectionSource then
      if traceInclusion then dbg_trace "[inclusion.lower] constructor projection {projection.declaration}"
      if let .mdata data _ := projection.parent.getAppFn then
        if selectedPointBoundary data || data.getName `CasCompiler.source.kind == ``RoutedMethodFamily ||
            data.getName `CasCompiler.source.kind == ``ObjectEntry.application then
          if traceInclusion then dbg_trace "[inclusion.lower] routed projection selected"
          return ← project (← lower projection.parent) projection.info.i
            m!"{projection.declaration}"
      let mut parent := projection.parent
      if let .const declaration _ := parent.getAppFn then
        -- The selected field of an ordinary native record constructor (for example,
        -- Functor.comp.obj) is structural code. Open exactly one unregistered
        -- definition, only if its head is the expected constructor. This preserves
        -- the actual selected functors inside the field's lambda rather than
        -- constructing a whole intermediate record or normalizing their addresses.
        unless parent.getAppFn.isConstOf projection.info.ctorName ||
            requiresSourceAddress (← semanticState) declaration do
          if let some expanded ← unfoldSourceApplication? parent then
            if expanded.getAppFn.isConstOf projection.info.ctorName then
              parent := expanded
      if parent.getAppFn.constName? == some projection.info.ctorName then
        if let some selected ← projectCore? parent projection.info.i then
          if traceInclusion then dbg_trace "[inclusion.lower] native constructor field selected"
          return ← lower (mkAppN selected
            (arguments.extract projectionSource.getAppNumArgs arguments.size))
    if traceInclusion then dbg_trace "[inclusion.lower] after constructor projection"
    if let .proj owner index (.mdata data value) := expression then
      if (markedKey? data).isSome then
        let some info := getStructureInfo? (← getEnv) owner
          | throwError "internal: a source projection has no structure metadata"
        if traceInclusion then dbg_trace "[inclusion.lower] marked projection selected"
        return ← project (← lower (.mdata data value)) index m!"{info.fieldNames[index]?}"
    if traceInclusion then dbg_trace "[inclusion.lower] before inferType head={repr expression.getAppFn.constName?} arity={expression.getAppNumArgs}"
    let inferredType ← inferType expression
    if traceInclusion then dbg_trace "[inclusion.lower] after inferType; before type whnf head={repr inferredType.getAppFn.constName?} arity={inferredType.getAppNumArgs}"
    let type ← whnf inferredType
    if traceInclusion then dbg_trace "[inclusion.lower] after type whnf head={repr type.getAppFn.constName?} arity={type.getAppNumArgs}"
    trace[cas.lower] "{expression.getAppFn} [{expression.getAppNumArgs}] : {type}"
    if traceInclusion then dbg_trace "[inclusion.lower] before isProp"
    let proofType ← isProp type
    if traceInclusion then dbg_trace "[inclusion.lower] after isProp result={proofType}; before isClass"
    if proofType then throwError "internal: a source proof has no computational value"
    let typeClass ← isClass? type
    if traceInclusion then dbg_trace "[inclusion.lower] after isClass result={typeClass.isSome}"
    if typeClass.isSome then return ← closure expression
    -- A structure value is a dependent record of its fields. Only data-kind terms are packets.
    -- A type is an object of the category of sets, and is lowered like any other term.
    if traceInclusion then dbg_trace "[inclusion.lower] before literal/record dispatch"
    unless type.isSort || (type.getAppFn.constName?.map (isStructure (← getEnv))).getD false do
      if let some packet ← literal? expression then
        return ← stage expression (.portable packet.compress.toUTF8)
    if (type.getAppFn.constName?.map (isStructure (← getEnv))).getD false then
      if traceInclusion then dbg_trace "[inclusion.lower] before nativeInputRecord"
      if let some value ← nativeInputRecord? expression then
        if traceInclusion then dbg_trace "[inclusion.lower] nativeInputRecord selected"
        return value
      if traceInclusion then dbg_trace "[inclusion.lower] after nativeInputRecord none"
    -- Structural head reduction only. Iota and auxiliary-definition unfolding would execute
    -- a matcher or recursor before the explicit missing-operation boundary below.
    if traceInclusion then dbg_trace "[inclusion.lower] before whnfCore"
    let reduced ← withConfig (fun config =>
      { config with zeta := false, zetaDelta := false, iota := false, proj := .yes })
      (whnfCore expression)
    if traceInclusion then dbg_trace "[inclusion.lower] after whnfCore changed={reduced != expression} head={repr reduced.getAppFn.constName?} arity={reduced.getAppNumArgs}"
    if reduced != expression then return ← lower reduced
    if traceInclusion then dbg_trace "[inclusion.lower] before final native dispatch"
    match expression with
    | .proj owner index value => do
      let some info := getStructureInfo? (← getEnv) owner
        | throwError "internal: a source projection has no structure metadata"
      let some name := info.fieldNames[index]?
        | throwError "internal: a source projection is outside its structure"
      field owner index value m!"{name}"
    | .forallE .. | .sort .. =>
      if type.isProp then
        -- A quantified proposition is decided by a published predicate or not at all (C22).
        throwStratum .noImplementation m!"the proposition {expression} has no published predicate"
      descriptor expression "lean:type" #[]
    | _ => application expression

/-- The original named packet at its actual explicit operands. This same sealed packet is
used by ordinary descriptors and by a formal leg's inert view; neither evaluates the leg. -/
private partial def descriptorPacket (address : String) (arguments : Array Expr)
    (originals : Option (Array ValueBinding) := none) : LowerM ValueContainer := do
  if let some originals := originals then
    unless originals.size == arguments.size do
      throwError "a named descriptor lost its original explicit argument table"
    discard <| IO.ofExcept <|
      ((← (← read).environment.transaction.view).requiredOwners originals).mapError IO.userError
  let mut packets := #[]
  let mut slots := #[]
  for argument in arguments, index in [:arguments.size] do
    let value ← match originals with
      | some originals => do
        let some original := originals[index]?
          | throwError "a named descriptor lost an original explicit argument"
        pure original
      | none => lower argument
    slots := slots.push ({
      path := #[.field "args", .index packets.size], binding := value, fieldIndex := none } :
      ContainerSlot)
    packets := packets.push Json.null
  let template := Json.mkObj [("ctor", toJson address), ("args", .arr packets)]
  let .ok payload := ValuePayload.descriptor template slots
    | throwError "internal: the descriptor of {address} has an invalid reference layout"
  let .container packet := payload.data
    | throwError "internal: the original named descriptor lost its complete packet"
  return packet

/-- A descriptor of a named source constant at its actual explicit arguments.
Reference: CasContract.Port descriptor grammar `{"ctor": address, "args": [...]}`.
Each argument is lowered and keeps its own retained reference in a typed slot. -/
private partial def descriptor (expression : Expr) (address : String) (arguments : Array Expr)
    (fields : Option (Array ValueBinding) := none)
    (originals : Option (Array ValueBinding) := none) : LowerM ValueBinding := do
  let packet ← descriptorPacket address arguments originals
  if let some fields := fields then
    let role := (← origin expression).role
    if role.kind == .record then
      return ← stageRecord (← RecordLayout.ofSource role) fields
        (some (packet.template, packet.slots))
  let built := match fields with
    | some fields => ValuePayload.container packet.template packet.slots fields none
    | none => ValuePayload.descriptor packet.template packet.slots
  let .ok payload := built
    | throwError "internal: the descriptor of {address} has an invalid reference layout"
  stage expression payload

/-- A finite list or finite-subset literal `[a₁, …, aₙ]`, `List.toFinset [a₁, …, aₙ]`: the array of
its elements' data (leaf contract api/wire-examples.md, "List or finite subset literal"). Each
element is lowered and keeps its own retained reference in a typed slot. -/
private partial def array (expression : Expr) (elements : Array Expr) : LowerM ValueBinding := do
  let mut slots := #[]
  for element in elements, index in [:elements.size] do
    let binding ← lower element
    slots := slots.push ({ path := #[.index index], binding, fieldIndex := none } : ContainerSlot)
  let .ok payload := ValuePayload.container (.arr (Array.replicate elements.size Json.null)) slots
      #[] none
    | throwError "internal: a finite literal has an invalid reference layout"
  stage expression payload

/-- A registered named constant at its explicit arguments. A callable is retained as code; a
record value keeps each computational field as a closure beside its descriptor. -/
private partial def namedConstant (expression : Expr) (address : String) (application : Expr) :
    LowerM ValueBinding := do
  let frame ← read
  let (closed, actual) ← actualArguments application.getAppArgs
  let information ← getFunInfoNArgs application.getAppFn closed.size
  let mut arguments := #[]
  let mut explicitSources := #[]
  let mut explicitValues := #[]
  for source in closed, index in [:closed.size] do
    let source ← source.inContext frame.context
    let selected := actual.find? (·.index == index)
    let retained ← match selected with
      | some selected => markValue frame.environment.marks selected.value source
      | none =>
        unless ← isProof source do
          throwError "a named source lost an original computational argument"
        pure source
    arguments := arguments.push retained
    let explicit := (information.paramInfo[index]?.map (·.isExplicit)).getD true
    if explicit && !(← isProof source) then
      let some selected := selected
        | throwError "a named descriptor lost an original explicit computational argument"
      explicitSources := explicitSources.push retained
      explicitValues := explicitValues.push selected.value
  let expression ← IO.ofExcept <|
    (withApplicationArguments expression arguments).mapError IO.userError
  let role := (← origin expression).role
  if role.kind == .function then return ← closure expression
  descriptor expression address explicitSources (some (← fieldClosures role))
    (some explicitValues)

/-- Retain the complete declared native record and its original delayed fields. Formation
does not evaluate a comparison, constructor action or any of its mathematical data. Each
later field demand retains this same selected interface as its native projection parent. -/
private partial def nativeInterface (expression : Expr) : LowerM ValueBinding := do
  let role := (← origin expression).role
  if role.kind == .function then return ← closure expression
  unless role.kind == .record do
    throwStratum .noImplementation
      "the selected native interface has no computational record fields"
  stageRecord (← RecordLayout.ofSource role) (← fieldClosures role)

/-- Native fields of an ordinary registered constant whose definition `field` may open.
Published element descriptors do not use these closures: their fields require computation. -/
private partial def fieldClosures (role : SourceLayout)
    (inputFields : Array (Name × ValueBinding × Array Name) := #[]) :
    LowerM (Array ValueBinding) := do
  let frame ← read
  let mut fields := #[]
  for prepared in role.fields do
    if prepared.wireIndex.isSome then
      let mut retained : Option ValueBinding := none
      if let some (_, operand, path) := inputFields.find?
          (fun selected => selected.1 == prepared.projection) then
        let graph ← frame.environment.transaction.view
        let frontier ← IO.ofExcept <|
          (graph.projectionFrontier operand path).mapError IO.userError
        if let some (_, remaining) := frontier then
          if remaining.isEmpty then
            -- The rigid producer selected this exact input path, and every field is
            -- already available. Normal projection publishes its original reference;
            -- this branch never asks an executor for an unavailable native field.
            let selected ← projectPath operand path
            let graph ← frame.environment.transaction.view
            let environment ← runtimeEnvironment
            let checked ← environment.checkResult graph (← prepared.toLayout) selected
            retained := some checked.root
      match retained with
      | some value => fields := fields.push value
      | none => fields := fields.push (← closure (← prepared.source.inContext frame.context))
  return fields

/-- Retain the native field code of an endpoint declared by this actual named morphism.
The endpoint is read before specialization, in its original rigid parameter telescope. The
same registered-constant authority used by `namedConstant` supplies its field closures;
a formal endpoint or a computation-produced choice remains an unchanged descriptor.
The map's sealed original argument table supplies every actual computational occurrence. -/
private partial def selectedEndpointFields? (sourceEnd : Bool) (hom : ValueBinding) :
    LowerM (Option (Array ValueBinding)) := do
  let frame ← read
  let graph ← frame.environment.transaction.view
  let some descriptorView ← InputDescriptorView.namedMorphism? graph
      (← frame.environment.codes.get) hom | return none
  let some request := descriptorView.family
    | throwError "the selected endpoint lost its original named morphism family"
  let .primitive (.registered family) levels := request.action
    | throwError "the selected endpoint lost its registered source family"
  let some application := request.application | return none
  let state ← semanticState
  let declaredType := family.source.familyType.instantiateLevelParams family.universeParams levels
  let endpointCode? : Option (Expr × Array (Name × Nat × Array Name)) ←
      forallBoundedTelescope declaredType (some application.arguments.size) fun formals result => do
    unless formals.size == application.arguments.size do
      throwError "the selected endpoint lost its complete original parameter telescope"
    -- Keep the authored Hom spine when it is already explicit. Its native projection
    -- may reduce past the endpoint-bearing interface at stronger transparency.
    let result ← if result.isAppOfArity ``Quiver.Hom 4 then pure result else whnfR result
    unless result.isAppOfArity ``Quiver.Hom 4 do return none
    let endpoint := result.getAppArgs[if sourceEnd then 2 else 3]!
    let .const declaration _ := endpoint.getAppFn | return none
    unless isRegisteredDescriptor state declaration do return none
    -- Only this original rigid endpoint family can authorize an input-backed field.
    -- Keep a separate full-index map because proof formals are not runtime inputs.
    let mut computational := #[]
    let mut sourceIndices : Array Nat := #[]
    for formal in formals, sourceIndex in [:formals.size] do
      unless ← isProof formal do
        computational := computational.push formal
        sourceIndices := sourceIndices.push sourceIndex
    let mut routes : Array (Name × Nat × Array Name) := #[]
    let endpointType ← whnf (← inferType endpoint)
    if let some structureName := endpointType.getAppFn.constName? then
      if let some info := getStructureInfo? (← getEnv) structureName then
        for fieldName in info.fieldNames, fieldIndex in [:info.fieldNames.size] do
          let some projection := info.getProjFn? fieldIndex
            | throwError "the declared endpoint lost its original field projection"
          let fieldValue ← mkProjection endpoint fieldName
          unless ← isProof fieldValue do
            if let some (position, path) ← sourceInputProjection? fieldValue computational then
              let some sourceIndex := sourceIndices[position]?
                | throwError "the declared endpoint lost its complete original input position"
              routes := routes.push (projection, sourceIndex, path)
    let code ← mkLambdaFVars formals endpoint
      (usedOnly := false) (usedLetOnly := false)
    return some (code, routes)
  let some (endpointCode, routes) := endpointCode? | return none
  let some original := request.origin.application
    | throwError "the selected endpoint lost its complete original argument table"
  unless original.arguments.size == application.arguments.size do
    throwError "the selected endpoint changed its original argument positions"
  let mut arguments := #[]
  for parameter in application.arguments do
    let source ← parameter.source.source.inContext frame.context
    let source ← match original.arguments[parameter.sourceIndex]?.bind id with
      | some value => markValue frame.environment.marks value source
      | none =>
        if parameter.wireIndex.isSome then
          throwError "the selected endpoint is missing an original computational argument"
        pure source
    arguments := arguments.push source
  let endpoint := (mkAppN endpointCode arguments).headBeta
  let role := (← origin endpoint).role
  let mut inputFields := #[]
  for (projection, sourceIndex, path) in routes do
    unless role.fields.any (·.projection == projection) do
      throwError "the selected endpoint changed a declared original field"
    let some operand := original.arguments[sourceIndex]?.bind id
      | throwError "the selected endpoint lost its original field input"
    inputFields := inputFields.push (projection, operand, path)
  return some (← fieldClosures role inputFields)

/-- The explicit arguments of an application that are not proofs. -/
private partial def explicitArguments (expression : Expr) : LowerM (Array Expr) := do
  let arguments := expression.getAppArgs
  let info ← getFunInfoNArgs expression.getAppFn arguments.size
  let mut selected := #[]
  for argument in arguments, index in [:arguments.size] do
    let explicit := (info.paramInfo[index]?.map (·.isExplicit)).getD true
    if explicit && !(← isProof argument) then selected := selected.push argument
  return selected

/-- Select one field of a checked source record. A declared interface or selected instance
may expose its exact native constructor without running an eliminator. Other records retain
their original runtime parent and use the ordinary field demand. -/
private partial def field (owner : Name) (index : Nat) (value : Expr) (name : MessageData) :
    LowerM ValueBinding := do
  let traceInclusion := (value.find? (·.isConstOf
    `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traceInclusion then dbg_trace "[inclusion.field] enter owner={owner} index={index}"
  if let some native ← nativeInterfaceSource? value then
    let original := .proj owner index value
    let role := (← origin original).role
    if role.kind == .record then return ← nativeInterface original
    let frame ← read
    -- Inspect the parent only, then read its exact field without reducing that field's
    -- mathematical body. Intermediate native records retain the complete original path.
    let parent ← frame.context.inputProjectionSource native (frame.bound.toArray.map (·.1))
    let [constructor] := (← getConstInfoInduct owner).ctors
      | throwError "the selected native interface has no unique record constructor"
    if parent.getAppFn.isConstOf constructor then
      let some selected ← projectCore? parent index
        | throwError "the selected native interface lost its original constructor field"
      return ← lower selected
    return ← lower (.proj owner index parent)
  if let .mdata data head := value.getAppFn then
    checkSelectedAddress data
    if (selectedReference? data).isSome || (namedElement? data).isSome ||
        selectedPointBoundary data ||
        data.getName `CasCompiler.source.kind == ``RoutedMethodFamily ||
        data.getName `CasCompiler.source.kind == ``ObjectEntry.application then
      return ← project (← lower value) index name
    if let some (declaration, _) := selectedDescriptor? data then
      let native := (mkAppN head value.getAppArgs).consumeMData
      unless native.getAppFn.isConstOf declaration do
        throwError "the selected descriptor lost its original declaration application"
      -- This original named descriptor authorizes its native definition fields. In
      -- particular a field closure must not re-publish that same descriptor recursively.
      if let some unfolded ← unfoldSourceApplication? native then
        return ← lower (.proj owner index unfolded)
  if let .mdata data _ := value then
    if (markedKey? data).isSome ||
        data.getName `CasCompiler.source.kind == ``PresentationFamily then
      if traceInclusion then dbg_trace "[inclusion.field] marked parent: before lower"
      let loweredParent ← lower value
      if traceInclusion then dbg_trace "[inclusion.field] marked parent: after lower; before project"
      return ← project loweredParent index name
  if traceInclusion then dbg_trace "[inclusion.field] before inferType"
  let inferredType ← inferType value
  if traceInclusion then dbg_trace "[inclusion.field] after inferType; before type whnf"
  let normalizedType ← whnf inferredType
  if traceInclusion then dbg_trace "[inclusion.field] after type whnf; before isClass head={repr normalizedType.getAppFn.constName?}"
  let selectedClass ← isClass? normalizedType
  if traceInclusion then dbg_trace "[inclusion.field] after isClass result={selectedClass.isSome}"
  if selectedClass.isSome then
    let frame ← read
    -- Inspect this parent only. Constructor arguments remain unchanged, and exact
    -- retained inputs stay opaque to the existing metadata-preserving source reader.
    let normalizedParent ← frame.context.inputProjectionSource value
      (frame.bound.toArray.map (·.1))
    let [constructor] := (← getConstInfoInduct owner).ctors
      | throwError "the selected instance field has no unique native record constructor"
    if normalizedParent.getAppFn.isConstOf constructor then
      let some reduced ← projectCore? normalizedParent index
        | throwError "the selected instance lost its native constructor field"
      return ← lower reduced
    if let .const declaration _ := normalizedParent.getAppFn then
      if ← isMatcher declaration then
        throwStratum .noImplementation m!"{declaration} is a match with no published operation"
      match (← getEnv).find? declaration with
      | some (.recInfo _) | some (.quotInfo _) =>
        throwStratum .noImplementation
          m!"{declaration} is an eliminator with no published operation"
      | _ =>
        throwStratum .noImplementation m!"{declaration} has no native instance constructor"
  if let .const declaration _ := value.consumeMData.getAppFn then
    if traceInclusion then dbg_trace "[inclusion.field] declaration {declaration}: before authorization"
    if isRegisteredDescriptor (← semanticState) declaration then
      if traceInclusion then dbg_trace "[inclusion.field] declaration {declaration}: before unfolding"
      if let some unfolded ← unfoldSourceApplication? value.consumeMData then
        if traceInclusion then dbg_trace "[inclusion.field] declaration {declaration}: unfolded; before lower"
        return ← lower (.proj owner index unfolded)
    if traceInclusion then dbg_trace "[inclusion.field] declaration {declaration}: unchanged"
  let frame ← read
  if traceInclusion then dbg_trace "[inclusion.field] before environment"
  let environment ← retainedEnvironment
  if traceInclusion then dbg_trace "[inclusion.field] after environment; before retained-source check"
  -- An unretained inner projection still owns its native definition boundary. Lower it
  -- before the outer demand; flattening through its named field closure would re-enter
  -- that same projection code. Actual retained roots keep their complete selected path.
  let retained ← environment.hasRetainedSource frame.context value
  if traceInclusion then dbg_trace "[inclusion.field] after retained-source check result={retained}"
  if !retained then
    if traceInclusion then dbg_trace "[inclusion.field] unretained parent: before lower"
    let loweredParent ← lower value
    if traceInclusion then dbg_trace "[inclusion.field] unretained parent: after lower; before project"
    return ← project loweredParent index name
  if traceInclusion then dbg_trace "[inclusion.field] before projection source path"
  let (parent, path) ← projectionSourcePath environment (.proj owner index value)
  if traceInclusion then dbg_trace "[inclusion.field] after projection source path length={path.size}"
  if path.isEmpty then
    if traceInclusion then dbg_trace "[inclusion.field] empty path: before parent lower"
    let loweredParent ← lower value
    if traceInclusion then dbg_trace "[inclusion.field] empty path: after parent lower; before project"
    return ← project loweredParent index name
  if traceInclusion then dbg_trace "[inclusion.field] selected path: before parent lower"
  let loweredParent ← lower parent
  if traceInclusion then dbg_trace "[inclusion.field] selected path: after parent lower; before projectPath"
  projectPath loweredParent path

/-- Read only the exact native projection chain, stopping at source selections and formal
class definitions. No intermediate projected record is lowered while discovering the path. -/
private partial def projectionSourcePath (environment : RuntimeEnvironment) (expression : Expr) :
    LowerM (Expr × Array Name) := do
  let some projection ← SourceProjection.ofExpr? expression | return (expression, #[])
  if projection.info.fromClass &&
      !(← environment.hasRetainedSource (← read).context projection.parent) then
    return (expression, #[])
  let (parent, path) ← projectionSourcePath environment projection.parent
  return (parent, path.push projection.declaration)

private partial def project (operand : ValueBinding) (index : Nat) (field : MessageData) :
    LowerM ValueBinding := do
  let frame ← read
  let identities ← supply
  let some layout := operand.role.fields[index]?
    | throwError "internal: the source field {field} is outside its retained record interface"
  unless layout.wireIndex.isSome do
    throwError "internal: the source field {field} is a proof and has no computational value"
  let graph ← frame.environment.transaction.view
  let request ← PreparedRequest.forProjection identities frame.program
    (← frame.environment.ledger.allocate) frame.context graph operand index (← parameters)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

/-- Complete the longest already stored prefix as one selected demand. A lazy frontier keeps
the ordinary one-field execution boundary, including its provider's atomic reply admission. -/
private partial def projectPath (operand : ValueBinding) (path : Array Name) :
    LowerM ValueBinding := do
  if path.isEmpty then return operand
  let frame ← read
  let graph ← frame.environment.transaction.view
  let frontier ← IO.ofExcept <| (graph.projectionFrontier operand path).mapError IO.userError
  if let some (_, remaining) := frontier then
    let count := path.size - remaining.size
    if count > 0 then
      let request ← PreparedRequest.forStoredProjection (← supply) frame.program
        (← frame.environment.ledger.allocate) frame.context graph operand
        (path.extract 0 count) (← parameters)
        (validatedEnvironment := some (← retainedEnvironment))
      return ← projectPath (← demand request) remaining
  let projection := path[0]!
  let some field := operand.role.fields.find? (·.projection == projection)
    | throwError "the native projection path is outside its retained record interface"
  projectPath (← project operand field.sourceIndex m!"{projection}") (path.extract 1 path.size)

/-- Keep a source argument's native projection chain while marking only its actual root.
Inert metadata stays in place; source boundaries and formal class fields are lowered normally. -/
private partial def projectionArgumentSource (environment : RuntimeEnvironment)
    (expression : Expr) : LowerM Expr := do
  let frame ← read
  if let .mdata data body := expression then
    -- Match SourceProjection's boundary rule before traversing any parent projection.
    if !data.contains `CasCompiler.lower.value && !data.contains `CasCompiler.source.kind &&
        !data.contains `CasCompiler.selection then
      return .mdata data (← projectionArgumentSource environment body)
  if let some projection ← SourceProjection.ofExpr? expression then
    if !projection.info.fromClass ||
        (← environment.hasRetainedSource frame.context projection.parent) then
      let parent ← projectionArgumentSource environment projection.parent
      return .proj (← getConstInfoCtor projection.info.ctorName).induct projection.info.i parent
  let source ← argumentSource environment expression
  let value ← lower source
  return ← markValue frame.environment.marks value source

/-- Retain each actual projection root before preparing the complete selected path.
Native metadata distinguishes formal selected instances from runtime class records. No
intermediate whole-record demand is manufactured for a nested stored source argument. -/
private partial def argumentSource (environment : RuntimeEnvironment) (expression : Expr) :
    LowerM Expr := do
  let frame ← read
  -- Use the same retained constructor argument as endpoint lowering, so native
  -- argument admission checks its original source reference and association chain.
  if let some endpoint := selectedEndpoint? expression then
    if ← environment.hasRetainedSource frame.context endpoint then
      return ← argumentSource environment endpoint
    -- The endpoint of this exact selected arrow is itself a source boundary.
    -- Do not rewrite its Arrow projection as an ordinary stored-record path.
    return expression
  if let .mdata data body := expression then
    if (markedKey? data).isSome || (data.find `CasCompiler.source.kind).isSome then
      return expression
    if (selectedField? data).isSome then
      let value ← lower expression
      return ← markValue frame.environment.marks value expression
    return .mdata data (← argumentSource environment body)
  if let .fvar id := expression then
    if let some binding := frame.context.bindings.find? (·.expression.fvarId! == id) then
      if frame.bound.contains binding.id then return expression
    if let some value := (← id.getDecl).value? then
      return ← argumentSource environment value
  let some projection ← SourceProjection.ofExpr? expression | return expression
  if projection.info.fromClass &&
      !(← environment.hasRetainedSource frame.context projection.parent) then
    return expression
  let parent ← projectionArgumentSource environment projection.parent
  return .proj (← getConstInfoCtor projection.info.ctorName).induct projection.info.i parent

private partial def actualArguments (arguments : Array Expr)
    (deferAfter : Option Nat := none) (required : Option (Array Nat) := none)
    (traceArguments : Bool := false) :
    LowerM (Array ClosedTerm × Array RuntimeArgument) := do
  let frame ← read
  if traceArguments then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[lower.arguments] before environment context={frame.context.bindings.size} arguments={arguments.size} ticks={ticks}"
  let environment ← retainedEnvironment
  if traceArguments then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[lower.arguments] after environment ticks={ticks}"
  let mut values : Array (Nat × ValueBinding) := #[]
  let mut sources : Array Expr := #[]
  for argument in arguments, index in [:arguments.size] do
    if traceArguments then
      let ticks ← IO.getNumHeartbeats
      dbg_trace "[lower.argument] before slot classification index={index} ticks={ticks}"
    if ← isProof argument then
      if traceArguments then
        let ticks ← IO.getNumHeartbeats
        dbg_trace "[lower.argument] original proof slot index={index} ticks={ticks}"
      sources := sources.push argument
    else
      -- Complete source coverage has already identified unused admission evidence. Keep its
      -- formal slot without touching its source parent or manufacturing a runtime value.
      if deferAfter.any (· < index) && required.any (fun needed => !needed.contains index) then
        if traceArguments then
          let ticks ← IO.getNumHeartbeats
          dbg_trace "[lower.argument] original unused slot index={index} ticks={ticks}"
        sources := sources.push argument
        continue
      -- Used evidence follows ordinary retained-source preparation first. A projection of a
      -- lazy parent is a genuine demand; only unanchored native evidence code remains lazy.
      if traceArguments then
        let ticks ← IO.getNumHeartbeats
        dbg_trace "[lower.argument] before source index={index} head={repr argument.consumeMData.getAppFn.constName?} ticks={ticks}"
      let source ← argumentSource environment argument
      if traceArguments then
        let ticks ← IO.getNumHeartbeats
        dbg_trace "[lower.argument] after source index={index} ticks={ticks}"
        let selected := source.find? fun term => match term with
          | .mdata data _ => !(data.getName `CasCompiler.source.kind).isAnonymous
          | _ => false
        let selection := selected.map fun term => match term with
          | .mdata data _ =>
            (data.getName `CasCompiler.source.kind, data.getString `CasCompiler.source.id,
              data.getName `CasCompiler.source.declaration)
          | _ => (Name.anonymous, "", Name.anonymous)
        let ticks ← IO.getNumHeartbeats
        dbg_trace "[lower.argument] selected source index={index} head={repr source.consumeMData.getAppFn.constName?} selected={repr selection} ticks={ticks}"
      let deferred ← if deferAfter.any (· < index) then
          environment.hasRetainedSource frame.context source <&> Bool.not
        else pure false
      if traceArguments then
        let ticks ← IO.getNumHeartbeats
        dbg_trace "[lower.argument] before lower index={index} deferred={deferred} ticks={ticks}"
      let value ← if deferred then closure source else lower source
      if traceArguments then
        let ticks ← IO.getNumHeartbeats
        dbg_trace "[lower.argument] after lower index={index} value={repr value.value} ticks={ticks}"
      values := values.push (index, value)
      sources := sources.push source
  if traceArguments then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[lower.arguments] before runtime table values={values.size} ticks={ticks}"
  let graph ← frame.environment.transaction.view
  let marks ← frame.environment.marks.get
  let actual ← values.mapM fun (index, value) => do
    let .ok argument := RuntimeArgument.ofValue graph index value marks
      | throwError "internal: a lowered source argument is outside the active graph"
    return argument
  if traceArguments then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[lower.arguments] runtime table ready; before source closure count={sources.size} ticks={ticks}"
  let closed ← sources.mapIdxM fun index argument => do
    if traceArguments then
      let ticks ← IO.getNumHeartbeats
      dbg_trace "[lower.argument] before final source closure index={index} ticks={ticks}"
    let source ← frame.context.close argument
    if traceArguments then
      let ticks ← IO.getNumHeartbeats
      dbg_trace "[lower.argument] after final source closure index={index} ticks={ticks}"
    return source
  if traceArguments then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[lower.arguments] complete ticks={ticks}"
  return (closed, actual)

/-- Retain the original admission arguments and use the common application result plan.
Only Prop hypotheses are erased. Selected lazy fields use ordinary projection demands;
neither the admission nor its evidence is evaluated to discover a record interface. -/
private partial def admission (expression : Expr) (data : MData) (body : Expr) :
    LowerM ValueBinding := do
  let frame ← read
  let declaration := data.getName `CasCompiler.source.declaration
  let arguments := body.getAppArgs
  let family := body.getAppFn
  unless family.isLambda && arguments.size ==
      data.getNat `CasCompiler.source.admissionArguments 0 do
    throwError "internal: the admitted element lost its complete point family"
  let element := data.getNat `CasCompiler.source.element 0
  unless element < arguments.size do
    throwError "internal: the admitted element lost its value"
  lambdaBoundedTelescope family arguments.size fun parameters value => do
    let some admitted := value.find? (·.getAppFn.isConstOf declaration)
      | throwError "internal: the admitted point family lost its registered declaration"
    unless parameters.size == arguments.size && admitted.getAppArgs == parameters do
      throwError "internal: the admitted point family changed its complete argument telescope"
  -- Establish complete source coverage before preparing any actual argument. The runtime
  -- independently seals the same formal coverage against its exact prepared role telescope.
  let sourceArguments ← arguments.mapM fun argument => frame.context.close argument
  let (_, sourceApplication) ← ApplicationLayout.ofSource
    (← SourceLayout.ofTerm (← frame.context.close family)) frame.context sourceArguments
  let required ← sourceApplication.inputResultArguments ((← parameters).map (·.source))
  if required.isNone then
    for argument in arguments.extract (element + 1) arguments.size do
      unless ← isProof argument do
        throwStratum .noImplementation
          m!"the admission {data.getString `CasCompiler.source.id} requires unavailable computational evidence fields"
  let callable ← closure family
  let (closed, actual) ← actualArguments arguments (some element) required
  let request ← PreparedRequest.forApplication (← supply) frame.program
    (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  if (← request.inputResultPlan (← frame.environment.transaction.view)).isSome then
    return ← demand request
  -- Proof-only admissions also retain a transparent presentation of the original value
  -- (for example a finite subset's extent). It is a descriptor, not a native field table:
  -- no result field is invented from its type, and no choice definition is opened.
  for argument in arguments.extract (element + 1) arguments.size do
    unless ← isProof argument do
      throwStratum .noImplementation
        m!"the admission {data.getString `CasCompiler.source.id} requires unavailable computational evidence fields"
  let some value := actual.find? (·.index == element)
    | throwError "internal: the admitted element lost its actual value"
  let .ok payload := ValuePayload.descriptor .null
      #[{ path := #[], binding := value.value, fieldIndex := none }]
    | throwError "internal: the admitted element has an invalid reference layout"
  stage expression payload

/-- Keep each original formal argument once when a native record conversion returns only
its input projections. Delta substitution may duplicate a closed record expression beneath
several dependent fields; the existing prepared application preserves its actual occurrence.
Source coverage is complete before any argument is touched. Unused computational arguments
leave this path unchanged. Retained arguments still require this boundary: unfolding their
source expressions would replace unavailable actual fields with reconstructed source fields. -/
private partial def nativeInputRecord? (expression : Expr) : LowerM (Option ValueBinding) := do
  let .const declaration _ := expression.getAppFn | return none
  let arguments := expression.getAppArgs
  if arguments.isEmpty then return none
  let traceInclusion := (expression.find? (·.isConstOf
    `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  let state ← semanticState
  unless !isRegisteredComputation state declaration &&
      !isRegisteredDescriptor state declaration &&
      ((← getEnv).getProjectionFnInfo? declaration).isNone do return none
  let some (.defnInfo _) := (← getEnv).find? declaration | return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] before native definition unfolding ticks={ticks}"
  let some expanded ← unfoldSourceApplication? expression | return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] after native definition unfolding ticks={ticks}"
  let some constructor := expanded.getAppFn.constName? | return none
  let some (.ctorInfo _) := (← getEnv).find? constructor | return none
  let frame ← read
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] before closing actual sources count={arguments.size} ticks={ticks}"
  let sourceArguments ← arguments.mapM fun argument => do
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      dbg_trace "[inclusion.record] before source close head={repr argument.getAppFn.constName?} arity={argument.getAppNumArgs} ticks={ticks}"
    let closed ← frame.context.close argument
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      dbg_trace "[inclusion.record] after source close ticks={ticks}"
    return closed
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] actual sources closed; before bare SourceLayout ticks={ticks}"
  -- This bare constant has no captured source bindings. Its actual arguments retain
  -- the complete original frame and still undergo the concrete coverage check below.
  let source ← (show MetaM SourceLayout from withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    SourceLayout.ofTerm (← empty.close expression.getAppFn))
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] bare SourceLayout complete; before concrete ApplicationLayout ticks={ticks}"
  let (result, application) ← ApplicationLayout.ofSource source frame.context sourceArguments
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] concrete ApplicationLayout complete fields={result.fields.size} ticks={ticks}"
  unless result.kind == .record && result.fields.any
      (fun field => field.wireIndex.isSome && !field.precedingDependencies.isEmpty) do return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] before original parameter table ticks={ticks}"
  let actualParameters ← parameters
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] original parameter table ready; before inputResultArguments ticks={ticks}"
  let required? ← application.inputResultArguments (actualParameters.map (·.source))
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] after inputResultArguments complete={required?.isSome} ticks={ticks}"
  let some required := required? | return none
  -- Ordinary application admission stays total. This conservative path never evaluates a
  -- source slot that the complete native result and its type dependencies did not require.
  for argument in application.arguments do
    if argument.wireIndex.isSome && !required.contains argument.sourceIndex then return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] complete original coverage; before callable closure ticks={ticks}"
  let callable ← closure expression.getAppFn
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] callable closure ready; before actualArguments ticks={ticks}"
  let (closed, actual) ← actualArguments arguments (traceArguments := traceInclusion)
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] actualArguments ready; before prepared application ticks={ticks}"
  let request ← PreparedRequest.forApplication (← supply) frame.program
    (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] prepared application ready; before actual inputResultPlan ticks={ticks}"
  let actualPlan ← request.inputResultPlan (← frame.environment.transaction.view)
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] after actual inputResultPlan complete={actualPlan.isSome} ticks={ticks}"
  unless actualPlan.isSome do
    throwStratum .noImplementation
      "the native record conversion requires unavailable input fields"
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    dbg_trace "[inclusion.record] before demand ticks={ticks}"
  return some (← demand request)

private partial def apply (callable : ValueBinding) (arguments : Array Expr) :
    LowerM ValueBinding := do
  if arguments.isEmpty then return callable
  let frame ← read
  let traceArguments := (callable.role.source.expression.find? (·.isConstOf
    `CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormBaseChangeDeclaration)).isSome
  if traceArguments then dbg_trace "[basechange.application] callable={repr callable.value} arguments={arguments.size}"
  let (closed, actual) ← actualArguments arguments (traceArguments := traceArguments)
  if traceArguments then dbg_trace "[basechange.application] actual inputs prepared"
  let request ← PreparedRequest.forApplication (← supply) frame.program
    (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

private partial def record (expression : Expr) (fields : Array Expr) : LowerM ValueBinding := do
  let frame ← read
  traceExpensiveLower "record.total" expression frame.context.bindings.size do
    let role := (← origin expression).role
    let layout ← traceExpensiveLower "record.layout" expression frame.context.bindings.size do
      RecordLayout.ofSource role
    let mut values := #[]
    for prepared in layout.fields do
      if prepared.field.wireIndex.isSome then
        let some field := fields[prepared.field.sourceIndex]?
          | throwError "internal: a source constructor lost a computational field"
        let value ← traceExpensiveLower
            s!"record.lowerField.{prepared.field.projection}[{prepared.field.sourceIndex}]"
            field frame.context.bindings.size do
          lower field
        values := values.push value
    stageRecord layout values

/-- Stage the same prepared record from its computational fields, in source order.
The initial layout remains sealed; actual runtime context capture occurs after field lowering. -/
private partial def stageRecord (layout : RecordLayout) (values : Array ValueBinding)
    (envelope : Option (Json × Array ContainerSlot) := none) :
    LowerM ValueBinding := do
  let frame ← read
  let expression := layout.source.source.expression
  traceExpensiveLower "record.stage.total" expression frame.context.bindings.size do
    let identities ← supply
    let produced ← originFor layout.source
    unless values.size == (layout.fields.filter (·.field.wireIndex.isSome)).size do
      throwError "internal: a source record has a different number of computational fields"
    let mut draft ← traceExpensiveLower "record.stage.draft" expression
        frame.context.bindings.size do
      frame.environment.transaction.draft
    let mut selected ← traceExpensiveLower "record.prefix.begin" expression
        frame.context.bindings.size do
      RecordPrefix.prepare identities produced.program produced.occurrence layout
        draft.view produced.sourceMarks
    for value in values, wireIndex in [:values.size] do
      -- Metadata is read only to label this timed call; binding still uses the original prefix.
      let projection := (layout.fields.find? (fun prepared =>
        prepared.field.wireIndex == some wireIndex)).map (·.field.projection)
      let (next, extended, _) ← traceExpensiveLower
          s!"record.prefix.bindField.{repr projection}[{wireIndex}]"
          value.role.source.expression frame.context.bindings.size do
        draft.bindField selected value
      draft := next
      selected := extended
    let payload ← traceExpensiveLower "record.prefix.finish" expression
        frame.context.bindings.size do
      IO.ofExcept <| selected.finish.mapError IO.userError
    let payload ← match envelope with
      | none => pure payload
      | some (packet, slots) => do
        let .product fields := payload.data
          | throwError "the original source prefix lost its complete native field table"
        IO.ofExcept <| (ValuePayload.container packet slots fields none).mapError IO.userError
    let (complete, binding) ← traceExpensiveLower "record.stage.store" expression
        frame.context.bindings.size do
      draft.stage produced payload
    let installed ← traceExpensiveLower "record.stage.install" expression
        frame.context.bindings.size do
      frame.environment.transaction.installDraft complete
    match installed with
    | .ok () => return binding
    | .error failure => throwError "internal: a source record could not be retained: {repr failure}"

/-- A published computation of a selected lift (`LiftFamily.mark`) at its evidence parameters: a
prepared demand on the lift boundary, whose fields are the lift's ports. -/
private partial def liftFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let lift := data.getString `CasCompiler.source.id
  let some row := (← semanticState).lifts.find? (·.id.raw == lift)
    | throwError "internal: the selected lift {lift} is not registered"
  let some port := LiftPort.ofName? (data.getString `CasCompiler.source.port)
    | throwError "internal: the selected lift computation has no port"
  let family ← LiftFamily.forLift row port
  let (head, levels) ← family.instantiate
  unless ← isDefEq head body.getAppFn do
    throwError "internal: the selected lift computation changed its family"
  let (closed, actual) ← actualArguments body.getAppArgs
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.lift family) (← levels.mapM instantiateLevelMVars)
    frame.context closed actual #[] (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

/-- Prepare the original comparison family and its exact complete endpoint values before any
point demand. Default endpoints use the same admitted native parameter positions; explicitly
supplied endpoints retain their own scoped bindings. No endpoint field data is manufactured. -/
private partial def presentationFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let address := data.getString `CasCompiler.source.id
  let some row := (← semanticState).presentations.find? (·.id.raw == address)
    | throwError "the selected presentation {address} is not registered"
  let family ← PresentationFamily.forEntry row
  let (applied, supplied) ← family.unmark data body
  let (head, levels) ← family.instantiate
  unless ← isDefEq head applied.getAppFn do
    throwError "the selected presentation changed its native declaration"
  let (closed, actual) ← actualArguments applied.getAppArgs
  let endpoints ← match supplied with
    | some endpoints => pure endpoints
    | none => do
      let mut arguments ← closed.mapM (·.inContext frame.context)
      for argument in actual do
        arguments := arguments.set! argument.index (← markValue frame.environment.marks
          argument.value arguments[argument.index]!)
      family.endpoints (mkAppN applied.getAppFn arguments)
  let (endpointSources, endpointValues) ← actualArguments #[endpoints.1, endpoints.2]
  let request ← PreparedRequest.forPresentation (← supply) frame.program
    (← frame.environment.ledger.allocate) family (← levels.mapM instantiateLevelMVars)
    frame.context closed actual endpointSources endpointValues (← parameters)
    (← frame.environment.transaction.view) (← frame.environment.marks.get)
  demand request

/-- Retain the original receiver once, then its exact category inputs and ordinary delayed
callable/application. The result request still contains the complete native composite family,
so whole input-projection results complete before any registration is inspected. -/
private partial def routedMethodFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let (body, supplied) ← routedMethodInputs data body
  let family ← RoutedMethodFamily.fromMark data
  let (head, levels) ← family.instantiate
  unless body.getAppNumArgs == family.parameterCount + 1 &&
      (← isDefEq head body.getAppFn) do
    throwError "the selected routed method changed its complete native family application"
  let some source := body.getAppArgs[family.parameterCount]?
    | throwError "the routed method lost its original receiver"
  let receiver ← lower source
  let environment ← runtimeEnvironment
  let arguments ← environment.methodParameters frame.context frame.environment.transaction
    frame.environment.marks frame.environment.ledger.allocate family
    (body.getAppArgs.extract 0 family.parameterCount) receiver
    (fun expression => lower expression frame) frame.environment.sourceSnapshot
  let (closed, actual) ← actualArguments arguments
  let levels ← levels.mapM instantiateLevelMVars
  let mut scope := #[]
  if let some supplied := supplied then
    let actions ← family.specializeActions levels arguments
    let inputs ← supplied.mapM (·.mapM lower)
    discard <| environment.methodActionsWithInputs frame.context
      (← frame.environment.transaction.view) frame.environment.marks family actions inputs
    scope := inputs.flatten
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.routedMethod family)
    levels frame.context closed actual scope (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  let callable ← demand request
  apply callable #[← markValue frame.environment.marks receiver source]

/-- A property remains one complete primitive observation of its accepted native proposition.
The original receiver fixes every source category slot before the request is emitted. -/
private partial def propertyObservation (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let family ← PropertyFamily.fromMark data
  let (levels, arguments, source) ← family.application body
  let receiver ← lower source
  let environment ← runtimeEnvironment
  let arguments ← environment.sourceCategoryParameters frame.context frame.environment.transaction
    frame.environment.marks frame.environment.ledger.allocate family.route.source
    family.categoryFamily family.universeParams family.parameterCount arguments receiver
    (fun expression => lower expression frame) frame.environment.sourceSnapshot
  let marked ← markValue frame.environment.marks receiver source
  let (closed, actual) ← actualArguments (arguments.push marked)
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.property family) levels frame.context closed actual
    #[] (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

/-- Retain the exact published application field as a checked delayed native family. Its
parameters are ordinary actual source inputs; no application definition is executed here. -/
private partial def objectApplicationFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let id := data.getString `CasCompiler.source.id
  let #[entry] := (← semanticState).objects.filter (·.id.raw == id)
    | throwError "the selected application lost its exact registered object owner"
  let family ← PointFamily.forApplication entry
  let .const declaration levels := body.getAppFn
    | throwError "the selected application lost its original native declaration"
  unless declaration == family.declaration &&
      data.getName `CasCompiler.source.declaration == family.declaration do
    throwError "the selected application changed its original native declaration"
  let arguments := body.getAppArgs
  let arity ← forallBoundedTelescope family.familyType (some arguments.size)
    fun formals _ => pure formals.size
  let (closed, actual) ← actualArguments (arguments.extract 0 arity)
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.application family) levels frame.context closed actual
    #[] (← parameters) (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  apply (← demand request) (arguments.extract arity arguments.size)

/-- A categorical endpoint descriptor retains this actual original arrow. If source formation
already supplied an exact binding for the endpoint, keep that binding instead. -/
private partial def pointEndpoint (arrow : ValueBinding) (source : Expr) (selector : String) :
    LowerM ValueBinding := do
  let frame ← read
  let environment ← retainedEnvironment
  if ← environment.hasRetainedSource frame.context source then
    return ← lower (← argumentSource environment source)
  let packet := Json.mkObj [("ctor", toJson "morphismEndpoint"),
    ("args", .arr #[.null, toJson selector])]
  let payload ← IO.ofExcept <| (ValuePayload.descriptor packet #[
    { path := #[.field "args", .index 0], binding := arrow, fieldIndex := none }]).mapError IO.userError
  stage source payload

/-- Retain a native arrow family without manufacturing endpoint/identity values at formation.
An explicit complete request retains its actual arrow, domain, endpoints and generalized point
once, then uses the ordinary prepared-boundary/input/transaction machinery. -/
private partial def categoricalPointFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let family ← CategoricalPointFamily.fromMark data
  let (levels, arguments) ← family.application body
  let (parameterSources, parameterValues) ← actualArguments
    (arguments.extract 0 family.parameterCount)
  if !family.invocation then
    let request ← PreparedRequest.forBoundary (← supply) frame.program
      (← frame.environment.ledger.allocate) (.point family) levels frame.context
      parameterSources parameterValues #[] (← parameters)
      (some (← frame.environment.transaction.view)) (← sourceMarks parameterSources)
      (validatedEnvironment := some (← retainedEnvironment))
    return ← demand request
  let mut native ← parameterSources.mapM (·.inContext frame.context)
  let mut originals : Array (Option ValueBinding) := Array.replicate family.parameterCount none
  for value in parameterValues do
    native := native.set! value.index
      (← markValue frame.environment.marks value.value native[value.index]!)
    originals := originals.set! value.index (some value.value)
  let (nativeArrow, bundle) ← family.arrowAt levels native
  let (nativeSource, nativeTarget) ← categoricalPointEndpoints nativeArrow
  let supplied ← family.request? arguments[family.parameterCount + 1]!
  let (arrow, domain, source, target, point) ← match supplied with
    | some supplied => do
      pure (← lower supplied.arrow, ← lower supplied.domain,
        ← lower supplied.source, ← lower supplied.target, ← lower supplied.point)
    | none => do
      let packet ← CategoricalPointPacket.prepare family originals
      let arrow ← stage nativeArrow packet.arrow
      let source ← pointEndpoint arrow nativeSource "source"
      let target ← pointEndpoint arrow nativeTarget "target"
      let domain ← if family.whole then pure source else lower arguments[family.parameterCount]!
      let point ← if family.whole then do
          let identity ← categoricalPointIdentity bundle nativeSource
          let payload ← IO.ofExcept <| (ValuePayload.descriptor
            (Json.mkObj [("ctor", toJson "identity"), ("args", .arr #[.null, .null])]) #[
              { path := #[.field "args", .index 0], binding := source, fieldIndex := none },
              { path := #[.field "args", .index 1], binding := source, fieldIndex := none }]).mapError IO.userError
          stage identity payload
        else lower arguments[family.parameterCount + 1]!
      pure (arrow, domain, source, target, point)
  let retain := fun (binding : ValueBinding) (source : Expr) =>
    markValue frame.environment.marks binding source
  let domainSource ← retain domain arguments[family.parameterCount]!
  let pointSource ← retain point arguments[family.parameterCount + 1]!
  let pointSource ← family.withRequest levels native
    (← retain arrow nativeArrow) domainSource
    (← retain source nativeSource) (← retain target nativeTarget) pointSource
  let (closed, actual) ← actualArguments (native ++ #[domainSource, pointSource])
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.point family) levels frame.context closed actual
    #[arrow, domain, source, target, point] (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

private partial def objectActionFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let family ← SourceActionFamily.fromMark data
  let (levels, arguments) ← family.application body
  let (closed, actual) ← actualArguments arguments
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.objectAction family) levels frame.context closed actual
    #[] (← parameters) (some (← frame.environment.transaction.view)) (← sourceMarks closed)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

/-- Keep the original whole-cone owner envelope beside the complete native request.
The runtime view substitutes its already admitted actuals into that retained formal owner;
the source formation's construction and interface are not prepared again. -/
private partial def wholeLimitFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let family ← LimitFamily.fromMark data
  let (levels, arguments, owner, _) ← family.application body
  let (closed, actual) ← actualArguments arguments
  let owner ← frame.context.close owner
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.limit family owner) levels frame.context closed actual
    #[] (← parameters) (some (← frame.environment.transaction.view))
    (← sourceMarks (closed.push owner))
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

/-- Continue the universal field of this exact completed cone. The complete original
declaration parameter table comes from that cone's producing request; explicit source
marks are checked against those same values before the new native field is prepared. -/
private partial def universalLimitFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let family ← LimitUniversalFamily.fromMark data
  let (levels, arguments, owner, selected, coneSource) ← family.application body
  let cone ← lower coneSource
  let graph ← frame.environment.transaction.view
  let some node := graph.find cone.value
    | throwError "the universal source lost its actual completed cone"
  let some completion ← frame.environment.transaction.completionFor? node.origin.occurrence
    | throwError "the universal source lost its cone's original preparation"
  let original := completion.request
  let .primitive (.limit presentation originalOwner) originalLevels := original.action
    | throwError "the universal source requires an original raw-cone request"
  unless presentation.entry.id == family.presentation.entry.id && originalLevels == levels &&
      completion.response.root.value == cone.value &&
      completion.response.root.associationIds.toList.isPrefixOf cone.associationIds.toList do
    throwError "the universal source changed its original completed cone"
  discard <| original.admitInputs graph
  let (native, values) ← original.markedArguments frame.environment.marks frame.context
    family.parameterCount
  let originalSelection ← presentation.ownerAt (← originalOwner.inContext frame.context) native
  unless originalSelection.source.construction == selected.source.construction do
    throwError "the universal source selected another original construction"
  let environment ← retainedEnvironment
  for argument in arguments, value in values do
    if let some value := value then
      environment.checkDeclaredInput frame.context graph (← frame.environment.marks.get)
        argument value
    else
      unless ← isProof argument do
        throwError "the universal source lost an original computational parameter"
  let (closed, actual) ← actualArguments native
  let owner ← frame.context.close owner
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.limitUniversal family owner) levels
    frame.context closed actual #[cone] (← parameters) (some graph)
    (← sourceMarks (closed ++ #[owner, ← frame.context.close coneSource]))
    (validatedEnvironment := some environment)
  demand request

/-- Invoke the complete source-prepared creation. The source plan's let-bindings or the
public request provide its actual Cone and IsLimit values at these same native positions. -/
private partial def creationFamily (data : MData) (body : Expr) : LowerM ValueBinding := do
  let frame ← read
  let prepared ← PreparedCreationFamily.fromMark frame.context data body
  let arguments ← prepared.arguments.mapM (·.inContext frame.context)
  let (closed, actual) ← actualArguments arguments
  let sources := closed ++ #[prepared.owner, prepared.requestFamily] ++ prepared.captureSources
  let request ← PreparedRequest.forBoundary (← supply) frame.program
    (← frame.environment.ledger.allocate) (.creation prepared) prepared.universes
    frame.context closed actual #[] (← parameters)
    (some (← frame.environment.transaction.view)) (← sourceMarks sources)
    (validatedEnvironment := some (← retainedEnvironment))
  demand request

/-- Retain a created object before any provider demand. Its complete original source-input
telescope is lowered once and rebound positionally into both the source and mapped diagrams. -/
private partial def formalCreationDescriptor (prepared : PreparedCreationFamily) :
    LowerM ValueBinding := do
  let frame ← read
  let arguments ← prepared.sourceArguments.mapM (·.inContext frame.context)
  let (closed, actual) ← actualArguments arguments
  let mut native : Array Expr := #[]
  for source in closed, index in [:closed.size] do
    let source ← source.inContext frame.context
    let marked ← match actual.find? (·.index == index) with
      | some argument => markValue frame.environment.marks argument.value source
      | none => do
        unless ← isProof source do
          throwError "the created source lost an original computational parameter"
        pure source
    native := native.push marked
  let prepared ← prepared.rebindSource frame.context native
  let owner ← prepared.owner.inContext frame.context
  closureWith owner fun _ => .creationOwner prepared

/-- Lower every original direct-limit declaration parameter once, then positionally mark the
same retained owner family. Explicit wire fields keep those exact bindings; implicit source
parameters remain in node.origin.role.source for later whole-cone and constructor-port use. -/
private partial def formalLimitDescriptor (expression : Expr) : LowerM (Option ValueBinding) := do
  let some selection ← NativeLimitSelection.ofExpr? expression | return none
  let frame ← read
  if let some prepared ← PreparedCreationFamily.ofSelection frame.context expression then
    return some (← formalCreationDescriptor prepared)
  let application := selection.source.interface.presentation.consumeMData
  unless selection.source.presentation.consumeMData.getAppFn.isConstOf
      selection.source.declaration do return none
  let (closed, actual) ← actualArguments application.getAppArgs
  let information ← getFunInfoNArgs application.getAppFn closed.size
  let mut native := #[]
  let mut explicitSources := #[]
  let mut explicitValues := #[]
  for source in closed, index in [:closed.size] do
    let source ← source.inContext frame.context
    let original := actual.find? (·.index == index)
    let marked ← match original with
      | some original => markValue frame.environment.marks original.value source
      | none =>
        unless ← isProof source do
          throwError "the formal construction lost an original computational parameter"
        pure source
    native := native.push marked
    if (information.paramInfo[index]?.map (·.isExplicit)).getD false && !(← isProof source) then
      let some original := original
        | throwError "the formal construction lost its original explicit parameter"
      explicitSources := explicitSources.push marked
      explicitValues := explicitValues.push original.value
  let some selected ← LimitFamily.formalAt expression native
    | throwError "the direct formal construction lost its original owner family"
  return some (← descriptor selected selection.source.row explicitSources none
    (some explicitValues))

/-- Retain structural map data at the unchanged original native role. The descriptor's
endpoints/operands are actual lowered occurrences; no map implementation is evaluated. -/
private partial def structuralMap (selected : NativeStructuralMap) : LowerM ValueBinding := do
  let values ← if selected.tag == "identity" then do
      let value ← lower selected.source
      pure #[value, value]
    else selected.operands.mapM lower
  let slots := values.mapIdx fun index binding =>
    ({ path := #[.field "args", .index index], binding, fieldIndex := none } : ContainerSlot)
  let packet := Json.mkObj [("ctor", toJson selected.tag),
    ("args", .arr (Array.replicate values.size .null))]
  let role := (← origin selected.value).role
  let payload ← if role.kind == .function then do
      let framed ← IO.ofExcept <| (CallablePacket.symbolic packet).mapError IO.userError
      IO.ofExcept <| (ValuePayload.callablePacket framed slots).mapError IO.userError
    else IO.ofExcept <| (ValuePayload.descriptor packet slots).mapError IO.userError
  stage selected.value payload

private partial def application (expression : Expr) : LowerM ValueBinding := do
  let frame ← read
  let arguments := expression.getAppArgs
  let (function, selected) := match expression.getAppFn with
    | .mdata data head => match selectedReference? data with
      | some (declaration, reference) =>
        if head.isConstOf declaration then (head, some reference) else (expression.getAppFn, none)
      | none => (expression.getAppFn, none)
    | head => (head, none)
  let .const name levels := function
    | return ← apply (← lower function) arguments
  let expression := mkAppN function arguments
  if name == ``List.toFinset then
    if let some (_, elements) := (← instantiateMVars arguments.back!).consumeMData.listLit? then
      return ← array expression elements.toArray
  if let some reference := selected then
    let traced := name == `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration
    if traced then dbg_trace "[inclusion.stage] registered family: before source family"
    let family ← SourceFamily.forReference reference
    let arity ← forallBoundedTelescope family.source.familyType (some arguments.size)
      fun locals _ => pure locals.size
    if traced then dbg_trace "[inclusion.stage] registered family: before actual arguments"
    let traceArguments := name ==
      `CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormBaseChangeDeclaration
    let (closed, actual) ← actualArguments (arguments.extract 0 arity)
      (traceArguments := traceArguments)
    if traced then dbg_trace "[inclusion.stage] registered family: before request preparation"
    let request ← PreparedRequest.forBoundary (← supply) frame.program
      (← frame.environment.ledger.allocate) (.registered family) levels frame.context closed actual
      #[] (← parameters)
      (some (← frame.environment.transaction.view)) (← sourceMarks closed)
      (validatedEnvironment := some (← retainedEnvironment))
    if traced then dbg_trace "[inclusion.stage] registered family: before demand"
    return ← apply (← demand request) (arguments.extract arity arguments.size)
  if let some info := (← getEnv).getProjectionFnInfo? name then
    if info.numParams < arguments.size then
      let some operand := arguments[info.numParams]?
        | throwError "internal: a source projection lost its record"
      let owner := (← getConstInfoCtor info.ctorName).induct
      let selected ← field owner info.i operand m!"{name}"
      return ← apply selected (arguments.extract (info.numParams + 1) arguments.size)
  match (← getEnv).find? name with
  | some (.ctorInfo constructor) =>
    unless arguments.size == constructor.numParams + constructor.numFields do
      return ← closure (← etaExpand expression)
    let fields := arguments.extract constructor.numParams arguments.size
    if isStructure (← getEnv) constructor.induct then return ← record expression fields
    descriptor expression name.getString! (← fields.filterM fun field => return !(← isProof field))
  | some (.inductInfo _) =>
    if (← whnf (← inferType expression)).isProp then
      -- A proposition formed by a type former has no computed truth value of its own (C22).
      throwStratum .noImplementation m!"the proposition {name} has no published predicate"
    -- An unapplied type family retains its native callable code, as other functions do.
    if (← origin expression).role.kind == .function then return ← closure expression
    if name == ``Prod then
      unless arguments.size == 2 do
        throwError "the native object product lost its two ordered components"
      return ← descriptor expression "objectProduct" arguments
    -- A type former at its arguments is an object of the category of sets.
    descriptor expression s!"lean:{name}" (← explicitArguments expression)
  | some (.recInfo _) | some (.quotInfo _) =>
    -- The kernel evaluates no eliminator (constitution C22): branching belongs to the leaf
    -- that implements an operation.
    if name == ``Quot then
      let heads := arguments.map fun argument => match argument.consumeMData with
        | .lam _ type body _ => ("lambda", type.getAppFn.constName?, body.getAppFn.constName?)
        | value => ("value", value.getAppFn.constName?, none)
      dbg_trace "[basechange.quot] arity={arguments.size} argumentHeads={repr heads}"
    throwStratum .noImplementation m!"{name} is an eliminator with no published operation"
  | _ =>
    if ← isMatcher name then
      throwStratum .noImplementation m!"{name} is a match with no published operation"
    -- User definitions are the retained local bindings handled above; accepted derivation
    -- templates arrive as their checked composition. A remaining constant has neither
    -- authority, even when Lean exposes a reducible body.
    throwStratum .noImplementation m!"{name} has no published operation"

end

/-- Lower a checked source term in its complete context and return its actual retained value.
`bound` is the runtime-binding table of the context, by stable source identity. -/
opaque lowerTerm (environment : LowerEnvironment) (program : RuntimeId .program)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (validatedEnvironment : Option RuntimeEnvironment := none) :
    MetaM ValueBinding := do
  let retainedView ← IO.mkRef validatedEnvironment
  let frame : Frame := { environment, program, context, bound, retainedView }
  -- A request may reopen its already admitted scope. Validate that hint against this
  -- exact frame and current graph before any source-path lookup can use the cache.
  if validatedEnvironment.isSome then
    let admitted ← runtimeEnvironment.run frame
    retainedView.set (some admitted)
  (lower expression).run frame

end CasCompiler
