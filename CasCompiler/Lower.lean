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

structure NativeLimitLegDemand where
  private mk ::
  selection : NativeLimitLegSelection
  receiver : ValueBinding
  cone : ValueBinding

  apexSource : Option SourceLayout

  component : ClosedTerm

  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  selections : SourceSelectionScope Expr
  contextEnvironment : RuntimeEnvironment

structure LowerEnvironment where
  ledger : OccurrenceLedger
  transaction : CellTransaction
  codes : IO.Ref (Std.HashMap (RuntimeId .program) ClosureCode)
  sourceSnapshot : Option Json := none
  run : OperationalProgram ValueBinding → MetaM ValueBinding

  limitLeg : NativeLimitLegDemand → MetaM ValueBinding := fun _ =>
    throwStratum .noImplementation "the completed cone requires its native leg-data continuation"

private structure Frame where
  environment : LowerEnvironment
  program : RuntimeId .program
  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  selections : SourceSelectionScope Expr := {}

  retainedView : IO.Ref (Option RuntimeEnvironment)
  selection : Option Name := none
  selectionBinding : Option BindingId := none

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

private def runtimeEnvironment : LowerM RuntimeEnvironment := do
  let frame ← read
  RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
    (some (← frame.environment.transaction.view))
    (← frame.retainedView.get)
    (selections := frame.selections)

private def withScope (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding)
    (action : LowerM α) (incoming : SourceSelectionScope Expr := {}) : LowerM α := do
  let frame ← read
  let retainedView ← IO.mkRef none
  let mut selections ← SourceSelectionScope.merge frame.selections incoming
  for (_, value) in bound.toArray do
    selections ← SourceSelectionScope.merge selections (← value.role.selections.inContext context)
    if value.admittedInterface?.isSome then
      selections ← SourceSelectionScope.merge selections (← value.nativeRole.selections.inContext context)
  withReader (fun frame => { frame with context, bound, selections, retainedView }) action

private def withRetained (value : ValueBinding) (action : LowerM α) : LowerM α := do
  let frame ← read
  withBindingContext (← frame.environment.transaction.view) frame.context frame.bound value
    fun context bound => do
      let mut selections ← SourceSelectionScope.merge frame.selections
        (← value.role.selections.inContext context)
      if value.admittedInterface?.isSome then
        selections ← SourceSelectionScope.merge selections (← value.nativeRole.selections.inContext context)
      (withScope context bound action).run { frame with selections }

private def retainedEnvironment : LowerM RuntimeEnvironment := do
  let frame ← read

  discard <| frame.environment.transaction.view
  if let some view ← frame.retainedView.get then return view
  let view ← runtimeEnvironment
  frame.retainedView.set (some view)
  return view

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
  let frame ← read
  let started ← IO.getNumHeartbeats
  let detail := Json.mkObj [
    ("phase", toJson phase),
    ("program", Observation.identityJson frame.program),
    ("transaction", Observation.identityJson frame.environment.transaction.id),
    ("context", toJson contextSize),
    ("start", toJson started)]
  try
    try
      CasTools.Diagnostics.emit "lower.phase.started" detail
    catch _ => pure ()
    action
  finally
    try
      let finished ← IO.getNumHeartbeats
      let elapsed := finished - started
      CasTools.Diagnostics.emit "lower.phase.finished" <|
        (detail.setObjVal! "finish" (toJson finished)).setObjVal! "rawTicks" (toJson elapsed)
      if elapsed ≥ 10000000 then
        CasTools.Diagnostics.message m!"[lower.cost] phase={phase} head={sourceCostHead expression} arguments={expression.getAppNumArgs} context={contextSize} rawTicks={elapsed} start={started} finish={finished}"
    catch _ => pure ()

private def withValue (source : Expr) (value : ValueBinding)
    (action : Expr → LowerM α) : LowerM α := do
  let frame ← read
  traceExpensiveLower "value.total" source frame.context.bindings.size do
    withRetained value do
      let frame ← read
      traceExpensiveLower "value.bind" source frame.context.bindings.size do
        withBoundValue (← supply) frame.context frame.bound source value fun context bound scopedSource =>
          (traceExpensiveLower "value.scope" scopedSource context.bindings.size do
            withScope context bound (action scopedSource)).run frame

private def originFor (role : SourceLayout) : LowerM ValueOrigin := do
  let frame ← read
  let identities ← supply

  let checked ← retainedEnvironment
  let graph ← frame.environment.transaction.view
  let environment ← traceExpensiveLower "origin.refresh" role.source.expression
      frame.context.bindings.size do
    checked.withGraph (some graph)
  traceExpensiveLower "origin.transport" role.source.expression frame.context.bindings.size do
    environment.origin frame.program (← identities.fresh .occurrence) role

private def origin (expression : Expr) : LowerM ValueOrigin := do
  let frame ← read
  traceExpensiveLower "origin.total" expression frame.context.bindings.size do
    let source ← traceExpensiveLower "origin.close" expression frame.context.bindings.size do
      frame.context.close expression
    let role ← traceExpensiveLower "origin.layout" expression frame.context.bindings.size do
      let selected := do
        let .fvar localId := expression | none
        let binding ← frame.context.bindings.find? (·.expression.fvarId! == localId)
        if frame.selections.contains binding.id then some binding.id else none
      SourceLayout.ofTerm source (selections := ← frame.selections.close frame.context)
        (selectionBinding := selected)
    originFor role

private def stage (expression : Expr) (payload : ValuePayload) : LowerM ValueBinding := do
  (← read).environment.transaction.stage (← origin expression) payload

private def demand (request : PreparedRequest) : LowerM ValueBinding := do
  let frame ← read
  let request := (request.withSelection frame.selection).withSourceSnapshot
    frame.environment.sourceSnapshot
  traceExpensiveLower "demand.total" request.source.source.expression frame.context.bindings.size do
    frame.environment.run do
      let response ← PFunctor.FreeM.lift (P := OperationalSignature) request
      pure response.root

private def isRegisteredComputation (state : SemanticState) (declaration : Name) : Bool :=
  state.operations.any (·.declaration == declaration) ||
  state.functors.any (·.declaration == declaration) ||
  state.constructions.any (·.declaration == declaration) ||
  state.morphisms.any (·.declaration == declaration) ||
  state.objects.any (·.application == some declaration) ||
  state.binders.any (·.operation == declaration)

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

private def requiresSourceAddress (state : SemanticState) (declaration : Name) : Bool :=
  isRegisteredComputation state declaration || isRegisteredDescriptor state declaration ||
  state.limits.any (·.declaration == declaration) ||
  state.objects.any (fun entry => entry.generator == some declaration ||
    entry.refines.any (·.identification == declaration))

private def unfoldSourceApplication? (expression : Expr) : MetaM (Option Expr) := do
  let .const _ _ := expression.getAppFn | return none
  let some body ← withOptions (fun options => options.setBool `smartUnfolding false) <|
      unfoldDefinition? expression.getAppFn
    | return none
  return some (body.betaRev expression.getAppRevArgs (preserveMData := true))

private def selectionAt? (expression : Expr) : LowerM (Option (BindingId × SourceSelection Expr)) := do
  let frame ← read
  let .fvar localId := expression | return none
  let some binding := frame.context.bindings.find? (·.expression.fvarId! == localId)
    | return none
  return frame.selections[binding.id]?.map (binding.id, ·)

private partial def proofAliasSource (source : Expr) : MetaM Expr := do
  match source with
  | .letE _ type value body _ =>
    if ← isProp type then
      check value
      unless ← isDefEq (← inferType value) type do
        throwError "the source alias changed its authored proof"
      proofAliasSource (body.instantiate1 value)
    else pure source
  | .mdata _ body => proofAliasSource body
  | _ => pure source

private def withSelected (selection : SourceSelection Expr)
    (action : Expr → LowerM α) (declaredType : Option Expr := none) : LowerM α := do
  let frame ← read
  SourceSelectionScope.withBinding (← supply) frame.selections frame.context selection
    (fun context selections expression => do
      let retainedView ← IO.mkRef none
      (action expression).run { frame with context, selections, retainedView })
    (declaredType := declaredType)

private def checkSelectedAddress (reference : SelectedSourceReference) : MetaM Unit := do
  let state ← semanticState
  let require {α : Type} [Repr α] (rows : Array α) (selected : α)
      (identity : α → String) : MetaM Unit := do
    let #[original] := rows.filter (fun original => identity original == identity selected)
      | throwError "the selected source lost its unique original registered address"
    unless reprStr original == reprStr selected do
      throwError "the selected source changed its complete independently registered row"
  match reference with
  | .named (.registered (.inl entry) category) =>
    require state.objects entry (·.id.raw)
    require state.categories category (·.id.raw)
  | .named (.registered (.inr entry) category) =>
    require state.morphisms entry (·.id.raw)
    require state.categories category (·.id.raw)
  | .named (.construction entry) => require state.constructions entry (·.id.raw)
  | .category entry => require state.categories entry (·.id.raw)
  | .operation entry => require state.operations entry (·.id.raw)
  | .method entry functor =>
    require state.methods entry (·.id.raw)
    require state.functors functor (·.id.raw)
  | .functor entry => require state.functors entry (·.id.raw)
  | .classifier entry | .classifierForget entry => require state.classifiers entry (·.id.raw)
  | .constructor entry | .constructorInterface entry _ => require state.constructors entry (·.id.raw)
  | .cell entry => require state.cells entry (·.id.raw)
  | .binder entry => require state.binders entry (·.id.raw)
  | .lift entry => require state.lifts entry (·.id.raw)
  | .presentation entry => require state.presentations entry (·.id.raw)
  | .literal entry => require state.literals entry (·.id.raw)
  | .numeral entry => require state.numerals entry (·.id.raw)
  | .subset entry => require state.subsetLiterals entry (·.id.raw)
  | .graph entry => require state.graphLiterals entry (·.id.raw)
  | .generator entry | .components entry => require state.objects entry (·.id.raw)
  | .limit entry => require state.limits entry (·.id.raw)
  | .refinement entry refinement =>
    require state.objects entry (·.id.raw)
    unless entry.refines.any (fun original => reprStr original == reprStr refinement) do
      throwError "the selected refinement changed its original registered interface"

private partial def nativeInterfaceSource? (expression : Expr) : LowerM (Option Expr) := do
  if let some (_, selected) ← selectionAt? expression.getAppFn then
    if selected.formalBindings.isEmpty then
      if let some reference := selected.reference then
        if let some declaration := reference.nativeInterface? then
          checkSelectedAddress reference
          if (← selectionAt? selected.value).isSome then
            return ← nativeInterfaceSource? (mkAppN selected.value expression.getAppArgs)
          let native := mkAppN selected.value expression.getAppArgs
          unless native.consumeMData.getAppFn.isConstOf declaration do
            throwError "the selected native interface lost its original declaration application"
          let some body ← unfoldSourceApplication? native.consumeMData
            | throwStratum .noImplementation m!"{declaration} has no native interface definition"
          return some body
  let some projection ← SourceProjection.ofExpr? expression | return none
  let some parent ← nativeInterfaceSource? projection.parent | return none
  let owner := (← getConstInfoCtor projection.info.ctorName).induct
  return some (.proj owner projection.info.i parent)

private partial def literal? (expression : Expr) : MetaM (Option Json) := do
  let expression := (← instantiateMVars expression).consumeMData
  if expression.hasFVar || expression.hasMVar then return none
  if let some value := expression.rawNatLit? then return some (toJson value)
  if let .lit (.strVal value) := expression then return some (toJson value)

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

private def captured (frame : Frame) (graph : ValueGraph) (expression : Expr)
    (found : Array ValueBinding) : MetaM (Array ValueBinding) := do
  return found ++ (← boundSourceReferences (some graph) frame.context frame.bound
    expression frame.selections)

private def closureWith (expression : Expr)
    (build : ClosedTerm → SourceSelectionScope ClosedTerm → ClosureCode)
    (retainedRole : Option Expr := none) (retainedValues : Array ValueBinding := #[]) :
    LowerM ValueBinding := do
  let frame ← read
  if let some original := retainedRole then
    frame.context.withOriginalSources #[original, expression] fun source => do
      unless ← isDefEq (← inferType source[0]!) (← inferType source[1]!) do
        throwError "the delayed native continuation changed its original source interface"
  traceExpensiveLower "closure.total" expression frame.context.bindings.size do
    let program ← (← supply).fresh .program
    let source ← traceExpensiveLower "closure.close" expression frame.context.bindings.size do
      frame.context.close expression
    let captures ← traceExpensiveLower "closure.captures" expression
        frame.context.bindings.size do
      captured frame (← frame.environment.transaction.view) expression #[]

    for index in (← selectedContextDependencies frame.context frame.selections expression) do
      let some binding := frame.context.bindings[index]?
        | throwError "a closure dependency is outside its complete source context"
      if binding.role == .parameter && !frame.bound.contains binding.id then
        let name ← binding.expression.fvarId!.getUserName
        throwStratum .noImplementation (MessageData.tagged (missingValueTag binding.id)
          m!"source binding {name} ({binding.id.session}:{binding.id.serial}) has no supplied runtime capture")
    let captures := captures ++ retainedValues
    let code := build source (← frame.selections.close frame.context)
    frame.environment.codes.modify (·.insert program code)
    traceExpensiveLower "closure.stage" expression frame.context.bindings.size do
      stage (retainedRole.getD expression) (.closure program captures)

private def closure (expression : Expr) : LowerM ValueBinding :=
  closureWith expression (fun source selections => .term source selections)

mutual

private partial def lower (expression : Expr) : LowerM ValueBinding :=
  withReader (fun frame => { frame with selectionBinding := none }) (lowerCore expression)

private partial def lowerCore (expression : Expr) : LowerM ValueBinding := do
  let expression ← instantiateMVars expression
  match expression with
  | .mdata _ body => lower body
  | .fvar id =>
    let frame ← read
    let some binding := frame.context.bindings.find? (·.expression.fvarId! == id)
      | throwError m!"source variable {id.name}: a source variable is outside its complete binding context"
    if let some value := frame.bound[binding.id]? then return value
    let declaration ← id.getDecl
    let label := m!"source binding {declaration.userName} ({binding.id.session}:{binding.id.serial})"
    if let some selected := frame.selections[binding.id]? then
      if !selected.formalBindings.isEmpty then return ← closure expression
      let declaredType ← inferType expression
      return ← withSelected selected (fun actual => do
        let some (identity, _) ← selectionAt? actual
          | throwError m!"{label}: the actual selected source lost its native binding"
        withReader (fun frame => { frame with selectionBinding := some identity })
          (selectedSource actual selected)) (some declaredType)
    if binding.role == .result then
      throwError m!"{label}: the source lost a retained runtime binding"
    if binding.role == .selectedStructure then
      throwError m!"{label}: the source lost its retained typed selection"
    match declaration.value? with
    | some value =>
      unless binding.role == .definition do
        throwStratum .noImplementation m!"{label} has no retained computational value"
      lower value
    | none =>
      throwStratum .noImplementation (MessageData.tagged (missingValueTag binding.id)
        m!"{label} has no supplied runtime value or native definition")
  | .letE _ _ value body _ =>
    if (← isProof value) || (← isType value) then return ← lower (body.instantiate1 value)
    let bound ← lower value
    withValue value bound fun scopedSource => lower (body.instantiate1 scopedSource)
  | .lam .. => closure expression
  | _ =>
    let frame ← read
    if let some selected ← NativeStructuralMap.ofExpr? frame.context expression
        (frame.bound.toArray.map (·.1)) then
      return ← structuralMap selected

    if expression.getAppFn.isHeadBetaTargetFn false then
      let reduced := expression.getAppFn.betaRev expression.getAppRevArgs
        (preserveMData := true)
      if reduced != expression then return ← lower reduced

    if let .mdata _ head := expression.getAppFn then
      return ← lower (mkAppN head expression.getAppArgs)
    if let some (_, selected) ← selectionAt? expression.getAppFn then
      let arguments := expression.getAppArgs
      if !selected.formalBindings.isEmpty then
        if arguments.size < selected.formalBindings.size then return ← closure expression
        let instantiated ← selected.specialize (arguments.extract 0 selected.formalBindings.size)
        let declaredType ← inferType
          (mkAppN expression.getAppFn (arguments.extract 0 selected.formalBindings.size))
        return ← withSelected instantiated (fun value => do
          apply (← lower value) (arguments.extract selected.formalBindings.size arguments.size))
          (some declaredType)
      if selected.application.isSome || selected.endpoint.isSome || selected.field.isSome ||
          selected.leg.isSome then
        return ← apply (← lower expression.getAppFn) arguments
      return ← withSelected { selected with
        value := mkAppN selected.value arguments
        originalApplication := selected.originalApplication.map (mkAppN · arguments) } lower
    if let .const declaration _ := expression.getAppFn then
      if requiresSourceAddress (← semanticState) declaration then
        let frame ← read
        CasTools.Diagnostics.message m!"[lost-source] declaration={declaration} expression={repr expression}"
        CasTools.Diagnostics.message m!"[lost-source] context={repr (frame.context.bindings.map (·.id))} retained={repr (frame.bound.toArray.map (·.1))}"
        throwError "the registered source declaration {declaration} lost its selected source address"

    if expression.getAppFn.isConstOf ``id ||
        expression.getAppFn.isConstOf ``Function.const then
      if let some reduced ← unfoldSourceApplication? expression then
        return ← lower reduced

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
      if traced then CasTools.Diagnostics.message m!"[inclusion.stage] lower projection {projection.declaration}: before environment"
      let frame ← read
      let environment ← retainedEnvironment
      if traced then CasTools.Diagnostics.message m!"[inclusion.stage] lower projection {projection.declaration}: after environment"
      if ← environment.hasRetainedSource frame.context projection.parent then
        if traced then CasTools.Diagnostics.message m!"[inclusion.stage] lower projection {projection.declaration}: retained parent"
        let (parent, path) ← projectionSourcePath environment projectionSource
        let selected ← projectPath (← lower parent) path
        return ← apply selected (arguments.extract projectionSource.getAppNumArgs arguments.size)
      let (parent, path) ← projectionSourcePath environment projectionSource
      if let some (_, selected) ← selectionAt? parent then
        if selected.field.isSome then
          let value ← projectPath (← lower parent) path
          return ← apply value (arguments.extract projectionSource.getAppNumArgs arguments.size)
      if let some (_, selected) ← selectionAt? projection.parent.getAppFn then
        if (selected.reference.bind (·.nativeInterface?)).isSome then
          let owner := (← getConstInfoCtor projection.info.ctorName).induct
          let value ← field owner projection.info.i projection.parent m!"{projection.declaration}"
          return ← apply value (arguments.extract projectionSource.getAppNumArgs arguments.size)
        let value ← project (← lower projection.parent) projection.info.i m!"{projection.declaration}"
        return ← apply value (arguments.extract projectionSource.getAppNumArgs arguments.size)
      if traced then CasTools.Diagnostics.message m!"[inclusion.stage] lower projection {projection.declaration}: unretained parent"

    let traceInclusion := (expression.find? (·.isConstOf
      `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before constructor projection"
    if let some projection ← SourceProjection.ofExpr? projectionSource then
      if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] constructor projection {projection.declaration}"
      let mut parent := projection.parent
      if let .const declaration _ := parent.getAppFn then

        unless parent.getAppFn.isConstOf projection.info.ctorName ||
            requiresSourceAddress (← semanticState) declaration do
          if let some expanded ← unfoldSourceApplication? parent then
            if expanded.getAppFn.isConstOf projection.info.ctorName then
              parent := expanded
      if parent.getAppFn.constName? == some projection.info.ctorName then
        if let some selected ← projectCore? parent projection.info.i then
          if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] native constructor field selected"
          return ← lower (mkAppN selected
            (arguments.extract projectionSource.getAppNumArgs arguments.size))
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after constructor projection"
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before inferType head={repr expression.getAppFn.constName?} arity={expression.getAppNumArgs}"
    let inferredType ← inferType expression
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after inferType; before type whnf head={repr inferredType.getAppFn.constName?} arity={inferredType.getAppNumArgs}"
    let type ← whnf inferredType
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after type whnf head={repr type.getAppFn.constName?} arity={type.getAppNumArgs}"
    trace[cas.lower] "{expression.getAppFn} [{expression.getAppNumArgs}] : {type}"
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before isProp"
    let proofType ← isProp type
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after isProp result={proofType}; before isClass"
    if proofType then throwError "internal: a source proof has no computational value"
    let typeClass ← isClass? type
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after isClass result={typeClass.isSome}"
    if typeClass.isSome then return ← closure expression

    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before literal/record dispatch"
    unless type.isSort || (type.getAppFn.constName?.map (isStructure (← getEnv))).getD false do
      if let some packet ← literal? expression then
        return ← stage expression (.portable packet.compress.toUTF8)
    if (type.getAppFn.constName?.map (isStructure (← getEnv))).getD false then
      if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before nativeInputRecord"
      if let some value ← nativeInputRecord? expression then
        if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] nativeInputRecord selected"
        return value
      if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after nativeInputRecord none"

    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before whnfCore"
    let reduced ← withConfig (fun config =>
      { config with zeta := false, zetaDelta := false, iota := false, proj := .yes })
      (whnfCore expression)
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] after whnfCore changed={reduced != expression} head={repr reduced.getAppFn.constName?} arity={reduced.getAppNumArgs}"
    if reduced != expression then return ← lower reduced
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.lower] before final native dispatch"
    match expression with
    | .proj owner index value => do
      let some info := getStructureInfo? (← getEnv) owner
        | throwError "internal: a source projection has no structure metadata"
      let some name := info.fieldNames[index]?
        | throwError "internal: a source projection is outside its structure"
      field owner index value m!"{name}"
    | .forallE .. | .sort .. =>
      if type.isProp then

        throwStratum .noImplementation m!"the proposition {expression} has no published predicate"
      descriptor expression "lean:type" #[]
    | _ => application expression

private partial def selectedAlias (expression source : Expr) : LowerM ValueBinding := do
  let value ← lower source
  withValue source value fun _ => do
    let frame ← read
    let environment ← runtimeEnvironment
    let checked ← environment.checkResult (← frame.environment.transaction.view)
      (← origin expression).role value
    return checked.root

private partial def selectedSource (expression : Expr) (selected : SourceSelection Expr) :
    LowerM ValueBinding := do
  if let some reference := selected.reference then
    checkSelectedAddress reference
    if let some (declaration, _) := reference.element? then
      unless (← sourceApplication? declaration selected).isSome do
        throwError "the named element lost its explicitly retained original application"
  if let some reference := selected.observation then checkSelectedAddress reference
  for (reference, _) in selected.alternatives do checkSelectedAddress reference
  let originalAlias ← proofAliasSource selected.value
  if originalAlias != expression then
    if let some (_, original) ← selectionAt? originalAlias then
      if original.pointRequest.isNone then
        if let some request := selected.pointRequest then
          let point := match request with
            | .named _ request => request.point
            | .categorical _ request => request.point
          unless point.equal originalAlias do
            throwError "the selected point request replaced its actual original point"

      let preserved := { selected with
        value := original.value
        category := if original.category.isNone then none else selected.category
        pointRequest := if original.pointRequest.isNone then none else selected.pointRequest
        preferredRoute := if original.preferredRoute.isNone then none else selected.preferredRoute
        alternatives := if original.alternatives.isEmpty then #[] else selected.alternatives }
      if SourceSelection.exactlyMatches Expr.equal preserved original then
        return ← selectedAlias expression selected.value
  if let some endpoint := selected.endpoint then
    return ← selectedEndpoint expression endpoint
  if let some field := selected.field then
    let owner ← lower field.owner
    return ← withValue field.owner owner fun _ => do
      let transaction := (← read).environment.transaction
      let .ok prior ← transaction.selectedAt field.selection field.projection owner
        | throwStratum .unavailable "the selected owner's result is no longer available"
      if let some value := prior then return value
      let value ← if field.deferredCone then
          withRetained owner do
            let frame ← read
            let some original ← owner.role.selected? frame.context
              | throwError "the deferred cone lost its exact selected owner record"
            withValue (← owner.selectedSource frame.context) owner fun source => do
              let frame ← read
              limitConeSource (← supply) frame.context frame.selections source original
                fun context selections plan => do
                  let some plan := plan
                    | throwError "the deferred cone lost its complete original source plan"
                  let retainedView ← IO.mkRef none
                  (lower plan).run { frame with context, selections, retainedView }
        else if let some projection ← SourceProjection.ofExpr? selected.value then
          if projection.declaration == field.projection && projection.parent.equal field.owner then
            lower selected.value
          else
            withReader (fun frame => { frame with selection := some field.selection })
              (selectedSource expression { selected with field := none })
        else
          withReader (fun frame => { frame with selection := some field.selection })
            (selectedSource expression { selected with field := none })
      let .ok () ← transaction.bindSelectedAt field.selection field.projection owner value
        | throwError "the selected owner's field changed its computational occurrence"
      return value
  if let some application := selected.application then
    return ← selectedApplication expression selected application
  if let some admitted := selected.admission then return ← admission expression admitted
  if let some leg := selected.leg then return ← selectedLeg expression selected leg
  if let some limit := selected.limit then
    if let some formal ← formalLimitDescriptor expression selected limit then return formal
  if let some reference := selected.reference then
    if let some declaration := reference.nativeInterface? then
      unless selected.value.consumeMData.getAppFn.isConstOf declaration do
        throwError "the selected native interface changed its original declaration"
      return ← nativeInterface expression
    if let some (declaration, address) := reference.element? then
      let some application ← sourceApplication? declaration selected
        | throwError "the named element lost its explicitly retained original application"
      let arguments ← explicitArguments application
      if let some ordinal := selected.legOrdinal then
        if (← origin expression).role.kind == .function then
          throwStratum .noImplementation
            m!"the leg {ordinal} of {address} has no published point application"
        return ← descriptor expression (address ++ "#leg") (arguments.push (mkNatLit ordinal))
      if (← origin expression).role.kind == .function then return ← closure expression
      return ← descriptor expression address arguments
    if let some (declaration, address) := reference.descriptor? then
      let some application ← sourceApplication? declaration selected
        | throwError "the selected descriptor lost its explicitly retained original application"
      return ← namedConstant expression address application
    if let some computation := reference.computation? then
      let family ← SourceFamily.forReference computation
      let application ← if selected.originalApplication.isSome then do
          let some declaration := reference.declaration
            | throwError "the selected computation lost its original declaration"
          let some application ← sourceApplication? declaration selected
            | throwError "the selected computation lost its original declaration application"
          pure application
        else pure selected.value
      let .const declaration levels := application.consumeMData.getAppFn
        | throwError "the selected computation lost its original declaration"
      unless some declaration == reference.declaration do
        throwError "the selected computation changed its original declaration"
      return ← boundaryFamily (.registered family) levels application.getAppArgs
    if reference matches .binder _ then return ← closure expression
  selectedAlias expression selected.value

private partial def selectedEndpoint (expression : Expr) (endpoint : SelectedSourceEndpoint Expr) :
    LowerM ValueBinding := do
  let frame ← read
  let environment ← retainedEnvironment
  if ← environment.hasRetainedSource frame.context endpoint.value then
    return ← argumentSource environment endpoint.value lower
  let value ← lower endpoint.arrow
  withValue endpoint.arrow value fun _ => do
    let sourceEnd := endpoint.side == .source
    let selector := if sourceEnd then "source" else "target"
    let template := Json.mkObj [("ctor", "morphismEndpoint"),
      ("args", .arr #[.null, toJson selector])]
    let slots : Array ContainerSlot :=
      #[{ path := #[.field "args", .index 0], binding := value, fieldIndex := none }]
    let fields ← selectedEndpointFields? sourceEnd value
    if let some fields := fields then
      let role := (← origin expression).role
      if role.kind == .record then
        return ← stageRecord (← RecordLayout.ofSource role) fields (some (template, slots))
    let built := match fields with
      | some fields => ValuePayload.container template slots fields none
      | none => ValuePayload.descriptor template slots
    let .ok payload := built | throwError "the selected endpoint has an invalid reference layout"
    stage expression payload

private partial def selectedLeg (expression : Expr) (source : SourceSelection Expr)
    (selected : NativeLimitLegSelection) : LowerM ValueBinding := do
  let receiver ← lower selected.construction.receiver
  withValue selected.construction.receiver receiver fun _ => do
    let frame ← read
    let graph ← frame.environment.transaction.view
    let .ok projected := graph.projectionSelection receiver
      | throwError "the selected leg lost its receiver's actual projection parent"
    let mut retained : Option (ValueBinding × Option SourceLayout) := none
    if let some (role, cone, path) := projected then
      let apex := if selected.construction.source.colimit then
        ``CategoryTheory.Limits.Cocone.pt else ``CategoryTheory.Limits.Cone.pt
      if path == #[apex] then retained := some (cone, some role)
    if retained.isNone then
      let field := if selected.construction.source.colimit then
        ``CategoryTheory.Limits.ColimitCocone.cocone else
        ``CategoryTheory.Limits.LimitCone.cone
      let .ok cone ← frame.environment.transaction.selectedAt
          selected.construction.source.construction field receiver
        | throwStratum .unavailable "the selected construction's result is no longer available"
      retained := cone.map (fun cone => (cone, none))
    let componentAt (cone : Expr) : LowerM Expr := do
      let frame ← read
      frame.context.withOriginalSources #[cone, selected.construction.source.cone] fun terms => do
        unless ← isDefEq (← inferType terms[0]!) (← inferType terms[1]!) do
          throwError "the selected leg changed its complete original cone interface"
      let transformation ← mkAppM (if selected.construction.source.colimit then
        ``CategoryTheory.Limits.Cocone.ι else ``CategoryTheory.Limits.Cone.π) #[cone]
      mkAppM ``CategoryTheory.NatTrans.app #[transformation]
    if let some (cone, apexSource) := retained then
      return ← withRetained cone do
        let frame ← read
        withValue (← cone.selectedSource frame.context) cone fun coneSource => do
          let component ← componentAt coneSource
          actualArguments #[selected.index] (function := some component) fun closed _ => do
            let frame ← read
            let #[index] ← closed.mapM (·.inContext frame.context)
              | throwError "the selected component lost its exact native index"
            let component ← frame.context.close (mkApp component index)
            frame.environment.limitLeg {
              selection := selected, receiver, cone, apexSource, component
              context := frame.context, bound := frame.bound, selections := frame.selections
              contextEnvironment := ← runtimeEnvironment }
    withRetained receiver do
      let frame ← read
      let some original ← receiver.role.selected? frame.context
        | throwError "the delayed leg lost its exact selected owner record"
      withValue (← receiver.selectedSource frame.context) receiver fun owner => do
        let some plan ← deferredLimitConeSource owner original
          | throwError "the delayed leg lost its complete original cone plan"
        withSelected plan fun whole => do
          let component ← componentAt whole
          actualArguments #[selected.index] (function := some component) fun closed _ => do
            let frame ← read
            let #[index] ← closed.mapM (·.inContext frame.context)
              | throwError "the delayed leg lost its exact native index"
            let value := mkApp component index
            let packet : Option ValueContainer ←
              if selected.construction.source.creation.isSome then pure none
              else do
                let some reference := source.reference
                  | throwError "the formal leg lost its original named source row"
                let some (declaration, address) := reference.element?
                  | throwError "the formal leg lost its original descriptor address"
                let some application ← sourceApplication? declaration source
                  | throwError "the formal leg lost its complete original presentation"
                let some ordinal := source.legOrdinal
                  | throwError "the formal leg lost its original source ordinal"
                let arguments ← explicitArguments application
                pure (some (← descriptorPacket (address ++ "#leg")
                  (arguments.push (mkNatLit ordinal))))
            let captures := (packet.map (·.slots.map (·.binding))).getD #[]
            closureWith value (fun value selections => .formalLeg value packet selections)
              (some expression) captures

private partial def boundaryFamily (boundary : ProgramBoundary) (levels : List Level)
    (arguments : Array Expr) : LowerM ValueBinding := do
  let frame ← read
  let function ← boundary.familyIn levels frame.context
  let arity ← forallBoundedTelescope (← inferType function) (some arguments.size)
    fun formals _ => pure formals.size
  actualArguments (arguments.extract 0 arity) (function := some function) fun closed actual => do
    let frame ← read
    let request ← PreparedRequest.forBoundary (← supply) frame.program
      (← frame.environment.ledger.allocate) boundary levels frame.context closed actual
      #[] (← parameters) (some (← frame.environment.transaction.view))
      (validatedEnvironment := some (← retainedEnvironment))
      (selections := frame.selections) (selectionBinding := frame.selectionBinding)
    apply (← demand request) (arguments.extract arity arguments.size)

private partial def selectedApplication (expression : Expr) (selected : SourceSelection Expr)
    (application : SelectedSourceApplication Expr) : LowerM ValueBinding := do
  let arguments := application.parameters ++ application.arguments
  let levels := application.universes
  match application.family with
  | .registered family => boundaryFamily (.registered family) levels arguments
  | .target program => boundaryFamily (.target program) levels arguments
  | .prerequisite program index => boundaryFamily (.prerequisite program index) levels arguments
  | .lift family => boundaryFamily (.lift family) levels arguments
  | .application family => boundaryFamily (.application family) levels arguments
  | .objectAction family => boundaryFamily (.objectAction family) levels arguments
  | .presentation family =>
    presentationFamily family levels arguments selected.presentationEndpoints
  | .routedMethod family => routedMethodFamily family levels arguments selected.routedInputs
  | .property family => propertyObservation family levels arguments
  | .point family => categoricalPointFamily family levels arguments selected.pointRequest
  | .limit family => wholeLimitFamily family application
  | .limitUniversal family => universalLimitFamily family application
  | .creation family target => creationFamily expression family target application selected.limit

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

private partial def array (expression : Expr) (elements : Array Expr) : LowerM ValueBinding := do
  let mut slots := #[]
  for element in elements, index in [:elements.size] do
    let binding ← lower element
    slots := slots.push ({ path := #[.index index], binding, fieldIndex := none } : ContainerSlot)
  let .ok payload := ValuePayload.container (.arr (Array.replicate elements.size Json.null)) slots
      #[] none
    | throwError "internal: a finite literal has an invalid reference layout"
  stage expression payload

private partial def namedConstant (expression : Expr) (address : String) (application : Expr) :
    LowerM ValueBinding := do
  let some (_, selected) ← selectionAt? expression
    | throwError "the named constant lost its complete selected source record"
  actualArguments application.getAppArgs (function := some application.getAppFn) fun closed actual => do
    let frame ← read
    let information ← getFunInfoNArgs application.getAppFn closed.size
    let mut arguments := #[]
    let mut explicitSources := #[]
    let mut explicitValues := #[]
    for source in closed, index in [:closed.size] do
      let source ← source.inContext frame.context
      let selected := actual.find? (·.index == index)
      let retained ← match selected with
        | some _ => pure source
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
    let application := mkAppN application.getAppFn arguments
    withSelected { selected with value := application, originalApplication := some application }
        fun expression => do
      let role := (← origin expression).role
      if role.kind == .function then return ← closure expression
      descriptor expression address explicitSources (some (← fieldClosures role))
        (some explicitValues)

private partial def nativeInterface (expression : Expr) : LowerM ValueBinding := do
  let role := (← origin expression).role
  if role.kind == .function then return ← closure expression
  unless role.kind == .record do
    throwStratum .noImplementation
      "the selected native interface has no computational record fields"
  stageRecord (← RecordLayout.ofSource role) (← fieldClosures role)

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

            let selected ← projectPath operand path
            let graph ← frame.environment.transaction.view
            let environment ← runtimeEnvironment
            let checked ← environment.checkResult graph (← prepared.toLayout) selected
            retained := some checked.root
      match retained with
      | some value => fields := fields.push value
      | none => fields := fields.push (← closure (← prepared.source.inContext frame.context))
  return fields

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

    let result ← if result.isAppOfArity ``Quiver.Hom 4 then pure result else whnfR result
    unless result.isAppOfArity ``Quiver.Hom 4 do return none
    let endpoint := result.getAppArgs[if sourceEnd then 2 else 3]!
    let .const declaration _ := endpoint.getAppFn | return none
    unless isRegisteredDescriptor state declaration do return none

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
  request.withArguments (← supply) frame.context frame.bound application.arguments.size
      fun context bound arguments _ => do
    let selections ← SourceSelectionScope.merge
      (← request.selections.inContext context)
      (← request.environment.selections.inContext context)
    (withScope context bound (do
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
    ) selections).run frame

private partial def explicitArguments (expression : Expr) : LowerM (Array Expr) := do
  let arguments := expression.getAppArgs
  let info ← getFunInfoNArgs expression.getAppFn arguments.size
  let mut selected := #[]
  for argument in arguments, index in [:arguments.size] do
    let explicit := (info.paramInfo[index]?.map (·.isExplicit)).getD true
    if explicit && !(← isProof argument) then selected := selected.push argument
  return selected

private partial def field (owner : Name) (index : Nat) (value : Expr) (name : MessageData) :
    LowerM ValueBinding := do
  let traceInclusion := (value.find? (·.isConstOf
    `CasCatalogue.Modules.CatalogueRegistration.modulesFibreInclusionDeclaration)).isSome
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] enter owner={owner} index={index}"
  if let some native ← nativeInterfaceSource? value then
    let original := .proj owner index value
    let role := (← origin original).role
    if role.kind == .record then return ← nativeInterface original
    let frame ← read

    let parent ← frame.context.inputProjectionSource native (frame.bound.toArray.map (·.1))
    let [constructor] := (← getConstInfoInduct owner).ctors
      | throwError "the selected native interface has no unique record constructor"
    if parent.getAppFn.isConstOf constructor then
      let some selected ← projectCore? parent index
        | throwError "the selected native interface lost its original constructor field"
      return ← lower selected
    return ← lower (.proj owner index parent)
  if let some (_, selected) ← selectionAt? value.getAppFn then
    if !selected.formalBindings.isEmpty || selected.application.isSome ||
        selected.leg.isSome || selected.field.isSome ||
        (selected.reference.bind (·.computation?)).isSome ||
        (selected.reference.bind (·.element?)).isSome then
      return ← project (← lower value) index name
    if let some (declaration, _) := selected.reference.bind (·.descriptor?) then
      let some application ← sourceApplication? declaration selected
        | throwError "the selected descriptor lost its explicitly retained original application"
      let native := mkAppN application value.getAppArgs
      if let some unfolded ← unfoldSourceApplication? native.consumeMData then
        return ← lower (.proj owner index unfolded)
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] before inferType"
  let inferredType ← inferType value
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] after inferType; before type whnf"
  let normalizedType ← whnf inferredType
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] after type whnf; before isClass head={repr normalizedType.getAppFn.constName?}"
  let selectedClass ← isClass? normalizedType
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] after isClass result={selectedClass.isSome}"
  if selectedClass.isSome then
    let frame ← read

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
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] declaration {declaration}: before authorization"
    if isRegisteredDescriptor (← semanticState) declaration then
      if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] declaration {declaration}: before unfolding"
      if let some unfolded ← unfoldSourceApplication? value.consumeMData then
        if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] declaration {declaration}: unfolded; before lower"
        return ← lower (.proj owner index unfolded)
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] declaration {declaration}: unchanged"
  let frame ← read
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] before environment"
  let environment ← retainedEnvironment
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] after environment; before retained-source check"

  let retained ← environment.hasRetainedSource frame.context value
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] after retained-source check result={retained}"
  if !retained then
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] unretained parent: before lower"
    let loweredParent ← lower value
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] unretained parent: after lower; before project"
    return ← project loweredParent index name
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] before projection source path"
  let (parent, path) ← projectionSourcePath environment (.proj owner index value)
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] after projection source path length={path.size}"
  if path.isEmpty then
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] empty path: before parent lower"
    let loweredParent ← lower value
    if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] empty path: after parent lower; before project"
    return ← project loweredParent index name
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] selected path: before parent lower"
  let loweredParent ← lower parent
  if traceInclusion then CasTools.Diagnostics.message m!"[inclusion.field] selected path: after parent lower; before projectPath"
  projectPath loweredParent path

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
  let some layout := operand.nativeRole.fields[index]?
    | throwError "internal: the source field {field} is outside its retained record interface"
  unless layout.wireIndex.isSome do
    throwError "internal: the source field {field} is a proof and has no computational value"
  let graph ← frame.environment.transaction.view
  let request ← PreparedRequest.forProjection identities frame.program
    (← frame.environment.ledger.allocate) frame.context graph operand index (← parameters)
    (validatedEnvironment := some (← retainedEnvironment))
    (selections := frame.selections) (selectionBinding := frame.selectionBinding)
  demand request

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
        (selections := frame.selections) (selectionBinding := frame.selectionBinding)
      return ← projectPath (← demand request) remaining
  let projection := path[0]!
  let some field := operand.nativeRole.fields.find? (·.projection == projection)
    | throwError "the native projection path is outside its retained record interface"
  projectPath (← project operand field.sourceIndex m!"{projection}") (path.extract 1 path.size)

private partial def projectionArgumentSource (environment : RuntimeEnvironment)
    (expression : Expr) (action : Expr → LowerM α) : LowerM α := do
  let frame ← read
  if let .mdata data body := expression then
    return ← projectionArgumentSource environment body fun body => action (.mdata data body)
  if let some projection ← SourceProjection.ofExpr? expression then
    if !projection.info.fromClass ||
        (← environment.hasRetainedSource frame.context projection.parent) then
      return ← projectionArgumentSource environment projection.parent fun parent => do
        action (.proj (← getConstInfoCtor projection.info.ctorName).induct projection.info.i parent)
  argumentSource environment expression fun source => do
    withValue source (← lower source) action

private partial def argumentSource (environment : RuntimeEnvironment) (expression : Expr)
    (action : Expr → LowerM α) : LowerM α := do
  let frame ← read
  if let some (_, selected) ← selectionAt? expression then
    if let some endpoint := selected.endpoint then
      if ← environment.hasRetainedSource frame.context endpoint.value then
        return ← argumentSource environment endpoint.value action
    if selected.field.isSome then
      return ← withValue expression (← lower expression) action
    return ← action expression
  if let .mdata data body := expression then
    return ← argumentSource environment body fun body => action (.mdata data body)
  if let .fvar id := expression then
    if let some binding := frame.context.bindings.find? (·.expression.fvarId! == id) then
      if frame.bound.contains binding.id then return ← action expression
    if let some value := (← id.getDecl).value? then
      return ← argumentSource environment value action
  let some projection ← SourceProjection.ofExpr? expression | return ← action expression
  if projection.info.fromClass &&
      !(← environment.hasRetainedSource frame.context projection.parent) then
    return ← action expression
  projectionArgumentSource environment projection.parent fun parent => do
    action (.proj (← getConstInfoCtor projection.info.ctorName).induct projection.info.i parent)

private partial def actualArguments (arguments : Array Expr)
    (action : Array ClosedTerm → Array RuntimeArgument → LowerM α)
    (function : Option Expr := none) (deferAfter : Option Nat := none)
    (required : Option (Array Nat) := none) (traceArguments : Bool := false) : LowerM α := do
  let finish (sources : Array Expr) (values : Array (Option ValueBinding)) : LowerM α := do
    let frame ← read
    let graph ← frame.environment.transaction.view
    let mut actual := #[]
    for value in values, index in [:values.size] do
      if let some value := value then
        let .ok argument := RuntimeArgument.ofValue graph index value
          | throwError "internal: a lowered source argument is outside the active graph"
        actual := actual.push argument
    action (← liftM (m := MetaM) <| sources.mapM frame.context.close) actual
  let rec nameIndependent (remaining : List (Expr × Option ValueBinding))
      (sources : Array Expr) (values : Array (Option ValueBinding)) : LowerM α := do
    match remaining with
    | [] => finish sources values
    | (source, value) :: rest =>
      match value with
      | none => nameIndependent rest (sources.push source) (values.push none)
      | some value => withValue source value fun source =>
        nameIndependent rest (sources.push source) (values.push (some value))
  let rec visit (remaining : List Expr) (index : Nat)
      (sources : Array Expr) (values : Array (Option ValueBinding)) : LowerM α := do
    match remaining with
    | [] =>
      match function with
      | none => nameIndependent (sources.zip values).toList #[] #[]
      | some function =>
        let frame ← read
        withApplicationInputs (← supply) frame.context frame.bound function sources values
          fun context bound sources => (withScope context bound (finish sources values)).run frame
    | argument :: rest =>
      if ← isProof argument then
        return ← visit rest (index + 1) (sources.push argument) (values.push none)
      if deferAfter.any (· < index) && required.any (fun needed => !needed.contains index) then
        return ← visit rest (index + 1) (sources.push argument) (values.push none)
      let environment ← retainedEnvironment
      argumentSource environment argument fun source => do
        let frame ← read
        let environment ← retainedEnvironment
        let deferred ← if deferAfter.any (· < index) then
            environment.hasRetainedSource frame.context source <&> Bool.not
          else pure false
        if traceArguments then
          let ticks ← IO.getNumHeartbeats
          CasTools.Diagnostics.message m!"[lower.argument] source index={index} deferred={deferred} ticks={ticks}"
        let value ← if deferred then closure source else lower source
        withValue source value fun retained =>
          visit rest (index + 1) (sources.push retained) (values.push (some value))
  visit arguments.toList 0 #[] #[]

private partial def admission (expression : Expr) (selected : SelectedSourceAdmission Expr) :
    LowerM ValueBinding := do
  let frame ← read
  let some declaration := selected.entry.admission
    | throwError "the admitted object has no original declared admission"
  let arguments := selected.arguments
  let family := selected.family
  unless family.isLambda do
    throwError "the admitted element lost its complete native point family"
  let element := selected.element
  unless element < arguments.size do
    throwError "internal: the admitted element lost its value"
  lambdaBoundedTelescope family arguments.size fun parameters value => do
    let some admitted := value.find? (·.getAppFn.isConstOf declaration)
      | throwError "internal: the admitted point family lost its registered declaration"
    unless parameters.size == arguments.size && admitted.getAppArgs == parameters do
      throwError "internal: the admitted point family changed its complete argument telescope"

  let sourceArguments ← arguments.mapM fun argument => frame.context.close argument
  let (_, sourceApplication) ← ApplicationLayout.ofSource
    (← SourceLayout.ofTerm (← frame.context.close family)
      (selections := ← frame.selections.close frame.context)) frame.context sourceArguments
  let required ← sourceApplication.inputResultArguments ((← parameters).map (·.source))
  if required.isNone then
    for argument in arguments.extract (element + 1) arguments.size do
      unless ← isProof argument do
        throwStratum .noImplementation
          m!"the admission {selected.entry.id.raw} requires unavailable computational evidence fields"
  let callable ← closure family
  actualArguments arguments (function := some family) (deferAfter := some element)
      (required := required) fun closed actual => do
    let frame ← read
    let request ← PreparedRequest.forApplication (← supply) frame.program
      (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
      (some (← frame.environment.transaction.view))
      (validatedEnvironment := some (← retainedEnvironment))
      (selections := frame.selections) (selectionBinding := frame.selectionBinding)
    if (← request.inputResultPlan (← frame.environment.transaction.view)).isSome then
      return ← demand request

    for argument in arguments.extract (element + 1) arguments.size do
      unless ← isProof argument do
        throwStratum .noImplementation
          m!"the admission {selected.entry.id.raw} requires unavailable computational evidence fields"
    let some value := actual.find? (·.index == element)
      | throwError "internal: the admitted element lost its actual value"
    let .ok payload := ValuePayload.descriptor .null
        #[{ path := #[], binding := value.value, fieldIndex := none }]
      | throwError "internal: the admitted element has an invalid reference layout"
    stage expression payload

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
    CasTools.Diagnostics.message m!"[inclusion.record] before native definition unfolding ticks={ticks}"
  let some expanded ← unfoldSourceApplication? expression | return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] after native definition unfolding ticks={ticks}"
  let some constructor := expanded.getAppFn.constName? | return none
  let some (.ctorInfo _) := (← getEnv).find? constructor | return none
  let frame ← read
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] before closing actual sources count={arguments.size} ticks={ticks}"
  let sourceArguments ← arguments.mapM fun argument => do
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      CasTools.Diagnostics.message m!"[inclusion.record] before source close head={repr argument.getAppFn.constName?} arity={argument.getAppNumArgs} ticks={ticks}"
    let closed ← frame.context.close argument
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      CasTools.Diagnostics.message m!"[inclusion.record] after source close ticks={ticks}"
    return closed
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] actual sources closed; before bare SourceLayout ticks={ticks}"

  let source ← (show MetaM SourceLayout from withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    SourceLayout.ofTerm (← empty.close expression.getAppFn))
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] bare SourceLayout complete; before concrete ApplicationLayout ticks={ticks}"
  let (result, application) ← ApplicationLayout.ofSource source frame.context sourceArguments
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] concrete ApplicationLayout complete fields={result.fields.size} ticks={ticks}"
  unless result.kind == .record && result.fields.any
      (fun field => field.wireIndex.isSome && !field.precedingDependencies.isEmpty) do return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] before original parameter table ticks={ticks}"
  let actualParameters ← parameters
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] original parameter table ready; before inputResultArguments ticks={ticks}"
  let required? ← application.inputResultArguments (actualParameters.map (·.source))
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] after inputResultArguments complete={required?.isSome} ticks={ticks}"
  let some required := required? | return none

  for argument in application.arguments do
    if argument.wireIndex.isSome && !required.contains argument.sourceIndex then return none
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] complete original coverage; before callable closure ticks={ticks}"
  let callable ← closure expression.getAppFn
  if traceInclusion then
    let ticks ← IO.getNumHeartbeats
    CasTools.Diagnostics.message m!"[inclusion.record] callable closure ready; before actualArguments ticks={ticks}"
  actualArguments arguments (function := some expression.getAppFn)
      (traceArguments := traceInclusion) fun closed actual => do
    let frame ← read
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      CasTools.Diagnostics.message m!"[inclusion.record] actualArguments ready; before prepared application ticks={ticks}"
    let request ← PreparedRequest.forApplication (← supply) frame.program
      (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
      (some (← frame.environment.transaction.view))
      (validatedEnvironment := some (← retainedEnvironment))
      (selections := frame.selections) (selectionBinding := frame.selectionBinding)
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      CasTools.Diagnostics.message m!"[inclusion.record] prepared application ready; before actual inputResultPlan ticks={ticks}"
    let actualPlan ← request.inputResultPlan (← frame.environment.transaction.view)
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      CasTools.Diagnostics.message m!"[inclusion.record] after actual inputResultPlan complete={actualPlan.isSome} ticks={ticks}"
    unless actualPlan.isSome do
      throwStratum .noImplementation
        "the native record conversion requires unavailable input fields"
    if traceInclusion then
      let ticks ← IO.getNumHeartbeats
      CasTools.Diagnostics.message m!"[inclusion.record] before demand ticks={ticks}"
    return some (← demand request)

private partial def apply (callable : ValueBinding) (arguments : Array Expr) :
    LowerM ValueBinding := do
  if arguments.isEmpty then return callable
  let frame ← read
  traceExpensiveLower "application.total" callable.role.source.expression frame.context.bindings.size do
    withRetained callable do
      let frame ← read
      let traceArguments := (callable.role.source.expression.find? (·.isConstOf
        `CasCatalogue.Modules.Bilinear.Valued.CatalogueRegistration.bilWFormBaseChangeDeclaration)).isSome
      if traceArguments then CasTools.Diagnostics.message m!"[basechange.application] callable={repr callable.value} arguments={arguments.size}"
      let function ← traceExpensiveLower "application.source" callable.nativeRole.source.expression
          frame.context.bindings.size do
        callable.nativeRole.source.inContext frame.context
      traceExpensiveLower "application.arguments" function frame.context.bindings.size do
        actualArguments arguments (function := some function)
            (traceArguments := traceArguments) fun closed actual => do
          let frame ← read
          if traceArguments then CasTools.Diagnostics.message m!"[basechange.application] actual inputs prepared"
          let request ← traceExpensiveLower "application.prepare" function frame.context.bindings.size do
            PreparedRequest.forApplication (← supply) frame.program
              (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
              (some (← frame.environment.transaction.view))
              (validatedEnvironment := some (← retainedEnvironment))
              (selections := frame.selections) (selectionBinding := frame.selectionBinding)
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
        draft.view frame.bound
    for value in values, wireIndex in [:values.size] do

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

private partial def presentationFamily (family : PresentationFamily) (levels : List Level)
    (arguments : Array Expr) (supplied : Option (Expr × Expr)) : LowerM ValueBinding := do
  let function := family.family.instantiateLevelParams family.universeParams levels
  actualArguments arguments (function := some function) fun closed actual => do
    let frame ← read
    let finish (endpoints : Array Expr) : LowerM ValueBinding :=
      actualArguments endpoints fun endpointSources endpointValues => do
        let frame ← read
        let request ← PreparedRequest.forPresentation (← supply) frame.program
          (← frame.environment.ledger.allocate) family levels
          frame.context closed actual endpointSources endpointValues (← parameters)
          (← frame.environment.transaction.view)
          (selections := frame.selections) (selectionBinding := frame.selectionBinding)
        demand request
    match supplied with
    | some (source, target) => finish #[source, target]
    | none =>
      let endpoints ← family.endpoints
        (mkAppN function (← closed.mapM (·.inContext frame.context)))
      withSelected endpoints.1 fun source =>
        withSelected endpoints.2 fun target => finish #[source, target]

private partial def routedMethodFamily (family : RoutedMethodFamily) (levels : List Level)
    (arguments : Array Expr) (supplied : Option (Array (Array Expr))) : LowerM ValueBinding := do
  let frame ← read
  let head := family.family.instantiateLevelParams family.universeParams levels
  unless arguments.size == family.parameterCount + 1 do
    throwError "the selected routed method changed its complete original argument telescope"
  let some source := arguments[family.parameterCount]?
    | throwError "the routed method lost its original receiver"
  let receiver ← lower source
  let environment ← runtimeEnvironment
  environment.methodParameters frame.context frame.bound frame.environment.transaction
    frame.environment.ledger.allocate family (arguments.extract 0 family.parameterCount)
    receiver (fun context bound selections expression =>
      (withScope context bound (lower expression) selections).run frame)
    (fun context bound selections arguments => (withScope context bound (do
      actualArguments arguments (function := some head) fun closed actual => do
        let frame ← read
        let levels ← levels.mapM instantiateLevelMVars
        let finish (scope : Array ValueBinding) : LowerM ValueBinding := do
          let frame ← read
          let request ← PreparedRequest.forBoundary (← supply) frame.program
            (← frame.environment.ledger.allocate) (.routedMethod family)
            levels frame.context closed actual scope (← parameters)
            (some (← frame.environment.transaction.view))
            (validatedEnvironment := some (← retainedEnvironment))
            (selections := frame.selections) (selectionBinding := frame.selectionBinding)
          let callable ← demand request
          withValue source receiver fun receiver => apply callable #[receiver]
        match supplied with
        | none => finish #[]
        | some supplied =>
          let arguments ← closed.mapM (·.inContext frame.context)
          let actions ← family.specializeActions levels arguments
          let inputs ← supplied.mapM (·.mapM lower)
          let environment ← runtimeEnvironment
          environment.methodActionsWithInputs frame.context frame.bound (← supply)
            (← frame.environment.transaction.view) family actions inputs
            fun context bound selections _ =>
              (withScope context bound (finish inputs.flatten) selections).run frame
    ) selections).run frame) (sourceSnapshot := frame.environment.sourceSnapshot)

private partial def propertyObservation (family : PropertyFamily) (levels : List Level)
    (originals : Array Expr) : LowerM ValueBinding := do
  let frame ← read
  unless originals.size == family.parameterCount + 1 do
    throwError "the property changed its complete original argument telescope"
  unless family.receiverViews.size == family.route.refs.size + 1 do
    throwError "the property lost its complete original category receiver plans"
  let some receiverView := family.receiverViews[0]?
    | throwError "the property lost its original source category receiver plan"
  let arguments := originals.extract 0 family.parameterCount
  let source := originals[family.parameterCount]!
  let receiver ← lower source
  let environment ← runtimeEnvironment
  environment.sourceCategoryParameters frame.context frame.bound frame.environment.transaction
    frame.environment.ledger.allocate family.route.source receiverView family.categoryFamily
    family.universeParams family.parameterCount arguments receiver
    (fun context bound selections expression =>
      (withScope context bound (lower expression) selections).run frame)
    (fun context bound selections arguments => (withScope context bound (do
      withValue source receiver fun receiver => do
        let function := family.family.instantiateLevelParams family.universeParams levels
        actualArguments (arguments.push receiver) (function := some function) fun closed actual => do
          let frame ← read
          let request ← PreparedRequest.forBoundary (← supply) frame.program
            (← frame.environment.ledger.allocate) (.property family) levels frame.context closed actual
            #[] (← parameters) (some (← frame.environment.transaction.view))
            (validatedEnvironment := some (← retainedEnvironment))
            (selections := frame.selections) (selectionBinding := frame.selectionBinding)
          demand request
    ) selections).run frame) (sourceSnapshot := frame.environment.sourceSnapshot)

private partial def pointEndpoint (arrow : ValueBinding) (source : Expr) (selector : String) :
    LowerM ValueBinding := do
  let frame ← read
  let environment ← retainedEnvironment
  if ← environment.hasRetainedSource frame.context source then
    return ← argumentSource environment source lower
  let packet := Json.mkObj [("ctor", toJson "morphismEndpoint"),
    ("args", .arr #[.null, toJson selector])]
  let payload ← IO.ofExcept <| (ValuePayload.descriptor packet #[
    { path := #[.field "args", .index 0], binding := arrow, fieldIndex := none }]).mapError IO.userError
  stage source payload

private partial def categoricalPointFamily (family : CategoricalPointFamily) (levels : List Level)
    (arguments : Array Expr) (requestData : Option (SelectedSourcePointRequest Expr)) :
    LowerM ValueBinding := do
  unless arguments.size == family.parameterCount + (if family.invocation then 2 else 0) do
    throwError "the categorical point changed its complete original argument telescope"
  let function := family.family.instantiateLevelParams family.universeParams levels
  actualArguments (arguments.extract 0 family.parameterCount) (function := some function)
      fun parameterSources parameterValues => do
    let frame ← read
    if !family.invocation then
      let request ← PreparedRequest.forBoundary (← supply) frame.program
        (← frame.environment.ledger.allocate) (.point family) levels frame.context
        parameterSources parameterValues #[] (← parameters)
        (some (← frame.environment.transaction.view))
        (validatedEnvironment := some (← retainedEnvironment))
        (selections := frame.selections) (selectionBinding := frame.selectionBinding)
      return ← demand request
    let native ← parameterSources.mapM (·.inContext frame.context)
    let mut originals : Array (Option ValueBinding) := Array.replicate family.parameterCount none
    for value in parameterValues do
      originals := originals.set! value.index (some value.value)
    let (nativeArrow, bundle) ← family.arrowAt levels native
    let (nativeSource, nativeTarget) ← categoricalPointEndpoints nativeArrow
    let supplied ← match requestData with
      | none => pure none
      | some (.categorical selected request) =>
        unless (SelectedApplicationFamily.point selected).exactlyMatches (.point family) do
          throwError "the categorical point request changed its full selected family"
        pure (some request)
      | some (.named ..) => throwError "the categorical point has a named scalar request"
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
    withValue arguments[family.parameterCount]! domain fun domainSource => do
      withValue arguments[family.parameterCount + 1]! point fun pointSource => do
        withValue nativeArrow arrow fun arrowSource => do
          withValue nativeSource source fun sourceEndpoint => do
            withValue nativeTarget target fun targetEndpoint => do
              let selectedPoint ← family.withRequest levels native arrowSource domainSource
                sourceEndpoint targetEndpoint pointSource
              withSelected selectedPoint fun pointSource => do
                actualArguments (native ++ #[domainSource, pointSource]) (function := some function)
                    fun closed actual => do
                  let frame ← read
                  let request ← PreparedRequest.forBoundary (← supply) frame.program
                    (← frame.environment.ledger.allocate) (.point family) levels frame.context closed actual
                    #[arrow, domain, source, target, point] (← parameters)
                    (some (← frame.environment.transaction.view))
                    (validatedEnvironment := some (← retainedEnvironment))
                    (selections := frame.selections) (selectionBinding := frame.selectionBinding)
                  demand request

private partial def wholeLimitFamily (family : LimitFamily)
    (application : SelectedSourceApplication Expr) : LowerM ValueBinding := do
  let some owner := application.ownerSelection
    | throwError "the whole cone lost its complete typed owner template"
  unless application.arguments.isEmpty do
    throwError "the raw cone changed its original declaration argument table"
  let function ← family.ownerFamily owner
  actualArguments application.parameters (function := some function) fun closed actual => do
    let frame ← read
    let owner ← liftM (m := MetaM) <| owner.mapM frame.context.close
    let request ← PreparedRequest.forBoundary (← supply) frame.program
      (← frame.environment.ledger.allocate) (.limit family owner) application.universes
      frame.context closed actual #[] (← parameters)
      (some (← frame.environment.transaction.view))
      (validatedEnvironment := some (← retainedEnvironment))
      (selections := frame.selections) (selectionBinding := frame.selectionBinding)
    demand request

private partial def universalLimitFamily (family : LimitUniversalFamily)
    (application : SelectedSourceApplication Expr) : LowerM ValueBinding := do
  let frame ← read
  let levels := application.universes
  let arguments := application.parameters
  let some owner := application.ownerSelection
    | throwError "the universal request lost its complete typed owner template"
  let #[coneSource] := application.arguments
    | throwError "the universal request lost its single original cone operand"
  let selected ← family.presentation.ownerAt owner arguments
  let cone ← lower coneSource
  let graph ← frame.environment.transaction.view
  let some node := graph.find cone.value
    | throwError "the universal source lost its actual completed cone"
  let some completion ← frame.environment.transaction.completionFor? node.origin.occurrence
    | throwError "the universal source lost its cone's original preparation"
  let original := completion.request
  let .primitive (.limit presentation originalOwner) originalLevels := original.action
    | throwError "the universal source requires an original raw-cone request"
  unless (SelectedApplicationFamily.limit presentation).exactlyMatches (.limit family.presentation) && originalLevels == levels &&
      completion.response.root.value == cone.value &&
      completion.response.root.associationIds.toList.isPrefixOf cone.associationIds.toList do
    throwError "the universal source changed its original completed cone"
  discard <| original.admitInputs graph
  original.withArguments (← supply) frame.context frame.bound family.parameterCount
      fun context bound native values => do
    let selections ← SourceSelectionScope.merge
      (← original.selections.inContext context)
      (← original.environment.selections.inContext context)
    (withScope context bound (do
      let frame ← read
      let originalSelection ← presentation.ownerAt (← originalOwner.mapM (·.inContext frame.context)) native
      unless originalSelection.source.construction == selected.source.construction do
        throwError "the universal source selected another original construction"
      let environment ← retainedEnvironment
      for argument in arguments, value in values do
        if let some value := value then
          environment.checkDeclaredInput frame.context graph argument value
        else
          unless ← isProof argument do
            throwError "the universal source lost an original computational parameter"
      let function := mkConst presentation.entry.declaration levels
      actualArguments native (function := some function) fun closed actual => do
        let frame ← read
        let owner ← liftM (m := MetaM) <| owner.mapM frame.context.close
        let request ← PreparedRequest.forBoundary (← supply) frame.program
          (← frame.environment.ledger.allocate) (.limitUniversal family owner) levels
          frame.context closed actual #[cone] (← parameters) (some graph)
          (validatedEnvironment := some (← retainedEnvironment))
          (selections := frame.selections) (selectionBinding := frame.selectionBinding)
        demand request
    ) selections).run frame

private partial def creationFamily (expression : Expr) (family : CreationFamily)
    (target : LimitFamily) (application : SelectedSourceApplication Expr)
    (selected : Option NativeLimitSelection) : LowerM ValueBinding := do
  let frame ← read
  let some selected := selected
    | throwError "the creation request lost its complete original typed construction"
  let some owner := application.owner
    | throwError "the creation request lost its actual original owner"
  let some prepared ← PreparedCreationFamily.ofSelection frame.context owner selected
      family target frame.selections
    | throwError "the creation request lost its accepted complete family"
  unless application.parameters.isEmpty && application.universes == prepared.universes do
    throwError "the fixed creation changed its original evidence telescope"
  let #[cone, universal] := application.arguments
    | throwError "the fixed creation lost its original cone and universal operands"
  let prepared ← prepared.withArguments frame.context cone universal
  let arguments ← prepared.arguments.mapM (·.inContext frame.context)
  actualArguments arguments (function := some (← prepared.familyIn frame.context)) fun closed actual => do
    let frame ← read
    let request ← PreparedRequest.forBoundary (← supply) frame.program
      (← frame.environment.ledger.allocate) (.creation prepared) prepared.universes
      frame.context closed actual #[] (← parameters)
      (some (← frame.environment.transaction.view))
      (validatedEnvironment := some (← retainedEnvironment))
      (selections := frame.selections) (selectionBinding := frame.selectionBinding)
    let value ← demand request
    let graph ← frame.environment.transaction.view
    let environment ← runtimeEnvironment
    return (← environment.checkResult graph (← origin expression).role value).root

private partial def formalCreationDescriptor (prepared : PreparedCreationFamily) :
    LowerM ValueBinding := do
  let frame ← read
  let arguments ← prepared.sourceArguments.mapM (·.inContext frame.context)
  let function ← prepared.sourceOwner.selection.receiver.inContext frame.context
  actualArguments arguments (function := some function) fun closed _ => do
    let frame ← read
    let native ← closed.mapM (·.inContext frame.context)
    liftM (m := MetaM) <| prepared.rebindSource (← supply) frame.context frame.selections native
      fun context selections prepared => do
        let retainedView ← IO.mkRef none
        (show LowerM ValueBinding from do
          let owner ← prepared.owner.inContext context
          closureWith owner fun _ _ => .creationOwner prepared).run
            { frame with context, selections, retainedView }

private partial def formalLimitDescriptor (expression : Expr) (source : SourceSelection Expr)
    (selection : NativeLimitSelection) : LowerM (Option ValueBinding) := do
  let frame ← read
  if let some (family, target) := source.creationOwner then
    let some prepared ← PreparedCreationFamily.ofSelection frame.context expression selection
        family target frame.selections
      | throwError "the formal created object lost its complete original creation"
    return some (← formalCreationDescriptor prepared)
  let some owner := selection.source.ownerFamily | return none
  let some family := source.limitFamily
    | throwError "the formal construction lost its complete selected limit family"
  let owner ← SelectedLimitOwner.ofBinding frame.context frame.selections owner
  let some original ← sourceApplication? selection.source.declaration source
    | throwError "the named element lost its explicitly retained original application"
  unless source.originalApplication.any (·.equal selection.source.interface.presentation) do
    throwError "the formal construction changed its explicitly retained original application"
  let application := original.consumeMData
  unless selection.source.presentation.consumeMData.getAppFn.isConstOf
      selection.source.declaration do return none
  actualArguments application.getAppArgs (function := some application.getAppFn) fun closed actual => do
    let frame ← read
    let information ← getFunInfoNArgs application.getAppFn closed.size
    let mut native := #[]
    let mut explicitSources := #[]
    let mut explicitValues := #[]
    for source in closed, index in [:closed.size] do
      let source ← source.inContext frame.context
      let original := actual.find? (·.index == index)
      let marked ← match original with
        | some _ => pure source
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
    let some selected ← LimitFamily.formalAt family frame.context selection owner native
      | throwError "the direct formal construction lost its original owner family"
    let category := source.category.map fun category =>
      { category with bundle := selected.source.bundle, limit := some selected.source }
    let source := { source with
      value := selected.receiver
      limit := some selected
      originalApplication := some selected.source.presentation
      category := category }
    withSelected source fun value => do
      return some (← descriptor value selection.source.row explicitSources none
        (some explicitValues))

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
  let function := expression.getAppFn.consumeMData
  let .const name levels := function
    | return ← apply (← lower function) arguments
  let expression := mkAppN function arguments
  if name == ``List.toFinset then
    if let some (_, elements) := (← instantiateMVars arguments.back!).consumeMData.listLit? then
      return ← array expression elements.toArray
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

      throwStratum .noImplementation m!"the proposition {name} has no published predicate"

    if (← origin expression).role.kind == .function then return ← closure expression
    if name == ``Prod then
      unless arguments.size == 2 do
        throwError "the native object product lost its two ordered components"
      return ← descriptor expression "objectProduct" arguments

    descriptor expression s!"lean:{name}" (← explicitArguments expression)
  | some (.recInfo _) | some (.quotInfo _) =>

    if name == ``Quot then
      let heads := arguments.map fun argument => match argument.consumeMData with
        | .lam _ type body _ => ("lambda", type.getAppFn.constName?, body.getAppFn.constName?)
        | value => ("value", value.getAppFn.constName?, none)
      CasTools.Diagnostics.message m!"[basechange.quot] arity={arguments.size} argumentHeads={repr heads}"
    throwStratum .noImplementation m!"{name} is an eliminator with no published operation"
  | _ =>
    if ← isMatcher name then
      throwStratum .noImplementation m!"{name} is a match with no published operation"

    throwStratum .noImplementation m!"{name} has no published operation"

end

opaque lowerTerm (environment : LowerEnvironment) (program : RuntimeId .program)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding) (expression : Expr)
    (validatedEnvironment : Option RuntimeEnvironment := none)
    (selections : SourceSelectionScope Expr := {}) :
    MetaM ValueBinding := do
  let retainedView ← IO.mkRef validatedEnvironment
  let mut retainedSelections := selections
  for (_, value) in bound.toArray do
    retainedSelections ← SourceSelectionScope.merge retainedSelections
      (← value.role.selections.inContext context)
    if value.admittedInterface?.isSome then
      retainedSelections ← SourceSelectionScope.merge retainedSelections
        (← value.nativeRole.selections.inContext context)
  let mut frame : Frame := {
    environment, program, context, bound, retainedView, selections := retainedSelections }

  if validatedEnvironment.isSome then
    let admitted ← runtimeEnvironment.run frame
    retainedView.set (some admitted)
    let selections ← SourceSelectionScope.merge frame.selections
      (← admitted.selections.inContext context)
    frame := { frame with selections }
  (lower expression).run frame

end CasCompiler
