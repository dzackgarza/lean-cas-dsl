module

public import CasRuntime.Value
public import CasCatalogue.InterpretationFailure

public section

namespace CasRuntime

open Lean Meta CasCompiler


structure FixedInput where
  parent : ValueBinding
  path : Array Name
  source : ClosedTerm
  parameters : Array (Option ValueBinding)



structure FixedResult where
  path : Array Name
  input : FixedInput
  value : ValueBinding

private def selectedInputLayout (source : SourceLayout) (path : Array Name) :
    MetaM SourceLayout := do
  let mut source := source
  for projection in path do
    let some field := source.fields.find? (·.projection == projection)
      | throwError "a fixed input route is outside its actual native record interface"
    unless field.wireIndex.isSome do
      throwError "a fixed computational input route selected a proof field"
    source ← field.toLayout
  return source

private def FixedInput.checkPath (input : FixedInput) : MetaM Unit :=
  discard <| selectedInputLayout input.parent.nativeRole input.path




private def FixedInput.storedFrontier (input : FixedInput) (graph : ValueGraph) :
    MetaM (Option (ValueBinding × Array Name)) := do
  input.checkPath
  discard <| IO.ofExcept <| (graph.requiredOwners #[input.parent]).mapError IO.userError
  let mut value := input.parent
  for projection in input.path, offset in [:input.path.size] do
    let some field := value.nativeRole.fields.find? (·.projection == projection)
      | throwError "a fixed input route lost its actual native field"
    let some index := field.wireIndex
      | throwError "a fixed computational input route selected a proof field"
    let some node := graph.find value.value
      | throwError "the fixed input is outside the visible graph"
    if node.payload.data.storedFields?.isNone then
      if let some retained ← IO.ofExcept <|
          (graph.projected? value #[projection]).mapError IO.userError then
        value := retained
        continue
    match node.payload.data with
    | .closure .. | .ownedToken .. =>
      return some (value, input.path.extract offset input.path.size)
    | .container container =>
      if container.fields.isNone then return none
      value ← IO.ofExcept <| (graph.project value index).mapError IO.userError
    | .product .. =>
      value ← IO.ofExcept <| (graph.project value index).mapError IO.userError
    | .portable .. => throwError "the fixed input has no native record access interface"
  return some (value, #[])



opaque FixedInput.storedValue? (input : FixedInput) (graph : ValueGraph) :
    MetaM (Option ValueBinding) := do
  let some (value, remaining) ← input.storedFrontier graph | return none
  return if remaining.isEmpty then some value else none

opaque FixedInput.storedValue (input : FixedInput) (graph : ValueGraph) : MetaM ValueBinding := do
  let some value ← input.storedValue? graph
    | throwError "the fixed input requires its prepared lazy projection demand"
  return value





opaque FixedInput.resolveValue (input : FixedInput) (graphView : MetaM ValueGraph)
    (resolve : Option (FixedInput → MetaM ValueBinding) := none) : MetaM ValueBinding := do
  let graph ← graphView
  let some (value, remaining) ← input.storedFrontier graph
    | CasCatalogue.throwStratum .noImplementation
        m!"the retained descriptor supplies no native data for input path {input.path}"
  if remaining.isEmpty then return value
  let some resolve := resolve | return ← input.storedValue graph
  let access ← resolve input
  let graph ← graphView
  let some value ← IO.ofExcept <|
      (graph.projectionBasis access input.parent input.path).mapError IO.userError
    | throwError "a resolved fixed input did not retain its exact source access"
  return value



private inductive InputArgument where
  | actual (value : Option ValueBinding) (source : ClosedTerm)
      (context : ContextTelescope) (parameters : Array (Option ValueBinding))
  | expression (source : InputExpression) (parameters : Array (Option ValueBinding))
      (arguments : Array InputArgument)

private def inputArguments (layout : ApplicationLayout)
    (parameters values : Array (Option ValueBinding)) : MetaM (Array InputArgument) := do
  unless parameters.size == layout.result.source.context.entries.size &&
      values.size == layout.arguments.size do
    throwError "fixed input routing requires its original complete source tables"
  let mut actual : Array InputArgument := #[]
  for value in values, argument in layout.arguments do
    actual := actual.push (.actual value argument.source.source
      layout.result.source.context parameters)
  return actual

private structure InputRuntimeStep where
  selection : Array Name
  arguments : Array InputArgument



private def contextInputIds (context : ContextTelescope)
    (parameters : Array (Option ValueBinding)) : MetaM (Array BindingId) := do
  unless parameters.size == context.entries.size do
    throwError "fixed input routing requires its original complete context table"
  let mut selected := #[]
  for entry in context.entries, parameter in parameters do
    if parameter.isSome then selected := selected.push entry.id
  return selected

private def inputSelection (context : ContextTelescope)
    (parameters : Array (Option ValueBinding)) (arguments : Array InputArgument)
    (route : InputProjection) : MetaM InputArgument := do
  match route.target with
    | .argument index => do
      let some argument := arguments[index]?
        | throwError "a fixed source route is outside its original argument table"
      return argument
    | .context binding => do
      unless parameters.size == context.entries.size do
        throwError "a fixed context route lost its original complete parameter table"
      let some index := context.entries.findIdx? (·.id == binding)
        | throwError "a fixed context route is outside its original source telescope"
      let source ← context.withOpen fun bindings => do
        let some selected := bindings.find? (·.id == binding)
          | throwError "a fixed context route lost its exact reopened source binding"
        let opened ← ContextTelescope.capture bindings
        opened.close selected.expression
      return .actual parameters[index]! source context parameters

private def actualFixedInput (graph : ValueGraph) (value : Option ValueBinding)
    (source : ClosedTerm) (context : ContextTelescope)
    (parameters : Array (Option ValueBinding)) (path : Array Name) : MetaM FixedInput := do
  let some parent := value
    | throwError (MessageData.tagged `CasRuntime.FixedInput.missingInput
        "a fixed result requires its actual source input")
  discard <| IO.ofExcept <| (graph.requiredOwners #[parent]).mapError IO.userError
  let source ← context.withOpen fun bindings => do
    let context ← ContextTelescope.capture bindings
    context.close (← source.inContext context)
  let input : FixedInput := ⟨parent, path, source, parameters⟩
  input.checkPath
  return input



private def remainingInputApplications (context : ContextTelescope)
    (parameters : Array (Option ValueBinding)) (arguments : Array InputArgument)
    (remaining : Array CasCompiler.InputApplicationStep) : MetaM (Array InputRuntimeStep) := do
  let mut steps : Array InputRuntimeStep := #[]
  for step in remaining do
    let mut actual : Array InputArgument := #[]
    for argument in step.arguments do
      match argument with
      | .slot index =>
        let some argument := arguments[index]?
          | throwError "a composed input route lost an exact remaining argument slot"
        actual := actual.push argument
      | .expression source =>
        unless source.argumentCount ≤ arguments.size do
          throwError "a suspended input expression lost its original formal prefix"
        unless source.context.entries.map (·.id) == context.entries.map (·.id) &&
            parameters.size == context.entries.size do
          throwError "a suspended input expression lost its original context parameter plane"
        actual := actual.push (.expression source parameters
          (arguments.extract 0 source.argumentCount))
    steps := steps.push ⟨step.selection, actual⟩
  return steps

mutual



private partial def fixedFromArgument (graph : ValueGraph) (argument : InputArgument)
    (selection : Array Name) (steps : Array InputRuntimeStep) : MetaM (Option FixedInput) := do
  match argument with
  | .actual value source context parameters =>
    let input ← actualFixedInput graph value source context parameters selection
    let some (value, selection) ← input.storedFrontier graph | return none
    if steps.isEmpty then return some input
    fixedFromCallable graph value selection steps #[]
  | .expression source parameters arguments =>
    match steps[0]? with
    | none => fixedFromExpression graph source parameters arguments #[] selection
    | some next =>
      fixedFromExpression graph source parameters arguments
        (steps.set! 0 { next with selection := selection ++ next.selection }) #[]



private partial def fixedFromResult (graph : ValueGraph) (context : ContextTelescope)
    (parameters : Array (Option ValueBinding)) (arguments : Array InputArgument)
    (result : InputProjectionResult) : MetaM (Option FixedInput) := do
  match result with
  | .projection route =>
    fixedFromArgument graph (← inputSelection context parameters arguments route) route.path #[]
  | .callable route remaining =>
    fixedFromArgument graph (← inputSelection context parameters arguments route) route.path
      (← remainingInputApplications context parameters arguments remaining)



private partial def fixedFromExpression (graph : ValueGraph) (source : InputExpression)
    (parameters : Array (Option ValueBinding)) (actual : Array InputArgument)
    (steps : Array InputRuntimeStep) (path : Array Name) : MetaM (Option FixedInput) := do
  unless actual.size == source.argumentCount do
    throwError "a suspended input expression changed its exact formal prefix"
  let context := source.context
  let contextInputs ← contextInputIds context parameters
  let arguments := actual ++ steps.flatMap (·.arguments)
  let some traced ← source.inputProjectionThrough
      (steps.map fun step => (step.selection, step.arguments.size)) path contextInputs
    | return none
  fixedFromResult graph context parameters arguments traced




private partial def fixedFromCallable (graph : ValueGraph) (value : ValueBinding)
    (selection : Array Name) (steps : Array InputRuntimeStep) (path : Array Name) :
    MetaM (Option FixedInput) := do
  let some next := steps[0]?
    | throwError "a composed callable route has no remaining application"
  if let some native := value.admittedInterface? then
    return ← fixedFromCallable graph native selection steps path
  let projected ← IO.ofExcept <| (graph.projectionOrigin value).mapError IO.userError
  if let some (parent, accessPath) := projected then
    return ← fixedFromCallable graph parent (accessPath ++ selection) steps path
  let original ← IO.ofExcept <| (graph.applicationOrigin value).mapError IO.userError
  if let some original := original then
    let steps := steps.set! 0 {
      next with selection := original.path ++ selection ++ next.selection }
    return ← fixedFromApplication graph original.layout original.parameters
      (← inputArguments original.layout original.parameters original.arguments) original.callable
      steps path
  let some node := graph.find value.value
    | throwError "the selected callable is outside its original graph"
  node.origin.role.source.withOpen fun bindings _ => do
    let context ← ContextTelescope.capture bindings
    let source ← selectedInputLayout node.origin.role selection
    let (_, layout) ← ApplicationLayout.ofSource source context #[]
    fixedFromApplication graph layout node.origin.parameters #[] none steps path

private partial def fixedFromApplication (graph : ValueGraph) (layout : ApplicationLayout)
    (parameters : Array (Option ValueBinding)) (actual : Array InputArgument)
    (callable : Option ValueBinding) (steps : Array InputRuntimeStep) (path : Array Name) :
    MetaM (Option FixedInput) := do


  if let some callable := callable then
    return ← fixedFromCallable graph callable #[]
      (#[{ selection := #[], arguments := actual }] ++ steps) path
  let context := layout.result.source.context
  let contextInputs ← contextInputIds context parameters
  let arguments := actual ++ steps.flatMap (·.arguments)
  let some traced ← layout.inputProjectionThrough
      (steps.map fun step => (step.selection, step.arguments.size)) path contextInputs
    | return none
  fixedFromResult graph context parameters arguments traced

end




opaque ApplicationOrigin.fixedInputAt (origin : ApplicationOrigin) (graph : ValueGraph)
    (path : Array Name := #[]) : MetaM (Option FixedInput) := do
  fixedFromApplication graph origin.layout origin.parameters
    (← inputArguments origin.layout origin.parameters origin.arguments)
    origin.callable #[] (origin.path ++ path)

end CasRuntime
