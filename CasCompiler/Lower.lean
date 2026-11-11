module

public import CasCompiler.Program
public import CasCompiler.Elaborate
public import CasRuntime.Transaction
public import LeanCategories.Catalogue.Registry.Semantic
public import CasCatalogue.InterpretationFailure

public section

namespace CasCompiler

open Lean Meta CasRuntime CasCatalogue

/-- Operational code of a kernel closure. The value node retains the actual captures.
Source: data model §5, ComputationalClosure, lean-cas-dsl#66 comment 6664275536. -/
inductive ClosureCode
  /-- A checked source term. A field or application demand lowers that eliminator on it. -/
  | term (source : ClosedTerm)
  /-- A published family at its prepared parameters, with the fields already selected.
  Its realization is selected when an action reaches actual arguments
  (execution contract v2 §5.2, lean-cas-dsl#69 comment 6664277464). -/
  | family (request : PreparedRequest) (path : Array FieldLayout)

/-- The active cell consumed by compiled source code. `run` interprets each emitted program.
A later demand is prepared from the actual references that an earlier program returned. -/
structure LowerEnvironment where
  ledger : OccurrenceLedger
  transaction : CellTransaction
  codes : IO.Ref (Std.HashMap (RuntimeId .program) ClosureCode)
  marks : IO.Ref (Array ValueBinding)
  run : OperationalProgram ValueBinding → MetaM ValueBinding

private structure Frame where
  environment : LowerEnvironment
  program : RuntimeId .program
  context : OpenContext
  bound : Std.HashMap BindingId ValueBinding
  selected : Array (Name × ComputationRef)

private abbrev LowerM := ReaderT Frame MetaM

private def valueKey : Name := `CasCompiler.lower.value

private def markedKey? (data : MData) : Option Nat :=
  match data.find valueKey with
  | some (.ofNat key) => some key
  | _ => none

/-- Associate an actual retained value with one occurrence of its checked source term.
Reuse: Lean MData, preserved by closure and ignored by kernel conversion, as sourceReference. -/
def markValue (marks : IO.Ref (Array ValueBinding)) (value : ValueBinding) (expression : Expr) :
    BaseIO Expr := do
  let key ← marks.modifyGet fun values => (values.size, values.push value)
  return .mdata (KVMap.empty.setNat valueKey key) expression

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

private def origin (expression : Expr) : LowerM ValueOrigin := do
  let frame ← read
  let identities ← supply
  let role ← SourceLayout.ofTerm (← frame.context.close expression)
  let environment ← RuntimeEnvironment.capture identities.worker frame.context (← parameters)
  environment.origin frame.program (← identities.fresh .occurrence) role

private def stage (expression : Expr) (payload : ValuePayload) : LowerM ValueBinding := do
  (← read).environment.transaction.stage (← origin expression) payload

private def demand (request : PreparedRequest) : LowerM ValueBinding := do
  (← read).environment.run do
    let response ← PFunctor.FreeM.lift (P := OperationalSignature) request
    pure response.root

/-- Registry rows whose declaration is a published computation family.
A method denotes its functor family; the reader's retained reference selects the method row. -/
private def computationRefs (state : SemanticState) (declaration : Name) : Array ComputationRef :=
  (state.operations.filter (·.declaration == declaration)).map (.operation ·.id) ++
  (state.functors.filter (·.declaration == declaration)).map (.functor ·.id) ++
  (state.constructions.filter (·.declaration == declaration)).map (.construction ·.id) ++
  (state.morphisms.filter (·.declaration == declaration)).map (.morphism ·.id)

/-- Registry rows whose declaration is a named constant of the source, with its public address. -/
private def descriptorIds (state : SemanticState) (declaration : Name) : Array String :=
  (state.objects.filter (·.declaration == declaration)).map (·.id.raw) ++
  (state.categories.filter (·.declaration == declaration)).map (·.id.raw) ++
  (state.numerals.filter (·.declaration == declaration)).map (·.id.raw) ++
  (state.literals.filter (·.denotation == declaration)).map (·.id.raw) ++
  (state.graphLiterals.filter (·.denotation == declaration)).map (·.id.raw) ++
  (state.subsetLiterals.filter (·.denotation == declaration)).map (·.id.raw) ++
  (state.classifiers.filter (·.declaration == declaration)).map (·.id.raw) ++
  (state.cells.filter (·.declaration == declaration)).map (·.id.raw) ++
  (state.presentations.filter (·.declaration == declaration)).map (·.id.raw) ++
  (state.constructors.filter (·.semantics == declaration)).map (·.id.raw)

private def selectedReference? (data : MData) : Option (Name × ComputationRef) := do
  let declaration := data.getName `CasCompiler.source.declaration
  let id := data.getString `CasCompiler.source.id
  if declaration.isAnonymous || id.isEmpty then none
  let kind := data.getName `CasCompiler.source.kind
  if kind == ``MethodEntry then some (declaration, .method ⟨id⟩)
  else if kind == ``ConstructionEntry then some (declaration, .construction ⟨id⟩)
  else if kind == ``EdgeRef.functor then some (declaration, .functor ⟨id⟩)
  else none

/-- Closed scalar data in the released literal grammar, read by ScalarLiteral.check.
Reference: CasRuntime/Literal.lean decode; this is its inverse on literal constructor forms.
Only numerals, lists and constructor applications are read. No definition is unfolded. -/
private partial def literal? (expression : Expr) : MetaM (Option Json) := do
  let expression := (← instantiateMVars expression).consumeMData
  if expression.hasFVar || expression.hasMVar then return none
  if let some value := expression.rawNatLit? then return some (toJson value)
  if let some value := expression.nat? then return some (toJson value)
  if let some value := expression.int? then return some (toJson value)
  if let .lit (.strVal value) := expression then return some (toJson value)
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

private structure Symbol where
  packet : Json
  slots : Array ContainerSlot := #[]

/-- A mechanical descriptor of a formal source term. Registered declarations use their
public addresses. Retained values keep their own references in typed slots.
Reference: CasContract.Port descriptor grammar `{"ctor": address, "args": [...]}`. -/
private partial def symbol (frame : Frame) (marks : Array ValueBinding) (state : SemanticState)
    (expression : Expr) (path : Array CasCatalogue.Backend.InputPathStep) : MetaM Symbol := do
  let retained := fun (value : ValueBinding) =>
    ({ packet := .null, slots := #[{ path, binding := value, fieldIndex := none }] } : Symbol)
  match expression with
  | .mdata data body =>
    if let some key := markedKey? data then
      let some value := marks[key]? | throwError "internal: a retained source value lost its mark"
      return retained value
    symbol frame marks state body path
  | .fvar id =>
    if let some binding := frame.context.bindings.find? (·.expression.fvarId! == id) then
      if let some value := frame.bound[binding.id]? then return retained value
    return ⟨Json.mkObj [("ctor", "variable"), ("args", .arr #[toJson (← id.getUserName).toString])], #[]⟩
  | _ =>
    if let some packet ← literal? expression then return ⟨packet, #[]⟩
    let .const name _ := expression.getAppFn
      | return ⟨Json.mkObj [("ctor", "formal"), ("args", .arr #[])], #[]⟩
    let arguments := expression.getAppArgs
    let info ← getFunInfoNArgs expression.getAppFn arguments.size
    let mut packets := #[]
    let mut slots := #[]
    let address := match descriptorIds state name with
      | #[id] => id
      | _ => "lean:" ++ name.toString
    for argument in arguments, index in [:arguments.size] do
      let explicit := (info.paramInfo[index]?.map (·.isExplicit)).getD true
      if !explicit || (← isProof argument) then continue
      let child ← symbol frame marks state argument
        (path ++ #[.field "args", .index packets.size])
      packets := packets.push child.packet
      slots := slots ++ child.slots
    return ⟨Json.mkObj [("ctor", toJson address), ("args", .arr packets)], slots⟩

private partial def captured (frame : Frame) (marks : Array ValueBinding) (expression : Expr)
    (found : Array ValueBinding) : Array ValueBinding :=
  match expression with
  | .mdata data body =>
    match markedKey? data with
    | some key => match marks[key]? with
      | some value => found.push value
      | none => found
    | none => captured frame marks body found
  | .fvar id =>
    match frame.context.bindings.find? (·.expression.fvarId! == id) with
    | some binding => match frame.bound[binding.id]? with
      | some value => found.push value
      | none => found
    | none => found
  | .app function argument => captured frame marks argument (captured frame marks function found)
  | .lam _ type body _ | .forallE _ type body _ =>
    captured frame marks body (captured frame marks type found)
  | .letE _ type value body _ =>
    captured frame marks body (captured frame marks value (captured frame marks type found))
  | .proj _ _ value => captured frame marks value found
  | _ => found

/-- Retain a checked source term as code with its actual captured references.
Its fields and applications are lowered when a demand reaches them. -/
private def closure (expression : Expr) : LowerM ValueBinding := do
  let frame ← read
  let program ← (← supply).fresh .program
  let captures := captured frame (← frame.environment.marks.get) expression #[]
  let code := ClosureCode.term (← frame.context.close expression)
  frame.environment.codes.modify (·.insert program code)
  stage expression (.closure program captures)

/-- A formal source value: a type, or a registered named constant with its public descriptor. -/
private def formal (expression : Expr) (fields : Array ValueBinding) : LowerM ValueBinding := do
  let frame ← read
  let described ← symbol frame (← frame.environment.marks.get) (← semanticState) expression #[]
  let .ok payload := ValuePayload.container described.packet described.slots fields none
    | throwError "internal: a formal source descriptor has an invalid reference layout"
  stage expression payload

mutual

/-- Lower one checked source term to its actual retained value.
Source: mathematical-input contract §2 and plan §2, lean-cas-dsl#10 comment 6664354269.
Variables read their retained bindings. Published computation families become prepared
primitive demands at their actual arguments. Fields and applications of retained values become
projection and application demands. Lambdas and selected instances retain code and captures.
Ordinary definitions are unfolded with Lean's delta rule. No operation is recognized by name. -/
private partial def lower (expression : Expr) : LowerM ValueBinding := do
  let expression ← instantiateMVars expression
  match expression with
  | .mdata data body =>
    if let some key := markedKey? data then
      let some value := (← (← read).environment.marks.get)[key]?
        | throwError "internal: a retained source value lost its mark"
      return value
    match selectedReference? data with
    | some selection =>
      withReader (fun frame => { frame with selected := frame.selected.push selection }) (lower body)
    | none => lower body
  | .fvar id =>
    let frame ← read
    if let some binding := frame.context.bindings.find? (·.expression.fvarId! == id) then
      if let some value := frame.bound[binding.id]? then return value
    match (← id.getDecl).value? with
    | some value => lower value
    | none => formal expression #[]
  | .letE _ _ value body _ =>
    if (← isProof value) || (← isType value) then return ← lower (body.instantiate1 value)
    let bound ← lower value
    lower (body.instantiate1 (← markValue (← read).environment.marks bound value))
  | .lam .. => closure expression
  | _ =>
    let type ← whnf (← inferType expression)
    if ← isProp type then throwError "internal: a source proof has no computational value"
    if type.isSort then return ← formal expression #[]
    if (← isClass? type).isSome then return ← closure expression
    if let some packet ← literal? expression then
      return ← stage expression (.portable packet.compress.toUTF8)
    let reduced ← withConfig (fun config => { config with zeta := false, zetaDelta := false })
      (whnfCore expression)
    if reduced != expression then return ← lower reduced
    match expression with
    | .proj owner index value => do
      let some info := getStructureInfo? (← getEnv) owner
        | throwError "internal: a source projection has no structure metadata"
      let some field := info.fieldNames[index]?
        | throwError "internal: a source projection is outside its structure"
      project (← lower value) index m!"{field}"
    | _ => application expression

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
  demand request

private partial def actualArguments (arguments : Array Expr) :
    LowerM (Array ClosedTerm × Array RuntimeArgument) := do
  let frame ← read
  let mut values : Array (Nat × ValueBinding) := #[]
  for argument in arguments, index in [:arguments.size] do
    unless ← isProof argument do values := values.push (index, ← lower argument)
  let graph ← frame.environment.transaction.view
  let actual ← values.mapM fun (index, value) => do
    let .ok argument := RuntimeArgument.ofValue graph index value
      | throwError "internal: a lowered source argument is outside the active graph"
    return argument
  let closed ← arguments.mapM fun argument => frame.context.close argument
  return (closed, actual)

private partial def apply (callable : ValueBinding) (arguments : Array Expr) :
    LowerM ValueBinding := do
  if arguments.isEmpty then return callable
  let frame ← read
  let (closed, actual) ← actualArguments arguments
  let request ← PreparedRequest.forApplication (← supply) frame.program
    (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
  demand request

private partial def record (expression : Expr) (fields : Array Expr) : LowerM ValueBinding := do
  let frame ← read
  let identities ← supply
  let produced ← origin expression
  let layout ← RecordLayout.ofSource produced.role
  let mut values := #[]
  for prepared in layout.fields do
    if prepared.field.wireIndex.isSome then
      let some field := fields[prepared.field.sourceIndex]?
        | throwError "internal: a source constructor lost a computational field"
      values := values.push (← lower field)
  let mut draft ← frame.environment.transaction.draft
  let mut selected ← RecordPrefix.begin identities produced.program produced.occurrence layout
  for value in values do
    let (next, extended, _) ← draft.bindField selected value
    draft := next
    selected := extended
  let payload ← IO.ofExcept <| selected.finish.mapError IO.userError
  let (complete, binding) ← draft.stage produced payload
  match ← frame.environment.transaction.installDraft complete with
  | .ok () => return binding
  | .error failure => throwError "internal: a source record could not be retained: {repr failure}"

private partial def application (expression : Expr) : LowerM ValueBinding := do
  let frame ← read
  let function := expression.getAppFn
  let arguments := expression.getAppArgs
  let .const name levels := function
    | return ← apply (← lower function) arguments
  let state ← semanticState
  let selected := frame.selected.filterMap fun (declaration, reference) =>
    if declaration == name then some reference else none
  let references := if selected.isEmpty then computationRefs state name else selected
  if let some reference := references[0]? then
    unless references.all (· == reference) do
      throwError "internal: the declaration {name} has several published computation addresses"
    let family ← SourceFamily.forReference reference
    let arity ← forallBoundedTelescope family.source.familyType (some arguments.size)
      fun locals _ => pure locals.size
    let (closed, actual) ← actualArguments (arguments.extract 0 arity)
    let request ← PreparedRequest.forBoundary (← supply) frame.program
      (← frame.environment.ledger.allocate) (.registered family) levels frame.context closed actual
      #[] (← parameters)
    return ← apply (← demand request) (arguments.extract arity arguments.size)
  if let some info := (← getEnv).getProjectionFnInfo? name then
    if info.numParams < arguments.size then
      if info.fromClass then
        if let some reduced ← unfoldProjInst? expression then return ← lower reduced
      let some operand := arguments[info.numParams]?
        | throwError "internal: a source projection lost its record"
      let field ← project (← lower operand) info.i m!"{name}"
      return ← apply field (arguments.extract (info.numParams + 1) arguments.size)
  unless (descriptorIds state name).isEmpty do
    let kind := (← SourceLayout.ofTerm (← frame.context.close expression)).kind
    if kind == .function then return ← closure expression
    if kind == .record then
      let layout := (← origin expression).role
      let mut fields := #[]
      for field in layout.fields do
        if field.wireIndex.isSome then
          let value ← field.source.inContext frame.context
          fields := fields.push (← if field.kind == .data then lower value
            else if field.kind == .typeValue then formal value #[]
            else closure value)
      return ← formal expression fields
    return ← formal expression #[]
  match (← getEnv).find? name with
  | some (.ctorInfo constructor) =>
    unless arguments.size == constructor.numParams + constructor.numFields do
      return ← closure (← etaExpand expression)
    let fields := arguments.extract constructor.numParams arguments.size
    if isStructure (← getEnv) constructor.induct then return ← record expression fields
    let described ← symbol frame (← frame.environment.marks.get) state expression #[]
    let mut packets := #[]
    let mut slots := #[]
    for field in fields do
      if ← isProof field then continue
      let value ← lower field
      slots := slots.push ({
        path := #[.field "args", .index packets.size], binding := value, fieldIndex := none } :
        ContainerSlot)
      packets := packets.push Json.null
    let packet := Json.mkObj [("ctor", toJson name.getString!), ("args", .arr packets)]
    let .ok payload := ValuePayload.container packet slots #[] none
      | throwError "internal: a source constructor has an invalid reference layout: {described.packet}"
    stage expression payload
  | some (.recInfo _) | some (.quotInfo _) =>
    throwUnsupportedSource
      m!"source eliminator {name} requires the returned-value branch compiler"
  | _ =>
    if ← isMatcher name then
      throwUnsupportedSource
        m!"source match {name} requires the returned-value branch compiler"
    let some unfolded ← unfoldDefinition? expression
      | throwUnsupportedSource
          m!"source constant {name} has no published computational interface and no definition"
    lower unfolded

end

/-- Lower a checked source term in its complete context and return its actual retained value.
`bound` is the runtime-binding table of the context, by stable source identity. -/
opaque lowerTerm (environment : LowerEnvironment) (program : RuntimeId .program)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding) (expression : Expr) :
    MetaM ValueBinding :=
  (lower expression).run { environment, program, context, bound, selected := #[] }

end CasCompiler
