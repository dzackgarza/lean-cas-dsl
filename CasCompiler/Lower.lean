module

public import CasCompiler.Program
public import CasCompiler.Elaborate
public import CasRuntime.Transaction
public import LeanCategories.Catalogue.Registry.Semantic
public import CasCatalogue.InterpretationFailure

public section

namespace CasCompiler

open Lean Meta CasRuntime CasCatalogue

initialize registerTraceClass `cas.lower

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

/-- Closed ground data with no published computation family is ordinary Lean data: a numeral,
a finite index, a tuple of such. Lean's reduction gives its literal form.
A term that names a published family is never reduced here: its definition is mathematics,
and its computation is the published interface (mathematical-input contract §2).
Reuse: Lean.Meta.reduce at Lean v4.33.0. -/
private def evaluated? (state : SemanticState) (expression type : Expr) : MetaM (Option Json) := do
  if expression.hasFVar || expression.hasMVar || type.isForall || type.isSort then return none
  if (expression.find? fun term => match term with
      | .mdata data _ => (markedKey? data).isSome
      | _ => false).isSome then return none
  unless expression.getUsedConstants.all fun name => (computationRefs state name).isEmpty do
    return none
  literal? (← reduce expression (skipTypes := true) (skipProofs := true))

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
    -- The reader's selected address belongs to each occurrence of its declaration. It moves
    -- onto those occurrences, so retained code keeps it after this term is taken apart.
    match selectedReference? data with
    | some (declaration, _) =>
      if body.isConstOf declaration then application expression
      else lower (body.replace fun term =>
        if term.isConstOf declaration then some (.mdata data term) else none)
    | none => lower body
  | .fvar id =>
    let frame ← read
    if let some binding := frame.context.bindings.find? (·.expression.fvarId! == id) then
      if let some value := frame.bound[binding.id]? then return value
    match (← id.getDecl).value? with
    | some value => lower value
    | none =>
      -- A formal parameter of the source has no computed value. Its descriptor names it.
      let packet := Json.mkObj [("ctor", "variable"),
        ("args", .arr #[toJson (← id.getUserName).toString])]
      stage expression (.portable packet.compress.toUTF8)
  | .letE _ _ value body _ =>
    if (← isProof value) || (← isType value) then return ← lower (body.instantiate1 value)
    let bound ← lower value
    lower (body.instantiate1 (← markValue (← read).environment.marks bound value))
  | .lam .. => closure expression
  | _ =>
    -- Lean's head reduction drops metadata. A retained value at the head is applied as that
    -- same value, a retained record gives its field, and a selected family head is dispatched.
    if let .mdata data _ := expression.getAppFn then
      if (markedKey? data).isSome then
        return ← apply (← lower expression.getAppFn) expression.getAppArgs
      if (selectedReference? data).isSome then return ← application expression
    if let .proj owner index (.mdata data value) := expression then
      if (markedKey? data).isSome then
        let some info := getStructureInfo? (← getEnv) owner
          | throwError "internal: a source projection has no structure metadata"
        return ← project (← lower (.mdata data value)) index m!"{info.fieldNames[index]?}"
    let type ← whnf (← inferType expression)
    trace[cas.lower] "{expression.getAppFn} [{expression.getAppNumArgs}] : {type}"
    if ← isProp type then throwError "internal: a source proof has no computational value"
    if (← isClass? type).isSome then return ← closure expression
    -- A structure value is a dependent record of its fields. Only data-kind terms are packets.
    -- A type is an object of the category of sets, and is lowered like any other term.
    unless type.isSort || (type.getAppFn.constName?.map (isStructure (← getEnv))).getD false do
      if let some packet ← literal? expression then
        return ← stage expression (.portable packet.compress.toUTF8)
      if let some packet ← evaluated? (← semanticState) expression type then
        return ← stage expression (.portable packet.compress.toUTF8)
    -- Head reduction only: no let substitution and no unfolding under a projection, so a
    -- published family below a field stays a demand and is not replaced by its definition.
    let reduced ← withConfig (fun config =>
      { config with zeta := false, zetaDelta := false, proj := .yes }) (whnfCore expression)
    if reduced != expression then return ← lower reduced
    match expression with
    | .proj owner index value => do
      let some info := getStructureInfo? (← getEnv) owner
        | throwError "internal: a source projection has no structure metadata"
      let some name := info.fieldNames[index]?
        | throwError "internal: a source projection is outside its structure"
      field owner index value m!"{name}"
    | .forallE .. | .sort .. => descriptor expression "lean:type" #[] #[]
    | _ => application expression

/-- A descriptor of a named source constant at its actual explicit arguments.
Reference: CasContract.Port descriptor grammar `{"ctor": address, "args": [...]}`.
Each argument is lowered and keeps its own retained reference in a typed slot. -/
private partial def descriptor (expression : Expr) (address : String) (arguments : Array Expr)
    (fields : Array ValueBinding) : LowerM ValueBinding := do
  let mut packets := #[]
  let mut slots := #[]
  for argument in arguments do
    let value ← lower argument
    slots := slots.push ({
      path := #[.field "args", .index packets.size], binding := value, fieldIndex := none } :
      ContainerSlot)
    packets := packets.push Json.null
  let packet := Json.mkObj [("ctor", toJson address), ("args", .arr packets)]
  let .ok payload := ValuePayload.container packet slots fields none
    | throwError "internal: the descriptor of {address} has an invalid reference layout"
  stage expression payload

/-- The explicit arguments of an application that are not proofs. -/
private partial def explicitArguments (expression : Expr) : LowerM (Array Expr) := do
  let arguments := expression.getAppArgs
  let info ← getFunInfoNArgs expression.getAppFn arguments.size
  let mut selected := #[]
  for argument in arguments, index in [:arguments.size] do
    let explicit := (info.paramInfo[index]?.map (·.isExplicit)).getD true
    if explicit && !(← isProof argument) then selected := selected.push argument
  return selected

/-- Select one field of a checked source record.
A selected instance and a registered named constant are definitions, so the field comes from
Lean's reduction of that definition. Any other record is lowered, and the field is a demand. -/
private partial def field (owner : Name) (index : Nat) (value : Expr) (name : MessageData) :
    LowerM ValueBinding := do
  if let .mdata data _ := value then
    if (markedKey? data).isSome then return ← project (← lower value) index name
  if (← isClass? (← whnf (← inferType value))).isSome then
    let reduced ← whnfCore (.proj owner index (← whnf value))
    if reduced.isProj then
      throwUnsupportedSource m!"the selected instance field {name} has no definition in this context"
    return ← lower reduced
  if let .const declaration _ := value.consumeMData.getAppFn then
    unless (descriptorIds (← semanticState) declaration).isEmpty do
      if let some unfolded ← unfoldDefinition? value.consumeMData then
        return ← lower (.proj owner index unfolded)
  project (← lower value) index name

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
  let state ← semanticState
  let references := match selected with
    | some reference => #[reference]
    | none => computationRefs state name
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
      let owner := (← getConstInfoCtor info.ctorName).induct
      let selected ← field owner info.i operand m!"{name}"
      return ← apply selected (arguments.extract (info.numParams + 1) arguments.size)
  if let some address := (descriptorIds state name)[0]? then
    let layout := (← origin expression).role
    if layout.kind == .function then return ← closure expression
    let mut fields := #[]
    for prepared in layout.fields do
      if prepared.wireIndex.isSome then
        fields := fields.push (← closure (← prepared.source.inContext frame.context))
    return ← descriptor expression address (← explicitArguments expression) fields
  match (← getEnv).find? name with
  | some (.ctorInfo constructor) =>
    unless arguments.size == constructor.numParams + constructor.numFields do
      return ← closure (← etaExpand expression)
    let fields := arguments.extract constructor.numParams arguments.size
    if isStructure (← getEnv) constructor.induct then return ← record expression fields
    descriptor expression name.getString! (← fields.filterM fun field => return !(← isProof field))
      #[]
  | some (.inductInfo _) =>
    -- A type former at its arguments is an object of the category of sets.
    descriptor expression s!"lean:{name}" (← explicitArguments expression) #[]
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
  (lower expression).run { environment, program, context, bound }

end CasCompiler
