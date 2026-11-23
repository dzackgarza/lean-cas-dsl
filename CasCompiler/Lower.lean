module

public import CasRuntime.Closure
public import CasCompiler.Elaborate
public import CasCompiler.SelectedField
public import CasCompiler.SelectedMorphism
public import CasCompiler.InputCoverage
public import CasRuntime.Transaction
public import CasRuntime.InputResult
public import CasRuntime.RoutedMethod
public import LeanCategories.Catalogue.Registry.Semantic
public import CasCatalogue.InterpretationFailure

public section

namespace CasCompiler

open Lean Meta CasRuntime CasCatalogue

initialize registerTraceClass `cas.lower

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

private def origin (expression : Expr) : LowerM ValueOrigin := do
  let frame ← read
  let identities ← supply
  let role ← SourceLayout.ofTerm (← frame.context.close expression)
  let environment ← RuntimeEnvironment.capture identities.worker frame.context (← parameters)
  environment.origin frame.program (← identities.fresh .occurrence) role

private def stage (expression : Expr) (payload : ValuePayload) : LowerM ValueBinding := do
  (← read).environment.transaction.stage (← origin expression) payload

private def demand (request : PreparedRequest) : LowerM ValueBinding := do
  let request := request.withSelection (← read).selection
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
  if kind == ``OperationEntry then some (declaration, .operation ⟨id⟩)
  else if kind == ``MethodEntry then some (declaration, .method ⟨id⟩)
  else if kind == ``ConstructionEntry then some (declaration, .construction ⟨id⟩)
  else if kind == ``EdgeRef.functor then some (declaration, .functor ⟨id⟩)
  else none

/-- A registered distinguished element that the reader evaluated at its point: a subset literal,
an object's generator, a numeral, or the apex of a registered limit or colimit at its maps. Its address names the element; the declaration locates its
application inside the native point value. A numeral is the image of `k` under a universal map
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
      let environment ← RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
      -- This exact Arrow.mk argument may already name an actual input. Preserve that
      -- reference; otherwise the endpoint remains a descriptor of its selected arrow.
      if ← environment.hasRetainedSource frame.context endpoint then
        return ← lower (← argumentSource environment endpoint)
      let value ← lower arrow.getAppArgs.back!
      let template := Json.mkObj [("ctor", "morphismEndpoint"),
        ("args", .arr #[.null, toJson selector])]
      let .ok payload := ValuePayload.descriptor template
          #[{ path := #[.field "args", .index 0], binding := value, fieldIndex := none }]
        | throwError "the selected endpoint has an invalid reference layout"
      return ← stage expression payload
    if let some (selection, field) := selectedField? data then
      let transaction := (← read).environment.transaction
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
    -- The reader's selected address belongs to each occurrence of its declaration. It moves
    -- onto those occurrences, so retained code keeps it after this term is taken apart.
    -- A named element is sent as its descriptor at its explicit parameters, not as the
    -- unfolded definition of its point value.
    -- A registered object application is published as `<object>#application` (leaf contract
    -- api/manifest.md); ComputationRef has no object-application kind, so the kernel cannot
    -- address it, and it does not evaluate the application's definition (C22).
    if data.getName `CasCompiler.source.kind == ``ObjectEntry.application then
      throwStratum .noImplementation
        m!"{data.getString `CasCompiler.source.id}#application has no kernel computation address"
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
    if let some (declaration, address) := namedElement? data then
      let some element := body.find? (·.getAppFn.isConstOf declaration)
        | throwError "internal: the named element lost its registered declaration"
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
    if let .mdata data head := expression.getAppFn then
      if (markedKey? data).isSome ||
          data.getName `CasCompiler.source.kind == ``RoutedMethodFamily then
        return ← apply (← lower expression.getAppFn) expression.getAppArgs
      if (selectedReference? data).isSome then return ← application expression
      if !data.contains `CasCompiler.source.kind &&
          !data.contains `CasCompiler.lower.value &&
          !data.contains `CasCompiler.selection &&
          !data.contains `CasCompiler.endpoint then
        return ← lower (mkAppN head expression.getAppArgs)
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
      let frame ← read
      let environment ← RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
      if ← environment.hasRetainedSource frame.context projection.parent then
        let (parent, path) ← projectionSourcePath environment projectionSource
        let selected ← projectPath (← lower parent) path
        return ← apply selected (arguments.extract projectionSource.getAppNumArgs arguments.size)
    -- Select a native constructor field before head reduction can discard its retained-value
    -- or source-boundary metadata. This reads only the exact selected constructor argument.
    -- Reuse the metadata-preserving projection step from Layout.inputProjectionHead.
    if let some projection ← SourceProjection.ofExpr? expression then
      if let .mdata data _ := projection.parent.getAppFn then
        if data.getName `CasCompiler.source.kind == ``RoutedMethodFamily then
          return ← project (← lower projection.parent) projection.info.i
            m!"{projection.declaration}"
      if projection.parent.getAppFn.constName? == some projection.info.ctorName then
        if let some selected ← projectCore? projection.parent projection.info.i then
          return ← lower selected
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
    if (type.getAppFn.constName?.map (isStructure (← getEnv))).getD false then
      if let some value ← nativeInputRecord? expression then return value
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
    | .forallE .. | .sort .. =>
      if type.isProp then
        -- A quantified proposition is decided by a published predicate or not at all (C22).
        throwStratum .noImplementation m!"the proposition {expression} has no published predicate"
      descriptor expression "lean:type" #[]
    | _ => application expression

/-- A descriptor of a named source constant at its actual explicit arguments.
Reference: CasContract.Port descriptor grammar `{"ctor": address, "args": [...]}`.
Each argument is lowered and keeps its own retained reference in a typed slot. -/
private partial def descriptor (expression : Expr) (address : String) (arguments : Array Expr)
    (fields : Option (Array ValueBinding) := none) : LowerM ValueBinding := do
  let mut packets := #[]
  let mut slots := #[]
  for argument in arguments do
    let value ← lower argument
    slots := slots.push ({
      path := #[.field "args", .index packets.size], binding := value, fieldIndex := none } :
      ContainerSlot)
    packets := packets.push Json.null
  let packet := Json.mkObj [("ctor", toJson address), ("args", .arr packets)]
  let built := match fields with
    | some fields => ValuePayload.container packet slots fields none
    | none => ValuePayload.descriptor packet slots
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
private partial def namedConstant (expression : Expr) (address : String) (arguments : Array Expr) :
    LowerM ValueBinding := do
  if (← origin expression).role.kind == .function then return ← closure expression
  descriptor expression address arguments (some (← fieldClosures expression))

/-- Native fields of an ordinary registered constant whose definition `field` may open.
Published element descriptors do not use these closures: their fields require computation. -/
private partial def fieldClosures (expression : Expr) : LowerM (Array ValueBinding) := do
  let frame ← read
  let mut fields := #[]
  for prepared in (← origin expression).role.fields do
    if prepared.wireIndex.isSome then
      fields := fields.push (← closure (← prepared.source.inContext frame.context))
  return fields

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
    if (markedKey? data).isSome ||
        data.getName `CasCompiler.source.kind == ``PresentationFamily then
      return ← project (← lower value) index name
  if (← isClass? (← whnf (← inferType value))).isSome then
    let reduced ← whnfCore (.proj owner index (← whnf value))
    if reduced.isProj then
      throwUnsupportedSource m!"the selected instance field {name} has no definition in this context"
    return ← lower reduced
  if let .const declaration _ := value.consumeMData.getAppFn then
    unless (descriptorIds (← semanticState) declaration).isEmpty do
      if let some unfolded ← unfoldDefinition? value.consumeMData then
        return ← lower (.proj owner index unfolded)
  let frame ← read
  let environment ← RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
  -- An unretained inner projection still owns its native definition boundary. Lower it
  -- before the outer demand; flattening through its named field closure would re-enter
  -- that same projection code. Actual retained roots keep their complete selected path.
  if !(← environment.hasRetainedSource frame.context value) then
    return ← project (← lower value) index name
  let (parent, path) ← projectionSourcePath environment (.proj owner index value)
  if path.isEmpty then return ← project (← lower value) index name
  projectPath (← lower parent) path

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
    (deferAfter : Option Nat := none) (required : Option (Array Nat) := none) :
    LowerM (Array ClosedTerm × Array RuntimeArgument) := do
  let frame ← read
  let environment ← RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
  let mut values : Array (Nat × ValueBinding) := #[]
  let mut sources : Array Expr := #[]
  for argument in arguments, index in [:arguments.size] do
    if ← isProof argument then sources := sources.push argument
    else
      -- Complete source coverage has already identified unused admission evidence. Keep its
      -- formal slot without touching its source parent or manufacturing a runtime value.
      if deferAfter.any (· < index) && required.any (fun needed => !needed.contains index) then
        sources := sources.push argument
        continue
      -- Used evidence follows ordinary retained-source preparation first. A projection of a
      -- lazy parent is a genuine demand; only unanchored native evidence code remains lazy.
      let source ← argumentSource environment argument
      let deferred ← if deferAfter.any (· < index) then
          environment.hasRetainedSource frame.context source <&> Bool.not
        else pure false
      let value ← if deferred then closure source else lower source
      values := values.push (index, value)
      sources := sources.push source
  let graph ← frame.environment.transaction.view
  let marks ← frame.environment.marks.get
  let actual ← values.mapM fun (index, value) => do
    let .ok argument := RuntimeArgument.ofValue graph index value marks
      | throwError "internal: a lowered source argument is outside the active graph"
    return argument
  let closed ← sources.mapM fun argument => frame.context.close argument
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
  let state ← semanticState
  unless (computationRefs state declaration).isEmpty &&
      (descriptorIds state declaration).isEmpty &&
      ((← getEnv).getProjectionFnInfo? declaration).isNone do return none
  let some (.defnInfo _) := (← getEnv).find? declaration | return none
  let some expanded ← unfoldDefinition? expression | return none
  let some constructor := expanded.getAppFn.constName? | return none
  let some (.ctorInfo _) := (← getEnv).find? constructor | return none
  let frame ← read
  let sourceArguments ← arguments.mapM fun argument => frame.context.close argument
  let source ← SourceLayout.ofTerm (← frame.context.close expression.getAppFn)
  let (result, application) ← ApplicationLayout.ofSource source frame.context sourceArguments
  unless result.kind == .record && result.fields.any
      (fun field => field.wireIndex.isSome && !field.precedingDependencies.isEmpty) do return none
  let actualParameters ← parameters
  let some required ← application.inputResultArguments (actualParameters.map (·.source))
    | return none
  -- Ordinary application admission stays total. This conservative path never evaluates a
  -- source slot that the complete native result and its type dependencies did not require.
  for argument in application.arguments do
    if argument.wireIndex.isSome && !required.contains argument.sourceIndex then return none
  let callable ← closure expression.getAppFn
  let (closed, actual) ← actualArguments arguments
  let request ← PreparedRequest.forApplication (← supply) frame.program
    (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
  unless (← request.inputResultPlan (← frame.environment.transaction.view)).isSome do
    throwStratum .noImplementation
      "the native record conversion requires unavailable input fields"
  return some (← demand request)

private partial def apply (callable : ValueBinding) (arguments : Array Expr) :
    LowerM ValueBinding := do
  if arguments.isEmpty then return callable
  let frame ← read
  let (closed, actual) ← actualArguments arguments
  let request ← PreparedRequest.forApplication (← supply) frame.program
    (← frame.environment.ledger.allocate) frame.context callable closed actual (← parameters)
  demand request

private partial def record (expression : Expr) (fields : Array Expr) : LowerM ValueBinding := do
  let layout ← RecordLayout.ofSource (← origin expression).role
  let mut values := #[]
  for prepared in layout.fields do
    if prepared.field.wireIndex.isSome then
      let some field := fields[prepared.field.sourceIndex]?
        | throwError "internal: a source constructor lost a computational field"
      values := values.push (← lower field)
  stageRecord expression values

/-- Stage the record `expression` from the values of its computational fields, in order. -/
private partial def stageRecord (expression : Expr) (values : Array ValueBinding) :
    LowerM ValueBinding := do
  let frame ← read
  let identities ← supply
  let produced ← origin expression
  let layout ← RecordLayout.ofSource produced.role
  unless values.size == (layout.fields.filter (·.field.wireIndex.isSome)).size do
    throwError "internal: a source record has a different number of computational fields"
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
  let environment ← RuntimeEnvironment.capture (← supply).worker frame.context (← parameters)
  let arguments ← environment.methodParameters frame.context frame.environment.transaction
    frame.environment.marks frame.environment.ledger.allocate family
    (body.getAppArgs.extract 0 family.parameterCount) receiver
    (fun expression => lower expression frame)
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
  let callable ← demand request
  apply callable #[← markValue frame.environment.marks receiver source]

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
    return ← namedConstant expression address (← explicitArguments expression)
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
    -- A type former at its arguments is an object of the category of sets.
    descriptor expression s!"lean:{name}" (← explicitArguments expression)
  | some (.recInfo _) | some (.quotInfo _) =>
    -- The kernel evaluates no eliminator (constitution C22): branching belongs to the leaf
    -- that implements an operation.
    throwStratum .noImplementation m!"{name} is an eliminator with no published operation"
  | _ =>
    if ← isMatcher name then
      throwStratum .noImplementation m!"{name} is a match with no published operation"
    let some unfolded ← unfoldDefinition? expression
      | throwStratum .noImplementation
          m!"{name} has no published operation and no definition"
    lower unfolded

end

/-- Lower a checked source term in its complete context and return its actual retained value.
`bound` is the runtime-binding table of the context, by stable source identity. -/
opaque lowerTerm (environment : LowerEnvironment) (program : RuntimeId .program)
    (context : OpenContext) (bound : Std.HashMap BindingId ValueBinding) (expression : Expr) :
    MetaM ValueBinding :=
  (lower expression).run { environment, program, context, bound }

end CasCompiler
