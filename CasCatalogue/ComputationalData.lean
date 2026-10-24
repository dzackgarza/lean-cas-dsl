/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import CasCatalogue.Semantic
public import CasCatalogue.ObjectPresentation
public import CasCatalogue.Language
public import CasCatalogue.Codec
public import CasCatalogue.StructuredResult
public import CasCatalogue.Admission
public import CasContract.Port
public import Mathlib.CategoryTheory.FintypeCat

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.ComputationalData

/-- A finite structural inspection permits ordinary data constructors only.
Records containing types, proof obligations, functions or algebraic structures
never enter the codec. The bound rejects unsupported recursive representations. -/
def plainTypeAux (type : Expr) (fuel : Nat) : MetaM Bool := do
  let fuel + 1 := fuel | return false
  let type ← whnfR type
  if #[``Nat, ``Int, ``Bool, ``String, ``Unit].any type.isConstOf then return true
  if type.isAppOf ``Fin then return true
  if type.isAppOf ``List || type.isAppOf ``Array || type.isAppOf ``Option then
    return ← plainTypeAux type.appArg! fuel
  if type.isAppOf ``Prod then
    let args := type.getAppArgs
    return (← plainTypeAux args[0]! fuel) && (← plainTypeAux args[1]! fuel)
  let some name := type.getAppFn.constName? | return false
  let some (.inductInfo info) := (← getEnv).find? name | return false
  if info.numIndices != 0 then return false
  for name in info.ctors do
    let constructor ← getConstInfoCtor name
    let safe ← forallTelescopeReducing constructor.type fun fields _ => do
      for field in fields.extract constructor.numParams (constructor.numParams + constructor.numFields) do
        let fieldType ← inferType field
        if fieldType.isSort || (← isProp fieldType) then return false
        unless ← plainTypeAux fieldType fuel do return false
      return true
    unless safe do return false
  return true

def plainType (type : Expr) : MetaM Bool := plainTypeAux type 8

/-- Released constructor framing, independent of the mathematical value of its fields. -/
def envelope (json : Json) : Except String (String × Array Json) := do
  let tag ← json.getObjValAs? String "ctor"
  let args ← (json.getObjVal? "args").bind (·.getArr?)
  return (tag, args)

/-- Find a complete retained public declaration application without unfolding it. -/
def retainedApplication (declaration : Name) (formal : Expr) : TermElabM (Option Expr) := do
  let arity ← forallTelescopeReducing (← getConstInfo declaration).type
    fun fields _ => pure fields.size
  return formal.find? fun term =>
    term.getAppFn.constName? == some declaration && term.getAppNumArgs == arity

/-- Recover a complete public functor application from the fixed selected action.
This also handles a published lift's projection, without letting computational
parameters choose an action or treating an inner functor as the whole action. -/
def fixedFunctorApplication (declaration : Name) (formal : Expr) :
    TermElabM (Option Expr) := withoutModifyingState do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  let application := mkAppN constant parameters
  let action ← Semantic.asFunctor application
  unless ← withTransparency .all <| isDefEq action formal do return none
  let application ← instantiateMVars application
  if application.hasMVar || application.hasLevelMVar || application.hasFVar then return none
  return some application

/-- Recover an action from the fixed public context, including an object's projection.
The fresh-source check identifies the whole action, not equality at one computed value.
No computational field participates in parameter or receiver inference. -/
def actionContext (formalField : Expr) (edge : Json) :
    TermElabM (Except String (Expr × Expr)) := do
  let formal := formalField.consumeMData
  if formal.isAppOf ``CategoryTheory.Functor.obj then
    let fields := formal.getAppArgs
    return .ok (fields[fields.size - 2]!, fields.back!)
  if formal.isAppOf ``Prefunctor.obj then
    let fields := formal.getAppArgs
    let prefunctor := fields[fields.size - 2]!.consumeMData
    if prefunctor.isAppOf ``CategoryTheory.Functor.toPrefunctor then
      return .ok (prefunctor.getAppArgs.back!, fields.back!)
  let state ← registryState
  let .ok (tag, _) := envelope edge
    | return .error "the selected action has no complete declaration descriptor"
  let some entry := state.functors.find? (·.id.raw == tag)
    | return .error "the projected action has no registered public functor"
  let sources ← IO.mkRef (#[] : Array Expr)
  formal.forEach fun source => do
    if !source.hasMVar && !source.hasLevelMVar && !source.hasFVar &&
        !source.hasLooseBVars && (source.isApp || source.isConst) then
      sources.modify (·.push source)
  let mut contexts : Array (Expr × Expr) := #[]
  for source in ← sources.get do
    let candidate ← withoutModifyingState do
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType declaration)
      let action ← Semantic.asFunctor (mkAppN declaration parameters)
      let actionType ← whnfR (← inferType action)
      unless actionType.isAppOf ``CategoryTheory.Functor do return none
      let sourceType ← inferType source
      unless ← withTransparency .all <| isDefEq actionType.getAppArgs[0]! sourceType do
        return none
      let agrees ← withLocalDeclD `source sourceType fun selectedSource => do
        let context := formal.replace fun term =>
          if term == source then some selectedSource else none
        let image ← Semantic.objOf action selectedSource
        withTransparency .all <| isDefEq context image
      unless agrees do return none
      let action ← instantiateMVars action
      if action.hasMVar || action.hasLevelMVar || action.hasFVar then return none
      return some (action, source)
    if let some candidate := candidate then
      unless ← contexts.anyM (fun existing => withoutModifyingState do
          isDefEq existing.1 candidate.1 <&&> isDefEq existing.2 candidate.2) do
        contexts := contexts.push candidate
  match contexts with
  | #[(action, source)] => return .ok (action, source)
  | #[] => return .error "the action requires its independently retained formal receiver context"
  | _ => return .error "the projected action has several distinct fixed receiver contexts"

/-- Complete graph-domain framing against the actual computational endpoint's
published representation keys. The caller supplies keys from retained data;
this function never enumerates the independent formal construction's carrier. -/
def validateGraphDomain (domainKeys : Array Json) (graph : Json) : Except String Unit := do
  let pairs ← graph.getArr?
  unless pairs.size == domainKeys.size do
    throw "the computational graph is not total at its declared data endpoint"
  let mut keys : Array Json := #[]
  for pair in pairs do
    let #[input, _] ← pair.getArr?
      | throw "a computational graph entry requires input and output"
    if keys.contains input then throw "the computational graph repeats a domain key"
    unless domainKeys.contains input do
      throw "the computational graph uses a key outside its declared data endpoint"
    keys := keys.push input
  return ()

/-- Check finite callable completeness and range framing against keys from the
actual declared computational endpoints. Infinite codomains retain their
published point codec; `none` never substitutes the formal codomain's carrier. -/
def validateGraphEndpoints (actualDomainKeys : Array Json)
    (actualCodomainKeys : Option (Array Json)) (graph : Json) : Except String Unit := do
  validateGraphDomain actualDomainKeys graph
  if let some codomainKeys := actualCodomainKeys then
    let pairs ← graph.getArr?
    for pair in pairs do
      let #[_, output] ← pair.getArr?
        | throw "a computational graph entry requires input and output"
      unless codomainKeys.contains output do
        throw "the computational graph value is outside its declared data codomain"
  return ()

/-- Read the primitive finite point-codec parameter from a registered public
object declaration. Only explicit `Fin` and its public finite-category wrapper
are recognized; no private definition or law record is unfolded. -/
def finiteParameter (declaration : Name) : TermElabM (Option Nat) := do
  let .defnInfo definition ← getConstInfo declaration | return none
  lambdaTelescope definition.value fun parameters body => do
    let body := body.consumeMData
    let carrier := if body.isAppOf ``FintypeCat.of then body.getAppArgs[0]!
      else if body.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.mk then
        let args := body.getAppArgs
        args[args.size - 2]!
      else body
    let carrier := carrier.consumeMData
    unless carrier.isAppOf ``Fin do return none
    let bound := carrier.appArg!
    let mut position := 0
    for parameter in parameters do
      let info ← parameter.fvarId!.getBinderInfo
      if info.isExplicit && !(← isProp (← inferType parameter)) then
        if parameter == bound then return some position
        position := position + 1
    return none

/-- Match the released edge identity in an independently published refinement.
Ordered actual declaration parameters are checked by `validateAction`. -/
partial def matchesEdge (edge : EdgeRef) (data : Json) : Bool :=
  match edge, envelope data with
  | .functor id, .ok (tag, _) => tag == id.raw
  | .classifierForget id, .ok ("classifierForget", #[name, _]) =>
      name.getStr?.toOption == some id.raw
  | .constructMap id inner, .ok ("constructorMap", #[name, actualInner]) =>
      name.getStr?.toOption == some id.raw && matchesEdge inner actualInner
  | _, _ => false

/-- Actual finite keys from the public primitive representation, never from the
formal apex. `none` declines enumeration for opaque/nonprimitive representations. -/
partial def endpointKeys (data : Json) : TermElabM (Except String (Option (Array Json))) := do
  let .ok (tag, args) := envelope data
    | return .error "an endpoint requires its released complete object descriptor"
  if tag == "finiteData" then
    let #[_, inventory] := args
      | return .error "finiteData requires its complete object descriptor and point inventory"
    let .ok points := inventory.getArr?
      | return .error "a computational point inventory requires an array"
    let mut seen := #[]
    for point in points do
      if seen.contains point then return .error "a computational point inventory repeats a key"
      seen := seen.push point
    return .ok (some points)
  if tag == "opaqueData" then
    let #[token] := args | return .error "opaqueData requires one token"
    let .ok token := token.getStr? | return .error "an opaque token must be a string"
    if token.isEmpty then return .error "an opaque token must be nonempty"
    return .ok none
  if tag == "morphismEndpoint" then
    return (Backend.MorphismEndpoint.decode data).map fun _ => none
  if tag == "valueData" then
    let #[actual] := args | return .error "valueData requires one data field"
    return ← endpointKeys actual
  if tag == "objectPresentation" then
    let #[_, actual] := args | return .error "objectPresentation requires its action and actual data"
    return ← endpointKeys actual
  if tag == "objectProduct" then
    let #[left, right] := args | return .error "objectProduct requires two actual factors"
    let leftKeys ← endpointKeys left
    let rightKeys ← endpointKeys right
    match leftKeys, rightKeys with
    | .error message, _ | _, .error message => return .error message
    | .ok (some left), .ok (some right) =>
      return .ok (some (left.flatMap fun x => right.map fun y => Json.arr #[x, y]))
    | _, _ => return .ok none
  let state ← registryState
  if tag == "functorAction" then
    let #[action, source] := args | return .error "functorAction requires its action and source"
    let .ok (sourceTag, _) := envelope source | return .error "the action source has no object descriptor"
    let some entry := state.objects.find? (·.id.raw == sourceTag) | return .ok none
    let some refinement := entry.refines | return .ok none
    let #[edge] := refinement.route | return .ok none
    unless matchesEdge edge action do return .ok none
    let some base := state.objects.find? (·.id == refinement.base) | return .error "the refinement base is not registered"
    let some sourceParameter ← finiteParameter entry.declaration | return .ok none
    let some targetParameter ← finiteParameter base.declaration | return .ok none
    unless sourceParameter == targetParameter do return .ok none
    -- Both published endpoint codecs are Fin at this same actual parameter.
    -- No action on points or comparison map is replaced by this key-set check.
    return ← endpointKeys source
  let some entry := state.objects.find? (·.id.raw == tag)
    | return .error "the endpoint object descriptor is not registered"
  let some position ← finiteParameter entry.declaration | return .ok none
  let some bound := args[position]? | return .error "the finite representation omitted its size"
  let .ok bound := bound.getNat? | return .error "the finite representation size must be a natural number"
  return .ok (some ((Array.range bound).map toJson))

/-- The computational slots of a fixed public type. This carries no decoded
mathematical values, constructor laws or proofs. -/
inductive PointSchema where
  | plain (type : Expr)
  | keys (points : Array Json)
  | list (element : PointSchema)
  | graph (domain codomain : PointSchema) (domainKeys : Option (Array Json))
  | recordFields (unlabelled : Bool) (fields : Array PointSchema)
  | alternatives (constructors : Array (String × PointSchema))

/-- A scalar literal has only independently fixed scalar data slots. Callable
fields and computational endpoint inventories remain data-only interfaces. -/
partial def PointSchema.scalarLiteral : PointSchema → Bool
  | .plain _ => true
  | .list element => element.scalarLiteral
  | .recordFields _ fields => fields.all PointSchema.scalarLiteral
  | .alternatives constructors => constructors.all (fun (_, schema) => schema.scalarLiteral)
  | .keys _ | .graph .. => false

/-- Extract wholly inline literal data, preserving its public structure while
removing value wrappers. An owned opaque field cannot become a decoded literal. -/
partial def inlineLiteralData? (json : Json) : Option Json := do
  if let .ok (tag, args) := envelope json then
    if tag == "opaqueData" then return ← none
    if tag == "valueData" then
      let #[value] := args | return ← none
      return ← inlineLiteralData? value
  match json with
  | .arr values => return .arr (← values.mapM inlineLiteralData?)
  | .obj fields =>
      return Json.mkObj (← fields.toList.mapM fun (key, value) => do
        return (key, ← inlineLiteralData? value))
  | value => return value

/-- Derive only data slots from public constructor metadata. Dependent data
slots without an independent fixed type remain unsupported. -/
partial def pointSchema (type : Expr) (fuel : Nat := 32) :
    TermElabM (Option PointSchema) := do
  let fuel + 1 := fuel | return none
  let type ← withTransparency .all <| whnf type
  if type.hasMVar || type.hasLevelMVar || type.hasLooseBVars then return none
  if type.isSort || (← isProp type) then return none
  if ← plainType type then return some (.plain type)
  if type.isAppOf ``List || type.isAppOf ``Array then
    return (← pointSchema type.appArg! fuel).map PointSchema.list
  if type.isAppOf ``Quot then return ← pointSchema type.getAppArgs[0]! fuel
  if let .forallE _ domain body _ := type then
    if body.hasLooseBVars then return none
    let mut keys := none
    if ← plainType domain then
      if let some points ← Codec.finiteDomain domain then
        let encoded ← points.mapM fun point => Codec.encode point
        if encoded.all Except.isOk then keys := some (encoded.filterMap Except.toOption)
    let some domain ← pointSchema domain fuel | return none
    let some codomain ← pointSchema body fuel | return none
    return some (.graph domain codomain keys)
  let .const name levels := type.getAppFn | return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  let mut alternatives := #[]
  for name in info.ctors do
    let ctor ← getConstInfoCtor name
    let schema ← withoutModifyingState do
      let (fields, _, conclusion) ← forallMetaTelescopeReducing
        (← inferType (mkConst name levels))
      unless ← withTransparency .all <| isDefEq conclusion type do return none
      let mut schemas := #[]
      for field in fields.extract ctor.numParams (ctor.numParams + ctor.numFields) do
        let fieldType ← instantiateMVars (← inferType field)
        if ← isProp fieldType then continue
        let some schema ← pointSchema fieldType fuel | return none
        schemas := schemas.push schema
      return some (PointSchema.recordFields (Codec.isUnlabelled info) schemas)
    let some schema := schema | return none
    alternatives := alternatives.push (Codec.label name, schema)
  if Codec.isUnlabelled info then return alternatives[0]?.map Prod.snd
  return some (.alternatives alternatives)

/-- Inspect computational JSON against its independent schema without applying
constructors, filling proof slots, or producing a law-bearing Lean value. -/
partial def validatePoint (schema : PointSchema) (json : Json) :
    TermElabM (Except String Unit) := do
  -- Opaque fields may occur inside records as well as at the outer result. Their
  -- live owner is retained by the computational consumer. Actual finite endpoint
  -- keys, however, must still be members of the supplied inventory verbatim.
  unless schema matches .keys _ do
    if (json.getObjValAs? String "ctor").toOption == some "opaqueData" then
      return (Backend.ComputationalValue.decode json).map fun _ => ()
    if let .ok ("valueData", #[actual]) := envelope json then
      return ← validatePoint schema actual
  match schema with
  | .plain type => return (← Codec.decode type json).map fun _ => ()
  | .keys points =>
    return if points.contains json then .ok ()
      else .error "a point is outside its actual computational endpoint inventory"
  | .list element =>
    let .ok items := json.getArr? | return .error "a computational list requires an array"
    for item in items do
      if let .error message ← validatePoint element item then return .error message
    return .ok ()
  | .graph domain codomain independentKeys =>
    let (actualKeys, graph) ← if let .ok ("finiteGraph", #[inventory, graph]) := envelope json then do
        let .ok points := inventory.getArr?
          | return .error "a finite callable inventory requires an array"
        let mut seen := #[]
        for point in points do
          if seen.contains point then return .error "a computational point inventory repeats a key"
          seen := seen.push point
          if let .error message ← validatePoint domain point then return .error message
        pure (some points, graph)
      else pure (independentKeys, json)
    let .ok pairs := graph.getArr? | return .error "a computational function field requires a graph"
    let mut keys := #[]
    for pair in pairs do
      let .ok #[input, output] := pair.getArr?
        | return .error "a computational graph entry requires input and output"
      if keys.contains input then return .error "the computational graph repeats a domain key"
      keys := keys.push input
      if let .error message ← validatePoint domain input then return .error message
      if let .error message ← validatePoint codomain output then return .error message
    let some actualKeys := actualKeys
      | return .error "the callable's point types require their released data representation"
    return validateGraphDomain actualKeys graph
  | .recordFields unlabelled fields =>
    let args ← if unlabelled && fields.size == 1 then pure #[json]
      else match json.getArr? with
        | .ok args => pure args
        | .error _ => return .error "computational constructor fields require an array"
    unless args.size == fields.size do
      return .error "the computational constructor omitted or added data fields"
    for (field, data) in fields.zip args do
      if let .error message ← validatePoint field data then return .error message
    return .ok ()
  | .alternatives constructors =>
    let .ok (tag, args) := envelope json
      | return .error "a computational value requires its public constructor and data fields"
    let some (_, schema) := constructors.find? (·.1 == tag)
      | return .error "the computational value has no such public constructor"
    return ← validatePoint schema (Json.arr args)


/-- Instantiate a public projection at independently supplied arguments. Resolve
its concrete dictionary before prerequisite outparameter dictionaries. Expected
missing instances return `none`; interpreter errors are not relabelled. -/
def projectionApplication (declaration : Name) (arity : Nat)
    (supplied : Array (Nat × Expr)) : TermElabM (Option Expr) := withoutModifyingState do
  let projection ← mkConstWithFreshMVarLevels declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType projection)
  unless parameters.size >= arity do return none
  for (index, argument) in supplied do
    let some parameter := parameters[index]? | return none
    unless ← isDefEq (← inferType parameter) (← inferType argument) <&&>
        isDefEq parameter argument do return none
  for parameter in (parameters.extract 0 arity).reverse do
    let parameter ← instantiateMVars parameter
    if parameter.isMVar then
      let type ← instantiateMVars (← inferType parameter)
      if (← isClass? type).isSome then
        let some dictionary := (← trySynthInstance type).toOption | return none
        unless ← isDefEq parameter dictionary do return none
  let mut arguments ← (parameters.extract 0 arity).mapM instantiateMVars
  -- Preserve supplied formal placeholders verbatim across the speculative
  -- dictionary resolution; no newly created metavariable escapes its state.
  for (index, argument) in supplied do arguments := arguments.set! index argument
  let application := mkAppN (← instantiateMVars projection) arguments
  let type ← instantiateMVars (← inferType application)
  if type.hasMVar || type.hasLevelMVar then return none
  return some application

/-- A public record projection is applicable only at its independently fixed
receiver type. A reply's constructor tag cannot make an incompatible receiver
into a record or turn malformed data into an interpreter exception. -/
def recordProjection (declaration : Name) (receiver : Expr) : TermElabM (Option Expr) := do
  let arity ← forallTelescopeReducing (← getConstInfo declaration).type
    fun fields _ => pure fields.size
  if arity == 0 then return none
  projectionApplication declaration arity #[(arity - 1, receiver)]

/-- The published concrete-category dictionary fixes a point type independently
of any returned descriptor or inventory. -/
def objectPointSchema (object : Expr) : TermElabM (Option PointSchema) := do
  let category ← withTransparency .all <| whnf (← inferType object)
  let some carrier ← projectionApplication ``CategoryTheory.ToType 7
      #[(0, category), (6, object)] | return none
  pointSchema carrier

/-- Obtain the callable interface without applying its authoritative function to
backend data. The complete original categorical endpoint types are retained. -/
def callableValue (formal expectedType : Expr) : TermElabM (Option Expr) := do
  if let .forallE .. := (← whnfR (← inferType formal)) then return some formal
  if let some function ← projectionApplication ``DFunLike.coe 5 #[(4, formal)] then
    return some function
  let type := expectedType.consumeMData
  unless type.isAppOf ``Quiver.Hom do return none
  let category ← withTransparency .all <| whnf type.getAppArgs[0]!
  let some concrete ← projectionApplication ``CategoryTheory.ConcreteCategory.hom 9
      #[(0, category), (8, formal)] | return none
  projectionApplication ``DFunLike.coe 5 #[(4, concrete)]

/-- A finite graph uses its actual endpoint representations, not the canonical
carrier of the independently retained formal construction. -/
def validateGraphAtKeys (formal expectedType : Expr) (data : Json)
    (domain : Array Json) (codomain : Option (Array Json)) :
    TermElabM (Except String Unit) := do
  let some function ← callableValue formal expectedType
    | return .error "the computational graph requires its released callable interface"
  let .forallE _ _ body _ ← whnfR (← inferType function)
    | return .error "the computational graph requires its released callable interface"
  if body.hasLooseBVars then
    return .error "dependent callable data requires an explicit released representation"
  let outputSchema ← if let some keys := codomain then pure (some (PointSchema.keys keys))
    else pointSchema body
  let some outputSchema := outputSchema
    | return .error "the callable's point types require their released data representation"
  let unwrapped := if let .ok ("valueData", #[actual]) := envelope data then actual else data
  if let .ok ("finiteGraph", #[inventory, _]) := envelope unwrapped then
    let .ok declared := inventory.getArr?
      | return .error "a finite callable inventory requires an array"
    unless declared.size == domain.size && domain.all declared.contains do
      return .error "the callable inventory differs from its actual computational domain"
  validatePoint (.graph (.keys domain) outputSchema (some domain)) unwrapped


/-- The selected objects used only while checking the types of symbolic data. A
computational callable is represented by a fresh placeholder at its declared type;
no returned function, object law, admission proof or equality is reconstructed. -/
abbrev InterfaceObjects := Array (Json × Expr)

mutual
/-- Validate the public declaration's ordered data parameters. Only the independent
formal value binds dependent field types; no answer is substituted into the declaration. -/
partial def declarationPorts (declaration : Name) (formal expected : Expr)
    (args : Array Json) : TermElabM (Except String Unit) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (fields, infos, conclusion) ← forallMetaTelescopeReducing (← inferType constant)
  unless ← isDefEq conclusion expected do
    return .error "the computational descriptor has a different declared result type"
  let mut ports := #[]
  for (field, info) in fields.zip infos do
    let type ← instantiateMVars (← inferType field)
    if info.isExplicit && !(← isProp type) then ports := ports.push field
  unless ports.size == args.size do
    return .error "the computational descriptor omitted or added declaration parameters"
  -- Recover parameter context from the fixed public declaration, never from
  -- computational fields or a replacement canonical construction.
  if let some application := formal.find? fun term =>
      term.getAppFn.constName? == some declaration && term.getAppNumArgs == fields.size then
    for (field, parameter) in fields.zip application.getAppArgs do
      unless ← isDefEq field parameter do
        return .error "the retained public declaration has inconsistent parameter types"
  else
    -- A published declaration may denote the retained public action without
    -- occurring syntactically (for example an Arrow constructor's parameters).
    -- Recover only a complete closed application from that fixed formal value.
    let recovered ← withoutModifyingState do
      unless ← withTransparency .all <| isDefEq (mkAppN constant fields) formal do
        return none
      let parameters ← fields.mapM instantiateMVars
      if parameters.any (fun parameter => parameter.hasMVar || parameter.hasLevelMVar) then
        return none
      return some parameters
    if let some parameters := recovered then
      for (field, parameter) in fields.zip parameters do
        unless ← isDefEq field parameter do
          return .error "the fixed public declaration has inconsistent parameter types"
  for (field, data) in ports.zip args do
    let field ← instantiateMVars field
    let type ← instantiateMVars (← inferType field)
    if type.hasMVar || type.hasLevelMVar then
      return .error "the computational descriptor lacks an independent dependent parameter context"
    match ← validatePort field type data with
    | .error message => return .error message
    | .ok () => pure ()
  return .ok ()

/-- Released named, classifier and constructor actions retain their actual
parameters and selected inner edge from the independent formal expression. -/
partial def validateAction (formal : Expr) (json : Json) : TermElabM (Except String Unit) := do
  let state ← registryState
  let .ok (tag, args) := envelope json
    | return .error "the selected action has no complete declaration descriptor"
  if let some entry := state.functors.find? (·.id.raw == tag) then
    let some selected ← fixedFunctorApplication entry.declaration formal
      | return .error "the action descriptor differs from the retained selected edge"
    return ← declarationPorts entry.declaration selected (← inferType selected) args
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    let some selected ← fixedFunctorApplication entry.declaration formal
      | return .error "the action descriptor differs from the retained complete construction"
    return ← declarationPorts entry.declaration selected (← inferType selected) args
  if tag == "classifierForget" then
    let #[id, parameters] := args
      | return .error "classifierForget requires its registered classifier and parameters"
    let .ok id := id.getStr? | return .error "the classifier id is not a string"
    let .ok parameters := parameters.getArr?
      | return .error "the classifier parameters are not an ordered array"
    let some entry := state.classifiers.find? (·.id.raw == id)
      | return .error "the classifier is not registered"
    let some selected ← retainedApplication entry.declaration formal
      | return .error "the action descriptor differs from the retained classifier"
    return ← declarationPorts entry.declaration selected (← inferType selected) parameters
  if tag == "constructorMap" then
    let #[id, inner] := args
      | return .error "constructorMap requires its registered constructor and inner edge"
    let .ok id := id.getStr? | return .error "the constructor id is not a string"
    let some entry := state.constructors.find? (·.id.raw == id)
      | return .error "the action constructor is not registered"
    let some action := entry.functorialAction
      | return .error "the registered constructor has no published functorial action"
    let some selected ← retainedApplication action formal
      | return .error "the action descriptor differs from the retained constructor action"
    let infos ← forallTelescopeReducing (← getConstInfo action).type fun fields _ =>
      fields.mapM (·.fvarId!.getBinderInfo)
    let explicit := (selected.getAppArgs.zip infos).filterMap fun (field, info) =>
      if info.isExplicit then some field else none
    let some source := explicit.back?
      | return .error "the published constructor action has no selected inner edge"
    return ← validateAction source inner
  return .error "the selected action descriptor is not a released registered edge"

/-- Validate a computational port without producing a semantic value or evidence.
Opaque owners are checked by the live-session consumer, outside this framing check. -/
partial def validatePort (formalField expectedType : Expr) (json : Json) :
    TermElabM (Except String Unit) := do
  if ← isProp expectedType then
    return .error "a proposition is not a computational data port"
  let state ← registryState
  if let .ok (tag, args) := envelope json then
    if tag == "category" || tag == "constructedCategory" || tag == "functor" then
      let .ok selected ← interfaceArgument #[] expectedType json
        | return .error "the selected dictionary does not have its full declared interface"
      let formal ← if tag == "functor" then Semantic.asFunctor formalField else pure formalField
      unless ← withTransparency .all <| isDefEq selected formal do
        return .error "the computational dictionary changed the independently fixed full context"
      return .ok ()
    if tag == "opaqueData" then
      let #[token] := args | return .error "opaqueData requires one token"
      let .ok token := token.getStr? | return .error "an opaque token must be a string"
      if token.isEmpty then return .error "an opaque token must be nonempty"
      return .ok ()
    if tag == "finiteData" then
      let #[descriptor, inventory] := args
        | return .error "finiteData requires its complete object descriptor and point inventory"
      if let .error message ← validatePort formalField expectedType descriptor then
        return .error message
      let .ok declaredKeys ← endpointKeys descriptor
        | return .error "the finite object has a malformed actual descriptor"
      let schema ← if let some keys := declaredKeys then pure (some (PointSchema.keys keys))
        else objectPointSchema formalField
      let some schema := schema
        | return .error "the finite object requires its released concrete point-data interface"
      let .ok points := inventory.getArr?
        | return .error "a computational point inventory requires an array"
      let mut seen := #[]
      for point in points do
        if seen.contains point then return .error "a computational point inventory repeats a key"
        seen := seen.push point
        if let .error message ← validatePoint schema point then return .error message
      if let some keys := declaredKeys then
        unless points.size == keys.size && keys.all points.contains do
          return .error "the point inventory differs from its declared computational representation"
      return .ok ()
    if tag == "valueData" then
      let #[data] := args | return .error "valueData requires one data field"
      return ← validatePort formalField expectedType data
    if tag == "constrainedPoint" then
      return ← validateCallableAt #[] expectedType json
    if tag == "morphismEndpoint" then
      let .ok endpoint := Backend.MorphismEndpoint.decode json
        | return .error "the endpoint projection requires its complete callable and selector"
      let other ← mkFreshExprMVar expectedType
      let source := if endpoint.source then formalField else other
      let target := if endpoint.source then other else formalField
      let mapType ← mkAppM ``Quiver.Hom #[source, target]
      return ← validatePort (← mkFreshExprMVar mapType) mapType endpoint.callable
    if tag == "objectPresentation" then
      let #[action, actual] := args
        | return .error "objectPresentation requires its complete action and actual data"
      unless (action.getObjValAs? String "ctor").toOption == some "functorAction" do
        return .error "objectPresentation requires its selected action descriptor"
      match ← validatePort formalField expectedType action with
      | .error message => return .error message
      | .ok () => return ← validatePort formalField expectedType actual
    if tag == "functorAction" then
      let #[edge, receiver] := args
        | return .error "functorAction requires an action descriptor and receiver"
      let .ok (functor, source) ← actionContext formalField edge
        | return .error "the action requires its independently retained formal receiver context"
      match ← validateAction functor edge with
      | .error message => return .error message
      | .ok () => return ← validatePort source (← inferType source) receiver
    if let some entry := state.objects.find? (·.id.raw == tag) then
      return ← declarationPorts entry.declaration formalField expectedType args
    if let some entry := state.morphisms.find? (·.id.raw == tag) then
      return ← declarationPorts entry.declaration formalField expectedType args
    if let some entry := state.inclusions.find? (·.id.raw == tag) then
      return ← declarationPorts entry.declaration formalField expectedType args
    if let some (declaration, _) := state.callable? tag then
      return ← declarationPorts declaration formalField expectedType args
    if tag == "objectField" then
      let #[id, field, parameters] := args
        | return .error "objectField requires its object id, public field and ordered parameters"
      let .ok id := id.getStr? | return .error "an object field requires its registered object id"
      let some entry := state.objects.find? (·.id.raw == id)
        | return .error "the object field names no registered object"
      let .ok field := field.getStr? | return .error "an object field name must be a string"
      let some declaration := ObjectPresentation.fieldDeclaration entry field
        | return .error "the object has no such released callable field"
      let .ok parameters := parameters.getArr?
        | return .error "object field parameters must be ordered data"
      if field == "presentation" || field == "inversePresentation" then
        let application ← match ← retainedApplication declaration formalField with
          | some application => pure application
          | none => instantiateFresh declaration
        let arrow ← ObjectPresentation.fieldValue field application
        unless ← withTransparency .all <| isDefEq (← inferType arrow) expectedType do
          return .error "the object presentation has incompatible complete endpoints"
        return ← declarationPorts declaration application (← inferType application) parameters
      return ← declarationPorts declaration formalField expectedType parameters
    if tag == "powerObjectMap" then
      let #[id, field, parameters] := args
        | return .error "powerObjectMap requires its power object id, public field and ordered parameters"
      let .ok id := id.getStr? | return .error "a power-object map requires its registered id"
      let some entry := state.powerObjects.find? (·.id.raw == id)
        | return .error "the map names no registered power object"
      let .ok field := field.getStr? | return .error "a power-object field name must be a string"
      let declaration := match field with
        | "member" => some entry.member
        | "terminal" => some entry.terminal
        | "transpose" => some entry.transpose
        | "image" => some entry.image
        | "truth" => some entry.truth
        | _ => none
      let some declaration := declaration
        | return .error "the power object has no such released callable field"
      let .ok parameters := parameters.getArr?
        | return .error "power-object field parameters must be ordered data"
      return ← declarationPorts declaration formalField expectedType parameters
    if tag == "typedMap" then
      let .ok typed := Backend.TypedMap.decode json
        | return .error "typedMap requires its complete source, target and callable"
      let type := expectedType.consumeMData
      unless type.isAppOf ``Quiver.Hom do
        return .error "typedMap requires its retained categorical endpoint types"
      let fields := type.getAppArgs
      let source := fields[fields.size - 2]!
      let target := fields.back!
      for (field, data) in #[(source, typed.source), (target, typed.target)] do
        if let .error message ← validatePort field (← inferType field) data then
          return .error message
      return ← validateEndpointPort formalField typed.source typed.target typed.callable
    if tag == "map" then
      let #[action, sourceData] := args
        | return .error "map requires its selected action and source map"
      let some selected ← retainedApplication ``CategoryTheory.Functor.map formalField
        | return .error "the mapped callable requires its retained formal action context"
      let infos ← forallTelescopeReducing (← getConstInfo ``CategoryTheory.Functor.map).type
        fun fields _ => fields.mapM (·.fvarId!.getBinderInfo)
      let explicit := (selected.getAppArgs.zip infos).filterMap fun (field, info) =>
        if info.isExplicit then some field else none
      let #[functor, source] := explicit
        | return .error "the public functor-map interface has changed"
      match ← validateAction functor action with
      | .error message => return .error message
      | .ok () => return ← validatePort source (← inferType source) sourceData
    if tag == "compose" then
      let #[firstData, secondData] := args
        | return .error "compose requires two ordered maps"
      let some selected ← retainedApplication ``CategoryTheory.CategoryStruct.comp formalField
        | return .error "composition requires its independently retained component contexts"
      let fields := selected.getAppArgs
      let first := fields[fields.size - 2]!
      let second := fields.back!
      for (field, data) in #[(first, firstData), (second, secondData)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      return .ok ()
    if tag == "identity" || tag == "zero" then
      let #[sourceData, targetData] := args
        | return .error "a nullary map requires its complete source and target descriptors"
      let type := expectedType.consumeMData
      unless type.isAppOf ``Quiver.Hom do
        return .error "the nullary map requires its retained categorical endpoint types"
      let fields := type.getAppArgs
      let source := fields[fields.size - 2]!
      let target := fields.back!
      for (field, data) in #[(source, sourceData), (target, targetData)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      if tag == "identity" && sourceData != targetData then
        return .error "the identity descriptor declares different computational endpoints"
      return .ok ()
    if tag == "objectProduct" then
      let #[leftData, rightData] := args
        | return .error "objectProduct requires two complete object descriptors"
      unless (← whnfR expectedType).isSort do
        return .error "the product descriptor requires its declared object category"
      -- A returned apex need not use the formal universal object's representation.
      -- The factors are data at the declared object type, not values extracted
      -- from that independently retained universal object.
      let left ← mkFreshExprMVar expectedType
      let right ← mkFreshExprMVar expectedType
      for (field, data) in #[(left, leftData), (right, rightData)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      return .ok ()
    if tag == "arrow" || tag == "subobject" then
      let #[source, target, definingMap] := args
        | return .error "an Arrow record requires source, target and defining map"
      -- Full subcategories retain the same three Arrow data fields. Their
      -- independently fixed predicate is not a proof requested from the reply.
      let refined ← recordProjection ``CategoryTheory.ObjectProperty.FullSubcategory.obj formalField
      if tag == "subobject" && refined.isNone then
        return .error "subobject data require an independently declared full subcategory of Arrow"
      let arrow := refined.getD formalField
      let some sourceField ← recordProjection ``CategoryTheory.Arrow.left arrow
        | return .error "Arrow data require their independently declared source projection"
      let some targetField ← recordProjection ``CategoryTheory.Arrow.right arrow
        | return .error "Arrow data require their independently declared target projection"
      let some mapField ← recordProjection ``CategoryTheory.Arrow.hom arrow
        | return .error "Arrow data require their independently declared defining-map projection"
      for (field, data) in #[(sourceField, source), (targetField, target)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      if let .error message ← validateEndpointPort mapField source target definingMap then
        return .error message
      if refined.isSome then
        if let some presentation := (json.getObjVal? "presentation").toOption then
          -- The existing optional presentation compares the source slot. It
          -- does not change the direction of an epi or any other defining map.
          let mapType ← mkAppM ``Quiver.Hom #[sourceField, sourceField]
          for key in #["hom", "inv"] do
            let .ok data := presentation.getObjVal? key
              | return .error "the supplied computational presentation omitted a comparison map"
            let placeholder ← mkFreshExprMVar mapType
            match ← validateEndpointPort placeholder source source data with
            | .error message => return .error message
            | .ok () => pure ()
      return .ok ()
  if ← plainType expectedType then
    return (← Codec.decode expectedType json).map fun _ => ()
  -- Literal representations are published upstream. Only their proof-free
  -- data type is decoded; the denotation is not applied to a backend value.
  for entry in state.literals do
    let literalType ← mkConstWithFreshMVarLevels entry.type
    unless ← plainType literalType do continue
    let denotation ← mkConstWithFreshMVarLevels entry.denotation
    let (_, _, result) ← forallMetaTelescopeReducing (← inferType denotation)
    let matchesType ← withoutModifyingState <| isDefEq result expectedType
    if matchesType then return (← Codec.decode literalType json).map fun _ => ()
  -- A callable's graph is checked as data. Its laws are neither inspected nor
  -- reconstructed. The function's type comes solely from its formal interface.
  let function := (← callableValue formalField expectedType).getD formalField
  let functionType ← whnfR (← inferType function)
  if let .forallE _ domain body _ := functionType then
    if body.hasLooseBVars then
      return .error "dependent callable data requires an explicit released representation"
    let domain ← whnfR domain
    let body ← whnfR body
    if !(← plainType domain) || !(← plainType body) ||
        (json.getObjValAs? String "ctor").toOption == some "finiteGraph" then
      let some schema ← pointSchema functionType
        | return .error "the callable's point types require their released data representation"
      return ← validatePoint schema json
    let .ok graph := json.getArr? | return .error "a finite callable requires a graph array"
    let mut keys : Array Json := #[]
    for pair in graph do
      let .ok #[input, output] := pair.getArr?
        | return .error "a computational graph entry requires input and output"
      -- Fin bounds belong to the actual computational endpoints, which may be
      -- a wrong returned apex. The formal apex's cardinal is not their bound.
      let inputType := if domain.isAppOf ``Fin then Lean.mkConst ``Nat else domain
      let outputType := if body.isAppOf ``Fin then Lean.mkConst ``Nat else body
      match ← Codec.decode inputType input, ← Codec.decode outputType output with
      | .ok _, .ok _ =>
        if keys.contains input then return .error "the computational graph repeats a domain key"
        keys := keys.push input
      | .error message, _ | _, .error message => return .error message
    return .ok ()
  -- Public records and quotients retain their complete data fields. Wholly
  -- inline scalar literals additionally satisfy the independently declared
  -- representation constraints (for example, a rational denominator is nonzero).
  -- The checked literal is discarded. Callable/type-valued fields and opaque
  -- components never enter this decoder or contribute mathematical evidence.
  if let some schema ← pointSchema expectedType then
    if let .error message ← validatePoint schema json then return .error message
    if schema.scalarLiteral then
      if let some literal := inlineLiteralData? json then
        return (← Codec.decode expectedType literal).map fun _ => ()
    return .ok ()
  return .error "the computational port has no supported released data representation"

/-- A finite map is complete at its actual supplied domain. Inventories are
computational data, never an enumeration of the requested formal construction. -/
partial def validateEndpointPort (formal : Expr) (source target data : Json) :
    TermElabM (Except String Unit) := do
  let unwrapped := if let .ok ("valueData", #[actual]) := envelope data then actual else data
  if (unwrapped.getObjValAs? String "ctor").toOption == some "typedMap" then
    let .ok typed := Backend.TypedMap.decode unwrapped
      | return .error "typedMap requires its complete source, target and callable"
    unless typed.source == source && typed.target == target do
      return .error "the callable's complete endpoint descriptors differ from its selected computational endpoints"
    return ← validateEndpointPort formal source target typed.callable
  let graph := if let .ok ("finiteGraph", #[_, actual]) := envelope unwrapped then actual else unwrapped
  unless graph.getArr?.isOk do return ← validatePort formal (← inferType formal) data
  let .ok (some domain) ← endpointKeys source
    | return .error "a finite callable requires its actual computational domain point inventory"
  if let .ok ("finiteGraph", #[inventory, _]) := envelope unwrapped then
    let .ok declared := inventory.getArr?
      | return .error "a finite callable inventory requires an array"
    unless declared.size == domain.size && domain.all declared.contains do
      return .error "the callable inventory differs from its actual computational domain"
  let .ok codomain ← endpointKeys target
    | return .error "a finite callable has malformed actual codomain data"
  validateGraphAtKeys formal (← inferType formal) data domain codomain


/-- Check a public declaration's complete explicit data slots without substituting
the reply into dependent formal parameters. Closed primitive slot types are
checked by the existing codec; other slots retain their public data grammar. -/
partial def validateDeclaredData (declaration : Name) (data : Array Json) :
    TermElabM (Except String Unit) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (fields, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let mut types := #[]
  for (field, info) in fields.zip infos do
    let type ← instantiateMVars (← inferType field)
    if info.isExplicit && !(← isProp type) then types := types.push type
  unless types.size == data.size do
    return .error "the public descriptor omitted or added declaration parameters"
  for (type, datum) in types.zip data do
    if !type.hasMVar && !type.hasLevelMVar && (← plainType type) then
      if let .error message ← Codec.decode type datum then return .error message
    else if let .error message ← validatePublicData datum then return .error message
  return .ok ()

/-- Released symbolic computational framing. This traversal produces no Lean
value or proof and does not treat a supplied symbolic expression as the original
formal answer. Its caller retains the independent complete interface. -/
partial def validatePublicData (data : Json) : TermElabM (Except String Unit) := do
  match data with
  | .num _ => return data.getInt?.map fun _ => ()
  | .str _ | .bool _ => return .ok ()
  | .arr values =>
      for value in values do
        if let .error message ← validatePublicData value then return .error message
      return .ok ()
  | .null => return .error "null is not a released mathematical data constructor"
  | .obj _ => pure ()
  let .ok (tag, args) := envelope data
    | return .error "symbolic computational data require a public constructor and ordered fields"
  let state ← registryState
  if tag == "morphismEndpoint" then
    let .ok endpoint := Backend.MorphismEndpoint.decode data
      | return .error "the endpoint projection requires its complete callable and selector"
    return ← validateCallableData endpoint.callable
  if let some entry := state.objects.find? (·.id.raw == tag) then
    return ← validateDeclaredData entry.declaration args
  if let some entry := state.morphisms.find? (·.id.raw == tag) then
    return ← validateDeclaredData entry.declaration args
  if let some entry := state.inclusions.find? (·.id.raw == tag) then
    return ← validateDeclaredData entry.declaration args
  if let some (declaration, _) := state.callable? tag then
    return ← validateDeclaredData declaration args
  if let some entry := state.functors.find? (·.id.raw == tag) then
    return ← validateDeclaredData entry.declaration args
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    return ← validateDeclaredData entry.declaration args
  if tag == "category" || tag == "constructedCategory" || tag == "functor" then
    let #[id, parameters] := args | return .error "a selected dictionary requires its id and ordered parameters"
    let .ok id := id.getStr? | return .error "a selected dictionary id must be a string"
    let .ok parameters := parameters.getArr? | return .error "dictionary parameters must be ordered"
    let declaration := if tag == "category" then
      (state.categories.find? (·.id.raw == id)).map (·.declaration)
    else if tag == "constructedCategory" then
      (state.constructors.find? (·.id.raw == id)).map (·.semantics)
    else (state.functors.find? (·.id.raw == id)).map (·.declaration)
    let some declaration := declaration | return .error "the selected dictionary is not registered"
    if tag == "constructedCategory" then
      let some constructor := state.constructor? ⟨id⟩ | unreachable!
      unless parameters.size == constructor.signature.size do
        return .error "the constructed category changed its declared argument count"
    return ← validateDeclaredData declaration parameters
  if tag == "cellComponent" then
    let .ok component := Backend.CellComponent.decode data
      | return .error "the cell component omitted its complete public context"
    let some entry := state.cells.find? (·.id.raw == component.cell)
      | return .error "the cell component is not registered"
    unless !component.inverse || entry.invertible do
      return .error "the selected cell has no accepted inverse"
    if let .error message ← validateDeclaredData entry.declaration component.parameters then
      return .error message
    return ← validatePublicData component.receiver
  if tag == "constructedCellComponent" then
    let #[constructors, component] := args
      | return .error "a constructed component requires its complete constructor path and cell"
    let .ok constructors := constructors.getArr?
      | return .error "the constructed comparison path must be ordered"
    let .ok selected := Backend.CellComponent.decode component
      | return .error "the constructed comparison omitted its complete selected cell"
    let address := "component:" ++ (Json.arr #[toJson selected.cell, Json.arr constructors]).compress
    unless (state.component? address).isSome do
      return .error "the constructed comparison has no accepted full action path"
    return ← validatePublicData component
  let mut diagramConstructors : Array Name := #[]
  for row in state.limits do
    if let some constructor ← Semantic.diagramConstructor row then
      if Codec.label constructor == tag && !diagramConstructors.contains constructor then
        diagramConstructors := diagramConstructors.push constructor
  unless diagramConstructors.isEmpty do
    for constructor in diagramConstructors do
      if (← validateDeclaredData constructor args).isOk then return .ok ()
    return .error "the diagram data do not frame any registered diagram constructor"
  if tag == "opaqueData" || tag == "valueData" then
    let .ok value := Backend.ComputationalValue.decode data
      | return .error "the computational value envelope is malformed"
    match value with
    | .opaque _ => return .ok ()
    | .inline value => return ← validatePublicData value
  if tag == "operationExpression" then
    let #[id, parameters, operands] := args
      | return .error "operationExpression requires its id, complete parameters and operands"
    let .ok id := id.getStr? | return .error "an operation id must be a string"
    let some entry := state.operations.find? (·.id.raw == id)
      | return .error "the expression names no registered operation"
    let .ok parameters := parameters.getArr?
      | return .error "operation parameters must be ordered data"
    let .ok operands := operands.getArr?
      | return .error "operation operands must be ordered data"
    unless operands.size == entry.arity do
      return .error "the operation expression has the wrong declared arity"
    if let .error message ← validateDeclaredData entry.declaration parameters then
      return .error message
    for operand in operands do
      if let .error message ← validatePublicData operand then return .error message
    return .ok ()
  if tag == "objectField" || tag == "powerObjectMap" then
    let #[id, field, parameters] := args
      | return .error "a public field requires its owner id, field and ordered parameters"
    let .ok id := id.getStr? | return .error "the public field owner id must be a string"
    let .ok field := field.getStr? | return .error "the public field name must be a string"
    let .ok parameters := parameters.getArr?
      | return .error "the public field parameters must be ordered data"
    let declaration := if tag == "objectField" then
      (state.objects.find? (·.id.raw == id)).bind fun entry =>
        ObjectPresentation.fieldDeclaration entry field
    else
      (state.powerObjects.find? (·.id.raw == id)).bind fun entry =>
        match field with
        | "member" => some entry.member | "terminal" => some entry.terminal
        | "transpose" => some entry.transpose | "image" => some entry.image
        | "truth" => some entry.truth | _ => none
    let some declaration := declaration
      | return .error "the registered owner has no such public callable field"
    return ← validateDeclaredData declaration parameters
  if tag == "presentation" then
    let #[id, parameters, inverse] := args
      | return .error "a presentation requires its id, ordered parameters and orientation"
    let .ok id := id.getStr? | return .error "a presentation id must be a string"
    let some entry := state.presentations.find? (·.id.raw == id)
      | return .error "the presentation is not registered"
    let .ok parameters := parameters.getArr?
      | return .error "presentation parameters must be ordered data"
    unless inverse.getBool?.isOk do return .error "presentation orientation must be Boolean"
    return ← validateDeclaredData entry.declaration parameters
  if tag == "classifierForget" then
    let #[id, parameters] := args
      | return .error "classifierForget requires its registered classifier and parameters"
    let .ok id := id.getStr? | return .error "a classifier id must be a string"
    let some entry := state.classifiers.find? (·.id.raw == id)
      | return .error "the classifier action is not registered"
    let .ok parameters := parameters.getArr?
      | return .error "classifier parameters must be ordered data"
    return ← validateDeclaredData entry.declaration parameters
  if tag == "constructorMap" then
    let #[id, inner] := args
      | return .error "constructorMap requires its registered constructor and inner action"
    let .ok id := id.getStr? | return .error "a constructor id must be a string"
    let some entry := state.constructors.find? (·.id.raw == id)
      | return .error "the constructor action is not registered"
    unless entry.functorialAction.isSome do
      return .error "the constructor has no released action on functors"
    return ← validatePublicData inner
  if tag == "operationPoint" then
    let #[id, parameters, comparison, domain, selected] := args
      | return .error "operationPoint requires its full operation, comparison, domain and selected target"
    let .ok id := id.getStr? | return .error "an operation id must be a string"
    let some entry := state.operations.find? (·.id.raw == id)
      | return .error "the terminal operation is not registered"
    unless entry.arity == 0 do return .error "the operation is not nullary"
    let .ok parameters := parameters.getArr?
      | return .error "operation parameters must be ordered data"
    if let .error message ← validateDeclaredData entry.declaration parameters then
      return .error message
    for datum in #[comparison, domain, selected] do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "extent" then
    let #[id, ambient, subset] := args
      | return .error "extent requires its power object, ambient object and subset data"
    let .ok id := id.getStr? | return .error "a power-object id must be a string"
    unless state.powerObjects.any (·.id.raw == id) do
      return .error "the extent names no registered power object"
    for datum in #[ambient, subset] do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if #["limitApex", "limitLeg", "constructionApex", "constructionLeg"].contains tag then
    let count := if tag == "limitApex" then 2 else if tag == "constructionLeg" then 4 else 3
    unless args.size == count do
      return .error "the construction projection omitted part of its complete receiver or index"
    let .ok id := args[0]!.getStr? | return .error "a construction id must be a string"
    unless state.limits.any (·.id.raw == id) do
      return .error "the construction is not registered"
    for datum in args.extract 1 args.size do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "cone" || tag == "cocone" then
    if args.isEmpty then return .error "a complete construction requires its actual apex"
    for datum in args do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "createdCone" || tag == "liftStep" then
    unless args.size == (if tag == "createdCone" then 3 else 5) do
      return .error "the prescribed lift omitted its complete construction context"
    let .ok id := args[0]!.getStr? | return .error "a lift id must be a string"
    unless state.lifts.any (·.id.raw == id) do return .error "the selected lift is not registered"
    if tag == "liftStep" then
      let .ok fields := args[4]!.getArr?
        | return .error "a completed lift step requires all four ordered component outputs"
      unless fields.size == 4 do
        return .error "a completed lift step requires all four ordered component outputs"
    for datum in args.extract 1 args.size do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "liftedSubobject" then
    let #[base, source, ids, steps] := args
      | return .error "a completed lifted subobject requires its base, source, route and complete steps"
    let .ok ids := ids.getArr? | return .error "a prescribed lift route must be ordered data"
    let .ok steps := steps.getArr? | return .error "completed lift steps must be ordered data"
    unless ids.size == steps.size do return .error "the completed lift route omitted component outputs"
    for (id, step) in ids.zip steps do
      let .ok id := id.getStr? | return .error "a lift id must be a string"
      let .ok ("liftStep", fields) := envelope step
        | return .error "the completed lift route contains no complete step"
      unless fields[0]?.bind (fun field => field.getStr?.toOption) == some id do
        return .error "a completed lift step differs from its selected route id"
      if let .error message ← validatePublicData step then return .error message
    for datum in #[base, source] do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "admittedPoint" then
    let .ok point := Backend.AdmittedPoint.decode data
      | return .error "the admitted point has incomplete public context"
    let some entry := state.objects.find? (·.id.raw == point.object)
      | return .error "the admission names no registered object"
    unless entry.admission.isSome do return .error "the registered object has no admission interface"
    if let .error message ← validateDeclaredData entry.declaration point.parameters then
      return .error message
    for datum in #[point.domain, point.source, point.target, point.argument] do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "constrainedPoint" then
    let .ok point := Backend.ConstrainedPoint.decode data
      | return .error "the constrained point has incomplete public context"
    let some (.ctorInfo _) := (← getEnv).find? point.constructor.toName
      | return .error "the constrained point names no actual constructor"
    for datum in #[point.domain, point.source, point.target, point.argument] do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "numeral" then
    let #[number] := args | return .error "a numeral requires exactly one natural number"
    return number.getNat?.map fun _ => ()
  if tag == "generator" then
    match args with
    | #[] => return .ok ()
    | #[index] => return index.getNat?.map fun _ => ()
    | #[id, parameters] =>
      let .ok id := id.getStr? | return .error "a generator arrow requires its object id"
      let some entry := state.objects.find? (·.id.raw == id)
        | return .error "the generator names no registered object"
      let some declaration := entry.generator | return .error "the object has no registered generator"
      let .ok parameters := parameters.getArr?
        | return .error "generator declaration parameters must be ordered data"
      return ← validateDeclaredData declaration parameters
    | _ => return .error "the generator has the wrong declared framing"
  if tag == "typedMap" then
    let .ok typed := Backend.TypedMap.decode data
      | return .error "typedMap requires its complete source, target and callable"
    for datum in #[typed.source, typed.target, typed.callable] do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  let arity := match tag with
    | "true" | "false" | "none" => some 0
    | "point" | "neg" | "some" | "arrowHom" | "subobjectApex" | "subobjectInclusion" |
        "coreObject" => some 1
    | "add" | "mul" | "element" | "compose" | "mediator" | "map" |
        "identity" | "zero" | "functorAction" | "objectPresentation" |
        "objectProduct" | "finiteData" | "finiteGraph" => some 2
    | "pointView" | "arrow" | "subobject" => some 3
    | "coreIso" => some 4
    | _ => none
  let some arity := arity
    | return .error "the symbolic data use no supported released constructor"
  unless args.size == arity do return .error "the public symbolic constructor has the wrong arity"
  for datum in args do
    if let .error message ← validatePublicData datum then return .error message
  return .ok ()

/-- An element envelope contains the published expression grammar, not arbitrary
public parameter data. In particular a raw string, scalar or object descriptor
cannot masquerade as an element expression. This check frames syntax only; it
neither evaluates the expression nor proves it equal to the requested point. -/
partial def validateElementExpression (expression : Json) :
    TermElabM (Except String Unit) := do
  let .ok (tag, args) := envelope expression
    | return .error "an element expression requires a published expression constructor"
  match tag, args with
  | "numeral", #[value] => return value.getNat?.map fun _ => ()
  | "generator", #[] => return .ok ()
  | "generator", #[index] => return index.getNat?.map fun _ => ()
  | "add", #[left, right] | "mul", #[left, right] =>
      if let .error message ← validateElementExpression left then return .error message
      validateElementExpression right
  | "neg", #[value] => validateElementExpression value
  | "operationExpression", #[_, _, operands] =>
      if let .error message ← validatePublicData expression then return .error message
      let .ok operands := operands.getArr?
        | return .error "operation operands must be ordered element expressions"
      for operand in operands do
        if let .error message ← validateElementExpression operand then return .error message
      return .ok ()
  | "point", #[arrow] => validateCallableData arrow
  | _, _ => return .error "the element expression has an unknown constructor or incorrect arity"

/-- Framing for an actual callable, as distinct from an object descriptor or a
scalar parameter. Composition recursively preserves that distinction. This is
computational syntax validation, not reconstruction of a law-bearing arrow. -/
partial def validateCallableData (data : Json) : TermElabM (Except String Unit) := do
  if let .arr entries := data then
    for entry in entries do
      let .ok #[_, _] := entry.getArr?
        | return .error "a finite callable graph requires ordered input/output pairs"
    return ← validatePublicData data
  let .ok (tag, args) := envelope data
    | return .error "a point requires its callable or finite-graph representation"
  let state ← registryState
  if state.morphisms.any (·.id.raw == tag) || state.inclusions.any (·.id.raw == tag) ||
      (state.callable? tag).isSome then
    return ← validatePublicData data
  match tag, args with
  | "valueData", #[value] => validateCallableData value
  | "element", #[descriptor, expression] =>
      let .ok _ := envelope descriptor
        | return .error "an element point requires its complete selected object descriptor"
      if let .error message ← validatePublicData descriptor then return .error message
      validateElementExpression expression
  | "compose", #[first, second] | "mediator", #[first, second] =>
      if let .error message ← validateCallableData first then return .error message
      validateCallableData second
  | "map", #[action, arrow] =>
      let .ok (actionTag, _) := envelope action
        | return .error "a mapped callable requires its selected action descriptor"
      unless state.functors.any (·.id.raw == actionTag) ||
          state.constructions.any (·.id.raw == actionTag) ||
          #["classifierForget", "constructorMap"].contains actionTag do
        return .error "a mapped callable requires a registered functor or structural edge"
      if let .error message ← validatePublicData action then return .error message
      validateCallableData arrow
  | "typedMap", #[source, target, arrow] | "arrow", #[source, target, arrow] =>
      for endpoint in #[source, target] do
        if let .error message ← validatePublicData endpoint then return .error message
      validateCallableData arrow
  | "finiteGraph", #[inventory, graph] =>
      let .ok _ := inventory.getArr?
        | return .error "a finite callable inventory requires its complete point array"
      if let .error message ← validatePublicData inventory then return .error message
      validateCallableData graph
  | "generator", #[_, _] => validatePublicData data
  | "operationPoint", #[_, _, comparison, _, _] =>
      if let .error message ← validatePublicData data then return .error message
      validateCallableData comparison
  | _, _ =>
      if #["opaqueData", "objectField", "powerObjectMap", "presentation", "pointView",
          "arrowHom", "limitLeg", "constructionLeg", "subobjectInclusion", "identity",
          "zero", "admittedPoint", "constrainedPoint", "cellComponent",
          "constructedCellComponent", "coreIso"].contains tag then
        validatePublicData data
      else return .error "an object or scalar descriptor cannot serve as a callable"




/-- Instantiate public signature parameters for type checking. Named descriptors
refer to accepted declarations; arbitrary data occupy typed placeholders. The
result is discarded by the response validator and is never a computed answer. -/
partial def interfaceDeclaration (objects : InterfaceObjects)
    (declaration : Name) (expected : Expr) (data : Array Json) :
    TermElabM (Except String Expr) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (fields, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
  -- A carrier does not determine a selected ring or other structured parameter.
  -- Supply the declared arguments before requiring the resulting Hom type.
  if ← withoutModifyingState (withTransparency .all <| isDefEq result expected) then
    discard <| withTransparency .all <| isDefEq result expected
  let mut position := 0
  for (field, info) in fields.zip infos do
    let type ← instantiateMVars (← inferType field)
    if !info.isExplicit || (← isProp type) then continue
    let some datum := data[position]?
      | return .error "the symbolic declaration omitted a parameter"
    let .ok argument ← interfaceArgument objects type datum
      | return .error "a symbolic parameter does not have its declared interface"
    unless ← withTransparency .all <| isDefEq field argument do
      return .error "a symbolic parameter changes its selected dependent endpoint"
    position := position + 1
  unless position == data.size do return .error "the symbolic declaration added a parameter"
  for field in fields do
    let field ← instantiateMVars field
    if field.isMVar then
      let type ← instantiateMVars (← inferType field)
      if (← isClass? type).isSome then
        if let some dictionary := (← trySynthInstance type).toOption then
          unless ← isDefEq field dictionary do
            return .error "the symbolic declaration has incompatible selected structure"
  unless ← withTransparency .all <| isDefEq result expected do
    return .error "the symbolic declaration has incompatible complete endpoints"
  return .ok (← instantiateMVars (mkAppN constant fields))

partial def interfaceObject (objects : InterfaceObjects) (data : Json) :
    TermElabM (Except String Expr) := do
  if let some (_, fixed) := objects.find? (·.1 == data) then return .ok fixed
  let .ok (tag, args) := envelope data
    | return .error "a symbolic endpoint requires its complete object descriptor"
  let state ← registryState
  if let some entry := state.objects.find? (·.id.raw == tag) then
    let expected ← inferType (← instantiateFresh entry.declaration)
    return ← interfaceDeclaration objects entry.declaration expected args
  if tag == "objectProduct" then
    let #[left, right] := args | return .error "a product endpoint requires both factors"
    let .ok left ← interfaceObject objects left | return .error "the first product factor is incomplete"
    let .ok right ← interfaceObject objects right | return .error "the second product factor is incomplete"
    return .ok (← mkAppM ``Prod #[left, right])
  if tag == "coreObject" then
    let #[source] := args | return .error "a core object requires its complete original object"
    let .ok source ← interfaceObject objects source
      | return .error "the core object's selected source is incomplete"
    return .ok (← mkAppM ``CategoryTheory.Core.mk #[source])
  if tag == "finiteData" || tag == "objectPresentation" then
    let #[descriptor, _] := args | return .error "the endpoint wrapper is incomplete"
    return ← interfaceObject objects descriptor
  if tag == "functorAction" then
    let #[action, source] := args | return .error "an object action requires its selected source"
    let .ok action ← interfaceAction objects action | return .error "the endpoint action is incomplete"
    let .ok source ← interfaceObject objects source | return .error "the endpoint source is incomplete"
    return .ok (← Semantic.objOf action source)
  return .error "the symbolic endpoint requires its independently selected object context"

partial def interfaceAction (objects : InterfaceObjects) (data : Json) :
    TermElabM (Except String Expr) := do
  let .ok (tag, args) := envelope data | return .error "the action requires a public descriptor"
  let state ← registryState
  if let some entry := state.functors.find? (·.id.raw == tag) then
    let expected ← inferType (← instantiateFresh entry.declaration)
    let .ok action ← interfaceDeclaration objects entry.declaration expected args
      | return .error "the action parameters have incompatible declared types"
    return .ok (← Semantic.asFunctor action)
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    let expected ← inferType (← instantiateFresh entry.declaration)
    let .ok action ← interfaceDeclaration objects entry.declaration expected args
      | return .error "the construction parameters have incompatible complete declared types"
    return .ok (← Semantic.asFunctor action)
  if tag == "classifierForget" then
    let #[id, parameters] := args | return .error "the classifier action is incomplete"
    let .ok id := id.getStr? | return .error "the classifier id must be a string"
    let .ok parameters := parameters.getArr? | return .error "classifier parameters must be ordered"
    let some row := state.classifiers.find? (·.id.raw == id)
      | return .error "the classifier action is not registered"
    let .ok classifier ← interfaceDeclaration objects row.declaration
        (← inferType (← instantiateFresh row.declaration)) parameters
      | return .error "the classifier parameters have incompatible declared types"
    let mut classifier := classifier
    let type ← whnfR (← inferType classifier)
    if type.isAppOf ``LeanCategories.PropertyClassifier then
      classifier ← mkAppM ``LeanCategories.PropertyClassifier.toClassifier #[classifier]
    else if type.isAppOf ``LeanCategories.StructureClassifier then
      classifier ← mkAppM ``LeanCategories.StructureClassifier.toClassifier #[classifier]
    return .ok (← mkAppM ``CategoryTheory.Cat.Hom.toFunctor
      #[← mkAppM ``LeanCategories.Classifier.forget #[classifier]])
  if tag == "constructorMap" then
    let #[id, inner] := args | return .error "the constructor action is incomplete"
    let .ok id := id.getStr? | return .error "the constructor id must be a string"
    let some action := (state.constructors.find? (·.id.raw == id)).bind (·.functorialAction)
      | return .error "the constructor has no registered action"
    let .ok inner ← interfaceAction objects inner | return .error "the inner action is incomplete"
    return .ok (← Semantic.applyConstructorFunctor action inner)
  return .error "the symbolic action requires its independently selected context"

partial def interfaceArgument (objects : InterfaceObjects) (expected : Expr) (data : Json) :
    TermElabM (Except String Expr) := do
  let expected ← instantiateMVars expected
  if ← isProp expected then return .error "a proof is not computational data"
  if let .ok (tag, #[id, parameters]) := envelope data then
    if tag == "category" || tag == "constructedCategory" || tag == "functor" then
      let .ok id := id.getStr? | return .error "a selected dictionary id must be a string"
      let .ok parameters := parameters.getArr? | return .error "dictionary parameters must be ordered"
      let state ← registryState
      let declaration := if tag == "category" then
        (state.categories.find? (·.id.raw == id)).map (·.declaration)
      else if tag == "constructedCategory" then
        (state.constructors.find? (·.id.raw == id)).map (·.semantics)
      else (state.functors.find? (·.id.raw == id)).map (·.declaration)
      let some declaration := declaration | return .error "the selected dictionary is not registered"
      if tag == "constructedCategory" then
        let some constructor := state.constructor? ⟨id⟩ | unreachable!
        unless parameters.size == constructor.signature.size do
          return .error "the constructed category changed its complete argument count"
      let resultType ← inferType (← instantiateFresh declaration)
      let .ok value ← interfaceDeclaration objects declaration resultType parameters
        | return .error "the selected dictionary has incompatible complete parameters"
      let value ← if tag == "functor" then Semantic.asFunctor value else pure value
      unless ← withTransparency .all <| isDefEq (← inferType value) expected do
        return .error "the selected dictionary has a different complete declared type"
      return .ok value
  if let some (_, fixed) := objects.find? (·.1 == data) then
    unless ← isDefEq (← inferType fixed) expected do
      return .error "the selected descriptor has a different declared type"
    return .ok fixed
  if let some _ := Language.homEnds? expected then
    let .ok () ← validateCallableAt objects expected data
      | return .error "the callable parameter has incompatible endpoints"
    return .ok (← mkFreshExprMVar expected)
  if let .ok (tag, _) := envelope data then
    let state ← registryState
    if state.objects.any (·.id.raw == tag) ||
        #["objectProduct", "finiteData", "functorAction", "objectPresentation", "coreObject"].contains tag then
      let .ok object ← interfaceObject objects data
        | return .error "the object parameter has no complete declared interface"
      unless ← withTransparency .all <| isDefEq (← inferType object) expected do
        return .error "the object parameter has a different selected category"
      return .ok object
  if ← plainType expected then return ← Codec.decode expected data
  let placeholder ← mkFreshExprMVar expected
  let .ok () ← validatePort placeholder expected data
    | return .error "the symbolic parameter has no supported declared data representation"
  return .ok placeholder

/-- Check the complete Hom type recursively, without constructing a runtime map.
Compositions infer their middle object from declared constituents or typedMap;
two untyped opaque maps cannot invent that missing interface. -/
partial def validateCallableAt (objects : InterfaceObjects) (expected : Expr) (data : Json) :
    TermElabM (Except String Unit) := do
  let expected ← instantiateMVars expected
  let some (source, target) := Language.homEnds? expected
    | return .error "a symbolic point requires its independently fixed Hom type"
  let placeholder ← mkFreshExprMVar expected
  let state ← registryState
  if let .ok (tag, args) := envelope data then
    let declaration := (state.callable? tag).map Prod.fst <|>
      (state.inclusions.find? (·.id.raw == tag)).map (·.declaration)
    if let some declaration := declaration then
      return (← interfaceDeclaration objects declaration expected args).map fun _ => ()
    match tag, args with
    | "valueData", #[value] => return ← validateCallableAt objects expected value
    | "opaqueData", _ => return (Backend.ComputationalValue.decode data).map fun _ => ()
    | "coreIso", #[sourceData, targetData, forward, backward] =>
      let sourceType ← whnfR (← inferType source)
      let targetType ← whnfR (← inferType target)
      unless sourceType.isAppOf ``CategoryTheory.Core && targetType.isAppOf ``CategoryTheory.Core do
        return .error "a core comparison requires the exact selected core endpoints"
      let source ← mkAppM ``CategoryTheory.Core.of #[source]
      let target ← mkAppM ``CategoryTheory.Core.of #[target]
      for (fixed, descriptor) in #[(source, sourceData), (target, targetData)] do
        let .ok actual ← interfaceArgument objects (← inferType fixed) descriptor
          | return .error "the core comparison endpoint is incomplete"
        unless ← withTransparency .all <| isDefEq fixed actual do
          return .error "the core comparison changes its complete selected endpoint"
      if let .error message ← validateCallableAt objects
          (← mkAppM ``Quiver.Hom #[source, target]) forward then return .error message
      return ← validateCallableAt objects (← mkAppM ``Quiver.Hom #[target, source]) backward
    | "cellComponent", _ | "constructedCellComponent", _ =>
      if let .error message ← validatePublicData data then return .error message
      let (component, constructors) ← if tag == "cellComponent" then
        pure (data, (#[] : Array ConstructorId))
      else do
        let #[path, base] := args | return .error "the constructed component is incomplete"
        let .ok path := path.getArr? | return .error "the constructed component path is incomplete"
        let .ok path := path.mapM fun value => value.getStr?.map ConstructorId.mk
          | return .error "the constructed component has an invalid constructor id"
        pure (base, path)
      let .ok component := Backend.CellComponent.decode component
        | return .error "the natural component has incomplete data"
      let some entry := state.cells.find? (·.id.raw == component.cell)
        | return .error "the natural component is not registered"
      let declaredType ← inferType (← instantiateFresh entry.declaration)
      let .ok value ← interfaceDeclaration objects entry.declaration declaredType component.parameters
        | return .error "the component parameters have different complete declared types"
      let receiver ← mkFreshExprMVar (← mkFreshTypeMVar)
      let action ← CellAction.assemble entry { value, arguments := value.getAppArgs, explicit := #[] }
        constructors component.inverse receiver
      let .ok actual ← interfaceArgument objects (← inferType receiver) component.receiver
        | return .error "the component receiver has an incompatible full interface"
      unless ← withTransparency .all <| isDefEq actual receiver do
        return .error "the component changed its selected receiver"
      unless ← withTransparency .all <| isDefEq
          (← inferType (← CellAction.component action receiver)) expected do
        return .error "the component changed a complete declared endpoint"
      return .ok ()
    | "typedMap", #[sourceData, targetData, callable] =>
      for (fixed, descriptor) in #[(source, sourceData), (target, targetData)] do
        let .ok actual ← interfaceArgument objects (← inferType fixed) descriptor
          | return .error "a typed callable endpoint has no complete interface"
        unless ← withTransparency .all <| isDefEq fixed actual do
          return .error "the typed callable changes a complete endpoint"
      return ← validateCallableAt objects expected callable
    | "identity", #[sourceData, targetData] | "zero", #[sourceData, targetData] =>
      for (fixed, descriptor) in #[(source, sourceData), (target, targetData)] do
        let .ok actual ← interfaceArgument objects (← inferType fixed) descriptor
          | return .error "the nullary callable omitted a complete endpoint"
        unless ← withTransparency .all <| isDefEq fixed actual do
          return .error "the nullary callable changes a complete endpoint"
      if tag == "identity" then
        unless ← withTransparency .all <| isDefEq source target do
          return .error "identity requires the same complete endpoint"
      else
        let zeroType ← mkAppM ``CategoryTheory.Limits.HasZeroMorphisms #[expected.getAppArgs[0]!]
        unless (← trySynthInstance zeroType).toOption.isSome do
          return .error "zero requires the selected category's zero-morphism structure"
      return .ok ()
    | "presentation", #[id, parameters, inverse] =>
      let .ok id := id.getStr? | return .error "the presentation id must be a string"
      let .ok parameters := parameters.getArr? | return .error "presentation parameters must be ordered"
      let .ok inverse := inverse.getBool? | return .error "presentation orientation must be Boolean"
      let some row := state.presentations.find? (·.id.raw == id)
        | return .error "the presentation is not registered"
      let .ok comparison ← interfaceDeclaration objects row.declaration
          (← inferType (← instantiateFresh row.declaration)) parameters
        | return .error "the presentation parameters have incompatible declared types"
      let arrow ← Semantic.presentationArrow row comparison inverse
      unless ← withTransparency .all <| isDefEq (← inferType arrow) expected do
        return .error "the presentation has incompatible complete endpoints"
      return .ok ()
    | "generator", #[id, parameters] =>
      let .ok id := id.getStr? | return .error "the generator owner must be a string"
      let .ok parameters := parameters.getArr? | return .error "generator parameters must be ordered"
      let some declaration := (state.objects.find? (·.id.raw == id)).bind (·.generator)
        | return .error "the object has no registered generator"
      return (← interfaceDeclaration objects declaration expected parameters).map fun _ => ()
    | "constrainedPoint", _ =>
      let .ok point := Backend.ConstrainedPoint.decode data
        | return .error "the constrained point omitted its complete interface"
      if let .error message ← validatePublicData data then return .error message
      let .ok domain ← interfaceObject objects point.domain
        | return .error "the constrained point domain is incomplete"
      let .ok original ← interfaceObject objects point.source
        | return .error "the constrained point data-field type is incomplete"
      let .ok selected ← interfaceObject objects point.target
        | return .error "the constrained point selected target is incomplete"
      unless ← withTransparency .all <| isDefEq source domain <&&> isDefEq target selected do
        return .error "the constrained point changes a complete endpoint"
      let some schema ← ConstrainedPoint.schema? target
        | return .error "the fixed target has no single-data-field constrained record interface"
      unless schema.constructor.toString == point.constructor &&
          (← withTransparency .all <| isDefEq schema.dataType original) do
        return .error "the constrained point changes its actual constructor or data-field type"
      let checked ← withoutModifyingState <|
        validateCallableAt objects (← mkAppM ``Quiver.Hom #[domain, original]) point.argument
      if checked.isOk then return checked
      unless ← withTransparency .all <| isDefEq domain (← Language.globalPointSource.run {}) do
        return checked
      return ← validatePort (← mkFreshExprMVar original) original point.argument
    | "admittedPoint", _ =>
      let .ok admitted := Backend.AdmittedPoint.decode data
        | return .error "the admitted point omitted its complete interface"
      if let .error message ← validatePublicData data then return .error message
      let .ok domain ← interfaceObject objects admitted.domain | return .error "the admitted domain is incomplete"
      let .ok original ← interfaceObject objects admitted.source | return .error "the original endpoint is incomplete"
      let .ok selected ← interfaceObject objects admitted.target | return .error "the admitted endpoint is incomplete"
      unless ← withTransparency .all <| isDefEq source domain <&&> isDefEq target selected do
        return .error "the admitted point changes a complete endpoint"
      let checked ← withoutModifyingState <|
        validateCallableAt objects (← mkAppM ``Quiver.Hom #[domain, original]) admitted.argument
      if checked.isOk then return checked
      unless ← withTransparency .all <| isDefEq domain (← Language.globalPointSource.run {}) do
        return checked
      return ← validatePort (← mkFreshExprMVar original) original admitted.argument
    | "pointView", #[selectedData, original, domainData] =>
      let .ok domain ← interfaceObject objects domainData | return .error "the point view domain is incomplete"
      let .ok selected ← interfaceObject objects selectedData | return .error "the selected point view is incomplete"
      let .ok carrier ← interfaceCarrier selected selectedData | return .error "the point view has no declared carrier"
      unless ← withTransparency .all <| isDefEq source domain <&&> isDefEq target carrier do
        return .error "the point view changes a complete endpoint"
      return ← validateCallableAt objects expected original
    | "operationPoint", #[id, parameters, comparison, domainData, selectedData] =>
      let .ok id := id.getStr? | return .error "the nullary operation id must be a string"
      let .ok parameters := parameters.getArr? | return .error "nullary parameters must be ordered"
      let some row := state.operations.find? (·.id.raw == id)
        | return .error "the nullary operation is not registered"
      unless row.arity == 0 do return .error "the operation is not nullary"
      let .ok domain ← interfaceObject objects domainData | return .error "the nullary point domain is incomplete"
      let .ok selected ← interfaceObject objects selectedData | return .error "the nullary selection is incomplete"
      let .ok carrier ← interfaceCarrier selected selectedData | return .error "the nullary selection has no carrier"
      unless ← withTransparency .all <| isDefEq source domain <&&> isDefEq target carrier do
        return .error "the nullary point changes a complete endpoint"
      let operationSource ← mkFreshExprMVar (← inferType target)
      let .ok _ ← interfaceDeclaration objects row.declaration
          (← mkAppM ``Quiver.Hom #[operationSource, target]) parameters
        | return .error "the nullary operation changes its selected result interface"
      return ← validateCallableAt objects (← mkAppM ``Quiver.Hom #[source, operationSource]) comparison
    | "compose", #[first, second] =>
      let middle ← mkFreshExprMVar (← inferType source)
      if let .error message ← validateCallableAt objects (← mkAppM ``Quiver.Hom #[source, middle]) first then
        return .error message
      if let .error message ← validateCallableAt objects (← mkAppM ``Quiver.Hom #[middle, target]) second then
        return .error message
      if (← instantiateMVars middle).hasMVar then
        return .error "the symbolic composition omitted its intermediate object interface"
      return .ok ()
    | "mediator", #[first, second] =>
      let left ← mkFreshExprMVar (← inferType target)
      let right ← mkFreshExprMVar (← inferType target)
      unless ← withTransparency .all <| isDefEq target (← mkAppM ``Prod #[left, right]) do
        return .error "the mediator does not land in the declared product"
      if let .error message ← validateCallableAt objects (← mkAppM ``Quiver.Hom #[source, left]) first then
        return .error message
      return ← validateCallableAt objects (← mkAppM ``Quiver.Hom #[source, right]) second
    | "element", #[descriptor, expression] =>
      let .ok selected ← interfaceObject objects descriptor
        | return .error "the nested point lost its selected object"
      let .ok carrier ← interfaceCarrier selected descriptor
        | return .error "the nested point has no independently declared carrier"
      unless ← withTransparency .all <| isDefEq source (← Language.globalPointSource.run {}) <&&>
          isDefEq target carrier do
        return .error "the nested point has incompatible complete endpoints"
      return ← validateElementExpressionAt (objects.push (descriptor, selected)) selected carrier expression
    | "map", #[action, arrow] =>
      let .ok action ← interfaceAction objects action | return .error "the mapped callable has no selected action"
      let actionType ← whnfR (← inferType action)
      unless actionType.isAppOf ``CategoryTheory.Functor do return .error "the action is not a functor"
      let category := actionType.getAppArgs[0]!
      let left ← mkFreshExprMVar category
      let right ← mkFreshExprMVar category
      let mapType ← mkAppM ``Quiver.Hom #[left, right]
      let callable ← mkFreshExprMVar mapType
      unless ← withTransparency .all <| isDefEq (← inferType (← Semantic.mapOf action callable)) expected do
        return .error "the mapped callable has incompatible result endpoints"
      return ← validateCallableAt objects mapType arrow
    | "objectField", #[id, field, parameters] | "powerObjectMap", #[id, field, parameters] =>
      let .ok id := id.getStr? | return .error "the callable field owner must be a string"
      let .ok field := field.getStr? | return .error "the callable field must be a string"
      let .ok parameters := parameters.getArr? | return .error "the callable field parameters are incomplete"
      let declaration := if tag == "objectField" then
        (state.objects.find? (·.id.raw == id)).bind fun row =>
          ObjectPresentation.fieldDeclaration row field
      else (state.powerObjects.find? (·.id.raw == id)).bind fun row =>
        match field with
        | "member" => some row.member | "terminal" => some row.terminal
        | "transpose" => some row.transpose | "image" => some row.image
        | "truth" => some row.truth | _ => none
      let some declaration := declaration | return .error "the owner has no such callable field"
      if tag == "objectField" && (field == "presentation" || field == "inversePresentation") then
        let .ok comparison ← interfaceDeclaration objects declaration
            (← inferType (← instantiateFresh declaration)) parameters
          | return .error "the object presentation parameters have incompatible declared types"
        let arrow ← ObjectPresentation.fieldValue field comparison
        unless ← withTransparency .all <| isDefEq (← inferType arrow) expected do
          return .error "the object presentation has incompatible complete endpoints"
        return .ok ()
      return (← interfaceDeclaration objects declaration expected parameters).map fun _ => ()
    | _, _ =>
      -- Construction packets are checked by their complete-result consumers.
      -- Their stored computational apex must not be substituted for the fixed
      -- formal projection's type here (a wrong but framed apex is still data).
      if #["constructionLeg", "limitLeg", "arrowHom", "subobjectInclusion"].contains tag then
        return ← validateCallableData data
  validatePort placeholder expected data

partial def interfaceCarrier (selected : Expr) (descriptor : Json) :
    TermElabM (Except String Expr) := do
  if ← isType selected then return .ok selected
  let state ← registryState
  let .ok (tag, _) := envelope descriptor | return .error "a selected object requires its descriptor"
  let category ← if let some entry := state.objects.find? (·.id.raw == tag) then do
      let some category := state.categories.find? (·.id == entry.category)
        | return .error "the selected category is not registered"
      pure category
    else if let .ok ("functorAction", #[action, _]) := envelope descriptor then do
      let .ok (actionTag, actionArgs) := envelope action
        | return .error "the selected object action is incomplete"
      let category := (state.functors.find? (·.id.raw == actionTag)).map (·.target) <|>
        (if actionTag == "classifierForget" then do
          let id ← actionArgs[0]?.bind (·.getStr?.toOption)
          (state.classifiers.find? (·.id.raw == id)).map (·.host)
        else none)
      let some category := category
        | return .error "the selected action requires its retained carrier context"
      Semantic.namedCategoryFor state category
    else return .error "the selected structured descriptor requires its retained carrier context"
  let value ← (Language.recognize state selected category).run {}
  return .ok (← (Language.semanticObject (← (Language.carrierObject value).run {})).run {})

partial def validateElementExpressionAt (objects : InterfaceObjects) (selected carrier : Expr)
    (expression : Json) : TermElabM (Except String Unit) := do
  let .ok (tag, args) := envelope expression | return .error "an element requires its expression envelope"
  match tag, args with
  | "point", #[arrow] =>
      validateCallableAt objects (← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, carrier]) arrow
  | "add", #[left, right] | "mul", #[left, right] =>
      if let .error message ← validateElementExpressionAt objects selected carrier left then return .error message
      validateElementExpressionAt objects selected carrier right
  | "neg", #[value] => validateElementExpressionAt objects selected carrier value
  | "operationExpression", #[id, parameters, operands] =>
      let state ← registryState
      let .ok id := id.getStr? | return .error "the operation id must be a string"
      let some row := state.operations.find? (·.id.raw == id)
        | return .error "the expression names no registered operation"
      let .ok parameters := parameters.getArr? | return .error "operation parameters must be ordered"
      let .ok operands := operands.getArr? | return .error "operation operands must be ordered"
      unless operands.size == row.arity do return .error "the operation has a different declared arity"
      let source ← mkFreshExprMVar (← inferType carrier)
      let .ok operation ← interfaceDeclaration objects row.declaration
          (← mkAppM ``Quiver.Hom #[source, carrier]) parameters
        | return .error "the operation expression changes its selected result interface"
      if row.result.isNone && !(← isType selected) then
        let explicit ← (Language.explicitArguments row.declaration operation).run {}
        unless ← explicit.anyM (fun field => withoutModifyingState <| isDefEq field selected) do
          return .error "the operation expression changes its selected mathematical structure"
      let sources ← if operands.isEmpty then pure #[] else if operands.size == 2 then do
          let source ← withTransparency .all <| whnf source
          unless source.isAppOf ``Prod do return .error "a binary operation requires its declared product source"
          pure source.getAppArgs
        else pure #[← instantiateMVars source]
      unless sources.size == operands.size do return .error "the operation has a different operand interface"
      for (source, operand) in sources.zip operands do
        if let .error message ← validateElementExpressionAt objects selected source operand then return .error message
      return .ok ()
  | _, _ => validateElementExpression expression

end

/-- Validate one constructor port with its original binder-role provenance.
Endpoint representations come only from earlier actual fields or retained input
roles. The representation callback supplies actual finite point keys; no resolved
formal-value equality or formal carrier enumeration participates. -/
def validatePlannedPort (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (seen : Array Json) (data : Json)
    (externalDescriptor : Nat → Option Json)
    (endpointKeys : Json → TermElabM (Except String (Option (Array Json)))) :
    TermElabM (Except String Unit) := do
  let unwrapped := if let .ok ("valueData", #[actual]) := envelope data then actual else data
  if (unwrapped.getObjValAs? String "ctor").toOption == some "typedMap" &&
      (port.domainBinder.isSome || port.codomainBinder.isSome) then
    let resolve := fun binder => plan.actualData? binder seen |>.orElse fun _ => externalDescriptor binder
    let some source := port.domainBinder.bind resolve
      | return .error "the typed callable has no actual computational domain descriptor"
    let some target := port.codomainBinder.bind resolve
      | return .error "the typed callable has no actual computational codomain descriptor"
    return ← validateEndpointPort port.formalField source target data
  let graph := if let .ok ("finiteGraph", #[_, actual]) := envelope unwrapped then actual else unwrapped
  -- Ordinary scalar/list ports have no callable endpoint roles.
  unless graph.getArr?.isOk && (port.domainBinder.isSome || port.codomainBinder.isSome) do
    return ← validatePort port.formalField port.expectedType data
  let resolve := fun binder => plan.actualData? binder seen |>.orElse fun _ => externalDescriptor binder
  let some domainBinder := port.domainBinder
    | return .error "the callable graph has no retained computational domain role"
  let some domainDescriptor := resolve domainBinder
    | return .error "the callable graph has no actual computational domain descriptor"
  let domainKeys ← match ← endpointKeys domainDescriptor with
    | .error message => return .error message
    | .ok (some keys) => pure keys
    | .ok none => return .error "a finite graph requires complete actual domain keys or an opaque callable"
  let mut codomainKeys := none
  if let some codomainBinder := port.codomainBinder then
    let some codomainDescriptor := resolve codomainBinder
      | return .error "the callable graph has no actual computational codomain descriptor"
    match ← endpointKeys codomainDescriptor with
    | .error message => return .error message
    | .ok keys => codomainKeys := keys
  validateGraphAtKeys port.formalField port.expectedType data domainKeys codomainKeys

/-- Frame a returned point at the caller's exact selected object. The formal
point is supplied independently and is never reconstructed from the answer.
Symbolic fields remain computational claims, including a different expression
for the same requested result; opaque owners are checked by the live consumer. -/
def validateElementAt (selected : Expr) (selectedData : Json) (formalPoint : Expr)
    (answer : Json) : TermElabM (Except String Unit) := do
  if selected.hasMVar || selected.hasLevelMVar then
    throwError "the selected element interface has unresolved formal parameters"
  let data := if let .ok ("valueData", #[data]) := envelope answer then data else answer
  if (data.getObjValAs? String "ctor").toOption == some "constrainedPoint" then
    let .ok point := Backend.ConstrainedPoint.decode data
      | return .error "the constrained point omitted its complete interface"
    unless point.target == selectedData do
      return .error "the constrained point differs from the exact selected target"
    return ← withoutModifyingState <|
      validateCallableAt #[(selectedData, selected)] (← inferType formalPoint) data
  if (data.getObjValAs? String "ctor").toOption == some "element" then
    let .ok (_, #[descriptor, expression]) := envelope data
      | return .error "an element requires its exact selected object and expression"
    unless descriptor == selectedData do
      return .error "the element descriptor differs from the exact selected endpoint"
    let pointType ← inferType formalPoint
    let carrier ← match Language.homEnds? pointType with
      | some (domain, target) =>
          unless ← withTransparency .all <| isDefEq domain (← Language.globalPointSource.run {}) do
            return .error "a closed element cannot replace a nonconstant generalized point"
          pure target
      | none => pure pointType
    return ← withoutModifyingState <|
      validateElementExpressionAt #[(selectedData, selected)] selected carrier expression
  validatePort formalPoint (← inferType formalPoint) answer

end CasCatalogue.ComputationalData
