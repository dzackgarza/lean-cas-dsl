/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import CasCatalogue.Semantic
public import CasCatalogue.Codec
public import CasCatalogue.StructuredResult
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
    unless ← isDefEq parameter argument do return none
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
      let formal := formalField.consumeMData
      unless formal.isAppOf ``Prod do
        return .error "the product descriptor requires its retained formal factor contexts"
      let fields := formal.getAppArgs
      let left := fields[fields.size - 2]!
      let right := fields.back!
      for (field, data) in #[(left, leftData), (right, rightData)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      return .ok ()
    if tag == "arrow" then
      let #[source, target, map] := args | return .error "arrow requires source, target and map"
      let sourceField ← mkAppM ``CategoryTheory.Arrow.left #[formalField]
      let targetField ← mkAppM ``CategoryTheory.Arrow.right #[formalField]
      let mapField ← mkAppM ``CategoryTheory.Arrow.hom #[formalField]
      for (field, data) in #[(sourceField, source), (targetField, target), (mapField, map)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      return .ok ()
    if tag == "subobject" then
      let #[source, target, inclusion] := args
        | return .error "subobject requires source, ambient object and inclusion"
      let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[formalField]
      let sourceField ← mkAppM ``CategoryTheory.Arrow.left #[arrow]
      let targetField ← mkAppM ``CategoryTheory.Arrow.right #[arrow]
      let inclusionField ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
      for (field, data) in #[(sourceField, source), (targetField, target)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      if let .error message ← validateEndpointPort inclusionField source target inclusion then
        return .error message
      if let some presentation := (json.getObjVal? "presentation").toOption then
        -- Both representations have the declared source-category object schema.
        -- These are interface placeholders, not chosen canonical comparison maps.
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
  return .error "the computational port has no supported released data representation"

/-- A finite map is complete at its actual supplied domain. Inventories are
computational data, never an enumeration of the requested formal construction. -/
partial def validateEndpointPort (formal : Expr) (source target data : Json) :
    TermElabM (Except String Unit) := do
  let unwrapped := if let .ok ("valueData", #[actual]) := envelope data then actual else data
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

end CasCatalogue.ComputationalData
