/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module
public import CasCatalogue.Semantic
public import CasCatalogue.ObjectPresentation
public import CasCatalogue.Language
public import CasCatalogue.OperationAgreement
public import CasCatalogue.Codec
public import CasCatalogue.DataOwnership
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

/-- Open only transparent computational-value envelopes before choosing an
interface check. The public decoder owns their framing; nesting cannot hide a
typed callable or a selected point from its actual endpoint checks. -/
partial def valuePayload (json : Json) : Except String Json := do
  unless (json.getObjValAs? String "ctor").toOption == some "valueData" do return json
  let .inline actual ← Backend.ComputationalValue.decode json
    | throw "a transparent computational value requires its inline payload"
  valuePayload actual

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
  if tag == "extent" then
    let #[id, _, subset] := args
      | return .error "extent requires its power object, ambient object and subset data"
    let .ok id := id.getStr? | return .error "the extent power-object id must be a string"
    let some power := state.powerObjects.find? (·.id.raw == id)
      | return .error "the extent names no registered power object"
    let some literal := state.subsetLiterals.find? (·.powerObject == power.id)
      | return .ok none
    -- Finset's released representation is its list of members. These are
    -- actual computational keys, not the original formal extent's members.
    unless literal.type == ``Finset do return .ok none
    let .ok actual := valuePayload subset | return .error "the subset data wrapper is malformed"
    let .ok points := actual.getArr? | return .ok none
    let mut seen := #[]
    for point in points do
      if seen.contains point then return .error "a finite subset representation repeats a key"
      seen := seen.push point
    return .ok (some points)
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
  | literal (type : Expr) (shape : PointSchema)
  | constrainedData (shape : PointSchema)
  | keys (points : Array Json)
  | list (element : PointSchema)
  | graph (domain codomain : PointSchema) (domainKeys : Option (Array Json))
  | recordFields (unlabelled : Bool) (fields : Array PointSchema)
  | alternatives (constructors : Array (String × PointSchema))

/-- A scalar literal has only independently fixed scalar data slots. Callable
fields and computational endpoint inventories remain data-only interfaces. -/
partial def PointSchema.scalarLiteral : PointSchema → Bool
  | .plain _ => true
  | .literal _ shape => shape.scalarLiteral
  | .list element => element.scalarLiteral
  | .recordFields _ fields => fields.all PointSchema.scalarLiteral
  | .alternatives constructors => constructors.all (fun (_, schema) => schema.scalarLiteral)
  | .constrainedData _ | .keys _ | .graph .. => false

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
partial def pointSchema (type : Expr) (fuel : Nat := 32) (actualPoints : Bool := false) :
    TermElabM (Option PointSchema) := do
  let fuel + 1 := fuel | return none
  let type ← withTransparency .all <| whnf type
  if type.hasLevelMVar || type.hasLooseBVars then return none
  if type.isSort || (← isProp type) then return none
  -- Atomic scalar codecs have no independently represented nested data slots.
  -- Composite plain types still expose their constructor fields, which may
  -- contain opaque computational values rather than wholly inline literals.
  if #[``Nat, ``Int, ``Bool, ``String, ``Unit].any type.isConstOf || type.isAppOf ``Fin then
    if type.hasMVar then return none
    return some (.plain type)
  -- Actual endpoint inventories supply computational points, not witnesses of
  -- membership in the formal reference object. Reuse the public constrained
  -- record interface while retaining every representation check of its data.
  -- The barrier prevents an enclosing scalar record from decoding that proof.
  if actualPoints then
    if let some constrained ← ConstrainedPoint.schema? type then
      if constrained.fieldCount > 1 then
        let some shape ← pointSchema constrained.dataType fuel actualPoints | return none
        return some (.constrainedData shape)
  -- A placeholder in a proposition does not change the record's data slots.
  -- Inspect those slots independently below; an unresolved data type still
  -- fails its own recursive check, including a scalar codec's selected bounds.
  if type.isAppOf ``List || type.isAppOf ``Array then
    return (← pointSchema type.appArg! fuel actualPoints).map PointSchema.list
  if type.isAppOf ``Quot then return ← pointSchema type.getAppArgs[0]! fuel actualPoints
  if let .forallE _ domain body _ := type then
    if body.hasLooseBVars then return none
    let mut keys := none
    if ← plainType domain then
      if let some points ← Codec.finiteDomain domain then
        let encoded ← points.mapM fun point => Codec.encode point
        if encoded.all Except.isOk then keys := some (encoded.filterMap Except.toOption)
    let some domain ← pointSchema domain fuel actualPoints | return none
    let some codomain ← pointSchema body fuel actualPoints | return none
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
        let some schema ← pointSchema fieldType fuel actualPoints | return none
        schemas := schemas.push schema
      return some (PointSchema.recordFields (Codec.isUnlabelled info) schemas)
    let some schema := schema | return none
    alternatives := alternatives.push (Codec.label name, schema)
  let result := if Codec.isUnlabelled info then alternatives[0]?.map Prod.snd
    else some (PointSchema.alternatives alternatives)
  -- Keep each scalar subtree's independently fixed complete type. Its public
  -- representation constraints apply even inside a graph or another record;
  -- opaque fields still use only the structural schema below.
  return result.map fun schema =>
    if !ConstrainedPoint.closed type then .constrainedData schema
    else if schema.scalarLiteral then .literal type schema else schema

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
  | .constrainedData shape => validatePoint shape json
  | .literal type shape =>
    if let .error message ← validatePoint shape json then return .error message
    if let some literal := inlineLiteralData? json then
      return (← Codec.decode type literal).map fun _ => ()
    return .ok ()
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
        if let some fixed := independentKeys then
          unless points.size == fixed.size && fixed.all points.contains do
            return .error "the callable inventory differs from its independently fixed domain"
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
  let retained ← supplied.foldlM (fun kept (_, value) => do
    return kept ++ (← getMVars value)) (#[] : Array MVarId)
  if type.hasLevelMVar || !(← getMVars type).all retained.contains then return none
  return some application

/-- A public record projection is applicable only at its independently fixed
receiver type. A reply's constructor tag cannot make an incompatible receiver
into a record or turn malformed data into an interpreter exception. -/
def recordProjection (declaration : Name) (receiver : Expr) : TermElabM (Option Expr) := do
  let arity ← forallTelescopeReducing (← getConstInfo declaration).type
    fun fields _ => pure fields.size
  if arity == 0 then return none
  projectionApplication declaration arity #[(arity - 1, receiver)]

/-- Whole record receivers already present in an independent expected type.
Only complete projection applications are inspected; a returned packet never
chooses the record's category, predicate, or field declaration. -/
def retainedRecordReceivers (expected : Expr) : TermElabM (Array Expr) := do
  let env ← getEnv
  let aliases : Array (Name × Nat) ← #[``CategoryTheory.Arrow.left, ``CategoryTheory.Arrow.right,
      ``CategoryTheory.Arrow.hom, ``CategoryTheory.ObjectProperty.FullSubcategory.obj].mapM
    fun name => do
      let arity ← forallTelescopeReducing (← getConstInfo name).type
        fun fields _ => pure fields.size
      return (name, arity)
  let receivers ← IO.mkRef (#[] : Array Expr)
  expected.forEach fun expression => do
    let receiver : Option Expr := match expression with
      | .proj _ _ owner => some owner
      | _ => do
        let name ← expression.getAppFn.constName?
        let projectionArity := (env.getProjectionFnInfo? name).map
          (fun (info : ProjectionFunctionInfo) => info.numParams + 1)
        let aliasArity := (aliases.find? (fun item => item.1 == name)).map (fun item => item.2)
        let arity ← projectionArity <|> aliasArity
        unless expression.getAppNumArgs == arity do none
        expression.getAppArgs.back?
    if let some receiver := receiver then
      unless receiver.hasLooseBVars do
        receivers.modify fun previous =>
          if previous.contains receiver then previous else previous.push receiver
  receivers.get

/-- The published concrete-category dictionary fixes a point type independently
of any returned descriptor or inventory. -/
def objectPointSchema (object : Expr) : TermElabM (Option PointSchema) := do
  let category ← withTransparency .all <| whnf (← inferType object)
  let some carrier ← projectionApplication ``CategoryTheory.ToType 7
      #[(0, category), (6, object)] | return none
  pointSchema carrier (actualPoints := true)

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
    else pointSchema body (actualPoints := true)
  let some outputSchema := outputSchema
    | return .error "the callable's point types require their released data representation"
  let unwrapped ← match valuePayload data with
    | .ok actual => pure actual
    | .error message => return .error message
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

/-- A construction interface comes from the registered presentation and its
retained diagram. Its computational fields never determine a universal witness. -/
structure ConstructionInterface where
  row : LimitEntry
  diagram : Expr
  presentation : Expr
  dataDiagram : Expr
  dataPresentation : Expr
  inputs : InterfaceObjects
  dataInputs : InterfaceObjects
  answer : Option Json
  comparison : Option Expr := none

/-- A completed lift retains every evidence-family data slot. Dependent slot
interfaces require the separately fixed selected plan; this traversal preserves
the public packets, including opaque and computed parameters. -/
def validateLiftParameters (entry : LiftEntry) (data : Json)
    (validate : Json → TermElabM (Except String Unit)) : TermElabM (Except String Unit) := do
  let .ok parameters := (data.getObjVal? "parameters").bind (·.getArr?)
    | return .error "a completed lift step requires its ordered selected evidence parameters"
  let declaration ← mkConstWithFreshMVarLevels entry.evidence
  let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let slots ← (arguments.zip infos).filterMapM fun (argument, info) => do
    if info.isExplicit && !(← isProp (← inferType argument)) then return some argument
    return none
  unless parameters.size == slots.size do
    return .error "a completed lift step omitted or added selected evidence parameters"
  for parameter in parameters do
    if let .error message ← validate parameter then return .error message
  return .ok ()

/-- Complete construction context for the existing creation and restriction tags. -/
def validateLiftContext (tag : String) (args : Array Json) (data : Json)
    (validate : Json → TermElabM (Except String Unit)) : TermElabM (Except String Unit) := do
  unless args.size == (if tag == "createdCone" then 3 else 5) do
    return .error "the prescribed lift omitted its complete construction context"
  let .ok id := args[0]!.getStr? | return .error "a lift id must be a string"
  let some entry := (← registryState).lifts.find? (·.id.raw == id)
    | return .error "the selected lift is not registered"
  if tag == "liftStep" then
    if let .error message ← validateLiftParameters entry data validate then
      return .error message
    let .ok fields := args[4]!.getArr?
      | return .error "a completed lift step requires all four ordered component outputs"
    unless fields.size == 4 do
      return .error "a completed lift step requires all four ordered component outputs"
  for datum in args.extract 1 args.size do
    if let .error message ← validate datum then return .error message
  return .ok ()

/-- Inspect a released record through the independently fixed receiver. The
callback checks only data framing at those complete projection types; no reply
field is used to choose another field's type or reconstruct a proof. Keeping this
structural traversal outside the recursive validator also avoids enlarging its
compiler group. -/
def validateRecordPortWith (formal expected : Expr) (json : Json)
    (objects : InterfaceObjects)
    (validate : Expr → Expr → Json → InterfaceObjects → TermElabM (Except String Unit)) :
    TermElabM (Option (Except String Unit)) := do
  let shape ← withTransparency .all <| whnf expected
  let some name := shape.getAppFn.constName? | return none
  let some info := getStructureInfo? (← getEnv) name | return none
  let mut fields := #[]
  for field in info.fieldNames do
    let projection ← withTransparency .all <| mkProjection formal field
    let type ← instantiateMVars (← inferType projection)
    unless ← isProp type do fields := fields.push (projection, type)
  let data ← if fields.size == 1 then pure #[json]
    else match json.getArr? with
      | .ok data => pure data
      | .error _ => return some (.error "computational record fields require an array")
  unless data.size == fields.size do
    return some (.error "the computational record omitted or added data fields")
  for ((projection, type), data) in fields.zip data do
    if let .error message ← validate projection type data objects then
      return some (.error message)
  return some (.ok ())

/-- Existing public record envelopes are distinguished from ordinary ordered
fields using only the independently fixed receiver interface. -/
inductive RecordFieldCodec where
  | ordered | core | arrow | arrowRefinement
  deriving BEq, Inhabited

/-- Every intermediate step retains its actual record and field declaration.
The public codec is selected at that complete formal receiver, never by a reply.
Proof fields are never computational slots. -/
structure RecordFieldStep where
  structureName : Name
  field : Name
  index : Nat
  count : Nat
  codec : RecordFieldCodec
  deriving Inhabited

abbrev RecordFieldPath := Array RecordFieldStep

/-- A public structural action may project retained fields or assemble another
record from those fields. This plan contains only existing field declarations
and codecs, never a formal value, proof, evaluator, or mathematical operation. -/
inductive RecordProjectionPlan where
  | input (path : RecordFieldPath)
  | record (codec : RecordFieldCodec) (fields : Array RecordProjectionPlan)

/-- Recognize a public record codec at its complete fixed interface. In
particular, an arbitrary Comma or full subcategory is not necessarily Arrow. -/
def recordFieldCodec (receiver : Expr) : TermElabM RecordFieldCodec := do
  if (← recordProjection ``CategoryTheory.Core.of receiver).isSome then return .core
  if (← recordProjection ``CategoryTheory.Arrow.left receiver).isSome then return .arrow
  if let some object ←
      recordProjection ``CategoryTheory.ObjectProperty.FullSubcategory.obj receiver then
    if (← recordProjection ``CategoryTheory.Arrow.left object).isSome then return .arrowRefinement
  return .ordered

/-- Read a projection chain on a fresh symbolic receiver. Equal actual field
values cannot make a different projection match this chain. -/
partial def recordFieldPath? (receiver selected : Expr) :
    TermElabM (Option RecordFieldPath) := do
  let selected ← withTransparency .all <| whnf selected
  if selected == receiver then return some #[]
  let .proj name index parent := selected | return none
  let some initial ← recordFieldPath? receiver parent | return none
  let some info := getStructureInfo? (← getEnv) name | return none
  let mut count := 0
  let mut position := none
  for offset in [:info.fieldNames.size] do
    let field ← withTransparency .all <| mkProjection parent info.fieldNames[offset]!
    unless ← isProp (← inferType field) do
      if offset == index then position := some count
      count := count + 1
  let some selectedPosition := position | return none
  let codec ← recordFieldCodec parent
  return some (initial.push {
    structureName := name, field := info.fieldNames[index]!,
    index := selectedPosition, count, codec })

/-- Compile only the structural field part of an independently selected action.
Every output data field must be a projection of the original receiver. No closed
constant, arithmetic application, proof, or arbitrary Lean body is evaluated. -/
partial def recordProjectionPlan? (receiver selected : Expr)
    (seen : Array Expr := #[]) : TermElabM (Option RecordProjectionPlan) := do
  let selected ← withTransparency .all <| whnf selected
  if let some path ← recordFieldPath? receiver selected then return some (.input path)
  if seen.contains selected then return none
  let type ← withTransparency .all <| whnf (← inferType selected)
  let some name := type.getAppFn.constName? | return none
  let some info := getStructureInfo? (← getEnv) name | return none
  let mut fields := #[]
  for field in info.fieldNames do
    let projection ← withTransparency .all <| mkProjection selected field
    unless ← isProp (← inferType projection) do
      let some plan ← recordProjectionPlan? receiver projection (seen.push selected)
        | return none
      fields := fields.push plan
  return some (.record (← recordFieldCodec selected) fields)

/-- Open only the public inline envelope, retaining its exact occurrence path. -/
partial def recordPayload? (data : DataOwnership.Data) : Option DataOwnership.Data := do
  if (data.json.getObjValAs? String "ctor").toOption == some "valueData" then
    let args ← ((data.json.getObjVal? "args").bind (·.getArr?)).toOption
    unless args.size == 1 do none
    return ← recordPayload? (← (data.project #[.field "args", .index 0]).toOption)
  return data

/-- Classify scalar representation slots only to reject unresolved or opaque
parameters before semantic-context lookup. Looking through a constrained-data
barrier here only classifies parameter slots; the closed-type and ordinary literal
checks below remain necessary and do not change point validation policy. -/
partial def actualScalarParameterSlots : PointSchema → Bool
  | .plain _ => true
  | .literal _ shape | .constrainedData shape => actualScalarParameterSlots shape
  | .list element => actualScalarParameterSlots element
  | .recordFields _ fields => fields.all actualScalarParameterSlots
  | .alternatives constructors => constructors.all (fun (_, schema) => actualScalarParameterSlots schema)
  | .keys _ | .graph .. => false

mutual
/-- Interpret actual public descriptor parameters without replacing a literal
representation parameter by an equal-JSON association to a formal field. This
is confined to point-schema inspection; ordinary semantic interfaces retain
their existing independently selected parameter context. -/
partial def actualDescriptorArgument (objects : InterfaceObjects)
    (semanticArgument : Expr → Json → TermElabM (Except String Expr))
    (expected : Expr) (data : Json) : TermElabM (Except String Expr) := do
  let expected ← instantiateMVars expected
  if ← isProp expected then return .error "a proof is not computational data"
  let literalSchema ← pointSchema expected
  if (← plainType expected) || literalSchema.any actualScalarParameterSlots then
    unless ConstrainedPoint.closed expected do
      return .error "an actual representation parameter requires its fixed literal type"
    let some literal := inlineLiteralData? data
      | return .error "an actual representation parameter requires its inline literal data"
    return ← Codec.decode expected literal
  if let .ok (tag, args) := envelope data then
    let state ← registryState
    if tag == "category" || tag == "constructedCategory" || tag == "functor" then
      let #[id, parameters] := args
        | return .error "a selected dictionary requires its complete ordered parameters"
      let .ok id := id.getStr? | return .error "a selected dictionary id must be a string"
      let .ok parameters := parameters.getArr? | return .error "dictionary parameters must be ordered"
      let declaration := if tag == "category" then
        (state.categories.find? (·.id.raw == id)).map (·.declaration)
      else if tag == "constructedCategory" then
        (state.constructors.find? (·.id.raw == id)).map (·.semantics)
      else (state.functors.find? (·.id.raw == id)).map (·.declaration)
      let some declaration := declaration
        | return .error "the selected dictionary is not registered"
      if tag == "constructedCategory" then
        let some constructor := state.constructor? ⟨id⟩ | unreachable!
        unless parameters.size == constructor.signature.size do
          return .error "the constructed category changed its complete argument count"
      let resultType ← inferType (← instantiateFresh declaration)
      let .ok value ← actualDescriptorDeclaration objects semanticArgument declaration resultType parameters
        | return .error "the selected dictionary has incompatible complete parameters"
      let value ← if tag == "functor" then Semantic.asFunctor value else pure value
      unless ← withTransparency .all <| isDefEq (← inferType value) expected do
        return .error "the selected dictionary has a different complete declared type"
      return .ok value
    if state.objects.any (·.id.raw == tag) ||
        #["objectProduct", "valueData", "finiteData", "objectPresentation"].contains tag then
      let .ok object ← actualDescriptorObject objects semanticArgument data
        | return .error "the actual object parameter has no complete public descriptor"
      unless ← withTransparency .all <| isDefEq (← inferType object) expected do
        return .error "the actual object parameter has a different selected category"
      return .ok object
  semanticArgument expected data

/-- The existing declaration-parameter checks with actual representation
literals resolved before retained semantic associations. No returned function,
law or proof is decoded, and the resulting expression is used only for shape. -/
partial def actualDescriptorDeclaration (objects : InterfaceObjects)
    (semanticArgument : Expr → Json → TermElabM (Except String Expr))
    (declaration : Name) (expected : Expr) (data : Array Json) :
    TermElabM (Except String Expr) := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (fields, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
  if ← withoutModifyingState (withTransparency .all <| isDefEq result expected) then
    discard <| withTransparency .all <| isDefEq result expected
  let mut position := 0
  for (field, info) in fields.zip infos do
    let type ← instantiateMVars (← inferType field)
    if !info.isExplicit || (← isProp type) then continue
    let some datum := data[position]?
      | return .error "the actual declaration omitted a parameter"
    let .ok argument ← actualDescriptorArgument objects semanticArgument type datum
      | return .error "an actual parameter does not have its declared interface"
    unless ← withTransparency .all <| isDefEq field argument do
      return .error "an actual parameter changes its selected dependent endpoint"
    position := position + 1
  unless position == data.size do return .error "the actual declaration added a parameter"
  for field in fields do
    let field ← instantiateMVars field
    if field.isMVar then
      let type ← instantiateMVars (← inferType field)
      if (← isClass? type).isSome then
        if let some dictionary := (← trySynthInstance type).toOption then
          unless ← isDefEq field dictionary do
            return .error "the actual declaration has incompatible selected structure"
  unless ← withTransparency .all <| isDefEq result expected do
    return .error "the actual declaration has incompatible complete endpoints"
  return .ok (← instantiateMVars (mkAppN constant fields))

/-- Derive an actual named descriptor's public interface from its declaration
and ordered parameters, bypassing a whole-descriptor formal-apex association.
Transparent envelopes follow actual data. Unsupported descriptors stay unsupported. -/
partial def actualDescriptorObject (objects : InterfaceObjects)
    (semanticArgument : Expr → Json → TermElabM (Except String Expr)) (data : Json) :
    TermElabM (Except String Expr) := do
  let .ok (tag, args) := envelope data
    | return .error "the actual endpoint requires its complete public object descriptor"
  if let .ok ("valueData", #[actual]) := envelope data then
    return ← actualDescriptorObject objects semanticArgument actual
  if let .ok ("objectPresentation", #[_, actual]) := envelope data then
    return ← actualDescriptorObject objects semanticArgument actual
  if let .ok ("finiteData", #[descriptor, _]) := envelope data then
    return ← actualDescriptorObject objects semanticArgument descriptor
  if tag == "objectProduct" then
    let #[left, right] := args | return .error "a product endpoint requires both factors"
    let .ok left ← actualDescriptorObject objects semanticArgument left
      | return .error "the first actual product factor is incomplete"
    let .ok right ← actualDescriptorObject objects semanticArgument right
      | return .error "the second actual product factor is incomplete"
    unless (← whnfR (← inferType left)).isSort && (← whnfR (← inferType right)).isSort &&
        !(← isProp left) && !(← isProp right) do
      return .error "the actual product factors require their declared set-object interfaces"
    return .ok (← mkAppM ``Prod #[left, right])
  let some entry := (← registryState).objects.find? (·.id.raw == tag)
    | return .error "the explicit inventory requires a supported actual public object descriptor"
  let expected ← inferType (← instantiateFresh entry.declaration)
  actualDescriptorDeclaration objects semanticArgument entry.declaration expected args

end

/-- Point shape comes from actual public descriptors and their parameters.
Known child inventories stay exact even when another product factor declines
enumeration. No requested formal apex supplies members or replacement shape. -/
partial def actualInventoryPointSchema (objects : InterfaceObjects)
    (semanticArgument : Expr → Json → TermElabM (Except String Expr)) (data : Json)
    (lookupKeys : Json → TermElabM (Except String (Option (Array Json)))) :
    TermElabM (Except String PointSchema) := do
  match ← lookupKeys data with
  | .error message => return .error message
  | .ok (some keys) => return .ok (.keys keys)
  | .ok none => pure ()
  if let .ok ("valueData", #[actual]) := envelope data then
    return ← actualInventoryPointSchema objects semanticArgument actual lookupKeys
  if let .ok ("objectPresentation", #[_, actual]) := envelope data then
    return ← actualInventoryPointSchema objects semanticArgument actual lookupKeys
  if let .ok ("objectProduct", #[left, right]) := envelope data then
    let .ok left ← actualInventoryPointSchema objects semanticArgument left lookupKeys
      | return .error "the first actual product factor has no public point schema"
    let .ok right ← actualInventoryPointSchema objects semanticArgument right lookupKeys
      | return .error "the second actual product factor has no public point schema"
    return .ok (.recordFields true #[left, right])
  let .ok actual ← actualDescriptorObject objects semanticArgument data
    | return .error "the explicit inventory has no supported actual object interface"
  let some schema ← objectPointSchema actual
    | return .error "the explicit inventory requires its actual public point-data schema"
  return .ok schema

/-- Preserve any independently available actual inventory. A declined
enumeration may use a returned explicit inventory only after validating every
point against the actual descriptor's public shape. The data remain untrusted. -/
partial def graphDomainKeys (objects : InterfaceObjects)
    (semanticArgument : Expr → Json → TermElabM (Except String Expr)) (source graph : Json)
    (lookupKeys : Json → TermElabM (Except String (Option (Array Json)))) :
    TermElabM (Except String (Array Json)) := do
  match ← lookupKeys source with
  | .error message => return .error message
  | .ok (some keys) => return .ok keys
  | .ok none => pure ()
  let .ok ("finiteGraph", #[inventory, _]) := envelope graph
    | return .error "a finite callable requires its actual computational domain point inventory"
  let .ok points := inventory.getArr?
    | return .error "a finite callable inventory requires an array"
  let .ok schema ← actualInventoryPointSchema objects semanticArgument source lookupKeys
    | return .error "the explicit inventory requires a supported actual public point interface"
  let mut seen := #[]
  for point in points do
    if seen.contains point then return .error "a computational point inventory repeats a key"
    if let .error message ← validatePoint schema point then return .error message
    seen := seen.push point
  return .ok points

/-- Read a complete callable-valued point type through definition aliases only.
A retained full Hom keeps its original category dictionary. A nondependent
function has the ordinary Sets Hom; no structured record projection is used. -/
partial def declaredCallableType? (type : Expr) (seen : Array Expr := #[]) :
    TermElabM (Option Expr) := do
  let type := (← instantiateMVars type).consumeMData.headBeta
  if type.hasMVar || type.hasLevelMVar || type.hasFVar || type.hasLooseBVars ||
      seen.contains type then return none
  if (Language.homEnds? type).isSome then return some type
  if let .forallE _ source target _ := type then
    if target.hasLooseBVars then return none
    return some (← mkAppM ``Quiver.Hom #[source, target])
  let some unfolded ← unfoldDefinition? type | return none
  declaredCallableType? unfolded (seen.push type)

/-- Check a function-valued graph outside the recursive declaration/port group.
The two callbacks are the original recursive owners at the same retained object
context; this traversal changes neither the inventory policy nor inner typing. -/
def validateCallableGraphAt (objects : InterfaceObjects)
    (semanticArgument : Expr → Json → TermElabM (Except String Expr))
    (validateOutput : Expr → Json → TermElabM (Except String Unit))
    (target : Expr) (sourceData targetData unwrapped graph : Json)
    (checked : Except String Unit) : TermElabM (Except String Unit) := do
  -- A finite point may itself contain a complete function or Hom value. Its
  -- outer keys still come only from the actual endpoint inventory; the
  -- independently fixed callable target supplies the inner full Hom.
  -- Actual codomain membership does not replace that inner type check.
  let some inputType ← declaredCallableType? target | return checked
  let .ok codomain ← endpointKeys targetData | return checked
  let .ok keys ← graphDomainKeys objects semanticArgument
      sourceData unwrapped endpointKeys
    | return checked
  if let .ok ("finiteGraph", #[inventory, _]) := envelope unwrapped then
    let .ok inventory := inventory.getArr? | return checked
    unless inventory.size == keys.size && keys.all inventory.contains do return checked
  if let .error message := validateGraphEndpoints keys codomain graph then return .error message
  let .ok pairs := graph.getArr? | return checked
  for pair in pairs do
    let .ok #[_, output] := pair.getArr? | return checked
    if let .error message ← validateOutput inputType output then
      return .error message
  return .ok ()

/-- Prepare the admission's complete input Hom outside the recursive port
validator. The caller supplies the independently declared full signature; actual
point and legacy whole-callable domains retain their separate checks. -/
def admissionInputHom (expected source domain original input : Expr) :
    TermElabM (Except String (Bool × Expr)) := do
  let pointInput ← withoutModifyingState do
    withTransparency .all <|
      isDefEq domain source <&&> isDefEq original input
  if pointInput then
    -- Resolve recovered endpoint parameters before AppBuilder opens a new
    -- metavariable depth. This point's independently declared full Hom owns
    -- the category dictionary; the legacy callable keeps its own below.
    unless ← withTransparency .all <|
        isDefEq (← inferType domain) expected.getAppArgs[0]! <&&>
          isDefEq domain source <&&>
          isDefEq (← inferType original) expected.getAppArgs[0]! <&&>
          isDefEq original input do
      return .error "the admitted point's data endpoints change its complete selected category"
  let originalType ← if pointInput then
      withTransparency .all <| mkAppOptM' expected.getAppFn
        #[some expected.getAppArgs[0]!, some expected.getAppArgs[1]!,
          some (← instantiateMVars domain), some (← instantiateMVars original)]
    else mkAppM ``Quiver.Hom #[domain, original]
  unless pointInput do
    -- Preserve the original whole-callable input form: its internal domain
    -- can differ from the admission's outer point domain, but its complete
    -- function type must still be precisely the declared input type.
    let formal ← mkFreshExprMVar originalType
    let some function ← callableValue formal originalType
      | return .error "the admission input is not the original complete callable"
    unless ← withTransparency .all <| isDefEq (← inferType function) input do
      return .error "the original callable changes the admission's complete input type"
  return .ok (pointInput, originalType)

mutual
/-- Validate the public declaration's ordered data parameters. Only the independent
formal value binds dependent field types; no answer is substituted into the declaration. -/
partial def declarationPorts (declaration : Name) (formal expected : Expr)
    (args : Array Json) (objects : InterfaceObjects := #[]) : TermElabM (Except String Unit) := do
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
    match ← validatePort field type data objects with
    | .error message => return .error message
    | .ok () => pure ()
  return .ok ()

/-- Released named, classifier and constructor actions retain their actual
parameters and selected inner edge from the independent formal expression. -/
partial def validateAction (formal : Expr) (json : Json) (objects : InterfaceObjects := #[]) :
    TermElabM (Except String Unit) := do
  let state ← registryState
  let .ok (tag, args) := envelope json
    | return .error "the selected action has no complete declaration descriptor"
  if tag == "structuredProjectionAction" then
    let .ok action ← interfaceAction objects json
      | return .error "the structured projection action has no complete accepted interface"
    unless ← withTransparency .all <| isDefEq action formal do
      return .error "the structured projection changed its independently selected complete action"
    return .ok ()
  if let some entry := state.functors.find? (·.id.raw == tag) then
    let some selected ← fixedFunctorApplication entry.declaration formal
      | return .error "the action descriptor differs from the retained selected edge"
    return ← declarationPorts entry.declaration selected (← inferType selected) args objects
  if let some entry := state.constructions.find? (·.id.raw == tag) then
    let some selected ← fixedFunctorApplication entry.declaration formal
      | return .error "the action descriptor differs from the retained complete construction"
    return ← declarationPorts entry.declaration selected (← inferType selected) args objects
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
    return ← declarationPorts entry.declaration selected (← inferType selected) parameters objects
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
    return ← validateAction source inner objects
  return .error "the selected action descriptor is not a released registered edge"

/-- Validate a computational port without producing a semantic value or evidence.
`objects` contains only independently retained input data and already validated
earlier ports. Reusing their exact descriptors retains an interface, never an
identification of their computed values with the accompanying formal terms.
Opaque owners are checked by the live-session consumer, outside this framing check. -/
partial def validatePort (formalField expectedType : Expr) (json : Json)
    (objects : InterfaceObjects := #[]) (explicitOnly : Bool := false) :
    TermElabM (Except String Unit) := do
  if ← isProp expectedType then
    return .error "a proposition is not a computational data port"
  if let .ok ("valueData", args) := envelope json then
    let #[actual] := args | return .error "valueData requires one data field"
    let opened := objects ++ objects.filterMap fun (retained, fixed) =>
      if retained == json then some (actual, fixed) else none
    return ← validatePort formalField expectedType actual opened explicitOnly
  -- Semantic dictionaries remain the independently selected context, even when
  -- the same descriptor is available among other retained computational inputs.
  if let .ok (tag, _) := envelope json then
    if tag == "category" || tag == "constructedCategory" || tag == "functor" then
      let .ok selected ← interfaceArgument objects expectedType json
        | return .error "the selected dictionary does not have its full declared interface"
      let formal ← if tag == "functor" then Semantic.asFunctor formalField else pure formalField
      unless ← withTransparency .all <| isDefEq selected formal do
        return .error "the computational dictionary changed the independently fixed full context"
      return .ok ()
  let retained := objects.filter (·.1 == json)
  unless retained.isEmpty do
    if ← retained.anyM (fun (_, fixed) => withoutModifyingState do
        withTransparency .all <| isDefEq (← inferType fixed) expectedType) then
      return .ok ()
    return .error "the retained computational datum has a different complete declared type"
  let state ← registryState
  if let .ok (tag, args) := envelope json then
    if tag == "opaqueData" then
      let #[token] := args | return .error "opaqueData requires one token"
      let .ok token := token.getStr? | return .error "an opaque token must be a string"
      if token.isEmpty then return .error "an opaque token must be nonempty"
      return .ok ()
    if tag == "extent" then
      let .ok actual ← interfaceExtent objects args
        | return .error "the extent has no complete published data interface"
      unless ← withTransparency .all <| isDefEq (← inferType actual) expectedType do
        return .error "the extent belongs to a different declared object category"
      return .ok ()
    if tag == "finiteData" then
      let #[descriptor, inventory] := args
        | return .error "finiteData requires its complete object descriptor and point inventory"
      if let .error message ← validatePort formalField expectedType descriptor objects then
        return .error message
      let .ok declaredKeys ← endpointKeys descriptor
        | return .error "the finite object has a malformed actual descriptor"
      let schema ← if let some keys := declaredKeys then pure (some (PointSchema.keys keys))
        else interfacePointSchema objects descriptor (some formalField)
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
    if #["constrainedPoint", "admittedPoint", "arrowHom", "subobjectInclusion"].contains tag then
      return ← validateCallableAt objects expectedType json
    if #["constructionLeg", "constructionField", "limitLeg"].contains tag then
      return ← validateConstructionProjection objects expectedType tag args (some formalField)
    if tag == "morphismEndpoint" then
      let .ok endpoint := Backend.MorphismEndpoint.decode json
        | return .error "the endpoint projection requires its complete callable and selector"
      let other ← mkFreshExprMVar expectedType
      let source := if endpoint.source then formalField else other
      let target := if endpoint.source then other else formalField
      let mapType ← mkAppM ``Quiver.Hom #[source, target]
      return ← validatePort (← mkFreshExprMVar mapType) mapType endpoint.callable objects
    if tag == "objectPresentation" then
      let #[action, actual] := args
        | return .error "objectPresentation requires its complete action and actual data"
      unless (action.getObjValAs? String "ctor").toOption == some "functorAction" do
        return .error "objectPresentation requires its selected action descriptor"
      match ← validatePort formalField expectedType action objects with
      | .error message => return .error message
      | .ok () => return ← validatePort formalField expectedType actual objects
    if tag == "functorAction" then
      let #[edge, receiver] := args
        | return .error "functorAction requires an action descriptor and receiver"
      let .ok (functor, source) ← actionContext formalField edge
        | return .error "the action requires its independently retained formal receiver context"
      match ← validateAction functor edge objects with
      | .error message => return .error message
      | .ok () => return ← validatePort source (← inferType source) receiver objects
    if let some entry := state.objects.find? (·.id.raw == tag) then
      return ← declarationPorts entry.declaration formalField expectedType args objects
    if let some entry := state.morphisms.find? (·.id.raw == tag) then
      return ← declarationPorts entry.declaration formalField expectedType args objects
    if let some entry := state.inclusions.find? (·.id.raw == tag) then
      return ← declarationPorts entry.declaration formalField expectedType args objects
    if let some (declaration, _) := state.callable? tag then
      return ← declarationPorts declaration formalField expectedType args objects
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
        return ← declarationPorts declaration application (← inferType application) parameters objects
      return ← declarationPorts declaration formalField expectedType parameters objects
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
      return ← declarationPorts declaration formalField expectedType parameters objects
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
        if let .error message ← validatePort field (← inferType field) data objects then
          return .error message
      return ← validateEndpointPort formalField typed.source typed.target typed.callable objects
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
      match ← validateAction functor action objects with
      | .error message => return .error message
      | .ok () => return ← validatePort source (← inferType source) sourceData objects
    if tag == "compose" then
      let #[firstData, secondData] := args
        | return .error "compose requires two ordered maps"
      let some selected ← retainedApplication ``CategoryTheory.CategoryStruct.comp formalField
        | return .error "composition requires its independently retained component contexts"
      let fields := selected.getAppArgs
      let first := fields[fields.size - 2]!
      let second := fields.back!
      for (field, data) in #[(first, firstData), (second, secondData)] do
        match ← validatePort field (← inferType field) data objects with
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
        match ← validatePort field (← inferType field) data objects with
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
      -- Resolve each factor's declared interface through retained data or its
      -- public descriptor, not through the formal universal object's factors.
      for data in #[leftData, rightData] do
        -- A nested product has the same already checked object category.
        -- Its fresh opaque children need no reconstructed semantic product:
        -- this placeholder is used only by recursive port validation below.
        let selected ← if (data.getObjValAs? String "ctor").toOption ==
            some "objectProduct" then do
          pure (.ok (← mkFreshExprMVar expectedType))
        else interfaceArgument objects expectedType data
        let .ok field := selected
          | return .error "the product factor lacks its complete retained object interface"
        match ← validatePort field expectedType data objects with
        | .error message => return .error message
        | .ok () => pure ()
      return .ok ()
    if tag == "coreObject" then
      let #[original] := args
        | return .error "a core object requires its complete original object"
      let some field ← recordProjection ``CategoryTheory.Core.of formalField
        | return .error "core data require their independently declared original-object projection"
      return ← validatePort field (← inferType field) original objects
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
        match ← validatePort field (← inferType field) data objects with
        | .error message => return .error message
        | .ok () => pure ()
      if let .error message ← validateEndpointPort mapField source target definingMap objects then
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
            match ← validateEndpointPort placeholder source source data objects with
            | .error message => return .error message
            | .ok () => pure ()
      return .ok ()
  -- Structural projection uses this same dispatch to distinguish a whole
  -- descriptor from exposed fields at each independently fixed nested record.
  if explicitOnly then return .error "the port has no applicable explicit envelope codec"
  if ← plainType expectedType then
    if let some literal := inlineLiteralData? json then
      return (← Codec.decode expectedType literal).map fun _ => ()
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
  -- A released structural record may contain types and dependent callable
  -- fields. Its independently fixed formal receiver supplies each projection's
  -- complete type; the reply supplies only data in the published field order.
  -- No constructor or proof is reconstructed from that data. In particular an
  -- opaque carrier cannot select the types or laws of later record fields.
  if let some result ← validateRecordPortWith formalField expectedType json objects
      (fun formal type data inputs => validatePort formal type data inputs) then
    return result
  return .error "the computational port has no supported released data representation"

/-- A finite map is complete at its actual supplied domain. Inventories are
computational data, never an enumeration of the requested formal construction. -/
partial def validateEndpointPort (formal : Expr) (source target data : Json)
    (objects : InterfaceObjects := #[]) :
    TermElabM (Except String Unit) := do
  let unwrapped ← match valuePayload data with
    | .ok actual => pure actual
    | .error message => return .error message
  if (unwrapped.getObjValAs? String "ctor").toOption == some "typedMap" then
    let .ok typed := Backend.TypedMap.decode unwrapped
      | return .error "typedMap requires its complete source, target and callable"
    unless typed.source == source && typed.target == target do
      return .error "the callable's complete endpoint descriptors differ from its selected computational endpoints"
    return ← validateEndpointPort formal source target typed.callable objects
  let graph := if let .ok ("finiteGraph", #[_, actual]) := envelope unwrapped then actual else unwrapped
  unless graph.getArr?.isOk do return ← validatePort formal (← inferType formal) data objects
  let domain ← match ← graphDomainKeys objects (interfaceArgument objects) source unwrapped endpointKeys with
    | .ok domain => pure domain
    | .error message => return .error message
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
  if tag == "cartesianMap" then
    let #[id, parameters, receiver] := args
      | return .error "the cartesian map requires its selected reindexing, parameters and receiver"
    let .ok id := id.getStr? | return .error "the reindexing id must be a string"
    let some entry := state.functor? ⟨id⟩ | return .error "the reindexing is not registered"
    unless entry.expression.registrationKind matches .familyReindex .. do
      return .error "the selected functor has no accepted family cartesian map"
    let .ok parameters := parameters.getArr? | return .error "reindexing parameters must be ordered"
    if let .error message ← validateDeclaredData entry.declaration parameters then
      return .error message
    return ← validatePublicData receiver
  if tag == "structuredProjectionAction" then
    let #[category, field] := args | return .error "the structured projection action is incomplete"
    let .ok field := field.getStr? | return .error "the structured field must be a string"
    unless #["source", "target", "inclusion"].contains field do
      return .error "the selected field has no declared object projection action"
    let .ok ("constructedCategory", _) := envelope category
      | return .error "the structured projection requires its complete constructed category"
    if let .error message ← validatePublicData category then return .error message
    return (← interfaceAction #[] data).map fun _ => ()
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
  if #["limitApex", "limitLeg", "constructionApex", "constructionLeg", "constructionField"].contains tag then
    let count := if tag == "limitApex" then 2 else
      if tag == "constructionLeg" || tag == "constructionField" then 4 else 3
    unless args.size == count do
      return .error "the construction projection omitted part of its complete receiver or index"
    let .ok id := args[0]!.getStr? | return .error "a construction id must be a string"
    unless state.limits.any (·.id.raw == id) do
      return .error "the construction is not registered"
    if tag == "constructionField" && !args[3]!.getNat?.isOk then
      return .error "the construction data-port index must be a natural number"
    for datum in args.extract 1 args.size do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "cone" || tag == "cocone" then
    if args.isEmpty then return .error "a complete construction requires its actual apex"
    for datum in args do
      if let .error message ← validatePublicData datum then return .error message
    return .ok ()
  if tag == "createdCone" || tag == "liftStep" then
    return ← validateLiftContext tag args data validatePublicData
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
          #["classifierForget", "constructorMap", "structuredProjectionAction"].contains actionTag do
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
          "arrowHom", "limitLeg", "constructionLeg", "constructionField", "subobjectInclusion", "identity",
          "zero", "admittedPoint", "constrainedPoint", "cellComponent",
          "constructedCellComponent", "coreIso", "cartesianMap"].contains tag then
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

/-- Point slots follow the actual public object representation. An extent keeps
its ambient point codec; its membership condition remains an unchecked part of
the computation and never becomes a proof or a replacement formal carrier.
After validating the descriptor, an opaque or context-dependent representation
may retain its independently fixed point interface. This supplies data slots,
never the requested object's members. An available actual interface always wins,
even when its point codec is unsupported. -/
partial def interfacePointSchema (objects : InterfaceObjects) (data : Json)
    (validatedContext : Option Expr := none) :
    TermElabM (Option PointSchema) := do
  if let .ok ("valueData", #[actual]) := envelope data then
    return ← interfacePointSchema objects actual validatedContext
  if let .ok ("finiteData", #[descriptor, _]) := envelope data then
    return ← interfacePointSchema objects descriptor validatedContext
  if let .ok ("objectPresentation", #[_, actual]) := envelope data then
    return ← interfacePointSchema objects actual validatedContext
  if let .ok ("extent", #[_, ambient, _]) := envelope data then
    let .ok ambientObject ← interfaceObject objects ambient | return none
    return ← objectPointSchema ambientObject
  match ← interfaceObject objects data with
  | .ok object => objectPointSchema object
  | .error _ =>
    match validatedContext with
    | some fixed => objectPointSchema fixed
    | none => return none

/-- Check an extent through its published power-object and subset-literal
interfaces. The subset occupies a fresh typed placeholder: no returned members,
membership proof or denotation is substituted into the formal construction. -/
partial def interfaceExtent (objects : InterfaceObjects) (args : Array Json) :
    TermElabM (Except String Expr) := do
  let #[id, ambient, subset] := args
    | return .error "extent requires its power object, ambient object and subset data"
  let .ok id := id.getStr? | return .error "the extent power-object id must be a string"
  let state ← registryState
  let some power := state.powerObjects.find? (·.id.raw == id)
    | return .error "the extent names no registered power object"
  let .ok ambientObject ← interfaceObject objects ambient
    | return .error "the extent requires its complete ambient object interface"
  let constant ← mkConstWithFreshMVarLevels power.extent
  let (fields, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  let explicit ← (fields.zip infos).filterMapM fun (field, info) => do
    if info.isExplicit && !(← isProp (← inferType field)) then return some field
    return none
  let #[ambientField, subsetField] := explicit
    | return .error "the published extent has no complete ambient-and-subset interface"
  unless ← withTransparency .all <| isDefEq (← inferType ambientObject) (← inferType ambientField) do
    return .error "the extent ambient object has a different declared category"
  unless ← withTransparency .all <| isDefEq ambientField ambientObject do
    return .error "the extent ambient object has incompatible complete parameters"
  let subsetType ← instantiateMVars (← inferType subsetField)
  let .ok actual := valuePayload subset
    | return .error "the extent subset has a malformed data wrapper"
  if actual.getArr?.isOk then
    let some literal := state.subsetLiterals.find? (·.powerObject == power.id)
      | return .error "the power object publishes no subset-literal data interface"
    let literalType ← mkAppM literal.type #[ambientObject]
    let some schema ← pointSchema literalType
      | return .error "the subset literal requires its complete point-data interface"
    if let .error message ← validatePoint schema actual then return .error message
    if let .error message ← endpointKeys (Json.mkObj [("ctor", toJson "extent"),
        ("args", Json.arr args)]) then return .error message
  else
    if let .error message ← validateCallableAt objects subsetType subset then
      return .error message
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
  if tag == "extent" then return ← interfaceExtent objects args
  if tag == "objectProduct" then
    let #[left, right] := args | return .error "a product endpoint requires both factors"
    let .ok left ← interfaceObject objects left | return .error "the first product factor is incomplete"
    let .ok right ← interfaceObject objects right | return .error "the second product factor is incomplete"
    unless (← whnfR (← inferType left)).isSort && (← whnfR (← inferType right)).isSort &&
        !(← isProp left) && !(← isProp right) do
      return .error "the product factors require their declared set-object interfaces"
    return .ok (← mkAppM ``Prod #[left, right])
  if tag == "arrow" then
    let #[source, target, callable] := args
      | return .error "a complete Arrow requires its source, target and defining map"
    let .ok sourceObject ← interfaceObject objects source
      | return .error "the complete Arrow source has no declared interface"
    let .ok targetObject ← interfaceObject objects target
      | return .error "the complete Arrow target has no declared interface"
    unless ← withTransparency .all <| isDefEq (← inferType sourceObject) (← inferType targetObject) do
      return .error "the complete Arrow endpoints belong to different selected categories"
    let homType ← mkAppM ``Quiver.Hom #[sourceObject, targetObject]
    let hom ← mkFreshExprMVar homType
    if let .error message ← validateCallableAt objects homType callable then
      return .error message
    if let .error message ← validateEndpointPort hom source target callable objects then
      return .error message
    return .ok (← mkAppM ``CategoryTheory.Arrow.mk #[hom])
  if tag == "coreObject" then
    let #[source] := args | return .error "a core object requires its complete original object"
    let .ok source ← interfaceObject objects source
      | return .error "the core object's selected source is incomplete"
    return .ok (← mkAppM ``CategoryTheory.Core.mk #[source])
  if tag == "objectPresentation" then
    let #[descriptor, actual] := args | return .error "the endpoint wrapper is incomplete"
    let .ok fixed ← interfaceObject objects descriptor
      | return .error "the presented object omitted its fixed complete action"
    if let .error message ← validatePort fixed (← inferType fixed) actual objects then
      return .error message
    return .ok fixed
  if tag == "finiteData" then
    let #[descriptor, _] := args | return .error "the endpoint wrapper is incomplete"
    return ← interfaceObject objects descriptor
  if tag == "functorAction" then
    let #[action, source] := args | return .error "an object action requires its selected source"
    let .ok action ← interfaceAction objects action | return .error "the endpoint action is incomplete"
    let .ok source ← interfaceObject objects source | return .error "the endpoint source is incomplete"
    let actionType ← whnfR (← inferType action)
    unless actionType.isAppOf ``CategoryTheory.Functor do
      return .error "the endpoint action has no declared functor interface"
    unless ← withoutModifyingState <| withTransparency .all <|
        isDefEq (← inferType source) actionType.getAppArgs[0]! do
      return .error "the endpoint receiver differs from the action's complete source category"
    return .ok (← Semantic.objOf action source)
  return .error "the symbolic endpoint requires its independently selected object context"

/-- Use the independently retained diagram when its presentation occurs in the
requested full field type. Otherwise the public diagram declaration supplies its
typed parameters; arbitrary callable data remain placeholders at those types. -/
partial def interfaceDiagram (objects : InterfaceObjects) (row : LimitEntry)
    (expected : Expr) (data : Json) (fixed : Option Expr := none) :
    TermElabM (Except String (Expr × InterfaceObjects)) := do
  let some constructor ← Semantic.diagramConstructor row
    | return .error "the registered construction has no public diagram declaration"
  let .ok (tag, parameters) := envelope data
    | return .error "the construction omitted its complete diagram"
  unless tag == Codec.label constructor do
    return .error "the construction changed its registered diagram constructor"
  let .ok diagram ← interfaceDeclaration objects constructor expected parameters
    | return .error "the diagram has incompatible complete ordered parameters"
  let diagram ← match fixed with
    | none => pure diagram
    | some fixed =>
      unless ← withTransparency .all <| isDefEq (← inferType fixed) expected do
        return .error "the retained diagram has a different complete selected category"
      unless ← withTransparency .all <| isDefEq diagram fixed do
        return .error "the supplied diagram changes a fixed complete input interface"
      pure fixed
  let infos ← forallTelescopeReducing (← getConstInfo constructor).type fun fields _ =>
    fields.mapM (·.fvarId!.getBinderInfo)
  let normalized ← withTransparency .all <| whnfHeadPred diagram fun term =>
    pure (term.getAppFn.constName? != some constructor)
  unless normalized.getAppFn.constName? == some constructor do
    return .error "the retained diagram lost its declared constructor interface"
  let explicit := (normalized.getAppArgs.zip infos).filterMap fun (field, info) =>
    if info.isExplicit then some field else none
  unless explicit.size == parameters.size do
    return .error "the retained diagram changed its complete parameter count"
  return .ok (diagram, parameters.zip explicit)

/-- Recover a complete canonical presentation only from the independent expected
type. The receiver packet itself cannot add a proof or a universal property. -/
partial def retainedConstructions (row : LimitEntry) (expected : Expr) :
    TermElabM (Array Expr) := do
  let projection := if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone
  let arity ← forallTelescopeReducing (← getConstInfo projection).type
    fun fields _ => pure fields.size
  let presentations ← IO.mkRef (#[] : Array Expr)
  expected.forEach fun expression => do
    if expression.isAppOfArity projection arity then
      let presentation := expression.getAppArgs.back!
      if (presentation.find? (fun term => term.isAppOf row.declaration)).isSome then
        presentations.modify fun current =>
          if current.contains presentation then current else current.push presentation
  presentations.get

/-- A returned diagram mismatch is a framing error. Internal failures of the
accepted declaration remain internal failures. -/
partial def interfaceLimitPresentation (row : LimitEntry) (diagram : Expr) :
    TermElabM (Except String Expr) := do
  try return .ok (← Semantic.limitPresentation row diagram)
  catch error =>
    if CasCatalogue.Exception.interpretationKind error == .invalid then
      return .error "the diagram is outside the registered presentation's complete interface"
    throw error

/-- Encode an independently fixed signature parameter, preferring its retained
actual descriptor. This is metadata for a type check, never a computational
answer synthesized from a formal construction. -/
partial def interfaceEncoding (objects : InterfaceObjects) (formal : Expr) :
    TermElabM (Except String Json) := do
  let formal ← instantiateMVars formal
  if let some (data, _) := objects.find? (·.2 == formal) then return .ok data
  let state ← registryState
  let head := formal.getAppFn.constName?
  let entry := (state.objects.find? (fun row => some row.declaration == head)).map
      (fun row => (row.id.raw, row.declaration, false)) <|>
    (state.categories.find? (fun row => some row.declaration == head)).map
      (fun row => (row.id.raw, row.declaration, true))
  if let some (id, declaration, category) := entry then
    let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
      fields.mapM (·.fvarId!.getBinderInfo)
    let mut parameters := #[]
    for (field, info) in formal.getAppArgs.zip infos do
      if !info.isExplicit || (← isProp (← inferType field)) then continue
      let .ok data ← interfaceEncoding objects field
        | return .error "a complete declared signature parameter has no retained data descriptor"
      parameters := parameters.push data
    return .ok (if category then Backend.CategoryParameter.encode { category := id, parameters }
      else Json.mkObj [("ctor", toJson id), ("args", Json.arr parameters)])
  if let .ok data ← Codec.encode formal then return .ok data
  return .error "the complete signature parameter requires its independently retained descriptor"

/-- The creation row fixes its action. Its complete ordered parameters are
recovered from that fixed declaration application, never from returned fields. -/
partial def interfaceEdgeEncoding (objects : InterfaceObjects) (edge : EdgeRef) (action : Expr) :
    TermElabM (Except String Json) := do
  let state ← registryState
  if let .constructMap constructor inner := edge then
    let .ok inner ← interfaceEdgeEncoding objects inner action
      | return .error "the creation action has an incomplete inner parameter interface"
    return .ok (Json.mkObj [("ctor", "constructorMap"),
      ("args", Json.arr #[toJson constructor.raw, inner])])
  let declaration : Option Name := match edge with
    | .functor id => (state.functor? id).map (fun (row : FunctorEntry) => row.declaration)
    | .classifierForget id => (state.classifiers.find? (fun row => row.id == id)).map
        (fun (row : ClassifierEntry) => row.declaration)
    | _ => none
  let some declaration := declaration | return .error "the creation action is not registered"
  let some application ← retainedApplication declaration (← instantiateMVars action)
    | return .error "the creation action lost its complete accepted declaration application"
  let infos ← forallTelescopeReducing (← getConstInfo declaration).type fun fields _ =>
    fields.mapM (·.fvarId!.getBinderInfo)
  let mut parameters := #[]
  for (field, info) in application.getAppArgs.zip infos do
    if !info.isExplicit || (← isProp (← inferType field)) then continue
    let .ok data ← interfaceEncoding objects field
      | return .error "the creation action omitted an independently fixed parameter descriptor"
    parameters := parameters.push data
  return .ok (match edge with
    | .functor id => Json.mkObj [("ctor", toJson id.raw), ("args", Json.arr parameters)]
    | .classifierForget id => Json.mkObj [("ctor", "classifierForget"),
        ("args", Json.arr #[toJson id.raw, Json.arr parameters])]
    | _ => unreachable!)

/-- Instantiate a declared construction and, where present, its exact creation
lift. Standardization is selected by the registered row's comparison, never by
the spelling of a diagram shape. -/
partial def constructionInterface (objects : InterfaceObjects) (row : LimitEntry)
    (diagramData : Json) (packet : Option Json) (retained : Option Expr := none) :
    TermElabM (Except String ConstructionInterface) := do
  let state ← registryState
  let fixedDiagram ← retained.mapM fun presentation =>
    return (← whnfR (← inferType presentation)).getAppArgs.back!
  let family ← instantiateFresh row.declaration
  let declaredDiagram := (← whnfR (← inferType family)).getAppArgs.back!
  let declaredType ← whnfR (← inferType declaredDiagram)
  unless declaredType.isAppOfArity ``CategoryTheory.Functor 4 do
    return .error "the construction has no complete declared diagram category"
  let mut answer := packet
  let mut creation : Option (LiftEntry × Expr) := none
  let diagramType ← match packet with
    | some data =>
      if let .ok ("createdCone", #[id, source, target]) := envelope data then
        let .ok id := id.getStr? | return .error "the creation lift id is not a string"
        let some lift := state.lifts.find? (·.id.raw == id)
          | return .error "the creation lift is not registered"
        unless !row.colimit && lift.kind == .createsLimits row.shape && source == diagramData do
          return .error "the creation packet changes its fixed construction or complete source diagram"
        let some edge := state.structuralEdge? lift.edge
          | return .error "the creation packet has no registered structural action"
        let some category := state.categories.find? (·.id == row.category)
          | return .error "the construction category is not registered"
        unless edge.target.syntacticEq category.expression do
          return .error "the creation action does not reach the registered construction category"
        let action ← Semantic.asFunctor (← Semantic.edgeFunctor state lift.edge)
        let actionType ← whnfR (← inferType action)
        unless actionType.isAppOfArity ``CategoryTheory.Functor 4 do
          return .error "the creation action has no complete category parameters"
        let actionArguments := actionType.getAppArgs
        let diagramArguments := declaredType.getAppArgs
        unless ← withTransparency .all <| isDefEq actionArguments[2]! diagramArguments[2]! <&&>
            isDefEq actionArguments[3]! diagramArguments[3]! do
          return .error "the creation action changes the selected target category dictionary"
        creation := some (lift, action)
        answer := some target
        mkAppOptM ``CategoryTheory.Functor #[some diagramArguments[0]!,
          some diagramArguments[1]!, some actionArguments[0]!, some actionArguments[1]!]
      else pure declaredType
    | none => pure declaredType
  let .ok (diagram, inputs) ← interfaceDiagram objects row diagramType diagramData fixedDiagram
    | return .error "the construction has no compatible complete retained diagram"
  let (presentation, dataDiagram, dataPresentation, dataInputs, comparison) ← match creation with
    | none =>
      let .ok presentation ← interfaceLimitPresentation row diagram
        | return .error "the source diagram is outside the declared presentation interface"
      pure (presentation, diagram, presentation, inputs, none)
    | some (lift, action) =>
      let mapped ← withTransparency .all <| mkFunctorComp diagram action
      let .ok lower ← interfaceLimitPresentation row mapped
        | return .error "the selected creation action has no compatible target presentation"
      let evidence ← instantiateFresh lift.evidence
      let actionType ← whnfR (← inferType action)
      let diagramType ← whnfR (← inferType diagram)
      let a := actionType.getAppArgs
      let d := diagramType.getAppArgs
      let evidenceType ← mkAppOptM ``CategoryTheory.CreatesLimitsOfShape
        #[some a[0]!, some a[1]!, some a[2]!, some a[3]!, some d[0]!, some d[1]!, some action]
      unless ← withTransparency .all <| isDefEq (← inferType evidence) evidenceType do
        return .error "the creation evidence changes the full selected action or diagram shape"
      let presentation ← withTransparency .all <| mkAppOptM ``CasCatalogue.liftedLimitCone
        #[some a[0]!, some a[1]!, some a[2]!, some a[3]!, some d[0]!, some d[1]!,
          some action, some evidence, some diagram, some lower]
      let some constructor ← Semantic.diagramConstructor row
        | return .error "the creation target has no declared diagram constructor"
      let mappedArguments ← inputs.mapM fun (_, formal) => do
        if (Language.homEnds? (← inferType formal)).isSome then Semantic.mapOf action formal
        else Semantic.objOf action formal
      let dataDiagram ← mkAppM constructor mappedArguments
      let comparison ← match row.standardization with
        | some declaration => mkAppM declaration #[mapped]
        | none =>
          unless ← withTransparency .all <| isDefEq mapped dataDiagram do
            return .error "the creation packet requires a registered diagram standardization comparison"
          mkAppM ``CategoryTheory.Iso.refl #[mapped]
      let comparison ← instantiateMVars comparison
      unless ← withTransparency .all <| isDefEq (← inferType comparison)
          (← mkAppM ``CategoryTheory.Iso #[mapped, dataDiagram]) do
        return .error "the registered creation comparison has different complete diagram endpoints"
      if comparison.hasMVar || comparison.hasLevelMVar || !(← isTypeCorrect comparison) then
        return .error "the creation comparison has unresolved independent parameters"
      let .ok dataPresentation ← interfaceLimitPresentation row dataDiagram
        | return .error "the standardized target diagram has no compatible presentation"
      let .ok descriptor ← interfaceEdgeEncoding (objects ++ inputs) lift.edge action
        | return .error "the selected creation action has incomplete retained parameters"
      let dataInputs ← (inputs.zip mappedArguments).mapM fun ((data, formal), mapped) => do
        let tag := if (Language.homEnds? (← inferType formal)).isSome then "map" else "functorAction"
        return (Json.mkObj [("ctor", toJson tag), ("args", Json.arr #[descriptor, data])], mapped)
      pure (presentation, dataDiagram, dataPresentation, dataInputs, some comparison)
  if let some retained := retained then
    unless ← withTransparency .all <| isDefEq presentation retained do
      return .error "the packet changes its independently retained complete construction or creation lift"
  let result : ConstructionInterface := {
    row := row
    diagram := diagram
    presentation := presentation
    dataDiagram := dataDiagram
    dataPresentation := dataPresentation
    inputs := inputs
    dataInputs := dataInputs
    answer := answer
    comparison := comparison }
  return .ok result

/-- The endpoint producer distinguishes a checked projection from new action
work and metadata recovered from a formal signature. Returned field bytes do
not determine this origin. -/
inductive EndpointDataOrigin where
  | projection
  | formal
  | action
  deriving BEq, Inhabited

structure EndpointProjectionData where
  data : DataOwnership.Data
  origin : EndpointDataOrigin

/-- Project a declared input's endpoint while retaining exact data occurrences.
This shared traversal also serves metadata-only validation: it does not invent
suppliers when the caller has no runtime table. Runtime callers validate complete
coverage before and after projection. A computed anonymous callable uses its
own endpoint reference rather than reconstructing a formal named object. -/
partial def interfaceEndpointDataWithOrigin (objects : InterfaceObjects) (formal : Expr)
    (data : DataOwnership.Data) (source : Bool) (recoverFormal : Bool := true) :
    TermElabM (Except String EndpointProjectionData) := do
  let fieldData := fun (data : DataOwnership.Data) (json : Json) (index : Nat) =>
    ({ json, ownership := DataOwnership.project #[.field "args", .index index]
        data.ownership } : DataOwnership.Data)
  if (data.json.getObjValAs? String "ctor").toOption == some "valueData" then
    let .ok (.inline child) := Backend.ComputationalValue.decode data.json
      | return .error "the input callable envelope is incomplete"
    return ← interfaceEndpointDataWithOrigin objects formal (fieldData data child 0) source recoverFormal
  match envelope data.json with
  | .ok ("typedMap", #[left, right, _]) | .ok ("arrow", #[left, right, _]) =>
    return .ok { data := (fieldData data (if source then left else right)
      (if source then 0 else 1)), origin := .projection }
  | .ok ("identity", #[left, right]) | .ok ("zero", #[left, right]) =>
    return .ok { data := (fieldData data (if source then left else right)
      (if source then 0 else 1)), origin := .projection }
  | .ok ("compose", #[first, second]) =>
    let some application ← retainedApplication ``CategoryTheory.CategoryStruct.comp formal
      | return .error "the composed input has no independently retained complete components"
    let fields := application.getAppArgs
    return ← interfaceEndpointDataWithOrigin objects
      (if source then fields[fields.size - 2]! else fields.back!)
      (fieldData data (if source then first else second) (if source then 0 else 1)) source recoverFormal
  | .ok ("map", #[action, original]) =>
    let some application ← retainedApplication ``CategoryTheory.Functor.map formal
      | return .error "the mapped input has no independently retained complete action"
    let .ok endpoint ← interfaceEndpointDataWithOrigin objects application.getAppArgs.back!
        (fieldData data original 1) source recoverFormal
      | return .error "the mapped input omitted an original complete endpoint"
    return .ok { origin := .action, data := {
      json := Json.mkObj [("ctor", "functorAction"),
        ("args", Json.arr #[action, endpoint.data.json])]
      ownership := DataOwnership.prefix #[.field "args", .index 0] (fieldData data action 0).ownership ++
        DataOwnership.prefix #[.field "args", .index 1] endpoint.data.ownership } }
  | _ =>
    let some (left, right) := Language.homEnds? (← inferType formal)
      | return .error "the construction input is not a complete callable"
    if recoverFormal then
      if let .ok endpoint ← interfaceEncoding objects (if source then left else right) then
        return .ok { data := { json := endpoint }, origin := .formal }
    return .ok { origin := .projection, data := {
      json := Backend.MorphismEndpoint.encode { callable := data.json, source }
      ownership := DataOwnership.prefix #[.field "args", .index 0] data.ownership } }

/-- The existing public traversal retains its data-only interface. Runtime
producers can also retain the origin supplied by the same traversal. -/
def interfaceEndpointData (objects : InterfaceObjects) (formal : Expr)
    (data : DataOwnership.Data) (source : Bool) (recoverFormal : Bool := true) :
    TermElabM (Except String DataOwnership.Data) := do
  return (← interfaceEndpointDataWithOrigin objects formal data source recoverFormal).map (·.data)

/-- Metadata-only projection uses the same complete endpoint traversal without
claiming runtime ownership. Its caller retains the independent formal interface. -/
partial def interfaceEndpointEncoding (objects : InterfaceObjects) (formal : Expr)
    (data : Json) (source : Bool) : TermElabM (Except String Json) := do
  return (← interfaceEndpointData objects formal { json := data } source).map (·.json)

/-- Restore constructor input roles without inspecting or identifying any
returned object with its formal counterpart. -/
partial def constructionInputs (context : ConstructionInterface) (plan : StructuredResult.DataPlan)
    (objects : InterfaceObjects) : TermElabM (Except String (Array (Nat × Json))) := do
  let mut external := #[]
  for binder in plan.binders do
    if binder.port.isSome then continue
    let some role := binder.inputRoles[0]? | continue
    let (position, source) := match role with
      | .argument position => (position, none)
      | .source position => (position, some true)
      | .target position => (position, some false)
    let some (data, formal) := context.dataInputs[position]?
      | return .error "the construction omitted an independent diagram input"
    let data ← match source with
      | none => pure data
      | some source =>
        let .ok data ← interfaceEndpointEncoding objects formal data source
          | return .error "the construction input omitted its complete endpoint context"
        pure data
    external := external.push (binder.index, data)
  return .ok external

/-- Check every actual returned field at the registered dependent data plan.
Earlier returned objects determine the computational endpoint representations;
the independent diagram fixes external endpoint types. No field supplies a law. -/
partial def validateConstructionData (objects : InterfaceObjects) (context : ConstructionInterface) :
    TermElabM (Except String Unit) := do
  let some answer := context.answer | return .ok ()
  let .ok plan ← StructuredResult.dataPlan context.row context.dataDiagram context.dataPresentation
    | return .error "the construction has no complete independently fixed data-port schema"
  let .ok external ← constructionInputs context plan objects
    | return .error "the construction lost its independent complete input roles"
  let externalDescriptor := fun binder => (external.find? (·.1 == binder)).map (·.2)
  StructuredResult.validatePlannedData plan answer fun port seen data => do
    let actual := (valuePayload data).toOption.getD data
    if let .ok typed := Backend.TypedMap.decode actual then
      let some (source, target) := Language.homEnds? port.expectedType
        | return .error "a construction object port cannot contain a typed callable"
      for (binder, descriptor) in #[(port.domainBinder, typed.source), (port.codomainBinder, typed.target)] do
        if let some binder := binder then
          if let some fixed := plan.actualData? binder seen then
            unless fixed == descriptor do
              return .error "a construction callable changes an earlier actual returned endpoint"
      let retained : InterfaceObjects := objects ++ plan.binders.filterMap fun binding => do
        let formal ← binding.formalValue
        let actual ← if binding.port.isSome then plan.actualData? binding.index seen
          else externalDescriptor binding.index
        return (actual, formal)
      for (fixed, descriptor) in #[(source, typed.source), (target, typed.target)] do
        let .ok declared ← interfaceArgument retained (← inferType fixed) descriptor
          | return .error "a construction callable has an incomplete external endpoint"
        unless ← withTransparency .all <| isDefEq fixed declared do
          return .error "a construction callable changes a complete fixed diagram endpoint"
      return ← validateEndpointPort port.formalField typed.source typed.target typed.callable retained
    validatePlannedPort plan port seen data externalDescriptor endpointKeys

/-- A defining-map descriptor is checked as a projection of the entire accepted
construction interface. Its computational packet is validated but never used to
reconstruct a mathematical cone, admission or universal-property proof. -/
partial def validateConstructionProjectionAt (objects : InterfaceObjects) (row : LimitEntry)
    (expected : Expr) (tag : String) (args : Array Json) (retained : Option Expr) :
    TermElabM (Except String Unit) := do
  let count := args.size
  let packet := if tag == "limitLeg" then none else some args[2]!
  let .ok context ← constructionInterface objects row args[1]! packet retained
    | return .error "the construction projection has no compatible complete retained interface"
  let value ← if tag == "constructionField" then do
      let .ok index := args[3]!.getNat? | return .error "a construction field requires its natural port index"
      let .ok plan ← StructuredResult.dataPlan row context.diagram context.presentation
        | return .error "the source construction has no complete data-port projection interface"
      let some port := plan.ports[index]?
        | return .error "the projection is outside the registered complete data-port schema"
      pure port.formalField
    else do
      let diagramType ← whnfR (← inferType context.diagram)
      let .ok index ← Codec.decode diagramType.getAppArgs[0]! args[count - 1]!
        | return .error "the defining leg changed its exact diagram-index type"
      let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
        else ``CategoryTheory.Limits.LimitCone.cone) #[context.presentation]
      let maps ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.ι
        else ``CategoryTheory.Limits.Cone.π) #[cone]
      mkAppM ``CategoryTheory.NatTrans.app #[maps, index]
  unless ← withTransparency .all <| isDefEq (← inferType value) expected do
    return .error "the construction projection changes a complete selected endpoint or field type"
  let fixed ← instantiateMVars value
  if fixed.hasMVar || fixed.hasLevelMVar then
    return .error "the construction projection omitted an independent complete formal input"
  validateConstructionData objects context

/-- Every complete occurrence is considered with its requested projection type.
Nested constructions of the same row cannot select a source or target merely by
their traversal order. Validation does not choose a new mathematical witness. -/
partial def validateConstructionProjection (objects : InterfaceObjects) (expected : Expr)
    (tag : String) (args : Array Json) (formal : Option Expr := none) :
    TermElabM (Except String Unit) := do
  let count := if tag == "limitLeg" then 3 else 4
  unless args.size == count do
    return .error "the construction projection omitted its complete receiver or index"
  let .ok id := args[0]!.getStr? | return .error "the construction projection has no registered id"
  let some row := (← registryState).limits.find? (·.id.raw == id)
    | return .error "the construction projection names no registered presentation"
  let retained ← retainedConstructions row expected
  let retained ← match formal with
    | none => pure retained
    | some value => do
      let actual ← retainedConstructions row value
      pure ((retained ++ actual).toList.eraseDups.toArray)
  let candidates := if retained.isEmpty then #[none] else retained.map some
  let mut accepted := false
  let mut failure := "the construction projection has no compatible complete retained interface"
  for candidate in candidates do
    match ← withoutModifyingState <|
        validateConstructionProjectionAt objects row expected tag args candidate with
    | .ok () => accepted := true
    | .error message => failure := message
  return if accepted then .ok () else .error failure

partial def interfaceAction (objects : InterfaceObjects) (data : Json) :
    TermElabM (Except String Expr) := do
  let .ok (tag, args) := envelope data | return .error "the action requires a public descriptor"
  let state ← registryState
  if tag == "structuredProjectionAction" then
    let #[category, field] := args | return .error "the structured projection action is incomplete"
    let .ok field := field.getStr? | return .error "the structured field must be a string"
    unless #["source", "target", "inclusion"].contains field do
      return .error "the structured field has no accepted projection functor"
    let .ok ("constructedCategory", #[id, parameters]) := envelope category
      | return .error "the structured projection has no complete constructed category"
    let .ok id := id.getStr? | return .error "the category constructor id must be a string"
    let .ok parameters := parameters.getArr? | return .error "constructor arguments must be ordered"
    let some row := state.constructor? ⟨id⟩ | return .error "the category constructor is not registered"
    unless row.signature == #[ConstructorArgKind.category] && parameters.size == 1 do
      return .error "the selected constructor has no unary category projection interface"
    let .ok bundle ← interfaceDeclaration objects row.semantics
        (← inferType (← instantiateFresh row.semantics)) parameters
      | return .error "the constructed category arguments have incompatible complete types"
    let carrier ← StructuredProjection.interfaceType
      (← mkAppM ``CategoryTheory.Bundled.α #[bundle])
    let arrow ← if carrier.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory then
        withLocalDeclD `selected carrier fun value => do
          StructuredProjection.interfaceType
            (← inferType (← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[value]))
      else pure carrier
    unless arrow.isAppOfArity ``CategoryTheory.Arrow 2 do
      return .error "the accepted constructor has no actual Arrow or full-subcategory projection"
    return .ok (← StructuredProjection.projectionFunctorOfBundle bundle field)
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
        #["objectProduct", "finiteData", "extent", "functorAction", "objectPresentation", "coreObject"].contains tag then
      let .ok object ← interfaceObject objects data
        | return .error "the object parameter has no complete declared interface"
      unless ← withTransparency .all <| isDefEq (← inferType object) expected do
        return .error "the object parameter has a different selected category"
      return .ok object
  if ← plainType expected then return ← Codec.decode expected data
  let placeholder ← mkFreshExprMVar expected
  let .ok () ← validatePort placeholder expected data objects
    | return .error "the symbolic parameter has no supported declared data representation"
  return .ok placeholder

/-- Recover only the published admission's complete input and result interfaces.
The ordered prefix is declaration data; the admitted value and every subsequent
hypothesis remain fresh placeholders. No returned field supplies evidence of
membership or a law of the admitted object. -/
partial def admissionInterface (objects : InterfaceObjects) (entry : ObjectEntry)
    (expected : Expr) (parameters : Array Json) :
    TermElabM (Except String Expr) := do
  let some declaration := entry.admission
    | return .error "the selected object has no registered admission"
  let constant ← mkConstWithFreshMVarLevels declaration
  let (fields, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
  let some (_, target) := Language.homEnds? result
    | return .error "the registered admission has no complete point interface"
  let some (_, fixedTarget) := Language.homEnds? expected
    | return .error "the admitted result has no independently fixed target"
  let explicit := (List.range fields.size).toArray.filter (infos[·]!.isExplicit)
  let some valueIndex := explicit.find? fun index =>
      (result.findMVar? (· == fields[index]!.mvarId!)).isNone
    | return .error "the registered admission has no original data binder"
  unless target.headBeta.getAppFn.constName? == some entry.declaration do
    return .error "the admission does not belong to the selected published object"
  let mut fixedTarget := fixedTarget.consumeMData.headBeta
  while fixedTarget.isAppOfArity ``id 2 do
    fixedTarget := fixedTarget.appArg!.consumeMData.headBeta
  unless fixedTarget.getAppFn.constName? == some entry.declaration do
    return .error "the admission changes the independently selected named object"
  unless ← withTransparency .all <| isDefEq result expected do
    return .error "the admission changes its complete declared result endpoints"
  let mut position := 0
  for index in explicit.filter (· < valueIndex) do
    let field := fields[index]!
    let type ← instantiateMVars (← inferType field)
    if ← isProp type then continue
    let some data := parameters[position]?
      | return .error "the admission omitted an ordered declaration parameter"
    let .ok argument ← interfaceArgument objects type data
      | return .error "an admission parameter has a different complete declared type"
    unless ← withTransparency .all <| isDefEq field argument do
      return .error "an admission parameter changes its fixed selected structure"
    position := position + 1
  unless position == parameters.size do
    return .error "the admission added an ordered declaration parameter"
  let input ← instantiateMVars (← inferType fields[valueIndex]!)
  unless ← withTransparency .all <| isDefEq result expected do
    return .error "the admission parameters change its complete result endpoints"
  if input.hasMVar || input.hasLevelMVar then
    return .error "the admission lacks its complete original data type"
  if let some inclusion := entry.inclusion then
    let inclusionType ← mkAppM ``Quiver.Hom #[← instantiateMVars target, input]
    if let .error message ← interfaceDeclaration objects inclusion inclusionType parameters then
      return .error s!"the admission disagrees with its declared inclusion: {message}"
  return .ok input

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
    | "cartesianMap", #[id, parameters, receiverData] =>
      let .ok id := id.getStr? | return .error "the cartesian reindexing id must be a string"
      let some entry := state.functor? ⟨id⟩ | return .error "the family reindexing is not registered"
      let .familyReindex familyId := entry.expression.registrationKind
        | return .error "the selected functor has no accepted cartesian-map interface"
      let some family := state.categoryFamily? familyId
        | return .error "the reindexing has no accepted family realization"
      let .ok parameters := parameters.getArr? | return .error "reindexing parameters must be ordered"
      let .ok selected ← interfaceDeclaration objects entry.declaration
          (← inferType (← instantiateFresh entry.declaration)) parameters
        | return .error "the cartesian map has incompatible complete declaration parameters"
      let action ← Semantic.asFunctor selected
      let (sourceBundle, _) ← functorCategoryBundles action
      let .ok receiver ← interfaceArgument objects
          (← mkAppM ``CategoryTheory.Bundled.α #[sourceBundle]) receiverData
        | return .error "the cartesian map receiver has a different complete selected fibre"
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type
        fun fields _ => fields.mapM (·.fvarId!.getBinderInfo)
      let mut matchingCount := 0
      for (argument, info) in selected.getAppArgs.zip infos do
        unless info.isExplicit do continue
        let some (baseSource, baseTarget) := Language.homEnds? (← inferType argument)
          | continue
        let compatible ← withoutModifyingState do
          let realization ← mkConstWithFreshMVarLevels family.realization
          let canonicalFamily ← mkAppM ``CasCatalogue.CategoryFamilyRealization.reindexFunctor #[realization]
          let (arguments, _, _) ← forallMetaTelescopeReducing (← inferType canonicalFamily)
          let some base := arguments.back? | return false
          unless ← withTransparency .all <| isDefEq (← inferType base) (← inferType argument) <&&>
              isDefEq base argument <&&> isDefEq (mkAppN canonicalFamily arguments) action do return false
          let transport ← mkAppM ``CasCatalogue.CategoryFamilyRealization.transport #[realization]
          let value ← withTransparency .all <|
            mkAppOptM ``CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift
              #[none, none, some transport, some baseSource, some baseTarget,
                some receiver, some argument]
          withTransparency .all <| isDefEq (← inferType value) expected
        if compatible then matchingCount := matchingCount + 1
      unless matchingCount == 1 do
        return .error "the cartesian map does not retain one exact base-map signature and full endpoints"
      return .ok ()
    | "valueData", #[value] => return ← validateCallableAt objects expected value
    | "opaqueData", _ => return (Backend.ComputationalValue.decode data).map fun _ => ()
    | "arrowHom", #[receiver] | "subobjectInclusion", #[receiver] =>
      let .ok receiver := valuePayload receiver
        | return .error "the stored-map projection has an incomplete receiver envelope"
      let .ok (receiverTag, _) := envelope receiver
        | return .error "the stored-map projection requires a complete structured receiver"
      unless #["arrow", "subobject", "functorAction", "objectPresentation", "liftedSubobject"].contains
          receiverTag do
        return .error "the stored-map receiver has no complete declared Arrow interface"
      if tag == "subobjectInclusion" && receiverTag == "arrow" then
        return .error "the inclusion requires its complete subobject receiver"
      let mut receivers ← retainedRecordReceivers expected
      if let .ok fixed ← interfaceObject objects receiver then
        unless receivers.contains fixed do receivers := receivers.push fixed
      let mut accepted := false
      let mut failure := "the stored-map receiver has no independently fixed structured interface"
      for fixed in receivers do
        let result ← withoutModifyingState do
          let refined ← recordProjection ``CategoryTheory.ObjectProperty.FullSubcategory.obj fixed
          if tag == "subobjectInclusion" && refined.isNone then
            return .error "the inclusion receiver is not a declared full subcategory of Arrow"
          let arrow := refined.getD fixed
          let some hom ← recordProjection ``CategoryTheory.Arrow.hom arrow
            | return .error "the receiver has no complete stored Arrow map"
          unless ← withTransparency .all <| isDefEq (← inferType hom) expected do
            return .error "the stored-map projection changes a complete selected endpoint"
          return ← validatePort fixed (← inferType fixed) receiver objects
        match result with
        | .ok () => accepted := true
        | .error message => failure := message
      return if accepted then .ok () else .error failure
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
      let unwrapped ← match valuePayload callable with
        | .ok actual => pure actual
        | .error message => return .error message
      let graph := if let .ok ("finiteGraph", #[_, graph]) := envelope unwrapped then graph
        else unwrapped
      if graph.getArr?.isOk then
        let checked ← withoutModifyingState <|
          validateEndpointPort placeholder sourceData targetData callable objects
        return ← validateCallableGraphAt objects (interfaceArgument objects)
          (validateCallableAt objects) target sourceData targetData unwrapped graph checked
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
      let some entry := state.objects.find? (·.id.raw == admitted.object)
        | return .error "the admitted point names no registered object"
      let .ok (targetOwner, _) := envelope admitted.target
        | return .error "the admitted point omitted its selected named target descriptor"
      unless targetOwner == entry.id.raw do
        return .error "the admitted target descriptor belongs to a different named object"
      let .ok input ← admissionInterface objects entry expected admitted.parameters
        | return .error "the admitted point changes its registered admission or complete parameters"
      let .ok domain ← interfaceObject objects admitted.domain | return .error "the admitted domain is incomplete"
      let .ok original ← interfaceObject objects admitted.source | return .error "the original endpoint is incomplete"
      let .ok selected ← interfaceObject objects admitted.target | return .error "the admitted endpoint is incomplete"
      unless ← withTransparency .all <| isDefEq target selected do
        return .error "the admitted point changes its complete selected endpoint"
      let selected ← admissionInputHom expected source domain original input
      let (pointInput, originalType) ← match selected with
        | .ok selected => pure selected
        | .error message => return .error message
      let checked ← withoutModifyingState <|
        validateCallableAt objects originalType admitted.argument
      if checked.isOk then return checked
      -- A different declared global domain (for example PUnit) keeps its full
      -- callable. Only this exact selected source has the scalar-data convention.
      unless pointInput && (← withoutModifyingState (withTransparency .all <|
          isDefEq domain (← Language.globalPointSource.run {}))) do return checked
      -- Function-valued point data retain their own complete internal Hom.
      -- This path starts from a declared full Hom or function type, never from
      -- erasing a structured Hom's laws or choosing a category by its carrier.
      if let some inputType ← declaredCallableType? input then
        return ← validateCallableAt objects inputType admitted.argument
      return ← validatePort (← mkFreshExprMVar input) input admitted.argument objects
    | "pointView", #[selectedData, original, domainData] =>
      let .ok domain ← interfaceObject objects domainData | return .error "the point view domain is incomplete"
      let .ok selected ← interfaceObject objects selectedData | return .error "the selected point view is incomplete"
      let .ok carrier ← interfaceCarrier selected selectedData objects | return .error "the point view has no declared carrier"
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
      let .ok carrier ← interfaceCarrier selected selectedData objects | return .error "the nullary selection has no carrier"
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
      let .ok carrier ← interfaceCarrier selected descriptor objects
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
      if #["constructionLeg", "constructionField", "limitLeg"].contains tag then
        return ← validateConstructionProjection objects expected tag args
  validatePort placeholder expected data objects

/-- Use the complete validated selection to obtain its declared carrier. An
accepted object action need not have a separately registered name at its target. -/
partial def interfaceCarrier (selected : Expr) (descriptor : Json)
    (objects : InterfaceObjects := #[]) :
    TermElabM (Except String Expr) := do
  if ← isType selected then return .ok selected
  let .ok value ← interfaceSelectedValue objects selected descriptor
    | return .error "the selected object has no complete declared carrier context"
  return .ok (← (Language.semanticObject (← (Language.carrierObject value).run {})).run {})

/-- Transparent computational wrappers do not turn an anonymous representation
into a selected mathematical object. Only the enclosed named/action descriptor
can supply selection syntax; anonymous data require an exact retained binding. -/
partial def hasSelectedObjectDescriptor (state : RegistryState) (descriptor : Json) : Bool :=
  match envelope descriptor with
  | .ok ("finiteData", #[underlying, _]) |
      .ok ("objectPresentation", #[underlying, _]) => hasSelectedObjectDescriptor state underlying
  | .ok (tag, _) => state.objects.any (·.id.raw == tag) || tag == "functorAction"
  | .error _ => false

/-- A packet without selection syntax can retain an independently fixed source
of an accepted action. Its exact input binding and the action's complete source
bundle supply that interface; neither a carrier match nor a missing parameter
can choose it. Named and action descriptors keep their recursive validation. -/
partial def interfaceActionSource (objects : InterfaceObjects) (original : Expr)
    (descriptor : Json) (action bundle : Expr) (expression : Option CategoryExpr) :
    TermElabM (Except String (Option Language.Value)) := do
  let original ← instantiateMVars original
  let action ← instantiateMVars action
  let bundle ← instantiateMVars bundle
  if original.hasMVar || original.hasLevelMVar || action.hasMVar ||
      action.hasLevelMVar || bundle.hasMVar || bundle.hasLevelMVar then
    return .error "the selected action source requires complete independent parameters"
  let state ← registryState
  let selection := hasSelectedObjectDescriptor state descriptor
  try
    unless ← isTypeCorrect bundle do
      return .error "the action source has no typed complete category bundle"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType original)
          (← mkAppM ``CategoryTheory.Bundled.α #[bundle])) do
      return .error "the retained action source differs from its complete declaration signature"
    if !selection then
      let retained := objects.filter (·.1 == descriptor)
      if retained.isEmpty then
        return .error "the action source packet has no exact retained input binding"
      for (_, fixed) in retained do
        let fixed ← instantiateMVars fixed
        if fixed.hasMVar || fixed.hasLevelMVar then
          return .error "the retained action source has unresolved formal parameters"
        unless ← withoutModifyingState (withTransparency .all <|
            isDefEq (← inferType fixed) (← inferType original) <&&>
              isDefEq fixed original) do
          return .error "the action source packet has distinct complete retained inputs"
      if let some expression := expression then
        return .ok (some (← (Language.objectInContext original { expression, bundle }).run {}))
      -- A construction's full dependent signature fixes its source bundle, but
      -- supplies no source category expression. No registry name is inferred.
      return .ok none
    let .ok source ← interfaceSelectedValue objects original descriptor
      | return .error "the selected action lost its complete source descriptor"
    let selectedContext ← (Language.objectContext source).run {}
    let selectedBundle ← instantiateMVars selectedContext.bundle
    if selectedBundle.hasMVar || selectedBundle.hasLevelMVar then
      return .error "the retained action source has an incomplete selected category"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq selectedBundle bundle) do
      return .error "the retained action source changed its complete selected category"
    return .ok (some source)
  catch error =>
    match CasCatalogue.Exception.interpretationKind error with
    | .invalid | .ambiguous =>
        return .error "the action source has no unique complete declared interface"
    | _ => throw error

/-- Recover the selected interface from the independently fixed descriptor. Its
complete named parameters or accepted action supply structure; a coincident
carrier cannot introduce a different ring, generator, or operation owner. -/
partial def interfaceSelectedValue (objects : InterfaceObjects) (selected : Expr)
    (descriptor : Json) : TermElabM (Except String Language.Value) := do
  let state ← registryState
  let .ok (tag, args) := envelope descriptor
    | return .error "the selected interface requires its complete descriptor"
  if let some row := state.objects.find? (·.id.raw == tag) then
    let some category := state.categories.find? (·.id == row.category)
      | return .error "the selected interface's category is absent"
    let .ok named ← interfaceDeclaration objects row.declaration
        (← inferType (← instantiateFresh row.declaration)) args
      | return .error "the selected name has incomplete dependent parameters"
    unless ← withTransparency .all <| isDefEq named selected do
      return .error "the selected descriptor changes the complete named object"
    return .ok (← (Language.recognize state (← instantiateMVars named) category).run {})
  if #["objectPresentation", "finiteData"].contains tag then
    let #[underlying, _] := args | return .error "the selected presentation is incomplete"
    return ← interfaceSelectedValue objects selected underlying
  if tag == "functorAction" then
    let selected ← instantiateMVars selected
    if selected.hasMVar || selected.hasLevelMVar then
      return .error "the selected action requires a complete independently fixed result"
    let #[descriptor, originalData] := args | return .error "the selected action is incomplete"
    let .ok action ← interfaceAction objects descriptor
      | return .error "the selected action has no complete declared interface"
    let .ok original ← interfaceObject objects originalData
      | return .error "the selected action lost its complete source"
    let original ← instantiateMVars original
    if original.hasMVar || original.hasLevelMVar then
      return .error "the selected action requires a complete independently fixed source"
    -- Fresh declaration universes are determined by the independently supplied
    -- source, before asking for complete category bundles. The expected result
    -- cannot supply an omitted source or select any action parameter.
    let actionType ← whnfR (← inferType action)
    unless actionType.isAppOfArity ``CategoryTheory.Functor 4 do
      return .error "the selected action has no ordinary functor interface"
    unless ← withTransparency .all <|
        isDefEq actionType.getAppArgs[0]! (← inferType original) do
      return .error "the selected action source differs from its declaration signature"
    Semantic.bindFunctorSource action original
    let action ← instantiateMVars action
    let .ok (actionTag, actionArgs) := envelope descriptor
      | return .error "the selected action descriptor is incomplete"
    let source := (state.functors.find? (·.id.raw == actionTag)).map (·.source) <|>
      (if actionTag == "classifierForget" then do
        let id ← actionArgs[0]?.bind (·.getStr?.toOption)
        (state.classifiers.find? (·.id.raw == id)).map fun row => .classifierTotal row.id
      else none)
    if source.isNone && !(state.constructions.any (·.id.raw == actionTag)) then
      return .error "the selected action requires its independently retained source context"
    let target := (state.functors.find? (·.id.raw == actionTag)).map (·.target) <|>
      (state.constructions.find? (·.id.raw == actionTag)).map (·.target) <|>
      (if actionTag == "classifierForget" then do
        let id ← actionArgs[0]?.bind (·.getStr?.toOption)
        (state.classifiers.find? (·.id.raw == id)).map (·.host)
      else none)
    let some target := target
      | return .error "the selected action requires its independently retained target context"
    let (sourceBundle, bundle) ← functorCategoryBundles action
    let bundle ← instantiateMVars bundle
    if bundle.hasMVar || bundle.hasLevelMVar then
      return .error "the selected action has an incomplete independent target context"
    let .ok source ← interfaceActionSource objects original originalData action sourceBundle source
      | return .error "the selected action lost its full source selection"
    unless ← withTransparency .all <| isDefEq (← Semantic.objOf action original) selected do
      return .error "the selected action changes its full result"
    let context : CategoryContext := { expression := target, bundle }
    let value ← (Language.objectInContext selected context source.toArray).run {}
    let edge := ((state.functors.find? fun row => row.id.raw == actionTag && row.structural).map
        fun row => EdgeRef.functor row.id) <|>
      (if actionTag == "classifierForget" then do
        let id ← actionArgs[0]?.bind (·.getStr?.toOption)
        (state.classifiers.find? (·.id.raw == id)).map fun row => EdgeRef.classifierForget row.id
      else none)
    if let some edge := edge then
      let some source := source
        | return .error "the structural action lost its complete retained source context"
      let registered ← Semantic.edgeFunctor state edge
      unless ← withTransparency .all <| isDefEq (← Semantic.asFunctor registered) action do
        return .error "the selected action changes its registered structural edge"
      let registered ← instantiateMVars registered
      if let .object handle category origin selected _ := value then
        return .ok (.object handle category origin selected
          (some (#[source], source, #[edge], #[], #[(edge, registered.getAppArgs)])))
    return .ok value
  if ← isType selected then
    let some sets := state.categories.find? (·.id == CategoryId.sets)
      | return .error "the selected set category is absent"
    return .ok (.object selected sets none none none)
  return .error "the expression requires its independently selected complete object context"

/-- Check a short operation's entire registered interface before inspecting any
operands. The candidates contain whole operation families only; no returned
operand is substituted into a mathematical result or compared with an answer. -/
partial def validateShortOperation (selected : Language.Value) (carrier : Expr)
    (name : String) (arity : Nat) : TermElabM (Except String Unit) := do
  let state ← registryState
  let mut candidates : Array OperationCandidate := #[]
  for row in state.operations.filter (fun row =>
      row.name == name && row.arity == arity && row.numerals == 0) do
    for (application, sources) in (← (Language.selectedOperationApplicationsWithSources
        row.declaration row.category selected #[] (some name)).run {}) do
      let some (source, target) := Language.homEnds? (← inferType application) | continue
      unless ← withoutModifyingState <| withTransparency .all <| isDefEq target carrier do continue
      let inputs ← if arity == 2 then do
          let source ← withTransparency .all <| whnf source
          unless source.isAppOfArity ``Prod 2 do continue
          pure source.getAppArgs
        else pure #[source]
      unless inputs.size == arity &&
          (← inputs.allM fun input => withoutModifyingState <| withTransparency .all <|
            isDefEq input carrier) do continue
      let candidate : OperationCandidate := {
        operation := row.id
        application := application
        result := application
        sources := (← OperationAgreement.orderSources sources) }
      candidates := candidates.push candidate
  candidates ← OperationAgreement.orderCandidates candidates
  let some representative := candidates[0]?
    | return .error "the short element tag has no registered operation on the selected interface"
  let mut comparisons : Array OperationFamilyComparison := #[]
  for right in [:candidates.size] do
    for left in [:right] do
      let some leftCandidate := candidates[left]? | unreachable!
      let some rightCandidate := candidates[right]? | unreachable!
      if let some comparison ← OperationAgreement.compare left right leftCandidate rightCandidate then
        comparisons := comparisons.push comparison
  OperationAgreement.validate representative.result 0 candidates comparisons
  return .ok ()

/-- A nested operation operand inherits the complete value selected by its
accepted declaration parameters. External envelopes still resolve that value
only through their independently fixed complete descriptor. -/
partial def elementSelection (objects : InterfaceObjects) (selected : Expr)
    (retained : Option Language.Value := none) : TermElabM (Except String Language.Value) := do
  if let some value := retained then return .ok value
  let some (descriptor, _) := objects.find? (·.2 == selected)
    | return .error "an element requires its fixed complete selected descriptor"
  interfaceSelectedValue objects selected descriptor

/-- Primitive point tags instantiate the existing declared point interface only.
The temporary signature term is discarded; it is never returned as computed
data or compared with the independently requested mathematical value. -/
partial def validateShortTag (objects : InterfaceObjects) (selected carrier : Expr)
    (tag : String) (args : Array Json) (retained : Option Language.Value := none) :
    TermElabM (Except String Unit) := do
  try
    let .ok value ← elementSelection objects selected retained
      | return .error "a short element tag has no complete selected interface"
    if tag == "add" || tag == "mul" || tag == "neg" then
      return ← validateShortOperation value carrier
        (if tag == "add" then "+" else if tag == "mul" then "·" else "-")
        (if tag == "neg" then 1 else 2)
    let object ← (Language.carrierObject value).run {}
    let point ← match tag, args with
      | "numeral", #[number] =>
        let .ok number := number.getNat? | return .error "an element numeral requires a natural number"
        (Language.toElement (.nat number) object).run {}
      | "generator", #[] => (Language.generatorOf object).run {}
      | "generator", #[number] =>
        let .ok number := number.getNat? | return .error "a generator index requires a natural number"
        (Language.generatorOf object (some number)).run {}
      | _, _ => return .error "the primitive element tag has the wrong declared parameters"
    let .element point _ := point | return .error "the primitive tag has no declared point interface"
    unless ← withTransparency .all <| isDefEq (← inferType point)
        (← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, carrier]) do
      return .error "the primitive tag changes its complete selected point interface"
    return .ok ()
  catch error =>
    match CasCatalogue.Exception.interpretationKind error with
    | .invalid | .ambiguous => return .error "the short tag has no unique accepted selected interface"
    | _ => throw error

partial def validateElementExpressionAt (objects : InterfaceObjects) (selected carrier : Expr)
    (expression : Json) (retained : Option Language.Value := none) :
    TermElabM (Except String Unit) := do
  let .ok (tag, args) := envelope expression | return .error "an element requires its expression envelope"
  match tag, args with
  | "point", #[arrow] =>
      validateCallableAt objects (← mkAppM ``Quiver.Hom #[← Language.globalPointSource.run {}, carrier]) arrow
  | "add", #[left, right] | "mul", #[left, right] =>
      if let .error message ← validateShortTag objects selected carrier tag args retained then return .error message
      if let .error message ← validateElementExpressionAt objects selected carrier left retained then return .error message
      validateElementExpressionAt objects selected carrier right retained
  | "neg", #[value] =>
      if let .error message ← validateShortTag objects selected carrier tag args retained then return .error message
      validateElementExpressionAt objects selected carrier value retained
  | "numeral", _ | "generator", _ => validateShortTag objects selected carrier tag args retained
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
      let .ok selection ← elementSelection objects selected retained
        | return .error "the operation expression lost its fixed complete selected interface"
      let selectedValue := match selection with
        | .object _ _ _ (some value) _ => value
        | value => value
      if row.result.isNone && !(← isType (← (Language.semanticObject selectedValue).run {})) then
        let explicit ← (Language.explicitArguments row.declaration operation).run {}
        unless explicit.size > row.numerals do
          return .error "the operation expression lost its declared owner parameter"
        let owner := explicit.size - 1 - row.numerals
        unless ← (Language.parameterCompatible
            (Language.bindSelectedReceiver explicit owner selection (some row.category))).run {} do
          return .error "the operation expression changes its selected mathematical structure"
      let sources ← if operands.isEmpty then pure #[] else if operands.size == 2 then do
          let source ← withTransparency .all <| whnf source
          unless source.isAppOf ``Prod do return .error "a binary operation requires its declared product source"
          pure source.getAppArgs
        else pure #[← instantiateMVars source]
      unless sources.size == operands.size do return .error "the operation has a different operand interface"
      let some sets := state.categories.find? (·.id == CategoryId.sets)
        | return .error "the operation expression lost its declared data category"
      try
        let known ← (Language.operationParameterObjects row operation #[selection]).run {}
        for (source, operand) in sources.zip operands do
          let operandSelection ← (Language.declaredEndpointObject source sets
            known operation.getAppArgs).run {}
          if let .error message ← validateElementExpressionAt objects source source operand
              (some operandSelection) then return .error message
        return .ok ()
      catch error =>
        match CasCatalogue.Exception.interpretationKind error with
        | .invalid | .ambiguous =>
            return .error "the operation operand has no unique complete declared interface"
        | _ => throw error
  | _, _ => validateElementExpression expression

/-- Validate one constructor port with its original binder-role provenance.
Endpoint representations come only from earlier actual fields or retained input
roles. The representation callback supplies actual finite point keys; no resolved
formal-value equality or formal carrier enumeration participates. -/
partial def validatePlannedPort (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (seen : Array Json) (data : Json)
    (externalDescriptor : Nat → Option Json)
    (endpointKeys : Json → TermElabM (Except String (Option (Array Json)))) :
    TermElabM (Except String Unit) := do
  let resolve : Nat → Option Json := fun binder =>
    (plan.actualData? binder seen).orElse fun _ => externalDescriptor binder
  let objects : InterfaceObjects := plan.binders.filterMap fun binding => do
    let formal ← binding.formalValue
    let actual ← if binding.port.isSome then plan.actualData? binding.index seen
      else externalDescriptor binding.index
    return (actual, formal)
  let unwrapped ← match valuePayload data with
    | .ok actual => pure actual
    | .error message => return .error message
  if (unwrapped.getObjValAs? String "ctor").toOption == some "typedMap" &&
      (port.domainBinder.isSome || port.codomainBinder.isSome) then
    let some source := port.domainBinder.bind resolve
      | return .error "the typed callable has no actual computational domain descriptor"
    let some target := port.codomainBinder.bind resolve
      | return .error "the typed callable has no actual computational codomain descriptor"
    return ← validateEndpointPort port.formalField source target data objects
  let graph := if let .ok ("finiteGraph", #[_, actual]) := envelope unwrapped then actual else unwrapped
  -- Ordinary scalar/list ports have no callable endpoint roles.
  unless graph.getArr?.isOk && (port.domainBinder.isSome || port.codomainBinder.isSome) do
    return ← validatePort port.formalField port.expectedType data objects
  let some domainBinder := port.domainBinder
    | return .error "the callable graph has no retained computational domain role"
  let some domainDescriptor := resolve domainBinder
    | return .error "the callable graph has no actual computational domain descriptor"
  let domainKeys ← match ← graphDomainKeys objects (interfaceArgument objects) domainDescriptor unwrapped endpointKeys with
    | .ok keys => pure keys
    | .error message => return .error message
  let mut codomainKeys := none
  if let some codomainBinder := port.codomainBinder then
    let some codomainDescriptor := resolve codomainBinder
      | return .error "the callable graph has no actual computational codomain descriptor"
    match ← endpointKeys codomainDescriptor with
    | .error message => return .error message
    | .ok keys => codomainKeys := keys
  validateGraphAtKeys port.formalField port.expectedType data domainKeys codomainKeys

end

/-- Project one actual field through its existing codec. A descriptor accepted
as the whole current record cannot become that record's single data slot. The
ordinary field check is repeated at each nested receiver, whose full formal
context comes only from the original independently selected projection path. -/
def RecordFieldStep.project? (step : RecordFieldStep) (receiver : Expr)
    (data : DataOwnership.Data) : TermElabM (Option DataOwnership.Data) :=
    withoutModifyingState do
  let type ← withTransparency .all <| whnf (← inferType receiver)
  unless type.getAppFn.constName? == some step.structureName do return none
  let some payload := recordPayload? data | return none
  let explicit ← validatePort receiver type payload.json #[] true
  if let .ok (tag, args) := envelope payload.json then
    if step.codec == .core && tag == "coreObject" then
      unless explicit.isOk && step.count == 1 && step.index == 0 && args.size == 1 do
        return none
      return (payload.project #[.field "args", .index 0]).toOption
    if step.codec == .arrow && tag == "arrow" then
      unless explicit.isOk && step.count == 3 && args.size == 3 && step.index < 3 do
        return none
      return (payload.project #[.field "args", .index step.index]).toOption
    if step.codec == .arrowRefinement && (tag == "arrow" || tag == "subobject") then
      unless explicit.isOk && step.count == 1 && step.index == 0 && args.size == 3 do
        return none
      let some fields := (payload.project #[.field "args"]).toOption | return none
      return some {
        json := Json.mkObj [("ctor", toJson "arrow"), ("args", fields.json)]
        ownership := DataOwnership.prefix #[.field "args"] fields.ownership }
  -- Unsupported whole-record codecs keep their ordinary action path. A named
  -- descriptor may still be a legitimate field of an outer ordered record.
  if explicit.isOk then return none
  let checked ← validateRecordPortWith receiver type payload.json #[]
    (fun formal expected json objects => validatePort formal expected json objects)
  let some (.ok ()) := checked | return none
  if step.count == 1 then
    unless step.index == 0 do return none
    return some payload
  let .ok fields := payload.json.getArr? | return none
  unless fields.size == step.count do return none
  return (payload.project #[.index step.index]).toOption

/-- Apply a structural plan to actual public record data. Every intermediate
existing codec is retained; opaque records and unsupported whole descriptors
cannot be opened. Nested fields retain their individual supplying sessions. -/
partial def RecordProjectionPlan.apply? (plan : RecordProjectionPlan)
    (receiver : Expr) (data : DataOwnership.Data) :
    TermElabM (Option DataOwnership.Data) := do
  match plan with
  | .input path =>
    let mut current := receiver
    let mut selected := data
    for step in path do
      let some field ← step.project? current selected | return none
      current ← withTransparency .all <| mkProjection current step.field
      selected := field
    return some selected
  | .record codec fields =>
    let mut results := #[]
    for field in fields do
      let some result ← field.apply? receiver data | return none
      results := results.push result
    match codec with
    | .ordered =>
      if results.size == 1 then return some results[0]!
      return some (DataOwnership.Data.array results)
    | .core | .arrow =>
      let count := if codec == .core then 1 else 3
      unless results.size == count do return none
      let fields := DataOwnership.Data.array results
      return some {
        json := Json.mkObj [("ctor", toJson (if codec == .core then "coreObject" else "arrow")),
          ("args", fields.json)]
        ownership := DataOwnership.prefix #[.field "args"] fields.ownership }
    | .arrowRefinement =>
      -- The existing full-subcategory codec retains its complete Arrow fields.
      -- A whole opaque Arrow does not expose fields for that construction.
      let #[arrow] := results | return none
      let .ok ("arrow", args) := envelope arrow.json | return none
      unless args.size == 3 do return none
      return some arrow

/-- A complete callable signature can expose its selected record's carrier or
products of those carriers. Preserve the supplied field packets rather than
recovering another presentation from an equal formal carrier. -/
partial def recordEndpointData? (receiver endpoint : Expr) (data : DataOwnership.Data) :
    TermElabM (Option DataOwnership.Data) := do
  if let some plan ← recordProjectionPlan? receiver endpoint then
    if let some result ← plan.apply? receiver data then return some result
  let endpoint ← withTransparency .all <| whnf endpoint
  if endpoint.isAppOfArity ``Prod 2 then
    let fields := endpoint.getAppArgs
    let some left ← recordEndpointData? receiver fields[0]! data | return none
    let some right ← recordEndpointData? receiver fields[1]! data | return none
    let fields := DataOwnership.Data.array #[left, right]
    return some {
      json := Json.mkObj [("ctor", toJson "objectProduct"), ("args", fields.json)]
      ownership := DataOwnership.prefix #[.field "args"] fields.ownership }
  return none

/-- Frame a returned point at the caller's exact selected object. The formal
point is supplied independently and is never reconstructed from the answer.
Symbolic fields remain computational claims, including a different expression
for the same requested result; opaque owners are checked by the live consumer. -/
def validateElementAt (selected : Expr) (selectedData : Json) (formalPoint : Expr)
    (answer : Json) : TermElabM (Except String Unit) := do
  if selected.hasMVar || selected.hasLevelMVar then
    throwError "the selected element interface has unresolved formal parameters"
  let data ← match valuePayload answer with
    | .ok actual => pure actual
    | .error message => return .error message
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
