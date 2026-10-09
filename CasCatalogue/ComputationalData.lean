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
  -- Recover only a retained application of this public declaration. No
  -- private definition, canonical construction, or backend value is unfolded.
  if let some application := formal.find? fun term =>
      term.getAppFn.constName? == some declaration && term.getAppNumArgs == fields.size then
    for (field, parameter) in fields.zip application.getAppArgs do
      unless ← isDefEq field parameter do
        return .error "the retained public declaration has inconsistent parameter types"
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
    let some selected ← retainedApplication entry.declaration formal
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
      let formal := formalField.consumeMData
      unless formal.isAppOf ``CategoryTheory.Functor.obj do
        return .error "the action requires its independently retained formal receiver context"
      let fields := formal.getAppArgs
      let functor := fields[fields.size - 2]!
      let source := fields.back!
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
      for (field, data) in #[(sourceField, source), (targetField, target),
          (inclusionField, inclusion)] do
        match ← validatePort field (← inferType field) data with
        | .error message => return .error message
        | .ok () => pure ()
      if let some presentation := (json.getObjVal? "presentation").toOption then
        -- Both representations have the declared source-category object schema.
        -- These are interface placeholders, not chosen canonical comparison maps.
        let mapType ← mkAppM ``Quiver.Hom #[sourceField, sourceField]
        for key in #["hom", "inv"] do
          let .ok data := presentation.getObjVal? key
            | return .error "the supplied computational presentation omitted a comparison map"
          let placeholder ← mkFreshExprMVar mapType
          match ← validatePort placeholder mapType data with
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
  let function ← try
      pure (some (← mkAppM ``DFunLike.coe #[formalField]))
    catch _ =>
      try
        let concrete ← mkAppM ``CategoryTheory.ConcreteCategory.hom #[formalField]
        pure (some (← mkAppM ``DFunLike.coe #[concrete]))
      catch _ => pure none
  let function := function.getD formalField
  let functionType ← whnfR (← inferType function)
  if let .forallE _ domain body _ := functionType then
    if body.hasLooseBVars then
      return .error "dependent callable data requires an explicit released representation"
    let domain ← whnfR domain
    let body ← whnfR body
    let .ok graph := json.getArr? | return .error "a finite callable requires a graph array"
    unless (← plainType domain) && (← plainType body) do
      return .error "the callable's point types require their released data representation"
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
end

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

/-- Validate one constructor port with its original binder-role provenance.
Endpoint representations come only from earlier actual fields or retained input
roles. The representation callback supplies actual finite point keys; no resolved
formal-value equality or formal carrier enumeration participates. -/
def validatePlannedPort (plan : StructuredResult.DataPlan)
    (port : StructuredResult.DataPort) (seen : Array Json) (data : Json)
    (externalDescriptor : Nat → Option Json)
    (endpointKeys : Json → TermElabM (Except String (Option (Array Json)))) :
    TermElabM (Except String Unit) := do
  match ← validatePort port.formalField port.expectedType data with
  | .error message => return .error message
  | .ok () => pure ()
  let graph := if let .ok ("valueData", #[actual]) := envelope data then actual else data
  unless graph.getArr?.isOk do return .ok ()
  -- Ordinary scalar/list data ports are not callable graphs.
  if port.domainBinder.isNone && port.codomainBinder.isNone then return .ok ()
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
  return validateGraphEndpoints domainKeys codomainKeys graph

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

end CasCatalogue.ComputationalData
