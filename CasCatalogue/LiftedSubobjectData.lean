/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic
public import CasCatalogue.StructuredResult
public import CasCatalogue.ComputationalData
public import CasCatalogue.SelectedLift

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.LiftedSubobjectData

/-- Obtain the actual object field's type from the independently fixed complete result type. -/
def sourceArrowType (expected : Expr) : TermElabM Expr := do
  let constructor ← mkConstWithFreshMVarLevels
    ``CategoryTheory.ObjectProperty.FullSubcategory.mk
  let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless ← withTransparency .all <| isDefEq result expected do
    throwError "a lifted descriptor is outside the fixed full subobject category"
  unless fields.size >= 2 do throwError "the full subobject constructor has no defining arrow"
  let type ← instantiateMVars (← inferType fields[fields.size - 2]!)
  let reduced ← whnfR type
  unless reduced.isAppOf ``CategoryTheory.Arrow do
    throwError "the fixed subobject predicate is not over complete arrows"
  if type.hasMVar || type.hasLevelMVar then
    throwError "the fixed subobject category leaves selected arrow data unresolved"
  return type

/-- Apply the registered subobject constructor to the exact base category
already retained by the complete Arrow type, including its selected dictionary. -/
def subobjectType (arrowType : Expr) : TermElabM Expr := do
  let arrowType ← withTransparency .all <| whnfHeadPred arrowType
    fun type => pure (!type.isAppOf ``CategoryTheory.Arrow)
  unless arrowType.isAppOfArity ``CategoryTheory.Arrow 2 do
    throwError "the subobject interface requires a complete accepted Arrow context"
  let arguments := arrowType.getAppArgs
  let base ← mkAppOptM ``CategoryTheory.Cat.of
    #[some arguments[0]!, some arguments[1]!]
  let #[constructor] := (← registryState).constructors.filter
      (·.semantics == `CasCatalogue.Constructors.subobjects)
    | throwError "the subobject interface has no unique accepted constructor"
  let bundle ← applyConstructorInterface constructor.semantics #[base] #[base]
  mkAppM ``CategoryTheory.Bundled.α #[bundle]

/-- Pending callable plans retain their formal meaning separately from untrusted data.
The four formal expressions specify ports; they are not computed outputs. No backend
map is converted into a law-bearing morphism or isomorphism. -/
structure Component where
  lift : LiftId
  selection : SelectedLift.Plan
  action : Expr
  receiver : Expr
  base : Expr
  /-- Route index; execution runs in reverse order and consumes the next step outputs. -/
  routeIndex : Nat
  /-- All four fully instantiated public fields, in declaration order. -/
  ports : Array Expr

/-- One finite packet for the prescribed route. Callable descriptors are retained rather
than enumerating maps on an infinite carrier. `formalResult` uses only formal inputs. -/
structure Plan where
  formalResult : Expr
  fixedSource : Expr
  fixedBase : Expr
  components : Array Component
  sourceCategory : CategoryExpr
  baseCategory : NamedCategoryEntry

structure Packet extends Plan where
  sourceData : Json
  baseData : Json
  /-- Actual component outputs in the original prescribed route order. -/
  outputs : Array (Array Json)
  data : Json

/-- Fix the entire reverse-route computation before consulting any returned data. -/
def planIn (expected : Expr) (sourceExpression : CategoryExpr)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr)
    (application? : Option MethodApplication := none) :
    TermElabM (Except String Plan) := do
  if prescribed.isEmpty then return .error "a prescribed lift requires a nonempty route"
  let state ← registryState
  let .construct subobjects #[.category source] := sourceExpression
    | return .error "a lifted result has no exact registered subobject constructor context"
  unless (state.constructor? subobjects).any
      (·.semantics == `CasCatalogue.Constructors.subobjects) do
    return .error "the lifted result context is not the registered subobject constructor"
  let #[arrowConstructor] := state.constructors.filter
      (·.semantics == `CasCatalogue.Constructors.arrow)
    | return .error "the complete arrow constructor is absent or ambiguous"
  let originalSource : CategoryExpr := .construct arrowConstructor.id #[.category source]
  let sourceType ← sourceArrowType expected
  try discard <| StructuredResult.checkReconstruction fixedSource
  catch _ => throwError "fixedSource is not closed"
  try discard <| StructuredResult.checkReconstruction fixedBase
  catch _ => throwError "fixedBase is not closed"
  unless ← withTransparency .all <| isDefEq (← inferType fixedSource) sourceType do
    return .error "the independently retained source has different complete arrow parameters"
  unless ← withTransparency .all <| isDefEq
      (← subobjectType (← inferType fixedSource)) expected do
    return .error "the descriptor context has different complete result parameters"
  if let some application := application? then
    unless application.sourceContext.expression.syntacticEq originalSource &&
        application.resultContext.expression.syntacticEq sourceExpression &&
        application.routeApplications.size == prescribed.size &&
        application.routeReceivers.size == prescribed.size &&
        application.lifts.map (·.id) == prescribed do
      throwError "the method lift plan changed its exact retained selection"
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq application.baseResult fixedBase <&&>
          isDefEq (← inferType application.result) expected) do
      throwError "the method lift plan changed its complete base or result interface"
  let mut current := originalSource
  let mut receiver := fixedSource
  let mut rows : Array LiftEntry := #[]
  let mut receivers : Array Expr := #[]
  for index in [:prescribed.size] do
    let id := prescribed[index]!
    let some row := state.lifts.find? (·.id == id)
      | return .error s!"the prescribed lift is unregistered: {id.raw}"
    unless row.kind == .subobjects do
      return .error "the prescribed lift names a different construction"
    let .constructMap constructor _ := row.edge
      | return .error "the prescribed subobject lift has no full arrow action"
    unless constructor == arrowConstructor.id do
      return .error "the prescribed lift acts on a different registered constructor"
    let some edge := (state.edgesFrom current).find? (·.ref == row.edge)
      | return .error "the prescribed lift does not start at the exact source category"
    unless edge.source.syntacticEq current do
      return .error "the prescribed lift changes its current registered source"
    let .construct targetConstructor #[.category _] := edge.target
      | return .error "the prescribed lift does not land in a complete arrow category"
    unless targetConstructor == arrowConstructor.id do
      return .error "the prescribed lift changes the registered arrow constructor"
    rows := rows.push row
    receivers := receivers.push receiver
    let action ← match application? with
      | none => Semantic.asFunctor (← Semantic.edgeFunctor state row.edge)
      | some application =>
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq application.routeReceivers[index]! receiver) do
            throwError "the method lift plan changed an original route receiver"
          let action := application.routeApplications[index]!
          discard <| Semantic.edgeEndpoints? state row.edge action
          pure action
    receiver ← Semantic.objOf action receiver
    current := edge.target
  let .construct _ #[.category target] := current
    | return .error "the lifted descriptor has no exact base category"
  let baseExpression : CategoryExpr := .construct subobjects #[.category target]
  let baseCategory ← Semantic.namedCategoryFor state baseExpression
  unless baseCategory.expression.syntacticEq baseExpression do
    return .error "the base reply has no exact named subobject context"
  let baseType ← subobjectType (← inferType receiver)
  unless ← withTransparency .all <| isDefEq (← inferType fixedBase) baseType do
    return .error "the independently retained base has different complete selected parameters"
  let baseArrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[fixedBase]
  unless ← withTransparency .all <| isDefEq
      (← mkAppM ``CategoryTheory.Arrow.right #[baseArrow])
      (← mkAppM ``CategoryTheory.Arrow.left #[receiver]) do
    return .error "the formal base changes the complete source ambient"
  -- Build every formal component before consulting any computational field.
  let mut formalResult := fixedBase
  let mut reverseComponents : Array Component := #[]
  for index in (List.range rows.size).reverse do
    let some row := rows[index]?
      | return .error "the prescribed lift lost its retained row"
    let saved := receivers[index]!
    let .constructMap _ inner := row.edge
      | return .error "the prescribed lift lost its selected inner action"
    let retained ← match application? with
      | none =>
          let action ← Semantic.asFunctor (← Semantic.edgeFunctor state inner)
          return (← Semantic.liftSubobjectApplication state row saved formalResult
            (action? := some action)).2
      | some application =>
          let retained := application.lifts[index]!
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq retained.receiver saved <&&> isDefEq retained.input formalResult) do
            throwError "the method lift plan changed its retained reverse-stage inputs"
          let .constructMap constructor _ := row.edge
            | throwError "the method lift plan lost its retained Arrow action"
          let action ← Semantic.constructorActionInput state constructor
            application.routeApplications[index]!
          unless ← withoutModifyingState (withTransparency .all <|
              isDefEq retained.action action) do
            throwError "the method lift plan changed its exact complete action"
          pure retained
    let next := retained.result
    try discard <| StructuredResult.checkReconstruction (← instantiateMVars next)
    catch _ => throwError "next is not closed"
    let selection ← SelectedLift.fromMethodApplication row retained
    let ports := selection.ports
    for port in ports do discard <| StructuredResult.checkReconstruction port
    reverseComponents := reverseComponents.push {
      lift := row.id, action := retained.action, receiver := saved,
      base := formalResult, routeIndex := index, ports, selection }
    formalResult := next
  unless ← withTransparency .all <| isDefEq (← inferType formalResult) expected do
    return .error "the formal lift has a different complete selected result category"
  if let some application := application? then
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq formalResult application.result) do
      throwError "the method lift plan changed its independently retained formal result"
  let closed ← StructuredResult.checkReconstruction formalResult
  return .ok {
    formalResult := closed, fixedSource, fixedBase,
    components := reverseComponents.reverse,
    sourceCategory := originalSource, baseCategory }

/-- Named entry point retains its independent complete category check. -/
def plan (expected : Expr) (sourceCategory : NamedCategoryEntry)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr)
    (application? : Option MethodApplication := none) :
    TermElabM (Except String Plan) := do
  unless ← withTransparency .all <| isDefEq (← categoryCarrierInstance sourceCategory) expected do
    return .error "the named lift context changes the complete selected result parameters"
  planIn expected sourceCategory.expression fixedSource prescribed fixedBase application?

/-- Complete fields remain computational data, never reconstructed mathematical objects. -/
def fields (tag : String) (count : Nat) (data : Json) : Except String (Array Json) := do
  unless (data.getObjValAs? String "ctor").toOption == some tag do
    throw s!"expected complete {tag} data"
  let args ← (data.getObjVal? "args").bind (·.getArr?)
  unless args.size == count do throw s!"{tag} requires {count} ordered fields"
  return args

/-- Both published spellings retain the same complete defining Arrow. The
caller has already fixed the full subobject category; the tag supplies no proof
of its predicate and cannot choose a different mathematical result interface. -/
def subobjectFields (data : Json) : Except String (Array Json) := do
  let (tag, args) ← ComputationalData.envelope data
  unless (tag == "arrow" || tag == "subobject") && args.size == 3 do
    throw "a complete subobject requires its source, target and defining map"
  return args

/-- Structural Arrow transport preserves complete actual endpoint and map data. -/
def mapArrowData (action source : Json) : Except String Json := do
  let args ← fields "arrow" 3 source
  let image value := Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[action, value])]
  let mapped := Json.mkObj [("ctor", "map"), ("args", Json.arr #[action, args[2]!])]
  return Json.mkObj [("ctor", "arrow"),
    ("args", Json.arr #[image args[0]!, image args[1]!, mapped])]

/-- A map carries its actual endpoints; a well-framed wrong map is still just data. -/
def validateMap (formal : Expr) (source target data : Json) :
    TermElabM (Except String Unit) := do
  let .ok args := fields "typedMap" 3 data
    | return .error "a lift map requires its actual source, target and callable data"
  unless args[0]! == source && args[1]! == target do
    let type := (← inferType formal).consumeMData
    unless type.isAppOf ``Quiver.Hom do
      return .error "endpoint inventories require independently retained categorical endpoint types"
    let parameters := type.getAppArgs
    for (expected, actual, fixed) in #[(source, args[0]!, parameters[parameters.size - 2]!),
        (target, args[1]!, parameters.back!)] do
      if expected == actual then continue
      -- Enrich only a symbolic endpoint. An already supplied inventory is part
      -- of its actual data and cannot be replaced by a different inventory.
      if (expected.getObjValAs? String "ctor").toOption == some "finiteData" then
        return .error "a lift map changes its declared computational endpoints"
      let .ok ("finiteData", #[descriptor, _]) := ComputationalData.envelope actual
        | return .error "a lift map changes its declared computational endpoints"
      unless descriptor == expected do
        return .error "a lift map changes its declared computational endpoints"
      if let .error message ← ComputationalData.validatePort fixed (← inferType fixed) actual then
        return .error message
  ComputationalData.validateEndpointPort formal args[0]! args[1]! args[2]!

/-- Validate all four outputs at the actual source object, without manufacturing an Arrow. -/
def validateSelectionPrefix (selection : SelectedLift.Plan) (action source base : Json)
    (outputs : Array Json) : TermElabM (Except String Unit) := do
  unless !outputs.isEmpty && outputs.size <= 4 && selection.ports.size == 4 do
    return .error "a lift requires an ordered prefix of its four public outputs"
  let .ok baseFields := subobjectFields base
    | return .error "the lift base omitted its complete actual subobject data"
  let .ok () ← ComputationalData.validatePort selection.ports[0]!
      (← inferType selection.ports[0]!) outputs[0]!
    | return .error "the lift object output has malformed framing"
  let mapped := Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[action, outputs[0]!])]
  let mut mappedEndpoint := mapped
  let mut baseEndpoint := baseFields[0]!
  for index in #[1, 2, 3] do
    if index >= outputs.size then continue
    let (domain, codomain) := if index == 1 then (outputs[0]!, source)
      else if index == 2 then (mappedEndpoint, baseEndpoint)
      else (baseEndpoint, mappedEndpoint)
    match ← validateMap selection.ports[index]! domain codomain outputs[index]! with
    | .error message => return .error message
    | .ok () => pure ()
    if index == 2 then
      let .ok actual := fields "typedMap" 3 outputs[index]!
        | return .error "a validated comparison lost its complete endpoint fields"
      mappedEndpoint := actual[0]!
      baseEndpoint := actual[1]!
  return .ok ()

/-- Prescribed lift execution additionally retains the entire original Arrow. -/
def validatePrefix (component : Component) (action source base : Json)
    (outputs : Array Json) : TermElabM (Except String Unit) := do
  let .ok sourceFields := fields "arrow" 3 source
    | return .error "the lift source omitted its complete original Arrow data"
  validateSelectionPrefix component.selection action sourceFields[0]! base outputs

/-- Advance with this step's actual object and defining map, not the original base packet. -/
def nextBase (source : Json) (outputs : Array Json) : Except String Json := do
  discard <| fields "arrow" 3 source
  unless outputs.size == 4 do throw "an incomplete lift cannot advance the reverse route"
  let inclusion ← fields "typedMap" 3 outputs[1]!
  return Json.mkObj [("ctor", "subobject"),
    ("args", Json.arr #[inclusion[0]!, inclusion[1]!, inclusion[2]!])]

/-- Evidence-family metadata is required independently of the action's parameters.
When actual request data is retained, compare that ordered data verbatim: its opaque
tokens and `valueData` wrappers are not interchangeable with a formal recipe.
Without request data this checks only the independently selected slot interfaces;
it does not establish equality to requests that this decoder has not received. -/
def validateParameters (selection : SelectedLift.Plan) (step : Json)
    (requested? : Option (Array Json)) : TermElabM (Except String Unit) := do
  let .ok parameters := (step.getObjVal? "parameters").bind (·.getArr?)
    | return .error "a completed lift step requires its ordered selected evidence parameters"
  let fixed ← DirectConstruction.dataArguments selection.parameters
  unless parameters.size == fixed.size do
    return .error "a completed lift step omitted or added selected evidence parameters"
  if let some requested := requested? then
    unless parameters == requested do
      return .error "a completed lift step changes its actual ordered request parameters"
  for (parameter, data) in fixed.zip parameters do
    if let .error message ← ComputationalData.validatePort parameter (← inferType parameter) data then
      return .error message
  return .ok ()

/-- Retain the validated original source and its prescribed images as input
interfaces. A reduced base object need not remember a forgetful action's source.
Only the fixed plan supplies these formal interfaces; descriptors supply no
mathematical identity, action, inverse or construction law. -/
def sourceInterfaces (prepared : Plan) (steps : Array Json) (source : Json) :
    TermElabM (Except String ComputationalData.InterfaceObjects) := do
  let mut current := source
  let mut objects : ComputationalData.InterfaceObjects := #[]
  for (component, stepData) in prepared.components.zip steps do
    let .ok step := fields "liftStep" 5 stepData
      | return .error "a component omits its selected action, source, base or outputs"
    unless step[2]! == current do
      return .error "a component changes the original or preceding actual transported source"
    if let .error message ← ComputationalData.validateAction component.action step[1]! then
      return .error message
    let .ok endpoints := fields "arrow" 3 current
      | return .error "a component has incomplete source Arrow data"
    for (projection, index) in #[(``CategoryTheory.Arrow.left, 0),
        (``CategoryTheory.Arrow.right, 1)] do
      let formal ← mkAppM projection #[component.receiver]
      objects := objects.push (endpoints[index]!, formal)
      let image ← Semantic.objOf component.action formal
      let descriptor := Json.mkObj [("ctor", "functorAction"),
        ("args", Json.arr #[step[1]!, endpoints[index]!])]
      objects := objects.push (descriptor, image)
    let .ok next := mapArrowData step[1]! current
      | return .error "a component has incomplete source Arrow data"
    current := next
  return .ok objects

/-- A completed reply reuses the formal plan fixed before dispatch. Check that
the caller retained that plan at the same full source, base and result roles;
neither returned bytes nor another declaration instantiation supplies a port. -/
def checkRetainedPlan (expected : Expr) (sourceExpression : CategoryExpr)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr) (prepared : Plan) :
    TermElabM Unit := do
  let same (left right : Expr) : TermElabM Unit := do
    unless ← withoutModifyingState (withTransparency .all <|
        isDefEq (← inferType left) (← inferType right) <&&> isDefEq left right) do
      throwError "the retained lift plan changed a complete typed interface"
  same prepared.fixedSource fixedSource
  same prepared.fixedBase fixedBase
  unless ← withoutModifyingState (withTransparency .all <|
      isDefEq (← inferType prepared.formalResult) expected) do
    throwError "the retained lift plan changed its complete result category"
  let state ← registryState
  let context ← Semantic.methodLiftResultContext state prepared.sourceCategory fixedSource
  unless context.expression.syntacticEq sourceExpression do
    throwError "the retained lift plan changed its selected result expression"
  unless prepared.components.map (·.lift) == prescribed do
    throwError "the retained lift plan changed its prescribed stage inventory"
  for index in [:prepared.components.size] do
    let component := prepared.components[index]!
    unless component.routeIndex == index && component.selection.entry.id == component.lift &&
        component.ports.size == component.selection.ports.size do
      throwError "the retained lift plan changed a selected stage or port position"
    same component.action component.selection.action
    same component.selection.source (← mkAppM ``CategoryTheory.Arrow.left #[component.receiver])
    let base ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[component.base]
    same component.selection.inclusion (← mkAppM ``CategoryTheory.Arrow.hom #[base])
    same component.selection.monic
      (← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[component.base])
    for (port, selected) in component.ports.zip component.selection.ports do same port selected

/-- Only completed packets with every actual output count as prescribed lifted data.
Source packets and selected action descriptors are supplied by the kernel's fixed route.
Execution must supply its retained request parameters; an explicit `none` is reserved
for formal-reference framing without a runtime request history. Session ownership
belongs to the containing wire and is preserved and checked by the realizer. -/
def decodeIn (expected : Expr) (sourceExpression : CategoryExpr)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr) (json : Json)
    (validateSource : CategoryExpr → Expr → Json → TermElabM (Except String Unit))
    (validateBase : NamedCategoryEntry → Expr → Json → ComputationalData.InterfaceObjects →
      TermElabM (Except String Unit))
    (requestParameters? : Option (Array (Array Json))) (prepared? : Option Plan := none) :
    TermElabM (Option (Except String Packet)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "liftedSubobject" do return none
  let work : TermElabM (Except String Packet) := do
    let .ok args := fields "liftedSubobject" 4 json
      | return .error "a completed lift requires base, source, exact ids and every component output"
    let .ok ids := args[2]!.getArr? | return .error "the lift ids are absent"
    unless ids == prescribed.map (fun id => toJson id.raw) do
      return .error "the completed packet changes the exact prescribed lift ids"
    let selected ← match prepared? with
      | some prepared =>
          checkRetainedPlan expected sourceExpression fixedSource prescribed fixedBase prepared
          pure (.ok prepared)
      | none => planIn expected sourceExpression fixedSource prescribed fixedBase
    let .ok prepared := selected
      | return .error "the completed packet has no full fixed lift plan"
    let .ok () ← validateSource prepared.sourceCategory fixedSource args[1]!
      | return .error "the computational source changed its complete fixed context"
    let .ok steps := args[3]!.getArr? | return .error "the component output array is absent"
    unless steps.size == prepared.components.size do
      return .error "the completed packet omits a prescribed component"
    if let some requested := requestParameters? then
      unless requested.size == steps.size do
        return .error "the retained requests omit a prescribed component's parameters"
    let .ok objects ← sourceInterfaces prepared steps args[1]!
      | return .error "the completed packet changes its retained original source or selected action"
    if let .error message ← validateBase prepared.baseCategory fixedBase args[0]! objects then
      return .error s!"the computational base changed its complete fixed context: {message}"
    let mut base := args[0]!
    let mut outputs := Array.replicate steps.size #[]
    for index in (List.range steps.size).reverse do
      let some component := prepared.components[index]?
        | return .error "the completed route lost a fixed component"
      let .ok step := fields "liftStep" 5 steps[index]!
        | return .error "a component omits its selected action, source, base or outputs"
      if let .error message ← validateParameters component.selection steps[index]!
          (requestParameters?.map (·[index]!)) then
        return .error message
      unless step[0]!.getStr?.toOption == some component.lift.raw && step[3]! == base do
        return .error "a component changes the exact reverse-route base or selected lift"
      if index == 0 && step[2]! != args[1]! then
        return .error "the final component changes the complete original source"
      match ← ComputationalData.validateAction component.action step[1]! with
      | .error message => return .error message
      | .ok () => pure ()
      if index + 1 < steps.size then
        let .ok following := fields "liftStep" 5 steps[index + 1]!
          | return .error "the next component has incomplete source provenance"
        let .ok image := mapArrowData step[1]! step[2]!
          | return .error "a component has incomplete source Arrow data"
        unless following[2]! == image do
          return .error "a component changes the preceding actual transported source"
      let .ok data := step[4]!.getArr? | return .error "a component has no ordered outputs"
      unless data.size == 4 do return .error "a completed component omits a public output"
      match ← validatePrefix component step[1]! step[2]! base data with
      | .error message => return .error message
      | .ok () => pure ()
      let .ok next := nextBase step[2]! data | return .error "the component cannot advance"
      base := next
      outputs := outputs.set! index data
    return .ok { prepared with sourceData := args[1]!, baseData := args[0]!, outputs, data := json }
  return some (← work)

def decode (expected : Expr) (sourceCategory : NamedCategoryEntry)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr) (json : Json)
    (validateSource : CategoryExpr → Expr → Json → TermElabM (Except String Unit))
    (validateBase : NamedCategoryEntry → Expr → Json → ComputationalData.InterfaceObjects →
      TermElabM (Except String Unit))
    (requestParameters? : Option (Array (Array Json))) (prepared? : Option Plan := none) :
    TermElabM (Option (Except String Packet)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "liftedSubobject" do return none
  unless ← withTransparency .all <| isDefEq (← categoryCarrierInstance sourceCategory) expected do
    return some (.error "the named lift context changes its complete selected result parameters")
  decodeIn expected sourceCategory.expression fixedSource prescribed fixedBase json
    validateSource validateBase requestParameters? prepared?

end CasCatalogue.LiftedSubobjectData
