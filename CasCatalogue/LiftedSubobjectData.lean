/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic
public import CasCatalogue.StructuredResult
public import CasCatalogue.ComputationalData

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

def subobjectType (arrowType : Expr) : TermElabM Expr := do
  withLocalDeclD `arrow arrowType fun arrow => do
    let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
    let property ← mkLambdaFVars #[arrow] (← mkAppM ``CategoryTheory.Mono #[inclusion])
    mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory #[property]

/-- Pending callable plans retain their formal meaning separately from untrusted data.
The four formal expressions specify ports; they are not computed outputs. No backend
map is converted into a law-bearing morphism or isomorphism. -/
structure Component where
  lift : LiftId
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
def plan (expected : Expr) (sourceCategory : NamedCategoryEntry)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr) :
    TermElabM (Except String Plan) := do
  if prescribed.isEmpty then return .error "a prescribed lift requires a nonempty route"
  let state ← registryState
  let .construct subobjects #[.category source] := sourceCategory.expression
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
      (← categoryCarrierInstance sourceCategory) expected do
    return .error "the descriptor context has different complete result parameters"
  let mut current := originalSource
  let mut receiver := fixedSource
  let mut rows : Array LiftEntry := #[]
  let mut receivers : Array Expr := #[]
  for id in prescribed do
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
    let action ← Semantic.asFunctor (← Semantic.edgeFunctor state row.edge)
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
    let action ← Semantic.asFunctor (← Semantic.edgeFunctor state inner)
    let next ← Semantic.liftSubobject state row saved formalResult
    try discard <| StructuredResult.checkReconstruction (← instantiateMVars next)
    catch _ => throwError "next is not closed"
    let some computationName := row.computation
      | return .error "the selected lift has no public computation signature"
    let computation ← instantiateFresh computationName
    let evidence ← instantiateFresh row.evidence
    let evidenceType ← withTransparency .all <| whnf (← inferType evidence)
    unless evidenceType.isAppOfArity ``CasCatalogue.MonoLift 5 do
      return .error "the selected lift lost its complete public dependent action"
    let selected := evidenceType.getAppArgs
    let X ← mkAppM ``CategoryTheory.Arrow.left #[saved]
    unless ← withTransparency .all <| isDefEq selected[0]! (← inferType X) do
      return .error "the computation has a different complete source category"
    unless ← withTransparency .all <| isDefEq selected[4]! action do
      return .error "the computation has a different complete selected action"
    let canonical ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.computation
      (selected.map some ++ #[some evidence])
    unless ← withTransparency .all <| isDefEq computation canonical do
      return .error "the computation differs from the independently selected lift"
    let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[formalResult]
    let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
    let monic ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[formalResult]
    let ports ← LiftField.all.mapM fun field => do
      let port ← withTransparency .all <| mkAppOptM field.declaration
        (selected.map some ++ #[some computation, some X, none, some inclusion, some monic])
      let port ← instantiateMVars port
      discard <| StructuredResult.checkReconstruction port
      unless ← isTypeCorrect port do throwError "the selected lift has an ill-typed public port"
      pure port
    reverseComponents := reverseComponents.push {
      lift := row.id, action := (← instantiateMVars action), receiver := saved,
      base := formalResult, routeIndex := index, ports }
    formalResult := next
  unless ← withTransparency .all <| isDefEq (← inferType formalResult) expected do
    return .error "the formal lift has a different complete selected result category"
  let closed ← StructuredResult.checkReconstruction formalResult
  return .ok {
    formalResult := closed, fixedSource, fixedBase,
    components := reverseComponents.reverse,
    sourceCategory := originalSource, baseCategory }

/-- Complete fields remain computational data, never reconstructed mathematical objects. -/
def fields (tag : String) (count : Nat) (data : Json) : Except String (Array Json) := do
  unless (data.getObjValAs? String "ctor").toOption == some tag do
    throw s!"expected complete {tag} data"
  let args ← (data.getObjVal? "args").bind (·.getArr?)
  unless args.size == count do throw s!"{tag} requires {count} ordered fields"
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
    return .error "a lift map changes its declared computational endpoints"
  match ← ComputationalData.validatePort formal (← inferType formal) args[2]! with
  | .error message => return .error message
  | .ok () => pure ()
  if args[2]!.getArr?.isOk then
    let .ok (some domain) ← ComputationalData.endpointKeys source
      | return .error "a finite lift map requires complete actual domain keys or an opaque callable"
    let .ok codomain ← ComputationalData.endpointKeys target
      | return .error "a lift map has malformed actual codomain data"
    return ComputationalData.validateGraphEndpoints domain codomain args[2]!
  return .ok ()

/-- Validate all four outputs against actual earlier fields and the fixed public types. -/
def validatePrefix (component : Component) (action source base : Json)
    (outputs : Array Json) : TermElabM (Except String Unit) := do
  unless !outputs.isEmpty && outputs.size <= 4 && component.ports.size == 4 do
    return .error "a lift requires an ordered prefix of its four public outputs"
  let .ok sourceFields := fields "arrow" 3 source
    | return .error "the lift source omitted its complete original Arrow data"
  let .ok baseFields := fields "subobject" 3 base
    | return .error "the lift base omitted its complete actual subobject data"
  let .ok () ← ComputationalData.validatePort component.ports[0]!
      (← inferType component.ports[0]!) outputs[0]!
    | return .error "the lift object output has malformed framing"
  let mapped := Json.mkObj [("ctor", "functorAction"),
    ("args", Json.arr #[action, outputs[0]!])]
  for (index, domain, codomain) in #[(1, outputs[0]!, sourceFields[0]!),
      (2, mapped, baseFields[0]!), (3, baseFields[0]!, mapped)] do
    if index >= outputs.size then continue
    match ← validateMap component.ports[index]! domain codomain outputs[index]! with
    | .error message => return .error message
    | .ok () => pure ()
  return .ok ()

/-- Advance with this step's actual object and defining map, not the original base packet. -/
def nextBase (source : Json) (outputs : Array Json) : Except String Json := do
  let sourceFields ← fields "arrow" 3 source
  unless outputs.size == 4 do throw "an incomplete lift cannot advance the reverse route"
  let inclusion ← fields "typedMap" 3 outputs[1]!
  return Json.mkObj [("ctor", "subobject"),
    ("args", Json.arr #[outputs[0]!, sourceFields[0]!, inclusion[2]!])]

/-- Only completed packets with every actual output count as prescribed lifted data.
Source packets and selected action descriptors are supplied by the kernel's fixed route. -/
def decode (expected : Expr) (sourceCategory : NamedCategoryEntry)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr) (json : Json)
    (validateSource : CategoryExpr → Expr → Json → TermElabM (Except String Unit))
    (validateBase : NamedCategoryEntry → Expr → Json → TermElabM (Except String Unit)) :
    TermElabM (Option (Except String Packet)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "liftedSubobject" do return none
  let work : TermElabM (Except String Packet) := do
    let .ok args := fields "liftedSubobject" 4 json
      | return .error "a completed lift requires base, source, exact ids and every component output"
    let .ok ids := args[2]!.getArr? | return .error "the lift ids are absent"
    unless ids == prescribed.map (fun id => toJson id.raw) do
      return .error "the completed packet changes the exact prescribed lift ids"
    let .ok prepared ← plan expected sourceCategory fixedSource prescribed fixedBase
      | return .error "the completed packet has no full fixed lift plan"
    let .ok () ← validateSource prepared.sourceCategory fixedSource args[1]!
      | return .error "the computational source changed its complete fixed context"
    let .ok () ← validateBase prepared.baseCategory fixedBase args[0]!
      | return .error "the computational base changed its complete fixed context"
    let .ok steps := args[3]!.getArr? | return .error "the component output array is absent"
    unless steps.size == prepared.components.size do
      return .error "the completed packet omits a prescribed component"
    let mut base := args[0]!
    let mut outputs := Array.replicate steps.size #[]
    for index in (List.range steps.size).reverse do
      let some component := prepared.components[index]?
        | return .error "the completed route lost a fixed component"
      let .ok step := fields "liftStep" 5 steps[index]!
        | return .error "a component omits its selected action, source, base or outputs"
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

end CasCatalogue.LiftedSubobjectData
