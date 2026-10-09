/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Semantic
public import CasCatalogue.StructuredResult

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
  computation : Expr
  receiver : Expr
  base : Expr
  obj : Expr
  hom : Expr
  forward : Expr
  backward : Expr
  declaration : Name
  /-- Route index; execution runs in reverse order and consumes the next step outputs. -/
  routeIndex : Nat

/-- One finite packet for the prescribed route. Callable descriptors are retained rather
than enumerating maps on an infinite carrier. `formalResult` uses only formal inputs. -/
structure Packet where
  formalResult : Expr
  fixedSource : Expr
  fixedBase : Expr
  sourceData : Json
  baseData : Json
  components : Array Component
  data : Json

/-- Validate complete computational lift fields at the independently fixed contexts.
Callbacks check representation and declared endpoints only; they return no Lean value,
law, monicity witness, inverse equation or universal-property certificate. -/
def decode (expected : Expr) (sourceCategory : NamedCategoryEntry)
    (fixedSource : Expr) (prescribed : Array LiftId) (fixedBase : Expr) (json : Json)
    (validateSource : CategoryExpr → Expr → Json → TermElabM (Except String Unit))
    (validateBase : NamedCategoryEntry → Expr → Json → TermElabM (Except String Unit)) :
    TermElabM (Option (Except String Packet)) := do
  unless (json.getObjValAs? String "ctor").toOption == some "liftedSubobject" do
    return none
  let work : TermElabM (Except String Packet) := do
    let .ok args := (json.getObjVal? "args").bind (·.getArr?)
      | return .error "a lifted subobject requires an ordered full envelope"
    unless args.size == 3 do
      return .error "a lifted subobject requires base, source and exact lift ids"
    let .ok ids := args[2]!.getArr?
      | return .error "a lifted subobject requires its ordered registered lift ids"
    unless !prescribed.isEmpty && ids.size == prescribed.size do
      return .error "the lifted envelope omits the independently prescribed route"
    for index in [:ids.size] do
      unless ids[index]!.getStr?.toOption == some prescribed[index]!.raw do
        return .error "the lifted envelope changes the independently prescribed ordered lift ids"
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
    discard <| StructuredResult.checkReconstruction fixedSource
    discard <| StructuredResult.checkReconstruction fixedBase
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
      receiver ← Semantic.objOf (← Semantic.asFunctor (← Semantic.edgeFunctor state row.edge)) receiver
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
      let some declaration := row.computation
        | return .error "the prescribed lift has no published computational signature"
      let computation ← instantiateFresh declaration
      let ambient ← mkAppM ``CategoryTheory.Arrow.left #[saved]
      let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[formalResult]
      let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
      let monic ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[formalResult]
      let .constructMap _ inner := row.edge
        | return .error "the prescribed lift lost its selected inner action"
      let action ← Semantic.asFunctor (← Semantic.edgeFunctor state inner)
      let signature ← withTransparency .all <| whnf (← inferType computation)
      unless signature.isAppOfArity ``CasCatalogue.MonoLiftComputation 5 do
        return .error "the published lift computation has no complete signature"
      let selected := signature.getAppArgs
      unless ← withTransparency .all <| isDefEq selected[0]! (← inferType ambient) do
        return .error "the lift computation changes its selected source category"
      unless ← withTransparency .all <| isDefEq selected[2]!
          (← inferType (← mkAppM ``CategoryTheory.Arrow.right #[arrow])) do
        return .error "the lift computation changes its selected base category"
      unless ← withTransparency .all <| isDefEq selected[4]! action do
        return .error "the lift computation changes its exact selected functor action"
      let arguments := selected.map some ++ #[some computation, some ambient,
        none, some inclusion, some monic]
      let obj ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLiftComputation.obj arguments
      let hom ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLiftComputation.hom arguments
      let forward ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLiftComputation.forward arguments
      let backward ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLiftComputation.backward arguments
      let next ← Semantic.liftSubobject state row saved formalResult
      for expression in #[action, computation, obj, hom, forward, backward, next] do
        discard <| StructuredResult.checkReconstruction (← instantiateMVars expression)
      reverseComponents := reverseComponents.push {
        lift := row.id, action := (← instantiateMVars action),
        computation := (← instantiateMVars computation), receiver := saved,
        base := formalResult, obj := (← instantiateMVars obj),
        hom := (← instantiateMVars hom), forward := (← instantiateMVars forward),
        backward := (← instantiateMVars backward),
        declaration, routeIndex := index }
      formalResult := next
    unless ← withTransparency .all <| isDefEq (← inferType formalResult) expected do
      return .error "the formal lift has a different complete selected result category"
    let .ok () ← validateSource originalSource fixedSource args[1]!
      | return .error "the computational source does not match its fixed full descriptor"
    let .ok () ← validateBase baseCategory fixedBase args[0]!
      | return .error "the computational base does not match its fixed full descriptor"
    let components := reverseComponents.reverse
    let closed ← StructuredResult.checkReconstruction formalResult
    return .ok {
      formalResult := closed
      fixedSource := fixedSource
      fixedBase := fixedBase
      sourceData := args[1]!
      baseData := args[0]!
      components := components
      data := json }
  return some (← work)

end CasCatalogue.LiftedSubobjectData
