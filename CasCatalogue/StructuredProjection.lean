/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.StructuredResult
public import CasCatalogue.CategoryContext

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.StructuredProjection

structure ArrowPlan where
  receiver : Expr
  context : CategoryContext
  arrow : Expr
  arrowContext : CategoryContext
  base : CategoryContext
  source : Expr
  target : Expr
  hom : Expr
  subobject : Bool

/-- Recognize only the accepted Arrow and subobject constructor interfaces. The
complete typed category, including its parameters and dictionary, fixes every field. -/
def arrow? (receiver : Expr) (context : CategoryContext) : TermElabM (Option ArrowPlan) := do
  let .construct constructor #[.category base] := context.expression | return none
  let state ← registryState
  let some row := state.constructor? constructor | return none
  unless row.signature == #[ConstructorArgKind.category] do return none
  CategoryContext.checkObject context receiver
  let receiverType ← withTransparency .all <| whnf (← inferType receiver)
  let subobject := receiverType.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory
  unless subobject || receiverType.isAppOfArity ``CategoryTheory.Arrow 2 do return none
  let arrow ← if subobject then
      mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[receiver]
    else pure receiver
  let type ← withTransparency .all <| whnf (← inferType arrow)
  unless type.isAppOfArity ``CategoryTheory.Arrow 2 do
    return none
  let bundle ← mkAppOptM ``CategoryTheory.Cat.of
    #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
  let base ← CategoryContext.presented { expression := base, bundle }
  let #[arrowConstructor] := state.constructors.filter
      (·.semantics == `CasCatalogue.Constructors.arrow)
    | throwSemanticAmbiguity "the accepted Arrow constructor is absent or ambiguous"
  let arrowContext ← CategoryContext.construct base arrowConstructor.id
  let source ← mkAppM ``CategoryTheory.Arrow.left #[arrow]
  let target ← mkAppM ``CategoryTheory.Arrow.right #[arrow]
  let hom ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
  CategoryContext.checkMorphism base hom source target
  return some { receiver, context, arrow, arrowContext, base, source, target, hom, subobject }

def ArrowPlan.field (plan : ArrowPlan) (field : String) : TermElabM (Expr × CategoryContext × Bool) := do
  match field with
  | "obj" | "source" => return (plan.source, plan.base, false)
  | "target" => return (plan.target, plan.base, false)
  | "hom" => return (plan.hom, plan.base, true)
  | "inclusion" => return (plan.arrow, plan.arrowContext, false)
  | _ => throwStratum .invalid "the complete structured result has no such declared field"

/-- Forget only the accepted full-subcategory condition when transporting a complete
selected comparison. No carrier-level comparison substitutes for this map of isomorphisms. -/
def ArrowPlan.arrowComparison (plan : ArrowPlan) (comparison : Expr) : TermElabM Expr := do
  if !plan.subobject then return comparison
  let type ← withTransparency .all <| whnf (← inferType plan.receiver)
  unless type.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory do
    throwError "the selected subobject lost its full-subcategory predicate"
  let inclusion ← mkAppM ``CategoryTheory.ObjectProperty.ι #[type.getAppArgs.back!]
  mkAppM ``CategoryTheory.Functor.mapIso #[inclusion, comparison]

/-- Interpret the existing projection fields of an independently selected complete
bundle. A registered alias is accepted by its actual Arrow/full-subcategory type. -/
def projectionFunctorOfBundle (bundle : Expr) (field : String) : TermElabM Expr := do
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let carrier ← withTransparency .all <| whnf carrier
  let subobject := carrier.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory
  let arrowType ← if subobject then withLocalDeclD `selected carrier fun receiver => do
      withTransparency .all <|
        whnf (← inferType (← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[receiver]))
    else pure carrier
  unless arrowType.isAppOfArity ``CategoryTheory.Arrow 2 do
    throwStratum .invalid "the selected constructor has no complete Arrow projection interface"
  let arguments := #[some arrowType.getAppArgs[0]!, some arrowType.getAppArgs[1]!]
  let projection ← match field with
    | "obj" | "source" => mkAppOptM ``CategoryTheory.Arrow.leftFunc arguments
    | "target" => mkAppOptM ``CategoryTheory.Arrow.rightFunc arguments
    | "inclusion" => mkAppM ``CategoryTheory.Functor.id #[arrowType]
    | _ => throwStratum .invalid "the structured field is not an object projection functor"
  if !subobject then return projection
  let inclusion ← mkAppM ``CategoryTheory.ObjectProperty.ι #[carrier.getAppArgs.back!]
  if field == "inclusion" then return inclusion
  mkAppM ``CategoryTheory.Functor.comp #[inclusion, projection]

def ArrowPlan.projectionFunctor (plan : ArrowPlan) (field : String) : TermElabM Expr :=
  projectionFunctorOfBundle plan.context.bundle field

/-- Find an already accepted object projection on a fresh receiver. Actual equal
fields cannot select the wrong functor, and distinct applicable declarations remain
explicitly ambiguous. This is needed only to transport stored presentation maps. -/
def ArrowPlan.projectionAction? (plan : ArrowPlan) (field : String) :
    TermElabM (Option (EdgeRef × Expr)) := do
  let state ← registryState
  let mut candidates : Array (EdgeRef × Expr) := #[]
  for entry in state.functors do
    let candidate ← withoutModifyingState do
      let action ← Semantic.asFunctor (← instantiateFresh entry.declaration)
      let (source, _) ← functorCategoryBundles action
      unless ← withTransparency .all <| isDefEq source plan.context.bundle do return none
      let compatible ← withLocalDeclD `selected (← inferType plan.receiver) fun symbolic => do
        let some symbolicPlan ← arrow? symbolic plan.context | return false
        let (expected, _, morphism) ← symbolicPlan.field field
        if morphism then return false
        withTransparency .all <| isDefEq (← Semantic.objOf action symbolic) expected
      unless compatible do return none
      let action ← instantiateMVars action
      if action.hasMVar || action.hasLevelMVar || action.hasFVar then return none
      return some (.functor entry.id, action)
    if let some candidate := candidate then candidates := candidates.push candidate
  match candidates with
  | #[] => return none
  | #[candidate] => return some candidate
  | _ => throwSemanticAmbiguity "several accepted actions project the complete structured field"

structure ConstructionPlan where
  row : LimitEntry
  lift : Option LiftId
  diagram : Expr
  presentation : Expr
  cone : Expr
  apex : Expr
  context : CategoryContext

/-- Keep a data-port address in the expression key even when different ports have
definitionally equal formal values. The transparent administrative application
retains the whole receiver and index; it changes neither the value nor its type. -/
def retainPortValue (receiver value : Expr) (index : Nat) : TermElabM Expr := do
  let retained := mkApp (mkLambda `selectedResult .default (← inferType receiver)
    (value.liftLooseBVars 0 1)) receiver
  mkAppM ``Function.const #[mkConst ``Nat, retained, mkNatLit index]

/-- Recover a whole universal construction from its exact retained presentation.
The registry-selected resolution is checked before any data-port projection. -/
def construction? (receiver : Expr) (context : CategoryContext) (trace? : Option Trace := none) :
    TermElabM (Option ConstructionPlan) := do
  let mut apex := receiver.consumeMData
  while apex.isAppOfArity ``id 2 do apex := apex.appArg!.consumeMData
  let colimit := apex.isAppOf ``CategoryTheory.Limits.Cocone.pt
  unless colimit || apex.isAppOf ``CategoryTheory.Limits.Cone.pt do return none
  let cone := apex.appArg!
  let projection := if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone
  unless cone.isAppOf projection do
    throwStratum .invalid "the structured result lost its accepted universal presentation"
  let presentation := cone.appArg!
  let diagram := (← instantiateMVars (← inferType presentation)).appArg!
  let state ← registryState
  let some category := CategoryContext.named? state context.expression
    | throwStratum .noImplementation "the universal construction has no registered resolution schema"
  let recorded ← match trace? with
    | some trace => trace.node? receiver
    | none => pure none
  let mut choices : Array (LimitEntry × Option LiftId) := #[]
  for row in state.limits do
    unless row.colimit == colimit do continue
    if let some (.limit id actual _) := recorded then
      unless row.id == id && (← withTransparency .all <| isDefEq actual diagram) do continue
    else
      unless (presentation.find? (fun part =>
        part.getAppFn.constName? == some row.declaration)).isSome do continue
    let .ok resolution := state.resolveLimit category.id row.shape colimit | continue
    unless resolution.limit == row.id do continue
    let accepted ← Semantic.limit colimit row.shape diagram category.id.raw none
    unless ← withoutModifyingState (withTransparency .all <| isDefEq accepted presentation) do continue
    if let some (.limit _ _ lift) := recorded then
      unless resolution.lift == lift do
        throwStratum .invalid "the construction projection changed its selected creation lift"
    choices := choices.push (row, resolution.lift)
  let #[(row, lift)] := choices
    | if choices.isEmpty then
        throwStratum .invalid "the structured result has no exact registered construction"
      else throwSemanticAmbiguity "the structured result has several accepted constructions"
  CategoryContext.checkObject context receiver
  Trace.record trace? receiver (.limit row.id diagram lift)
  return some { row, lift, diagram, presentation, cone, apex := receiver, context }

def ConstructionPlan.dataPlan (plan : ConstructionPlan) : TermElabM StructuredResult.DataPlan := do
  match ← StructuredResult.dataPlan plan.row plan.diagram plan.presentation with
  | .ok data => return data
  | .error message => throwStratum .noImplementation m!"the accepted data-port schema is unavailable: {message}"

/-- A generic `hom()` is unambiguous only when the accepted data constructor has
one independent map port. An explicit field index always addresses that exact slot. -/
def ConstructionPlan.selectPort (plan : ConstructionPlan) (index : Option Nat) :
    TermElabM StructuredResult.DataPort := do
  let data ← plan.dataPlan
  if let some index := index then
    let some port := data.ports[index]?
      | throwStratum .invalid "the selected field is outside its registered data-constructor schema"
    return port
  let mut maps := #[]
  for port in data.ports do
    let type ← whnfR port.expectedType
    if type.isAppOf ``Quiver.Hom then maps := maps.push port
  let #[port] := maps
    | if maps.isEmpty then
        throwStratum .invalid "the registered construction has no independent morphism data field"
      else throwSemanticAmbiguity "the construction has several defining maps; select field(i) or leg(i)"
  return port

end CasCatalogue.StructuredProjection
