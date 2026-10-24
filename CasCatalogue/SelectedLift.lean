/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.DirectConstruction
public import CasCatalogue.Admission
public import CasCatalogue.CategoryContext

@[expose] public section
open Lean Meta Elab Term

namespace CasCatalogue.SelectedLift

/-- The selected formal computation, independent of every returned computational field. -/
structure Plan where
  entry : LiftEntry
  parameters : Array Expr
  evidence : Expr
  computation : Expr
  action : Expr
  source : Expr
  inclusion : Expr
  monic : Expr
  /-- Complete instantiated public data ports, in declaration order. -/
  ports : Array Expr

/-- The functor on which the row's Arrow action is based. Selection does not require a
structural route: nonstructural functors remain usable only by explicit selection. -/
def innerEdge (state : RegistryState) (entry : LiftEntry) : TermElabM EdgeRef := do
  let .constructMap constructor inner := entry.edge
    | throwStratum .invalid "the selected subobject lift has no complete Arrow action"
  unless (state.constructor? constructor).any
      (·.semantics == `CasCatalogue.Constructors.arrow) do
    throwStratum .invalid "the selected lift uses a different registered constructor"
  return inner

/-- The selected action supplies both complete category dictionaries. A named
registry row is not needed for a constructed source or target context. -/
def context (plan : Plan) (target : Bool := false) : TermElabM CategoryContext := do
  let state ← registryState
  let inner ← innerEdge state plan.entry
  let some expression := if target then state.selectedEdgeTarget? inner
      else state.selectedEdgeSource? inner
    | throwStratum .invalid "the selected lift lost its accepted category expression"
  let (sourceBundle, targetBundle) ← functorCategoryBundles plan.action
  CategoryContext.presented {
    expression
    bundle := if target then targetBundle else sourceBundle }

/-- Select the declared evidence family using actual supplied parameters and endpoints.
Monicity is checked on the formal side and never requested from a computation. -/
def select (entry : LiftEntry) (parameters : Array Term) (source inclusion monic : Expr) :
    TermElabM Plan := do
  unless entry.kind == .subobjects do
    throwStratum .invalid "the selected lift does not lift subobjects"
  let state ← registryState
  let inner ← innerEdge state entry
  let application ← DirectConstruction.instantiate entry.evidence parameters
  let type ← withTransparency .all <| whnf (← inferType application.value)
  unless type.isAppOfArity ``CasCatalogue.MonoLift 5 do
    throwStratum .invalid "the selected evidence does not retain its complete MonoLift signature"
  let selected := type.getAppArgs
  let action := selected[4]!
  unless ← withTransparency .all <| isDefEq selected[0]! (← inferType source) do
    throwStratum .invalid "the selected lift source has different complete category parameters"
  let image ← Semantic.objOf action source
  let inclusionType ← whnfR (← inferType inclusion)
  unless inclusionType.isAppOf ``Quiver.Hom do
    throwStratum .invalid "the selected base inclusion is not a categorical morphism"
  let endpoints := inclusionType.getAppArgs
  unless ← withTransparency .all <| isDefEq endpoints.back! image do
    throwStratum .invalid "the selected base inclusion does not land at this exact functor image"
  let condition ← mkAppM ``CategoryTheory.Mono #[inclusion]
  unless !monic.hasSorry && (← Decide.kernelAccepts condition monic) do
    throwStratum .invalid "the selected base inclusion lacks checked formal monicity"
  let accepted ← Semantic.asFunctor (← Semantic.edgeFunctor state inner)
  unless ← withTransparency .all <| isDefEq accepted action do
    throwStratum .invalid "the selected evidence changes its registered complete functor action"
  let application ← DirectConstruction.close application
  let evidence := application.value
  let selected ← selected.mapM instantiateMVars
  -- Retain the accepted declaration application as well as its equality to the
  -- evidence's action. Unfolding the latter must not erase ordered edge parameters.
  let action ← instantiateMVars accepted
  let computation ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.computation
    (selected.map some ++ #[some evidence])
  let some declaration := entry.computation
    | throwStratum .invalid "the selected lift has no public computation signature"
  let registered ← instantiateFresh declaration
  unless ← withTransparency .all <| isDefEq registered computation do
    throwStratum .invalid "the registered computation differs from the selected complete lift"
  let ports ← LiftField.all.mapM fun field => do
    let value ← withTransparency .all <| mkAppOptM field.declaration
      (selected.map some ++ #[some computation, some source, none, some inclusion, some monic])
    let value ← instantiateMVars value
    unless !value.hasMVar && !value.hasLevelMVar && (← isTypeCorrect value) do
      throwStratum .invalid "the selected lift has an unresolved public data port"
    return value
  return {
    entry
    parameters := application.explicit
    evidence, computation, action, source, inclusion, monic, ports }

/-- Reuse an already fixed formal lift application without forgetting evidence-family data
parameters that may not occur in the functor itself. -/
def fromEvidence (entry : LiftEntry) (evidence source inclusion monic : Expr) :
    TermElabM Plan := do
  let constant ← mkConstWithFreshMVarLevels entry.evidence
  let (arguments, infos, _) ← forallMetaTelescopeReducing (← inferType constant)
  unless ← withTransparency .all <| isDefEq (mkAppN constant arguments) evidence do
    throwStratum .invalid "the retained lift evidence changed its selected declaration"
  let parameters ← (arguments.zip infos).filterMapM fun (argument, info) =>
    if info.isExplicit then return some (← exprToSyntax (← instantiateMVars argument)) else pure none
  select entry parameters source inclusion monic

/-- The separate canonical factor port consumes the accepted compatibility equation.
It creates no additional computation field and assumes no faithful underlying functor. -/
def factor (plan : Plan) (baseMap cone proof : Expr) : TermElabM Expr := do
  let type ← withTransparency .all <| whnf (← inferType plan.evidence)
  let selected := type.getAppArgs
  let canonical ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.factorComputation
    (selected.map some ++ #[some plan.evidence])
  let equation ← mkEq (← Semantic.mapOf plan.action cone)
    (← mkAppM ``CategoryTheory.CategoryStruct.comp #[baseMap, plan.inclusion])
  unless !proof.hasSorry && (← Decide.kernelAccepts equation proof) do
    throwStratum .invalid "the universal factor lacks its checked exact compatibility equation"
  let result ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLiftFactorComputation.factor
    (selected.map some ++ #[some plan.evidence, some canonical, some plan.source,
      none, some plan.inclusion, some plan.monic, none, some baseMap, some cone, some proof])
  let result ← instantiateMVars result
  unless !result.hasMVar && !result.hasLevelMVar && (← isTypeCorrect result) do
    throwStratum .invalid "the universal factor changed its complete declared endpoint types"
  return result

/-- The accepted source equation for a following stage of a composite factor. -/
def factorSourceEquation (plan : Plan) (baseMap cone proof : Expr) : TermElabM Expr := do
  let type ← withTransparency .all <| whnf (← inferType plan.evidence)
  let equality ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.factor_hom
    (type.getAppArgs.map some ++ #[some plan.evidence, some plan.source, none,
      some plan.inclusion, some plan.monic, none, some baseMap, some cone, some proof])
  mkAppM ``Eq.symm #[equality]

/-- Checked monicity of the selected computation's defining map is an accepted formal law. -/
def homMonic (plan : Plan) : TermElabM Expr := do
  let type ← withTransparency .all <| whnf (← inferType plan.evidence)
  withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.computation_hom_mono
    (type.getAppArgs.map some ++ #[some plan.evidence, some plan.source, none,
      some plan.inclusion, some plan.monic])

/-- Reconstruct a prescribed route's selected computations in route order. Each reverse
stage consumes the preceding actual formal defining map, including its original ambient. -/
def prescribed (state : RegistryState) (receiver : Expr) (route : Array EdgeRef)
    (lifts : Array LiftId) (base : Expr) : TermElabM (Array Plan) := do
  unless !route.isEmpty && route.size == lifts.size do
    throwStratum .invalid "a prescribed lift requires every ordered route step"
  let mut sources := #[]
  let mut current := receiver
  for edge in route do
    sources := sources.push (← mkAppM ``CategoryTheory.Arrow.left #[current])
    current ← Semantic.objOf (← Semantic.edgeFunctor state edge) current
  let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[base]
  let mut inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
  let mut monic ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[base]
  let mut reverse := #[]
  for index in (List.range route.size).reverse do
    let some entry := state.lifts.find? (·.id == lifts[index]!)
      | throwStratum .invalid "a prescribed lift is no longer registered"
    unless entry.edge == route[index]! do
      throwStratum .invalid "a prescribed lift changes its exact selected route step"
    let plan ← select entry #[] sources[index]! inclusion monic
    reverse := reverse.push plan
    inclusion := plan.ports[1]!
    monic ← homMonic plan
  return reverse.reverse

/-- The actual base of a recorded inherited method, reconstructed independently of execution. -/
def methodPlans (id : MethodId) (route : Array EdgeRef) (lifts : Array LiftId)
    (receiver : Expr) : TermElabM (Array Plan) := do
  let state ← registryState
  let some method := state.methods.find? (·.id == id)
    | throwStratum .invalid "the retained lifted method is no longer registered"
  let some functor := state.functor? method.functor
    | throwStratum .invalid "the retained lifted method has no accepted action"
  let image ← Semantic.objOf (← Semantic.routeFunctor state route) receiver
  let base ← Semantic.objOf (← registeredFunctorInstance functor) (← methodArgument method image)
  prescribed state receiver route lifts base

/-- Complete comparison of the composed selected lift, using the published functor maps
and the ordered comparison fields. The deepest base is retained in both directions. -/
def port (plans : Array Plan) (index : Nat) : TermElabM Expr := do
  let some first := plans[0]?
    | throwStratum .invalid "a lift projection requires its complete selected route"
  let some initial := first.ports[index]?
    | throwStratum .invalid "the requested lift projection is not a public field"
  if index < 2 then return initial
  let mut result := initial
  for next in plans.extract 1 plans.size do
    let mapped ← Semantic.mapOf next.action result
    result ← if index == 2 then
      mkAppM ``CategoryTheory.CategoryStruct.comp #[mapped, next.ports[2]!]
    else
      mkAppM ``CategoryTheory.CategoryStruct.comp #[next.ports[3]!, mapped]
  return result

structure FactorStep where
  selection : Plan
  baseMap : Expr
  cone : Expr
  proof : Expr
  factor : Expr

/-- Factor first through the deepest action, then through each earlier lift, using the
public source equation as the next compatibility proof. This is the accepted factor_comp
decomposition; no replacement base map, identity comparison, or faithfulness is assumed. -/
def factors (plans : Array Plan) (baseMap cone proof : Expr) :
    TermElabM (Array FactorStep) := do
  unless !plans.isEmpty do throwStratum .invalid "a factor requires a selected lift"
  let mut cones := #[]
  let mut transported := cone
  for plan in plans do
    cones := cones.push transported
    transported ← Semantic.mapOf plan.action transported
  let mut currentBase := baseMap
  let mut currentProof := proof
  let mut steps := #[]
  for index in (List.range plans.size).reverse do
    let some plan := plans[index]? | unreachable!
    let cone := cones[index]!
    let result ← factor plan currentBase cone currentProof
    steps := steps.push {
      selection := plan
      baseMap := currentBase
      cone
      proof := currentProof
      factor := result }
    currentProof ← factorSourceEquation plan currentBase cone currentProof
    currentBase := result
  return steps

end CasCatalogue.SelectedLift
