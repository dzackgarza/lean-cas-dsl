/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public import CasCatalogue.InterpretationFailure
public import CasCatalogue.Trace
public import CasCatalogue.Decide
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section

/-!
# The semantic reading of the language (`specs/architecture.md`, "The one-way workflow")

What a statement means is decided from `lean-categories`' catalogue alone, before and without any
leaf: each construct elaborates to its mathematics, and a statement that does not is invalid,
whichever leaves are installed. Only then is it decided (`CasCatalogue.Realize`): in Lean where
Lean decides it, else by evaluating the same term through the admitted registrations, where a
missing registration is a gap.

* A named object is its declaration at its parameters.
* A morphism `f : a ⟶ b` is `f` elaborated at `a ⟶ b` in the category.
* A limit or colimit is the registered presentation of its shape at the diagram, returned along the
  registered creation lift when it is computed in another category (`liftedLimitCone`).
* A method call is the method's functor after the structural route it resolves along.
* A property query is `Classifier.Holds` of the classifier after its route.

Each construction records, in the trace it is given (`CasCatalogue.Trace`), the catalogue
operation that formed its value, so that the realized reading evaluates the same term.
-/

open Lean Meta Elab Term CategoryTheory CategoryTheory.Limits

namespace CasCatalogue

universe v u v' u' w w'

/-- A limit cone of `G`, transported to a diagram `F ≅ G` (`IsLimit.postcomposeInvEquiv`). -/
def limitConeOfIso {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {F G : J ⥤ C}
    (α : F ≅ G) (L : LimitCone G) : LimitCone F :=
  ⟨(Cone.postcompose α.inv).obj L.cone, (IsLimit.postcomposeInvEquiv α L.cone).symm L.isLimit⟩

/-- A colimit cocone of `G`, transported to a diagram `F ≅ G` (`IsColimit.precomposeHomEquiv`). -/
def colimitCoconeOfIso {J : Type w} [Category.{w'} J] {C : Type u} [Category.{v} C] {F G : J ⥤ C}
    (α : F ≅ G) (L : ColimitCocone G) : ColimitCocone F :=
  ⟨(Cocone.precompose α.hom).obj L.cocone,
    (IsColimit.precomposeHomEquiv α L.cocone).symm L.isColimit⟩

/-- A limit cone of `K`, lifted from one of `K ⋙ U` along a functor creating limits of its shape
(Mathlib `liftLimit`, `liftedLimitIsLimit`). -/
noncomputable def liftedLimitCone {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {J : Type w} [Category.{w'} J] (U : C ⥤ E) [CreatesLimitsOfShape J U] {K : J ⥤ C}
    (L : LimitCone (K ⋙ U)) : LimitCone K :=
  ⟨liftLimit L.isLimit, liftedLimitIsLimit L.isLimit⟩

/-- A declaration applied to fresh metavariables for all its arguments. -/
def instantiateFresh (declaration : Name) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  return mkAppN constant args

namespace Semantic

/-- The polymorphic diagram constructor is published by the registered presentation's
result type. No shape name chooses a mathematical construction in the consumer. -/
def diagramConstructor (row : LimitEntry) : MetaM (Option Name) := do
  let family ← instantiateFresh row.declaration
  let type ← whnfR (← inferType family)
  let diagram := type.appArg!.consumeMData
  return diagram.getAppFn.constName?


/-- Reduce only the presentation of supplied parameter records before unification.
Structure eta reduction retains every field; it does not choose data from a carrier. -/
def parameterPresentation (value : Expr) : MetaM Expr := do
  Meta.transform value (pre := fun e => do
    let reduced ← withTransparency .reducible <| whnf e
    if let some short ← etaStruct? reduced (fun _ => true) then return .done short
    return .continue (some reduced))

/-- Read the actual selected family parameter from its published fibre witness. -/
def selectedFamilyParameter? (realization : Expr) : MetaM (Option (Expr × Expr)) := do
  let fibre ← withTransparency .all <| whnf
    (← mkAppHere ``CasCatalogue.CategoryRealization.familyFibre #[realization])
  if fibre.isAppOfArity ``Option.none 1 then return none
  unless fibre.isAppOf ``Option.some do
    throwError "a category realization has no determined fibre witness"
  let packed ← withTransparency .all <| whnf fibre.getAppArgs.back!
  let witness := packed.getAppArgs.back!
  let witnessType ← withTransparency .all <| whnf (← inferType witness)
  unless witnessType.isAppOf ``CasCatalogue.CategoryFamilyFibreWitness do
    throwError "a category realization has a malformed fibre witness"
  let family := witnessType.getAppArgs[4]!
  let parameter ← withTransparency .all <| mkAppHere
    ``CasCatalogue.CategoryFamilyFibreWitness.parameter #[witness]
  return some (family, parameter)

/-- Match complete parameters of the same published family, before comparing its carriers. -/
def alignCategoryParameters (left right : Expr) : MetaM Unit := do
  match ← selectedFamilyParameter? left, ← selectedFamilyParameter? right with
  | none, none => pure ()
  | some (leftFamily, leftParameter), some (rightFamily, rightParameter) =>
      unless ← withTransparency .all <| isDefEq leftFamily rightFamily do
        throwError "the adjacent endpoints have different registered family realizations"
      unless ← withTransparency .all <| isDefEq
          (← inferType leftParameter) (← inferType rightParameter) do
        throwError "the adjacent endpoints have different complete parameter types"
      let leftPresented ← parameterPresentation leftParameter
      let rightPresented ← parameterPresentation rightParameter
      unless ← withTransparency .all <| isDefEq leftPresented rightPresented do
        throwError "the adjacent endpoints have different complete selected parameters"
      -- The presentations can expose an as-yet unassigned bundle. Check the original
      -- full parameters after that assignment, rather than demanding projection inversion.
      unless ← withTransparency .all <| isDefEq leftParameter leftPresented do
        throwError "the source parameter presentation changed its complete data"
      unless ← withTransparency .all <| isDefEq rightParameter rightPresented do
        throwError "the target parameter presentation changed its complete data"
      unless ← withTransparency .all <| isDefEq leftParameter rightParameter do
        throwError "the original complete selected parameters differ"
  | _, _ => throwError "the adjacent endpoints disagree on their declared family context"

/-- Instantiate endpoint metadata at exactly the supplied public action. -/
def realizedFunctorEndpoints (realization action : Expr) : MetaM (Expr × Expr) := do
  let type ← withTransparency .all <| whnf (← inferType realization)
  unless type.isAppOf ``CasCatalogue.FunctorRealization do
    throwError "a registered action has no public typed realization"
  unless ← withTransparency .all <| isDefEq type.getAppArgs.back! action do
    throwError "a functor realization describes a different complete action"
  let source ← withTransparency .all <| mkAppHere
    ``CasCatalogue.FunctorRealization.sourceRealization #[realization]
  let target ← withTransparency .all <| mkAppHere
    ``CasCatalogue.FunctorRealization.targetRealization #[realization]
  return (source, target)

/-- Preserve the accepted category morphism while projecting its ordinary functor action. -/
def asFunctor (F : Expr) : MetaM Expr := do
  if (← withTransparency .all <| whnf (← inferType F)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[F]
  else pure F

/-- Supply the exact complete category bundles to an accepted constructor action. -/
def applyConstructorFunctor (action : Name) (F : Expr) : MetaM Expr := do
  let F ← asFunctor F
  let (source, target) ← functorCategoryBundles F
  applyConstructorInterface action #[source, target] #[F]

/-- Constructor actions consume the ordinary functor projection of their exact inner edge. -/
partial def edgeFunctor (state : RegistryState) : EdgeRef → MetaM Expr
  | .constructMap constructor inner => do
    let some action := (state.constructor? constructor).bind (·.functorialAction)
      | throwError "the registered constructor has no functorial action"
    applyConstructorFunctor action (← edgeFunctor state inner)
  | edge => state.edgeFunctor edge

/-- Parameter endpoint witnesses are supplied by the registered action, never recovered from
a leaf. A constructed edge retains its inner edge's complete parameter witnesses; the outer
carrier and category dictionaries are still checked when the actions are composed. -/
partial def edgeEndpoints? (state : RegistryState) (edge : EdgeRef) (action : Expr) :
    MetaM (Option (Expr × Expr)) := do
  match edge with
  | .functor id =>
      let some entry := state.functor? id | throwError "the route names an absent functor"
      return some (← realizedFunctorEndpoints (← instantiateFresh entry.realization)
        (← asFunctor action))
  | .classifierForget id =>
      let some entry := state.classifier? id | throwError "the route names an absent classifier"
      let realization ← instantiateFresh entry.realization
      let forgetful ← withTransparency .all <| mkAppHere
        ``CasCatalogue.ClassifierRealization.forgetfulRealization #[realization]
      return some (← realizedFunctorEndpoints forgetful (← asFunctor action))
  | .constructMap constructor inner =>
      let some name := (state.constructor? constructor).bind (·.functorialAction)
        | throwError "the constructed edge has no accepted functor action"
      unless action.getAppFn.isConstOf name do
        throwError "the constructed edge lost its accepted action application"
      let infos ← forallTelescopeReducing (← inferType action.getAppFn) fun args _ =>
        args.mapM (·.fvarId!.getBinderInfo)
      let explicit := (action.getAppArgs.zip infos).filterMap fun (argument, info) =>
        if info.isExplicit then some argument else none
      let #[innerAction] := explicit
        | throwError "the accepted constructor action has a different complete input interface"
      edgeEndpoints? state inner innerAction

/-- Construct the route and retain the very same edge applications for semantic provenance. -/
def routeFunctorWithApplications (state : RegistryState) (route : Array EdgeRef) :
    MetaM (Expr × Array Expr) := do
  let mut result : Option Expr := none
  let mut applications : Array Expr := #[]
  let mut previousTarget : Option Expr := none
  for edge in route do
    let application ← edgeFunctor state edge
    let endpoints ← edgeEndpoints? state edge application
    if let some previous := previousTarget then
      if let some (source, _) := endpoints then
        alignCategoryParameters previous source
    applications := applications.push application
    let next ← asFunctor application
    result ← some <$> match result with
      | none => pure next
      | some previous => mkFunctorComp previous next
    previousTarget := endpoints.map (·.2)
  let some composite := result | throwError "the empty structural route has no functor composite"
  return (composite, applications)

def routeFunctor (state : RegistryState) (route : Array EdgeRef) : MetaM Expr := do
  return (← routeFunctorWithApplications state route).1

/-- Compose the exact edge applications already interpreted for a route. Reusing these terms
preserves their selected parameters and avoids elaborating another copy of the same route. -/
def compositeOfApplications (applications : Array Expr) : MetaM Expr := do
  let some first := applications[0]?
    | throwError "the empty structural route has no functor composite"
  let mut composite ← asFunctor first
  for application in applications.extract 1 applications.size do
    composite ← mkFunctorComp composite (← asFunctor application)
  return composite

/-- The first and last complete parameter witnesses of the actual retained edge applications.
These bind separately constructed route segments before whiskering compares their carriers. -/
def routeParameterEndpoints? (state : RegistryState) (route : Array EdgeRef)
    (applications : Array Expr) : MetaM (Option Expr × Option Expr) := do
  unless route.size == applications.size do
    throwError "the structural route lost its exact edge applications"
  if route.isEmpty then return (none, none)
  let source ← edgeEndpoints? state route[0]! applications[0]!
  let target ← edgeEndpoints? state route.back! applications.back!
  return (source.map (·.1), target.map (·.2))

/-- Resolve a named family schema independently of its local bound parameter spelling.
The actual parameter terms remain in the elaborated value and are never copied from this row. -/
def namedCategoryFor (state : RegistryState) (expression : CategoryExpr) :
    TermElabM NamedCategoryEntry := do
  if let some entry := state.categories.find? (·.expression.syntacticEq expression) then
    return entry
  let .familyApp family _ := expression
    | throwStratum .invalid m!"the selected result category has no named declaration"
  let candidates := state.categories.filter fun entry =>
    match entry.expression with
    | .familyApp other _ => other == family
    | _ => false
  let #[entry] := candidates
    | if candidates.isEmpty then
        throwStratum .invalid m!"the selected result family has no named schema"
      else throwSemanticAmbiguity m!"the selected result family has multiple named schemas"
  return entry

/-- Use the source row's complete family witness to infer bundled action parameters.
The named source is supplied by the action's metadata, not selected by carrier equality. -/
partial def bindFunctorSource (F X : Expr) : TermElabM Unit := do
  let F := F.consumeMData
  if F.isAppOf ``CategoryTheory.Functor.comp then
    let args := F.getAppArgs
    bindFunctorSource args[args.size - 2]! X
    return
  let declaration := if F.isAppOf ``CategoryTheory.Cat.Hom.toFunctor then
    F.getAppArgs.back! else F
  let state ← registryState
  let some entry := state.functors.find?
      (fun entry => declaration.getAppFn.constName? == some entry.declaration) | return
  let some category := state.category? entry.source | return
  let categoryRealization ← instantiateFresh category.realization
  let realizationType ← withTransparency .all <| whnf (← inferType categoryRealization)
  unless realizationType.isAppOf ``CasCatalogue.CategoryRealization do
    throwError "the declared source has no complete category realization"
  -- The supplied action already fixes its complete source parameters. A fresh
  -- category schema can hide them behind carrier projections (for example a
  -- module category's ring), which cannot recover the original bundle.
  let (source, _) ← realizedFunctorEndpoints (← instantiateFresh entry.realization) F
  let sourceType ← withTransparency .all <| whnf (← inferType source)
  unless sourceType.isAppOf ``CasCatalogue.CategoryRealization do
    throwError "the selected action has no complete source realization"
  unless ← withTransparency .all <| isDefEq
      sourceType.getAppArgs[sourceType.getAppNumArgs - 2]!
      realizationType.getAppArgs[realizationType.getAppNumArgs - 2]! do
    throwError "the selected action has a different declared source category"
  -- A published fibre witness can elaborate an omitted full family parameter
  -- from the supplied structured receiver. Plain category schemas have no such
  -- parameter witness; their already selected action supplies the source.
  if (← selectedFamilyParameter? categoryRealization).isSome then
    -- A complete selected action can already fix the bundled parameter. Bind that
    -- witness before comparing carrier projections with an unbundled object type.
    alignCategoryParameters categoryRealization source
    let schemaCarrier ← mkAppHere ``CategoryTheory.Bundled.α #[realizationType.getAppArgs.back!]
    unless ← withTransparency .all <| isDefEq schemaCarrier (← inferType X) do
      throwError "the supplied receiver has a different complete declared family source type"
    alignCategoryParameters categoryRealization source
  let carrier ← mkAppHere ``CategoryTheory.Bundled.α #[sourceType.getAppArgs.back!]
  unless ← withTransparency .all <| isDefEq carrier (← inferType X) do
    throwError "the supplied receiver has a different complete declared source type"
  alignCategoryParameters categoryRealization source

/-- `F.obj X`, elaborated at the current depth, so that the universe levels and parameters of `F`'s
source category are assigned by `X`'s category (a bundled category is unfolded as needed). -/
def objOf (F X : Expr) : TermElabM Expr := do
  let F ← if (← withTransparency .all <| whnf (← inferType F)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[F] else pure F
  bindFunctorSource F X
  let value ← elabTermAndSynthesize
    (← `(Prefunctor.obj (CategoryTheory.Functor.toPrefunctor $(← exprToSyntax F)) $(← exprToSyntax X)))
    none
  instantiateMVars value

/-- Apply only an accepted functor declaration, with remaining parameters inferred from
the exact receiver type. Neither source nor target parameters receive default values. -/
def applyRegisteredFunctor (entry : FunctorEntry) (receiver : Expr)
    (parameters : Array Term := #[]) (trace? : Option Trace := none) :
    TermElabM (Expr × NamedCategoryEntry) := do
  let state ← registryState
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (args, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
  let explicit := (args.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  unless parameters.size <= explicit.size do
    throwStratum .invalid m!"the registered functor has too many supplied parameters"
  for (parameter, arg) in parameters.zip explicit do
    let value ← elabTerm parameter (some (← instantiateMVars (← inferType arg)))
    unless ← isDefEq arg value do
      throwStratum .invalid m!"a supplied functor parameter has the wrong declared type"
  let F := mkAppN declaration args
  let image ← objOf F receiver
  for arg in args do
    if (← instantiateMVars arg).isMVar then
      let type ← instantiateMVars (← inferType arg)
      if (← isClass? type).isSome then
        if let some instanceValue := (← trySynthInstance type).toOption then
          discard <| isDefEq arg instanceValue
      else if !type.hasMVar && (← isProp type) then
        if let some proof ← Decide.decisionProof type then discard <| isDefEq arg proof
  let F ← instantiateMVars F
  let image ← instantiateMVars image
  let type ← instantiateMVars (← inferType image)
  if F.hasMVar || F.hasLevelMVar || image.hasMVar || image.hasLevelMVar ||
      type.hasMVar || type.hasLevelMVar then
    throwStratum .invalid m!"the registered functor requires further typed parameters"
  let checked ← objOf F receiver
  unless ← isDefEq checked image do throwError "the accepted functor action changed its receiver"
  let params := (F.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  let target ← namedCategoryFor state entry.target
  Trace.record trace? image (.functor entry.id params receiver)
  return (image, target)

/-- The accepted functor's action on an actual typed arrow. Elaboration assigns its
universe levels from the arrow's declared category, including bundled categories. -/
def mapOf (F f : Expr) : TermElabM Expr := do
  let F ← if (← withTransparency .all <| whnf (← inferType F)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[F] else pure F
  let value ← elabTermAndSynthesize
    (← `(CategoryTheory.Functor.map $(← exprToSyntax F) $(← exprToSyntax f))) none
  instantiateMVars value

/-- A comparison must have the exact supplied functors as endpoints, including their selected
category structures and parameters. An isomorphism between equal carriers is insufficient. -/
def checkRouteComparison (comparison left right : Expr) : MetaM Unit := do
  let expected ← mkAppHere ``CategoryTheory.Iso #[left, right]
  unless ← withTransparency .all <| isDefEq (← inferType comparison) expected do
    throwError "the accepted route comparison has different complete functor endpoints"

/-- The two complete composites of retained route applications, including the identity when
one side is empty. Both nonempty sides use the same composition operation as route execution. -/
def comparisonApplicationEndpoints (left right : Array Expr) : MetaM (Expr × Expr) := do
  match left.isEmpty, right.isEmpty with
  | false, false => return (← compositeOfApplications left, ← compositeOfApplications right)
  | true, false =>
      let R ← compositeOfApplications right
      return (← identityOnSourceOf R, R)
  | false, true =>
      let L ← compositeOfApplications left
      return (L, ← identityOnSourceOf L)
  | true, true => throwError "a route comparison cannot identify two empty routes"

/-- Interpret both sides with the same route semantics used for execution, retaining their
complete edge applications. An empty side is the identity on the other's exact source. -/
def routeComparisonApplications (state : RegistryState) (left right : Array EdgeRef) :
    MetaM ((Expr × Array Expr) × (Expr × Array Expr)) := do
  match left.isEmpty, right.isEmpty with
  | false, false =>
      return (← routeFunctorWithApplications state left, ← routeFunctorWithApplications state right)
  | true, false =>
      let R ← routeFunctorWithApplications state right
      return ((← identityOnSourceOf R.1, #[]), R)
  | false, true =>
      let L ← routeFunctorWithApplications state left
      return (L, (← identityOnSourceOf L.1, #[]))
  | true, true => throwError "a route comparison cannot identify two empty routes"

def routeComparisonEndpoints (state : RegistryState) (left right : Array EdgeRef) :
    MetaM (Expr × Expr) := do
  let (L, R) ← routeComparisonApplications state left right
  return (L.1, R.1)

/-- Expand the image of a composite by the constructor's accepted composition comparison.
For an empty composite its accepted identity comparison is required. The constructed proof
relates `K(composite)` to the composite of the individually mapped route edges. -/
def constructorRouteComparison (state : RegistryState) (constructor : ConstructorId)
    (refs : Array EdgeRef) (composite : Expr) : MetaM Expr := do
  let some row := state.constructor? constructor
    | throwError "a comparison names an absent category constructor"
  let some action := row.functorialAction
    | throwError "the registered constructor has no functor action"
  let source ← applyConstructorFunctor action composite
  if refs.isEmpty then
    let some identity := row.identityComparison
      | throwError "the registered constructor has no identity comparison"
    let functorType ← whnfR (← inferType composite)
    unless functorType.isAppOfArity ``CategoryTheory.Functor 4 do
      throwError "the empty route has no complete category structure"
    let args := functorType.getAppArgs
    let category ← mkAppOptM ``CategoryTheory.Cat.of #[some args[0]!, some args[1]!]
    let comparison ← applyConstructorInterface identity #[category] #[category]
    let target ← identityOnSourceOf source
    checkRouteComparison comparison source target
    check comparison
    return comparison
  let some composition := row.compositionComparison
    | throwError "the registered constructor has no composition comparison"
  let (original, applications) ← routeFunctorWithApplications state refs
  unless ← withTransparency .all <| isDefEq original composite do
    throwError "the constructor comparison changed its underlying route composite"
  let mut raw ← asFunctor applications[0]!
  let mut mapped ← applyConstructorFunctor action raw
  let mut comparison ← mkAppM ``CategoryTheory.Iso.refl #[mapped]
  for application in applications.extract 1 applications.size do
    let next ← asFunctor application
    let mappedNext ← applyConstructorFunctor action next
    let composed ← mkFunctorComp raw next
    let (C, D) ← functorCategoryBundles raw
    let (_, E) ← functorCategoryBundles next
    let expansion ← applyConstructorInterface composition #[C, D, E] #[raw, next]
    let whiskered ← mkAppHere ``CategoryTheory.Functor.isoWhiskerRight #[comparison, mappedNext]
    comparison ← mkAppHere ``CategoryTheory.Iso.trans #[expansion, whiskered]
    raw := composed
    mapped ← mkFunctorComp mapped mappedNext
  unless ← withTransparency .all <| isDefEq raw composite do
    throwError "the constructor comparison changed its underlying route composite"
  let target ← routeFunctor state (refs.map (.constructMap constructor))
  unless ← withTransparency .all <| isDefEq mapped target do
    throwError "the constructor comparison changed its individual edge actions"
  checkRouteComparison comparison source target
  check comparison
  return comparison

/-- Reconstruct one exact accepted route comparison. Constructor actions are applied from
inside out, with their published comparisons on both composite endpoints, followed by the
recorded prefix and suffix whiskering. Every step is an actual Mathlib natural isomorphism. -/
def routeComparison (state : RegistryState) (witness : RouteComparison) : MetaM Expr := do
  let some cell := state.cells.find? (·.id == witness.cell)
    | throwError "the route comparison names an absent accepted cell"
  unless cell.invertible && cell.left != cell.right do
    throwError "the accepted cell does not identify two distinct routes"
  let mut leftRefs := cell.left
  let mut rightRefs := cell.right
  let ((left, leftApplications), (right, rightApplications)) ←
    routeComparisonApplications state leftRefs rightRefs
  let mut leftApplications := leftApplications
  let mut rightApplications := rightApplications
  let mut precedingApplications : Array Expr := #[]
  let mut followingApplications : Array Expr := #[]
  let mut comparison ← instantiateFresh cell.declaration
  checkRouteComparison comparison left right
  for constructor in witness.constructors.reverse do
    let some row := state.constructor? constructor
      | throwError "the comparison names an absent category constructor"
    let some action := row.comparisonAction
      | throwError "the registered constructor has no action on comparison cells"
    let some functorAction := row.functorialAction
      | throwError "the registered constructor has no action on functors"
    let type ← whnfR (← inferType comparison)
    let leftExpansion ← constructorRouteComparison state constructor leftRefs type.getAppArgs[2]!
    let rightExpansion ← constructorRouteComparison state constructor rightRefs type.getAppArgs[3]!
    let (C, D) ← functorCategoryBundles type.getAppArgs[2]!
    let mapped ← applyConstructorInterface action #[C, D] #[comparison]
    comparison ← mkAppHere ``CategoryTheory.Iso.trans #[
      ← mkAppHere ``CategoryTheory.Iso.trans #[
        ← mkAppM ``CategoryTheory.Iso.symm #[leftExpansion], mapped], rightExpansion]
    leftRefs := leftRefs.map (.constructMap constructor)
    rightRefs := rightRefs.map (.constructMap constructor)
    leftApplications ← leftApplications.mapM (applyConstructorFunctor functorAction)
    rightApplications ← rightApplications.mapM (applyConstructorFunctor functorAction)
    let (left, right) ← comparisonApplicationEndpoints leftApplications rightApplications
    checkRouteComparison comparison left right
  unless witness.before.isEmpty do
    let (preceding, applications) ← routeFunctorWithApplications state witness.before
    precedingApplications := applications
    let (_, previousTarget) ← routeParameterEndpoints? state witness.before applications
    let (nextSource, _) ← if leftRefs.isEmpty then
      routeParameterEndpoints? state rightRefs rightApplications
    else routeParameterEndpoints? state leftRefs leftApplications
    if let (some previous, some next) := (previousTarget, nextSource) then
      alignCategoryParameters previous next
    comparison ← mkAppHere ``CategoryTheory.Functor.isoWhiskerLeft
      #[preceding, comparison]
  unless witness.after.isEmpty do
    let (_, applications) ← routeFunctorWithApplications state witness.after
    followingApplications := applications
    let (_, previousTarget) ← if leftRefs.isEmpty then
      routeParameterEndpoints? state rightRefs rightApplications
    else routeParameterEndpoints? state leftRefs leftApplications
    let (nextSource, _) ← routeParameterEndpoints? state witness.after applications
    if let (some previous, some next) := (previousTarget, nextSource) then
      alignCategoryParameters previous next
    -- Route execution composes from left to right. Whiskering by the individual
    -- accepted applications retains that association, avoiding normalization of two
    -- differently parenthesized long composites (and all their category dictionaries).
    for application in applications do
      comparison ← mkAppHere ``CategoryTheory.Functor.isoWhiskerRight
        #[comparison, ← asFunctor application]
  let (left, right) ← comparisonApplicationEndpoints
    (precedingApplications ++ leftApplications ++ followingApplications)
    (precedingApplications ++ rightApplications ++ followingApplications)
  checkRouteComparison comparison left right
  check comparison
  return ← instantiateMVars comparison

/-- Validate all retained witnesses, optionally at the exact selected receiver. Any remaining
proof hypothesis must be discharged by the existing instance/decision machinery; it is never
requested from a computational leaf. -/
def validateRouteComparisons (state : RegistryState) (witnesses : Array RouteComparison)
    (receiver? : Option Expr := none) : TermElabM (Array Expr) :=
  witnesses.mapM fun witness => do
    let comparison ← routeComparison state witness
    if let some receiver := receiver? then
      let type ← whnfR (← inferType comparison)
      discard <| objOf type.getAppArgs[2]! receiver
      discard <| objOf type.getAppArgs[3]! receiver
      for id in ← getMVars comparison do
        let argument ← instantiateMVars (mkMVar id)
        if argument.isMVar then
          let type ← instantiateMVars (← inferType argument)
          if (← isClass? type).isSome then
            if let some instanceValue := (← trySynthInstance type).toOption then
              discard <| isDefEq argument instanceValue
          else if !type.hasMVar && (← isProp type) then
            if let some proof ← Decide.decisionProof type then
              discard <| isDefEq argument proof
      let comparison ← instantiateMVars comparison
      if comparison.hasMVar || comparison.hasLevelMVar then
        throwStratum .invalid m!"the accepted route comparison requires further typed parameters"
    let comparison ← instantiateMVars comparison
    check comparison
    return comparison

/-- Check the witness provenance as well as the complete comparison terms of a method. -/
def validateResolutionComparisons (state : RegistryState) (resolution : Resolution)
    (receiver? : Option Expr := none) : TermElabM (Array Expr) := do
  let ids := (resolution.comparisonWitnesses.map (·.cell)).toList.eraseDups.toArray
  unless ids.qsort (fun a b => a.raw < b.raw) ==
      resolution.comparisons.qsort (fun a b => a.raw < b.raw) do
    throwError "the method resolution lost its accepted comparison provenance"
  validateRouteComparisons state resolution.comparisonWitnesses receiver?

/-- The property path checks the same accepted cells and constructor actions as a method. -/
def validatePropertyResolutionComparisons (state : RegistryState) (resolution : PropertyResolution)
    (receiver? : Option Expr := none) : TermElabM (Array Expr) := do
  let ids := (resolution.comparisonWitnesses.map (·.cell)).toList.eraseDups.toArray
  unless ids.qsort (fun a b => a.raw < b.raw) ==
      resolution.comparisons.qsort (fun a b => a.raw < b.raw) do
    throwError "the property resolution lost its accepted comparison provenance"
  validateRouteComparisons state resolution.comparisonWitnesses receiver?

/-- The registered object `entry` at the parameters `params`. Recorded with its explicit
parameters (the declaration's explicit arguments). -/
def object (entry : ObjectEntry) (params : Array Term) (trace? : Option Trace := none) :
    TermElabM Expr := do
  let value ← elabTermAndSynthesize (← `($(mkCIdent entry.declaration) $params*)) none
  let value ← instantiateMVars value
  if value.getAppFn.constName? == some entry.declaration then
    let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
      xs.mapM (·.fvarId!.getBinderInfo)
    let explicit := (value.getAppArgs.zip infos).filterMap fun (a, i) =>
      if i.isExplicit then some a else none
    Trace.record trace? value (.object entry.id explicit)
  return value

/-- The morphism `f : a ⟶ b`. -/
def hom (f : Term) (a b : Expr) : TermElabM Expr := do
  let expected ← mkAppM ``Quiver.Hom #[a, b]
  let value ← elabTermEnsuringType f expected
  synthesizeSyntheticMVarsNoPostponing
  mkExpectedTypeHint (← instantiateMVars value) expected

/-- The accepted presentation at a diagram, using the standard-shape diagram isomorphism. -/
def limitPresentation (row : LimitEntry) (D : Expr) : TermElabM Expr := do
  let family ← instantiateFresh row.declaration
  let familyDiagram := (← whnfR (← inferType family)).appArg!
  if ← withReducible <| isDefEq familyDiagram D then return ← instantiateMVars family
  let some isoName := row.standardization
    | throwStratum .invalid m!"the shape {row.shape} has no standard form"
  let α ← mkAppM isoName #[D]
  let standard := (← whnfR (← inferType α)).getAppArgs.back!
  unless ← withTransparency .all <| isDefEq familyDiagram standard do
    throwStratum .invalid m!"the registered {row.shape} {row.id.raw} does not apply to this diagram"
  instantiateMVars (← mkAppM (if row.colimit then ``colimitCoconeOfIso else ``limitConeOfIso)
    #[α, family])

/-- Record a direct application of an accepted named object declaration. Expected-type `id`
wrappers are removed only to inspect the application; the exact selected term remains the key. -/
def recordNamedObject (value : Expr) (trace? : Option Trace := none) : TermElabM Bool := do
  let value ← instantiateMVars value
  let state ← registryState
  let mut application := value.consumeMData
  while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
  let some entry := state.objects.find? (fun entry =>
      application.getAppFn.constName? == some entry.declaration) | return false
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  Trace.record trace? value (.object entry.id params)
  return true

/-- Record a named morphism without enumerating its possibly infinite domain. -/
def presentationArrow (entry : PresentationComparisonEntry) (iso : Expr) (inverse : Bool)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let iso ← instantiateMVars iso
  let mut application := iso.consumeMData
  while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
  unless application.getAppFn.constName? == some entry.declaration do
    throwError "the presentation comparison does not retain its accepted declaration"
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  if iso.hasMVar || iso.hasLevelMVar then
    throwError "the selected presentation has unresolved declaration arguments"
  let arrow ← mkAppM (if inverse then ``CategoryTheory.Iso.inv else ``CategoryTheory.Iso.hom) #[iso]
  Trace.record trace? arrow (.presentation entry.id params inverse)
  return arrow

def namedMorphism (entry : MorphismEntry) (value : Expr) (trace? : Option Trace := none) :
    TermElabM Unit := do
  let value ← instantiateMVars value
  let mut application := value.consumeMData
  while application.isAppOfArity ``id 2 do application := application.appArg!.consumeMData
  unless application.getAppFn.constName? == some entry.declaration do
    throwError "the named morphism does not retain its accepted declaration application"
  let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
    xs.mapM (·.fvarId!.getBinderInfo)
  let params := (application.getAppArgs.zip infos).filterMap fun (arg, info) =>
    if info.isExplicit then some arg else none
  Trace.record trace? value (.namedMorphism entry.id params)

/-- Recover a retained diagram leg as an exact application of an accepted morphism row.
Both the complete term and all declaration parameters must agree; its carrier alone never
selects a row. This includes canonical legs already named by accepted declarations. -/
def recordRegisteredMorphism (category : CategoryId) (value : Expr)
    (trace? : Option Trace := none) : TermElabM Bool := do
  let state ← registryState
  let value ← instantiateMVars value
  if value.hasMVar || value.hasLevelMVar || value.hasFVar then return false
  let mut candidates : Array (MorphismEntry × Array Expr) := #[]
  for entry in state.morphisms do
    unless entry.category == category do continue
    let params? ← withoutModifyingState do
      let application ← instantiateFresh entry.declaration
      unless ← isDefEq application value do return none
      let application ← instantiateMVars application
      if application.hasMVar || application.hasLevelMVar || application.hasFVar then return none
      let infos ← forallTelescopeReducing (← getConstInfo entry.declaration).type fun xs _ =>
        xs.mapM (·.fvarId!.getBinderInfo)
      return some ((application.getAppArgs.zip infos).filterMap fun (arg, info) =>
        if info.isExplicit then some arg else none)
    if let some params := params? then candidates := candidates.push (entry, params)
  let #[(entry, params)] := candidates | return false
  Trace.record trace? value (.namedMorphism entry.id params)
  return true

/-- Reindex using the actual base morphism and an independently registered family transport.
Every candidate is elaborated at the selected object's type. More than one candidate remains
an ambiguity; source and target parameter names never identify fibres. -/
def reindex (X : Expr) (_source : NamedCategoryEntry) (baseMorphism : Expr)
    (trace? : Option Trace := none) : TermElabM (Expr × NamedCategoryEntry) := do
  let state ← registryState
  let baseType ← inferType baseMorphism
  let mut candidates : Array (FunctorEntry × Expr × Array Expr) := #[]
  for entry in state.functors do
    let isReindex : Bool := match entry.expression.registrationKind with
      | .familyReindex .. => true
      | _ => false
    unless isReindex do continue
    let attempt : TermElabM (Option (Expr × Array Expr)) := do
      let declaration ← mkConstWithFreshMVarLevels entry.declaration
      let (args, infos, _) ← forallMetaTelescopeReducing (← inferType declaration)
      let mut assigned := false
      for arg in args do
        if (← instantiateMVars arg).isMVar then
          if ← withoutModifyingState (isDefEq (← inferType arg) baseType) then
            discard <| isDefEq arg baseMorphism
            assigned := true
            break
      unless assigned do return none
      let raw := mkAppN declaration args
      let F ← if (← whnf (← inferType raw)).isAppOf ``CategoryTheory.Cat.Hom then
        mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[raw] else pure raw
      let functorType ← whnfR (← inferType F)
      let some domain := functorType.getAppArgs[0]? | return none
      unless ← withTransparency .all <| isDefEq domain (← inferType X) do return none
      let value ← objOf F X
      let value ← instantiateMVars value
      if value.hasMVar || value.hasLevelMVar then return none
      let params ← (args.zip infos).filterMapM fun (arg, info) => do
        if info.isExplicit then return some (← instantiateMVars arg) else return none
      return some (value, params)
    let candidate ← withoutModifyingState attempt
    if let some (value, params) := candidate then candidates := candidates.push (entry, value, params)
  let #[(entry, value, params)] := candidates
    | if candidates.isEmpty then
        throwStratum .invalid m!"no registered family reindexing applies to this object and base morphism"
      else throwSemanticAmbiguity m!"multiple registered family reindexings apply: \
        {candidates.map (·.1.id.raw)}"
  let target ← namedCategoryFor state entry.target
  Trace.record trace? value (.functor entry.id params X)
  return (value, target)

/-- The registered limit (colimit) of `shape` at the diagram `D` of the category `category`: its
presentation, returned along the registered creation lift when it is computed elsewhere. -/
def limit (colimit : Bool) (shape : String) (D : Expr) (category : String)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let state ← registryState
  let some entry := state.categories.find? (·.id.raw == category)
    | throwStratum .invalid m!"no registered category {category}"
  let resolution ← match state.resolveLimit entry.id shape colimit with
    | .ok resolution => pure resolution
    | .error message => throwStratum .invalid m!"{message}"
  let some row := state.limits.find? (·.id == resolution.limit) | unreachable!
  let presentationAt := limitPresentation row
  let presentation ← match resolution.lift.bind fun id => state.lifts.find? (·.id == id) with
    | none => presentationAt D
    | some lift => do
        if colimit then
          throwStratum .invalid m!"a colimit returned along a lift is not registered"
        let U ← asFunctor (← edgeFunctor state lift.edge)
        let L ← presentationAt (← withTransparency .all <| mkFunctorComp D U)
        let evidence ← instantiateFresh lift.evidence
        let diagramType ← withTransparency .all <| whnf (← inferType D)
        unless diagramType.isAppOf ``CategoryTheory.Functor && diagramType.getAppArgs.size >= 2 do
          throwError "the creation request has no complete diagram category"
        let functorType ← withTransparency .all <| whnf (← inferType U)
        unless functorType.isAppOfArity ``CategoryTheory.Functor 4 &&
            diagramType.isAppOfArity ``CategoryTheory.Functor 4 do
          throwError "the creation request has incomplete full categorical parameters"
        let endpoints := functorType.getAppArgs
        let shape := diagramType.getAppArgs
        unless (← withTransparency .all <| isDefEq shape[2]! endpoints[0]!) &&
            (← withTransparency .all <| isDefEq shape[3]! endpoints[1]!) do
          throwError "the creation request changed its complete source category dictionary"
        let creationDeclaration ← mkConstWithFreshMVarLevels ``CategoryTheory.CreatesLimitsOfShape
        let creationType := mkAppN creationDeclaration #[endpoints[0]!, endpoints[1]!,
          endpoints[2]!, endpoints[3]!, shape[0]!, shape[1]!, U]
        unless ← withTransparency .all <| isDefEq (← inferType evidence) creationType do
          throwError "the registered creation evidence has different full functor endpoints"
        let evidence ← instantiateMVars evidence
        if evidence.hasMVar || evidence.hasLevelMVar then
          throwError "the registered creation evidence has undetermined universes or parameters"
        let lifted ← withTransparency .all <| mkAppOptM ``CasCatalogue.liftedLimitCone
          #[some endpoints[0]!, some endpoints[1]!, some endpoints[2]!, some endpoints[3]!,
            some shape[0]!, some shape[1]!, some U, some evidence, some D, some L]
        instantiateMVars lifted
  Trace.record trace? presentation (.limit row.id D resolution.lift)
  return presentation

/-- Transport a checked subobject inclusion along its accepted ambient isomorphism. -/
def subobjectAmbientTransport (value iso : Expr) : TermElabM Expr := do
  let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[value]
  let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
  let monic ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[value]
  elabTermAndSynthesize (← `(
    letI : CategoryTheory.Mono $(← exprToSyntax inclusion) := $(← exprToSyntax monic)
    let i := $(← exprToSyntax inclusion)
    let e := $(← exprToSyntax iso)
    CategoryTheory.ObjectProperty.FullSubcategory.mk
      (CategoryTheory.Arrow.mk (CategoryTheory.CategoryStruct.comp i e.inv))
      (inferInstance : CategoryTheory.Mono (CategoryTheory.CategoryStruct.comp i e.inv)))) none

/-- Use the released cartesian lift and its accepted defining-map monicity instance. -/
def liftSubobject (state : RegistryState) (entry : LiftEntry) (receiver value : Expr) :
    TermElabM Expr := do
  let evidence ← instantiateFresh entry.evidence
  let X ← mkAppM ``CategoryTheory.Arrow.left #[receiver]
  let arrow ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.obj #[value]
  let inclusion ← mkAppM ``CategoryTheory.Arrow.hom #[arrow]
  let monic ← mkAppM ``CategoryTheory.ObjectProperty.FullSubcategory.property #[value]
  let sourceCategory ← inferType X
  let sourceType ← withTransparency .all <| whnfHeadPred (← inferType receiver)
    fun type => pure (!type.isAppOf ``CategoryTheory.Arrow)
  unless sourceType.isAppOfArity ``CategoryTheory.Arrow 2 do
    throwError "the prescribed lift receiver has no complete accepted Arrow context"
  let sourceArguments := sourceType.getAppArgs
  let sourceBundle ← mkAppOptM ``CategoryTheory.Cat.of
    #[some sourceArguments[0]!, some sourceArguments[1]!]
  let #[subobjects] := state.constructors.filter
      (·.semantics == `CasCatalogue.Constructors.subobjects)
    | throwError "the prescribed lift has no unique accepted subobject constructor"
  let expectedBundle ← applyConstructorInterface subobjects.semantics
    #[sourceBundle] #[sourceBundle]
  let expected ← mkAppM ``CategoryTheory.Bundled.α #[expectedBundle]
  -- Supply the actual checked monicity evidence directly; never ask instance search
  -- to rediscover it through a fresh local abbreviation of the inclusion.
  let evidenceType ← withTransparency .all <| whnf (← inferType evidence)
  unless evidenceType.isAppOfArity ``CasCatalogue.MonoLift 5 do
    throwError "the prescribed lift does not carry complete accepted category data"
  let selected := evidenceType.getAppArgs
  unless ← withTransparency .all <| isDefEq selected[0]! sourceCategory <&&>
      isDefEq selected[1]! sourceArguments[1]! do
    throwError "the prescribed lift has a different complete source category"
  let ambient ← mkAppM ``CategoryTheory.Arrow.right #[arrow]
  unless ← withTransparency .all <| isDefEq selected[2]! (← inferType ambient) do
    throwError "the prescribed lift has a different complete target category"
  let underlying := match entry.edge with
    | .constructMap _ inner => inner
    | other => other
  let acceptedU ← asFunctor (← edgeFunctor state underlying)
  unless ← withTransparency .all <| isDefEq selected[4]! acceptedU do
    throwError "the prescribed lift has a different complete accepted action"
  let arguments := selected.map some ++ #[some evidence, some X,
    none, some inclusion, some monic]
  let hom ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.hom arguments
  let liftedMono ← withTransparency .all <| mkAppOptM ``CasCatalogue.MonoLift.hom_mono arguments
  let liftedArrow ← mkAppOptM ``CategoryTheory.Arrow.mk
    #[some selected[0]!, some selected[1]!, none, some X, some hom]
  let constructor ← mkConstWithFreshMVarLevels
    ``CategoryTheory.ObjectProperty.FullSubcategory.mk
  let (fields, _, result) ← forallMetaTelescopeReducing (← inferType constructor)
  unless ← withTransparency .all <| isDefEq result expected do
    throwError "the prescribed lift has a different complete selected subobject category"
  unless fields.size >= 2 do throwError "the subobject constructor has changed"
  unless ← withTransparency .all <| isDefEq fields[fields.size - 2]! liftedArrow do
    throwError "the prescribed lift has a different complete defining arrow"
  unless ← withTransparency .all <| isDefEq fields.back! liftedMono do
    throwError "the prescribed lift rejects its accepted defining-map monicity"
  let lifted ← instantiateMVars (mkAppN constructor fields)
  if lifted.hasMVar || lifted.hasLevelMVar then
    throwError "the prescribed lift has unresolved selected data"
  return lifted

/-- The value of the method `name` on the object `X` of `category`, and the category it is in. -/
def methodIn (name : String) (X : Expr) (expression : CategoryExpr)
    (trace? : Option Trace := none) : TermElabM (Expr × CategoryContext) := do
  let state ← registryState
  let resolution ← match state.resolveMethod expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwResolutionError state error
  discard <| validateResolutionComparisons state resolution (some X)
  let some functor := state.functor? resolution.method.functor
    | throwStratum .invalid m!"`{name}` has no registered functor"
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← routeFunctor state (resolution.route.steps.map (·.ref))) X
  let F ← registeredFunctorInstance functor
  let input ← methodArgument resolution.method image
  let value ← objOf F input
  let (_, targetBundle) ← functorCategoryBundles (← asFunctor F)
  let target : CategoryContext := {
    expression := functor.target
    bundle := (← instantiateMVars targetBundle) }
  let (value, target) ← if resolution.lifts.isEmpty then pure (value, target) else do
    let mut receivers : Array Expr := #[]
    let mut before := X
    for step in resolution.route.refs do
      receivers := receivers.push before
      before ← objOf (← edgeFunctor state step) before
    unless receivers.size == resolution.lifts.size do
      throwError "the resolved result lifts do not match the structural route"
    let mut lifted := value
    for (id, receiver) in resolution.lifts.reverse.zip receivers.reverse do
      let some entry := state.lifts.find? (·.id == id) | unreachable!
      lifted ← liftSubobject state entry receiver lifted
    let .construct arrowConstructor args := expression
      | throwError "a subobject-returning lifted method is not on an arrow category"
    unless (state.constructors.find? (·.id == arrowConstructor)).any
        (·.semantics == `CasCatalogue.Constructors.arrow) do
      throwError "the selected source category is not the accepted arrow constructor"
    let some subobjects := state.constructors.find?
        (·.semantics == `CasCatalogue.Constructors.subobjects)
      | throwError "the subobject constructor is not registered"
    let resultCategory := CategoryExpr.construct subobjects.id args
    let sourceType ← whnfR (← inferType X)
    unless sourceType.isAppOfArity ``CategoryTheory.Arrow 2 do
      throwError "the lifted result lost its actual Arrow source category"
    let sourceArguments := sourceType.getAppArgs
    let sourceBundle ← mkAppOptM ``CategoryTheory.Cat.of
      #[some sourceArguments[0]!, some sourceArguments[1]!]
    let bundle ← applyConstructorInterface subobjects.semantics #[sourceBundle] #[sourceBundle]
    pure (lifted, { expression := resultCategory, bundle := (← instantiateMVars bundle) })
  Trace.record trace? value (if resolution.lifts.isEmpty then
    .method resolution.method.id resolution.route.refs X else
    .methodWithLifts resolution.method.id resolution.route.refs resolution.lifts X)
  return (value, target)

/-- The named-category entry point uses the same expression-based method reading. -/
def method (name : String) (X : Expr) (category : NamedCategoryEntry)
    (trace? : Option Trace := none) : TermElabM (Expr × NamedCategoryEntry) := do
  let (value, context) ← methodIn name X category.expression trace?
  return (value, ← namedCategoryFor (← registryState) context.expression)

/-- The proposition that the property `name` holds of the object `X` of `category`. -/
def propertyIn (name : String) (X : Expr) (expression : CategoryExpr)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let state ← registryState
  let resolution ← match state.resolveProperty expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwResolutionError state error
  discard <| validatePropertyResolutionComparisons state resolution (some X)
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← routeFunctor state (resolution.route.steps.map (·.ref))) X
  let classifier ← classifierInstance resolution.classifier
  let holds ← elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax image))) none
  let holds ← instantiateMVars holds
  Trace.record trace? holds (.property resolution.property.id resolution.route.refs X)
  return holds

def property (name : String) (X : Expr) (category : NamedCategoryEntry)
    (trace? : Option Trace := none) : TermElabM Expr :=
  propertyIn name X category.expression trace?

end Semantic

end CasCatalogue
