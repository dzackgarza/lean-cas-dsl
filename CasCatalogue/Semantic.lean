/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CasCatalogue.Resolve
public import CasCatalogue.Trace
public import CasCatalogue.Decide
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Functor.EpiMono
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

/-- Mathlib's identification of a diagram of a standard shape with its standard form. -/
def standardFormIso : String → Option Name
  | "pullback" => some ``CategoryTheory.Limits.diagramIsoCospan
  | "product" | "coproduct" => some ``CategoryTheory.Limits.diagramIsoPair
  | "kernel" | "cokernel" | "equalizer" | "coequalizer" =>
      some ``CategoryTheory.Limits.diagramIsoParallelPair
  | _ => none

/-- Mathlib's constructor of the cones (cocones) of a standard shape from their data: the apex
and the legs, with the commutation the legs must satisfy. A cone computed by a registration is
decoded in this form (`CasCatalogue.Realize`, CC-DECODE). -/
def standardCone (shape : String) (colimit : Bool) : Option Name :=
  match shape, colimit with
  | "product", false => some ``CategoryTheory.Limits.BinaryFan.mk
  | "coproduct", true => some ``CategoryTheory.Limits.BinaryCofan.mk
  | "pullback", false => some ``CategoryTheory.Limits.PullbackCone.mk
  | "pushout", true => some ``CategoryTheory.Limits.PushoutCocone.mk
  | "equalizer", false => some ``CategoryTheory.Limits.Fork.ofι
  | "coequalizer", true => some ``CategoryTheory.Limits.Cofork.ofπ
  | "kernel", false => some ``CategoryTheory.Limits.Fork.ofι
  | "cokernel", true => some ``CategoryTheory.Limits.Cofork.ofπ
  | _, _ => none

/-- A declaration applied to fresh metavariables for all its arguments. -/
def instantiateFresh (declaration : Name) : MetaM Expr := do
  let constant ← mkConstWithFreshMVarLevels declaration
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType constant)
  return mkAppN constant args

namespace Semantic

/-- Preserve the accepted category morphism while projecting its ordinary functor action. -/
def asFunctor (F : Expr) : MetaM Expr := do
  if (← withTransparency .all <| whnf (← inferType F)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[F]
  else pure F

/-- Constructor actions consume the ordinary functor projection of their exact inner edge. -/
partial def edgeFunctor (state : RegistryState) : EdgeRef → MetaM Expr
  | .constructMap constructor inner => do
    let some action := (state.constructor? constructor).bind (·.functorialAction)
      | throwError "the registered constructor has no functorial action"
    mkAppHere action #[← asFunctor (← edgeFunctor state inner)]
  | edge => state.edgeFunctor edge

/-- Construct the route and retain the very same edge applications for semantic provenance. -/
def routeFunctorWithApplications (state : RegistryState) (route : Array EdgeRef) :
    MetaM (Expr × Array Expr) := do
  let mut result : Option Expr := none
  let mut applications : Array Expr := #[]
  for edge in route do
    let application ← edgeFunctor state edge
    applications := applications.push application
    let next ← asFunctor application
    result ← some <$> match result with
      | none => pure next
      | some previous => mkFunctorComp previous next
  let some composite := result | throwError "the empty structural route has no functor composite"
  return (composite, applications)

def routeFunctor (state : RegistryState) (route : Array EdgeRef) : MetaM Expr := do
  return (← routeFunctorWithApplications state route).1

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
      else throwStratum .semanticAmbiguity m!"the selected result family has multiple named schemas"
  return entry

/-- `F.obj X`, elaborated at the current depth, so that the universe levels and parameters of `F`'s
source category are assigned by `X`'s category (a bundled category is unfolded as needed). -/
def objOf (F X : Expr) : TermElabM Expr := do
  let F ← if (← withTransparency .all <| whnf (← inferType F)).isAppOf ``CategoryTheory.Cat.Hom then
    mkAppM ``CategoryTheory.Cat.Hom.toFunctor #[F] else pure F
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
  let some isoName := standardFormIso row.shape
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
      else throwStratum .semanticAmbiguity m!"multiple registered family reindexings apply: \
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
  let expected ← elabTermAndSynthesize
    (← `(CategoryTheory.ObjectProperty.FullSubcategory
      (fun arrow : CategoryTheory.Arrow $(← exprToSyntax sourceCategory) =>
        CategoryTheory.Mono (CategoryTheory.Arrow.hom arrow)))) none
  -- Supply the actual checked monicity evidence directly; never ask instance search
  -- to rediscover it through a fresh local abbreviation of the inclusion.
  let evidenceType ← withTransparency .all <| whnf (← inferType evidence)
  unless evidenceType.isAppOfArity ``CasCatalogue.MonoLift 5 do
    throwError "the prescribed lift does not carry complete accepted category data"
  let selected := evidenceType.getAppArgs
  unless ← withTransparency .all <| isDefEq selected[0]! sourceCategory do
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
  let liftedArrow ← mkAppM ``CategoryTheory.Arrow.mk #[hom]
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
def method (name : String) (X : Expr) (category : NamedCategoryEntry)
    (trace? : Option Trace := none) : TermElabM (Expr × NamedCategoryEntry) := do
  let state ← registryState
  let resolution ← match state.resolveMethod category.expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let some functor := state.functor? resolution.method.functor
    | throwStratum .invalid m!"`{name}` has no registered functor"
  let some target := state.category? functor.target
    | throwStratum .invalid m!"the result category of `{name}` is not a registered category"
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← routeFunctor state (resolution.route.steps.map (·.ref))) X
  let F ← registeredFunctorInstance functor
  let input ← methodArgument resolution.method image
  let value ← objOf F input
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
    let .construct arrowConstructor args := category.expression
      | throwError "a subobject-returning lifted method is not on an arrow category"
    unless (state.constructors.find? (·.id == arrowConstructor)).any
        (·.semantics == `CasCatalogue.Constructors.arrow) do
      throwError "the selected source category is not the accepted arrow constructor"
    let some subobjects := state.constructors.find?
        (·.semantics == `CasCatalogue.Constructors.subobjects)
      | throwError "the subobject constructor is not registered"
    let resultCategory := CategoryExpr.construct subobjects.id args
    let some target := state.categories.find? (·.expression.syntacticEq resultCategory)
      | throwStratum .invalid m!"the lifted subobject category has no named declaration"
    pure (lifted, target)
  Trace.record trace? value (if resolution.lifts.isEmpty then
    .method resolution.method.id resolution.route.refs X else
    .methodWithLifts resolution.method.id resolution.route.refs resolution.lifts X)
  return (value, target)

/-- The proposition that the property `name` holds of the object `X` of `category`. -/
def property (name : String) (X : Expr) (category : NamedCategoryEntry)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let state ← registryState
  let resolution ← match state.resolveProperty category.expression name #[] with
    | .ok resolution => pure resolution
    | .error error => throwStratum .invalid (error.render state)
  let image ← if resolution.route.steps.isEmpty then pure X else do
    objOf (← routeFunctor state (resolution.route.steps.map (·.ref))) X
  let classifier ← classifierInstance resolution.classifier
  let holds ← elabTermAndSynthesize (← `(CasCatalogue.Classifier.Holds
    $(← exprToSyntax classifier) $(← exprToSyntax image))) none
  let holds ← instantiateMVars holds
  Trace.record trace? holds (.property resolution.property.id resolution.route.refs X)
  return holds

end Semantic

end CasCatalogue
