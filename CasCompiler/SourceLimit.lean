module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import CasCompiler.Elaborate
public import CasCompiler.LimitSelection
public import LeanCategories.Catalogue.Registry.Semantic
import CasCompiler.LimitFamily
import CasCompiler.CreationFamily
import CasCompiler.SourceCarrier
import CasCompiler.CategoricalPointFamily
import CasCompiler.RoutedMethodFamily

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue



private def limitPresentation (row : LimitEntry) (diagram : Expr) :
    TermElabM (Option Expr) := do
  discard <| checkedDeclaration row.declaration
  let declaration ← mkConstWithFreshMVarLevels row.declaration
  let (parameters, _, result) ← forallMetaTelescopeReducing (← inferType declaration)
  let result ← whnfR result
  let constructor := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
    else ``CategoryTheory.Limits.LimitCone
  unless result.isAppOf constructor do
    throwError "the registered universal presentation has a different native result family"
  let expected ← mkAppM constructor #[diagram]
  unless ← isDefEq result expected do return none
  let presentation ← instantiateMVars (mkAppN declaration parameters)
  if presentation.hasMVar || presentation.hasLevelMVar then
    throwError "the registered universal presentation requires its complete declaration parameters"
  return some presentation




private def preparedSourceLimit (row : LimitEntry) (family : LimitFamily) (presentation : Expr)
    (construction : Name) : SourceReadM (NativeLimitInterface × Expr) := do
  unless (SelectedSourceReference.limit row).exactlyMatches (.limit family.entry) do
    liftM (m := TermElabM) <| throwError "the selected limit changed its complete original row"
  let .const declaration levels := presentation.consumeMData.getAppFn
    | liftM (m := TermElabM) <| throwError "the selected limit lost its complete native declaration application"
  unless declaration == row.declaration &&
      presentation.getAppNumArgs == family.parameterCount do
    liftM (m := TermElabM) <| throwError "the selected limit changed its complete formal parameter telescope"
  let scope ← get
  let owner ← family.prepareOwner scope.identities levels construction
  let selection ← family.ownerAt owner presentation.getAppArgs
  unless selection.source.construction == construction &&
      selection.source.interface.presentation.consumeMData.equal presentation.consumeMData do
    liftM (m := TermElabM) <| throwError "the selected limit changed its original positional application"
  return (selection.source.interface, ← owner.bind family)




opaque sourceBinaryLimit (left right : NativeSourceJudgement) (colimit : Bool) :
    SourceReadM NativeSourceJudgement := do
  let left ← if left.category.isSome then pure left else sourceSetJudgement .object left.value
  let right ← if right.category.isSome then pure right else sourceSetJudgement .object right.value


  let (left, right) ← match left.category, right.category with
    | some source, some target =>
      if source.expression.syntacticEq target.expression then pure (left, right)
      else pure (← sourceCarrier left, ← sourceCarrier right)
    | _, _ => pure (left, right)
  let some source := left.category
    | liftM (m := TermElabM) <| throwError "the source binary construction requires its selected category"
  let some target := right.category
    | liftM (m := TermElabM) <| throwError "the source binary construction requires its selected category"
  unless source.role == .object && target.role == .object do
    liftM (m := TermElabM) <| throwError "source binary construction requires objects"
  unless source.expression.syntacticEq target.expression &&
      (← isDefEq source.bundle target.bundle) do
    liftM (m := TermElabM) <| throwError "source binary construction has different complete selected categories"
  let state ← semanticState
  let #[category] := state.categories.filter (·.expression.syntacticEq source.expression)
    | liftM (m := TermElabM) <| throwUnsupportedSource "source binary construction requires its declared complete category"
  discard <| checkedDeclaration category.declaration
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[source.bundle]
  let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[source.bundle]
  let diagram ← mkAppOptM ``CategoryTheory.Limits.pair
    #[some carrier, some categoryInstance, some left.value, some right.value]
  let shape := if colimit then "coproduct" else "product"
  let mut candidates := #[]
  for row in state.limits do
    unless row.category == category.id && row.colimit == colimit && row.shape == shape do continue
    let applicable ← withoutModifyingState do
      return (← limitPresentation row diagram).isSome
    if applicable then candidates := candidates.push row
  let #[row] := candidates
    | if candidates.isEmpty then
        liftM (m := TermElabM) <| throwUnsupportedSource
          "source binary construction has no applicable declared universal presentation"
      else
        liftM (m := TermElabM) <| throwSemanticAmbiguity
          "source binary construction requires its selected universal presentation"
  let some presentation ← limitPresentation row diagram
    | liftM (m := TermElabM) <| throwError "the selected universal presentation changed its complete diagram"
  let construction ← mkFreshUserName `selectedLimit
  let family ← LimitFamily.forId row.id
  let (interface, ownerFamily) ← preparedSourceLimit row family presentation construction
  let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  unless ← isDefEq (← inferType apex) carrier do
    liftM (m := TermElabM) <| throwError "the universal presentation changed its complete selected category"


  let reference ← sourceReferenceAt (.limit row) presentation apex
  let value ← SourceReadM.select { reference with limitFamily := some family }
  return ← retainLimitConstruction ⟨value,
    some ⟨.object, source.expression, source.bundle, none,
      some ⟨row.id.raw, row.declaration, cone, colimit, source.expression, source.bundle,
        presentation, diagram, interface, construction, some ownerFamily, none, none, #[]⟩⟩⟩



private structure PreparedCreationSource where
  family : CreationFamily
  evidence : Expr
  functor : Expr
  diagram : Expr
  targetBundle : Expr
  targetPresentation : Expr
  targetFamily : LimitFamily




private def creationTargetMap (edge : EdgeRef) (functor arrow : Expr) : SourceReadM Expr := do
  let native ← mkAppM ``CategoryTheory.Functor.map #[functor, arrow]
  unless native.isAppOfArity ``CategoryTheory.Functor.map 8 do
    liftM (m := TermElabM) <| throwError "the created target map lost its native action telescope"
  let stated ← liftM (m := MetaM) <| instantiateMVars (← inferType arrow)
  let stated ← if stated.isAppOfArity ``Quiver.Hom 4 then pure stated else whnfR stated
  let inputs := if stated.isAppOfArity ``Quiver.Hom 4 then
      (native.getAppArgs.set! 5 stated.getAppArgs[2]!).set! 6 stated.getAppArgs[3]!
    else if stated.isAppOfArity ``TypeCat.Hom 2 then
      (native.getAppArgs.set! 5 stated.getAppArgs[0]!).set! 6 stated.getAppArgs[1]!
    else native.getAppArgs
  let inputs := inputs.set! 7 arrow
  let native := mkAppN native.getAppFn inputs
  check native
  let objects ← SourceActionFamily.forEdge edge
  let application ← routedActionApplication objects functor
  let .const declaration levels := application.consumeMData.getAppFn
    | liftM (m := TermElabM) <| throwError "the created target map lost its original action declaration"
  let maps ← CategoricalPointFamily.forOwner (.action edge)
  unless declaration == objects.declaration && declaration == maps.declaration do
    liftM (m := TermElabM) <| throwError "the created target map changed its original action owner"
  let declarationInputs := application.getAppArgs
  let parameters := declarationInputs ++ inputs.extract 5 8
  let (selected, bundle) ← maps.arrowAt levels parameters
  unless ← isDefEq selected native do
    liftM (m := TermElabM) <| throwError "the created target map changed its original native action"
  let source ← SourceReadM.select (← objects.selected levels declarationInputs inputs[5]!)
  let target ← SourceReadM.select (← objects.selected levels declarationInputs inputs[6]!)
  let originalType ← inferType native
  let originalType ← if originalType.isAppOfArity ``Quiver.Hom 4 then pure originalType
    else whnfR originalType
  unless originalType.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the created target map lost its complete native Hom interface"
  let expected := mkAppN originalType.getAppFn
    ((originalType.getAppArgs.set! 2 source).set! 3 target)
  let (domain, _) ← categoricalPointEndpoints selected
  let identity ← categoricalPointIdentity bundle domain
  let family ← if (← maps.carrierFamily?).isSome then maps.asReference else maps.asWhole
  let value ← family.selected levels parameters domain { value := identity }
  SourceReadM.select value (some expected)

private def prepareCreatedLimitCandidate (state : SemanticState)
    (selected : NativeSourceCategory) (lift : LiftEntry) (target : NamedCategoryEntry)
    (row : LimitEntry) (maps : Array NativeSourceJudgement) :
    SourceReadM (Option PreparedCreationSource) := do
  let some steps := state.routeEdges? selected.expression target.expression #[lift.edge]
    | liftM (m := TermElabM) <| throwError "the selected creation lift is not a route of its own original step"
  let some diagram ← CreationFamily.diagramAt? row selected.bundle (maps.map (·.value))
    | return none
  let routed ← nativeRouteFunctor state
    { source := selected.expression, target := target.expression, steps } selected.bundle
  let family ← CreationFamily.forLift lift
  let some evidence ← family.evidenceAt? routed.functor diagram | return none
  let mapped ← maps.mapM fun map =>
    creationTargetMap lift.edge routed.functor map.value
  let some targetPresentation ←
      CreationFamily.presentationAt? row routed.target mapped | return none
  let mappedDiagram ← mkAppM ``CategoryTheory.Functor.comp #[diagram, routed.functor]


  discard <| prepareLimitInterface row targetPresentation (some mappedDiagram)
  return some ⟨family, evidence, routed.functor, diagram, routed.target, targetPresentation,
    ← LimitFamily.forId row.id⟩




private def creationSourceOwner (prepared : PreparedCreationSource)
    (selected : NativeSourceCategory) (row : LimitEntry) (targetOwner : Expr)
    (targetTemplate : SelectedLimitOwner Expr) (construction : Name) (diagram : Expr) :
    SourceReadM NativeLimitSelection := do
  let (_, sourceArguments) ← LimitFamily.diagramPorts diagram
  let mapped ← sourceArguments.mapM fun argument =>
    creationTargetMap prepared.family.entry.edge prepared.functor argument
  let some targetPresentation ←
      CreationFamily.presentationAt? row prepared.targetBundle mapped
    | liftM (m := TermElabM) <| throwError "the selected creation lost its original target family at the formal source inputs"
  let target ← prepared.targetFamily.ownerAt targetTemplate targetPresentation.getAppArgs
  unless target.source.construction == construction && target.source.row == row.id.raw &&
      target.source.interface.presentation.equal targetPresentation do
    liftM (m := TermElabM) <| throwError "the created source changed its exact target owner application"
  let mappedDiagram ← mkAppM ``CategoryTheory.Functor.comp #[diagram, prepared.functor]
  let interface ← NativeLimitInterface.withRequestedDiagram target.source.interface row mappedDiagram
  let creation ← prepared.family.interfaceAt prepared.evidence prepared.functor diagram interface
  let presentation ← NativeLimitCreationInterface.presentation creation
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  NativeLimitSelection.ofSource {
    row := row.id.raw, declaration := row.declaration, cone, colimit := false
    category := selected.expression, bundle := selected.bundle, presentation, diagram, interface
    construction, ownerFamily := some targetOwner, creation := some creation } apex



private partial def creationSourceTemplate (prepared : PreparedCreationSource)
    (selected : NativeSourceCategory) (row : LimitEntry) (targetOwner : Expr)
    (targetTemplate : SelectedLimitOwner Expr) (construction : Name) (template : Expr) :
    SourceReadM (SelectedLimitOwner Expr) := do
  match template with
  | .lam name domain body binderInfo =>
    SourceReadM.withBinder name domain none binderInfo
      (fun binding owner => do
        let owner ← owner.mapM fun field =>
          mkLambdaFVars #[binding.expression] field (usedOnly := false) (usedLetOnly := false)
        return { owner with formalBindings := #[binding.id] ++ owner.formalBindings })
      (fun parameter =>
        creationSourceTemplate prepared selected row targetOwner targetTemplate construction
          (body.instantiate1 parameter))
  | .letE name type value body _ =>
    SourceReadM.withBinder name type (some value) .default
      (fun binding owner => owner.mapM fun field =>
        mkLetFVars #[binding.expression] field (usedLetOnly := false)
          (generalizeNondepLet := false))
      (fun parameter =>
        creationSourceTemplate prepared selected row targetOwner targetTemplate construction
          (body.instantiate1 parameter))
  | diagram =>
    return ⟨← creationSourceOwner prepared selected row targetOwner targetTemplate
      construction diagram, #[]⟩








opaque sourceCreatedLimit? (state : SemanticState) (shape : String)
    (selected : NativeSourceCategory) (maps : Array NativeSourceJudgement) :
    SourceReadM (Option NativeSourceJudgement) := do
  let mut candidates : Array (LiftEntry × NamedCategoryEntry × LimitEntry) := #[]
  for lift in state.lifts do
    unless lift.kind == .createsLimits shape do continue
    let #[edge] := state.structuralEdges.filter (·.ref == lift.edge)
      | liftM (m := TermElabM) <| throwError "the selected creation lift lost its unique original structural edge"
    unless edge.source.syntacticEq selected.expression do continue
    for target in state.categories do
      unless target.expression.syntacticEq edge.target do continue
      for row in state.limits do
        unless !row.colimit && row.category == target.id && row.shape == shape do continue
        let applicable ← SourceReadM.inspect do
          return (← prepareCreatedLimitCandidate state selected lift target row maps).isSome
        if applicable then candidates := candidates.push (lift, target, row)
  let #[(lift, target, row)] := candidates
    | if candidates.isEmpty then return none
      else
        liftM (m := TermElabM) <| throwSemanticAmbiguity
          m!"the created {shape} has several applicable accepted lift/presentation pairs"
  let some prepared ← prepareCreatedLimitCandidate state selected lift target row maps
    | liftM (m := TermElabM) <| throwError "the selected creation changed its complete native applicability"
  let construction ← mkFreshUserName `selectedLimit
  let (_, ownerFamily) ←
    preparedSourceLimit row prepared.targetFamily prepared.targetPresentation construction
  let (sourceTelescope, positions) ← CreationFamily.sourceTelescope prepared.diagram
  let scope ← get
  let targetTemplate ← SelectedLimitOwner.ofBinding scope.context scope.selections ownerFamily
  let creationTemplate ← creationSourceTemplate prepared selected row ownerFamily
    targetTemplate construction sourceTelescope
  let creationFamily ← creationTemplate.bind prepared.targetFamily
    (some (prepared.family, prepared.targetFamily))
  let arguments ← positions.mapM fun index => do
    let some argument := prepared.diagram.getAppArgs[index]?
      | liftM (m := TermElabM) <| throwError "the created source lost an original constructor input position"
    pure argument
  let retained ← creationTemplate.specialize arguments
  let source := { retained.source with
    ownerFamily := some ownerFamily
    creationFamily := some creationFamily
    creationInputs := positions }
  let reference ← sourceReferenceAt (.limit row) prepared.targetPresentation retained.receiver
  let value ← SourceReadM.select { reference with
    limitFamily := some prepared.targetFamily
    creationOwner := some (prepared.family, prepared.targetFamily) }
  return some (← retainLimitConstruction {
    value
    category := some {
      role := .object, expression := selected.expression, bundle := selected.bundle,
      limit := some source } })






opaque sourceNamedLimit (shape : String) (maps : Array NativeSourceJudgement) :
    SourceReadM (Option NativeSourceJudgement) := do
  let state ← semanticState
  let rows := state.limits.filter (·.shape == shape)
  if rows.isEmpty then return none
  let some selected := maps[0]?.bind (·.category)
    | liftM (m := TermElabM) <| throwError "the universal construction {shape} requires maps of a selected category"
  unless maps.all (·.category.any (·.role == .morphism)) do
    liftM (m := TermElabM) <| throwError "the universal construction {shape} is applied to the maps of its diagram"
  let references := Array.replicate maps.size (← liftM (m := TermElabM) getRef)
  let present (row : LimitEntry) : TermElabM (Option Expr) := do
    discard <| checkedDeclaration row.declaration
    let declaration ← mkConstWithFreshMVarLevels row.declaration
    let explicitCount ← withoutModifyingState do
      let (_, binders, result) ← forallMetaTelescopeReducing (← inferType declaration)
      let constructor := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
        else ``CategoryTheory.Limits.LimitCone
      unless (← whnfR result).isAppOf constructor do
        liftM (m := TermElabM) <| throwError "the registered universal presentation has a different native result family"
      return (binders.filter (·.isExplicit)).size
    unless maps.size == explicitCount do return none
    let applied ← elabSourceApplicationApplicable declaration references none fun index _ => do
      let some map := maps[index]?
        | liftM (m := TermElabM) <| throwError "the universal presentation lost an original map"
      return .ok map.value
    let .ok (value, _) := applied | return none
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      liftM (m := TermElabM) <| throwError "the presentation of {shape} has undetermined parameters"
    return some value
  let mut candidates := #[]
  for row in rows do

    let accepts ← withoutModifyingState do
      return (← present row).isSome
    if accepts then candidates := candidates.push row
  if candidates.isEmpty then
    if let some created ← sourceCreatedLimit? state shape selected maps then return some created
  let #[row] := candidates
    | if candidates.isEmpty then
        liftM (m := TermElabM) <| throwUnsupportedSource m!"no registered {shape} accepts these maps"
      else liftM (m := TermElabM) <| throwSemanticAmbiguity s!"several registered presentations of {shape} accept these maps"
  let some presentation ← present row
    | liftM (m := TermElabM) <| throwError "the selected universal presentation no longer accepts its original maps"
  let construction ← mkFreshUserName `selectedLimit
  let family ← LimitFamily.forId row.id
  let (interface, ownerFamily) ← preparedSourceLimit row family presentation construction
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  let reference ← sourceReferenceAt (.limit row) presentation apex
  let value ← SourceReadM.select { reference with limitFamily := some family }
  return some (← retainLimitConstruction ⟨value,
    some ⟨.object, selected.expression, selected.bundle, none,
      some ⟨row.id.raw, row.declaration, cone, row.colimit,
        selected.expression, selected.bundle, presentation, interface.diagram, interface,
        construction, some ownerFamily, none, none, #[]⟩⟩⟩)




private partial def constructionCases (indexType : Expr) : TermElabM (Array Expr) := do
  let nativeType ← instantiateMVars (← withTransparency .all <| whnf indexType)
  if nativeType.hasMVar || nativeType.hasLevelMVar then
    throwStratum .invalid m!"the construction index type is not determined"
  let .const name levels := nativeType.getAppFn
    | throwStratum .invalid m!"the construction index {indexType} is not a finite native enumeration"
  let .inductInfo info ← getConstInfo name
    | throwStratum .invalid m!"the construction index {indexType} has no native constructor schema"
  unless !info.isRec && info.numIndices == 0 &&
      nativeType.getAppNumArgs == info.numParams do
    throwStratum .invalid m!"an ordinal cannot select a recursive or indexed constructor of {indexType}"
  let mut alternatives := #[]
  for constructor in info.ctors do
    let .ctorInfo constructorInfo ← getConstInfo constructor | unreachable!
    let head := mkAppN (mkConst constructor levels) nativeType.getAppArgs
    let values ← forallTelescopeReducing (← inferType head) fun fields result => do
      unless fields.size == constructorInfo.numFields && (← isDefEq result nativeType) do
        throwStratum .invalid m!"the construction index lost its original constructor telescope"
      let mut values := #[head]
      for field in fields, index in [:fields.size] do
        let domain ← inferType field
        if (← isProp domain) ||
            (fields.extract 0 index).any (fun prior => domain.containsFVar prior.fvarId!) then
          throwStratum .invalid m!"an ordinal cannot supply proof or dependent constructor fields of {indexType}"
        let choices ← constructionCases domain
        let mut next := #[]
        for value in values do
          for choice in choices do
            next := next.push (mkApp value choice)
        values := next
      return values
    for value in values do
      unless ← isDefEq (← inferType value) indexType do
        throwStratum .invalid m!"the index constructor does not inhabit {indexType}"
      check value
    alternatives := alternatives ++ values
  return alternatives






private partial def constructionIndex (indexType : Expr) (ordinal : Nat) : TermElabM Expr := do
  let indexType ← instantiateMVars (← whnfR indexType)
  if indexType.hasMVar || indexType.hasLevelMVar then
    throwStratum .invalid m!"the construction index type is not determined"
  if indexType.isAppOfArity ``CategoryTheory.Discrete 1 then
    let selected ← constructionIndex indexType.appArg! ordinal
    let index ← mkAppOptM ``CategoryTheory.Discrete.mk
      #[some indexType.appArg!, some selected]
    unless ← isDefEq (← inferType index) indexType do
      throwStratum .invalid m!"the index constructor does not inhabit {indexType}"
    return index
  if indexType.isConstOf ``Nat then return mkNatLit ordinal
  if indexType.isAppOfArity ``Fin 1 then
    let bound := indexType.appArg!
    let below ← mkAppM ``LT.lt #[mkNatLit ordinal, bound]
    let proof ← try mkDecideProof below
      catch _ => throwStratum .invalid m!"the construction index {ordinal} is outside {indexType}"
    return mkApp3 (mkConst ``Fin.mk) bound (mkNatLit ordinal) proof
  let alternatives ← constructionCases indexType
  let some index := alternatives[ordinal]?
    | throwStratum .invalid m!"the construction index {ordinal} is outside {indexType}"
  return index








def sourceLimitLeg? (receiver : NativeSourceJudgement) (ordinal : Nat) :
    SourceReadM (Option NativeSourceJudgement) := do
  let some category := receiver.category | return none
  let some selection := category.limit | return none
  let some retained ← SourceReadM.selection? receiver.value
    | liftM (m := TermElabM) <| throwError "the selected construction lost its original typed reference"
  let some presentation ← sourceApplication? selection.declaration retained
    | liftM (m := TermElabM) <| throwError "the selected construction lost its original registered application"
  let some (.limit row) := retained.reference
    | liftM (m := TermElabM) <| throwError "the selected construction changed its original registered row"
  let cone := selection.cone
  let colimit := selection.colimit
  let leg ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.ι
    else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[leg]
  let .forallE _ indexType _ _ ← whnf (← inferType component)
    | liftM (m := TermElabM) <| throwError "the defining leg has no shape index"
  let index ← constructionIndex indexType ordinal
  let native := mkApp component index
  check native
  let homType ← inferType native
  let homType ← if homType.isAppOfArity ``Quiver.Hom 4 then pure homType else whnfR homType
  unless homType.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the defining leg lost its complete native morphism type"
  let endpoints := homType.getAppArgs.set! (if colimit then 3 else 2) receiver.value
  let expected := mkAppN homType.getAppFn endpoints
  let hom ← retainLimitLeg category receiver.value index native (some expected)
  let some selected ← SourceReadM.selection? hom
    | liftM (m := TermElabM) <| throwError "the defining leg lost its original typed component"
  let reference ← sourceReferenceAt (.limit row) presentation hom
  let hom ← selectMorphism { selected with
      value := hom
      reference := reference.reference
      originalApplication := reference.originalApplication
      legOrdinal := some ordinal }
    (fun value expected => SourceReadM.select value expected) (some selection.bundle)
  return some ⟨hom, some ⟨.morphism, selection.category, selection.bundle, none, none⟩⟩

end CasCompiler
