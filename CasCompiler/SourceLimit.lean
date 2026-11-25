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

-- Match the complete native diagram, including its category structure, before
-- projecting any field. Reuse: LimitEntry and the native LimitCone/ColimitCocone family.
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

/-- Prepare the original owner under every formal M parameter before substituting actual
source arguments. Equal actual terms therefore retain their different declaration positions.
The returned template is also the authority for later whole-cone demand. -/
private def preparedSourceLimit (row : LimitEntry) (presentation : Expr)
    (construction : Name) : MetaM (NativeLimitInterface × Expr) := do
  let family ← LimitFamily.forId row.id
  let .const declaration levels := presentation.consumeMData.getAppFn
    | throwError "the selected limit lost its complete native declaration application"
  unless declaration == row.declaration &&
      presentation.getAppNumArgs == family.parameterCount do
    throwError "the selected limit changed its complete formal parameter telescope"
  let ownerFamily ← family.prepareOwner levels construction
  let owner := ownerFamily.betaRev presentation.getAppArgs.reverse (preserveMData := true)
  check owner
  let some selection ← NativeLimitSelection.ofExpr? owner
    | throwError "the selected limit lost its original formal owner application"
  family.requireInterface selection.source
  unless selection.source.construction == construction &&
      selection.source.interface.presentation.consumeMData.equal presentation.consumeMData do
    throwError "the selected limit changed its original positional application"
  return (selection.source.interface, ownerFamily)

/-- Form the declared binary presentation at the original complete source objects.
Reuse: Limits.pair, LimitEntry and the accepted native cone/cocone projections.
The category bundle fixes the diagram's chosen structure and dependent parameters. -/
opaque sourceBinaryLimit (left right : NativeSourceJudgement) (colimit : Bool) :
    TermElabM NativeSourceJudgement := do
  let left ← if left.category.isSome then pure left else sourceSetJudgement .object left.value
  let right ← if right.category.isSome then pure right else sourceSetJudgement .object right.value
  -- Objects of different selected categories meet in sets: each operand is its carrier, read
  -- through its whole structural carrier route (`Fin(2) × ℤ/3`).
  let (left, right) ← match left.category, right.category with
    | some source, some target =>
      if source.expression.syntacticEq target.expression then pure (left, right)
      else pure (← sourceCarrier left, ← sourceCarrier right)
    | _, _ => pure (left, right)
  let some source := left.category
    | throwError "the source binary construction requires its selected category"
  let some target := right.category
    | throwError "the source binary construction requires its selected category"
  unless source.role == .object && target.role == .object do
    throwError "source binary construction requires objects"
  unless source.expression.syntacticEq target.expression &&
      (← isDefEq source.bundle target.bundle) do
    throwError "source binary construction has different complete selected categories"
  let state ← semanticState
  let #[category] := state.categories.filter (·.expression.syntacticEq source.expression)
    | throwUnsupportedSource "source binary construction requires its declared complete category"
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
        throwUnsupportedSource
          "source binary construction has no applicable declared universal presentation"
      else
        throwSemanticAmbiguity
          "source binary construction requires its selected universal presentation"
  let some presentation ← limitPresentation row diagram
    | throwError "the selected universal presentation changed its complete diagram"
  let construction ← mkFreshUserName `selectedLimit
  let (interface, ownerFamily) ← preparedSourceLimit row presentation construction
  let cone ← mkAppM (if colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  unless ← isDefEq (← inferType apex) carrier do
    throwError "the universal presentation changed its complete selected category"
  -- The apex is the registered limit's named object at its diagram, as for a limit named by
  -- its shape: the lowerer sends it as that row's descriptor, not the presentation record.
  let value ← sourceReferenceAt ``LimitEntry row.id.raw row.declaration presentation apex
  let cone ← retainSourceApplication row.declaration presentation cone
  return ← retainLimitConstruction ⟨value,
    some ⟨.object, source.expression, source.bundle, none,
      some ⟨row.id.raw, row.declaration, cone, colimit, source.expression, source.bundle,
        presentation, diagram, interface, construction, some ownerFamily, none, none, #[]⟩⟩⟩

/-- Typed inputs of one applicable accepted creation/presentation pair. This is source
preparation only; the actual target completion and universal data remain runtime inputs. -/
private structure PreparedCreationSource where
  family : CreationFamily
  evidence : Expr
  functor : Expr
  diagram : Expr
  targetBundle : Expr
  targetPresentation : Expr

/-- Retain the selected action's complete declaration and the original arrow slots before
forming the target presentation. Its implicit object parameters use that same action's object
family; the native Hom keeps its original universe, carrier and Quiver dictionary. -/
private def creationTargetMap (edge : EdgeRef) (functor arrow : Expr) : MetaM Expr := do
  let native ← mkAppM ``CategoryTheory.Functor.map #[functor, arrow]
  unless native.isAppOfArity ``CategoryTheory.Functor.map 8 do
    throwError "the created target map lost its native action telescope"
  let stated ← instantiateMVars (← inferType arrow)
  let stated ← if stated.isAppOfArity ``Quiver.Hom 4 then pure stated else whnfR stated
  let inputs := if stated.isAppOfArity ``Quiver.Hom 4 then
      (native.getAppArgs.set! 5 stated.getAppArgs[2]!).set! 6 stated.getAppArgs[3]!
    else if stated.isAppOfArity ``TypeCat.Hom 2 then
      (native.getAppArgs.set! 5 stated.getAppArgs[0]!).set! 6 stated.getAppArgs[1]!
    else native.getAppArgs
  let inputs := inputs.set! 7 arrow
  let native := mkAppN native.getAppFn inputs
  check native
  let application ← routedActionApplication edge functor
  let .const declaration levels := application.consumeMData.getAppFn
    | throwError "the created target map lost its original action declaration"
  let objects ← SourceActionFamily.forEdge edge
  let maps ← CategoricalPointFamily.forOwner (.action edge)
  unless declaration == objects.declaration && declaration == maps.declaration do
    throwError "the created target map changed its original action owner"
  let declarationInputs := application.getAppArgs
  let parameters := declarationInputs ++ inputs.extract 5 8
  let (selected, bundle) ← maps.arrowAt levels parameters
  unless ← isDefEq selected native do
    throwError "the created target map changed its original native action"
  let source ← objects.mark levels declarationInputs inputs[5]!
  let target ← objects.mark levels declarationInputs inputs[6]!
  let originalType ← inferType native
  let originalType ← if originalType.isAppOfArity ``Quiver.Hom 4 then pure originalType
    else whnfR originalType
  unless originalType.isAppOfArity ``Quiver.Hom 4 do
    throwError "the created target map lost its complete native Hom interface"
  let expected := mkAppN originalType.getAppFn
    ((originalType.getAppArgs.set! 2 source).set! 3 target)
  let (domain, _) ← categoricalPointEndpoints selected
  let identity ← categoricalPointIdentity bundle domain
  let family ← if (← maps.carrierFamily?).isSome then maps.asReference else maps.asWhole
  let value ← family.mark levels parameters domain identity
  let value ← mkExpectedTypeHint value expected
  check value
  return value

private def prepareCreatedLimitCandidate (state : SemanticState)
    (selected : NativeSourceCategory) (lift : LiftEntry) (target : NamedCategoryEntry)
    (row : LimitEntry) (maps : Array NativeSourceJudgement) :
    TermElabM (Option PreparedCreationSource) := do
  let some steps := state.routeEdges? selected.expression target.expression #[lift.edge]
    | throwError "the selected creation lift is not a route of its own original step"
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
  -- Validate the same original comparison before treating this pair as applicable.
  -- The final selection retains its original whole owner family instead of this probe.
  discard <| prepareLimitInterface row targetPresentation (some mappedDiagram)
  return some ⟨family, evidence, routed.functor, diagram, routed.target, targetPresentation⟩

/-- Prepare the fixed selected creation under its source constructor's original formal inputs.
The same retained target owner family supplies its original constructor universes and schema;
only its declared parameter positions are substituted. -/
private def creationSourceOwner (prepared : PreparedCreationSource)
    (selected : NativeSourceCategory) (row : LimitEntry) (targetOwner : Expr)
    (construction : Name) (diagram : Expr) : TermElabM NativeSourceJudgement := do
  let (_, sourceArguments) ← LimitFamily.diagramPorts diagram
  let mapped ← sourceArguments.mapM fun argument =>
    creationTargetMap prepared.family.entry.edge prepared.functor argument
  let some targetPresentation ←
      CreationFamily.presentationAt? row prepared.targetBundle mapped
    | throwError "the selected creation lost its original target family at the formal source inputs"
  let targetApplication := targetOwner.betaRev targetPresentation.getAppArgs.reverse (preserveMData := true)
  check targetApplication
  let some target ← NativeLimitSelection.ofExpr? targetApplication
    | throwError "the created source lost its original complete target owner family"
  unless target.source.construction == construction && target.source.row == row.id.raw &&
      target.source.interface.presentation.equal targetPresentation do
    throwError "the created source changed its exact target owner application"
  let mappedDiagram ← mkAppM ``CategoryTheory.Functor.comp #[diagram, prepared.functor]
  let interface ← target.source.interface.withRequestedDiagram row mappedDiagram
  let creation ← prepared.family.interfaceAt prepared.evidence prepared.functor diagram interface
  let presentation ← creation.presentation
  let cone ← mkAppM ``CategoryTheory.Limits.LimitCone.cone #[presentation]
  let apex ← mkAppM ``CategoryTheory.Limits.Cone.pt #[cone]
  let value ← sourceReferenceAt ``LimitEntry row.id.raw row.declaration targetPresentation apex
  let cone ← retainSourceApplication row.declaration targetPresentation cone
  return ← retainLimitConstruction {
    value
    category := some {
      role := .object, expression := selected.expression, bundle := selected.bundle
      limit := some {
        row := row.id.raw, declaration := row.declaration, cone, colimit := false
        category := selected.expression, bundle := selected.bundle, presentation, diagram, interface
        construction, ownerFamily := some targetOwner, creation := some creation } } }

/-- Resolve every applicable accepted creation/presentation pair, independently of provider
availability and storage order. The diagram constructor comes from the declared standardization.
Only an actual absence or failed native applicability is skipped; required-data errors propagate.

The explicit state is the ordinary accepted source inventory (as in nativeRouteFunctor).
It also permits the original multiplicity controls to exercise both inventory orders without
declaring new mathematical examples or changing the formal operation. -/
opaque sourceCreatedLimit? (state : SemanticState) (shape : String)
    (selected : NativeSourceCategory) (maps : Array NativeSourceJudgement) :
    TermElabM (Option NativeSourceJudgement) := do
  let mut candidates : Array (LiftEntry × NamedCategoryEntry × LimitEntry) := #[]
  for lift in state.lifts do
    unless lift.kind == .createsLimits shape do continue
    let #[edge] := state.structuralEdges.filter (·.ref == lift.edge)
      | throwError "the selected creation lift lost its unique original structural edge"
    unless edge.source.syntacticEq selected.expression do continue
    for target in state.categories do
      unless target.expression.syntacticEq edge.target do continue
      for row in state.limits do
        unless !row.colimit && row.category == target.id && row.shape == shape do continue
        let applicable ← withoutModifyingState do
          return (← prepareCreatedLimitCandidate state selected lift target row maps).isSome
        if applicable then candidates := candidates.push (lift, target, row)
  let #[(lift, target, row)] := candidates
    | if candidates.isEmpty then return none
      else
        throwSemanticAmbiguity
          m!"the created {shape} has several applicable accepted lift/presentation pairs"
  let some prepared ← prepareCreatedLimitCandidate state selected lift target row maps
    | throwError "the selected creation changed its complete native applicability"
  let construction ← mkFreshUserName `selectedLimit
  let (_, ownerFamily) ←
    preparedSourceLimit row prepared.targetPresentation construction
  let (sourceTelescope, positions) ← CreationFamily.sourceTelescope prepared.diagram
  let creationFamily ← lambdaTelescope sourceTelescope fun parameters diagram => do
    let owner ← creationSourceOwner prepared selected row ownerFamily construction diagram
    mkLambdaFVars parameters owner.value (usedOnly := false) (usedLetOnly := false)
  check creationFamily
  let arguments ← positions.mapM fun index => do
    let some argument := prepared.diagram.getAppArgs[index]?
      | throwError "the created source lost an original constructor input position"
    pure argument
  let original := creationFamily.betaRev arguments.reverse (preserveMData := true)
  check original
  let some retained ← NativeLimitSelection.ofExpr? original
    | throwError "the created source lost its retained original source-owner family"
  let source := { retained.source with
    ownerFamily := some ownerFamily
    creationFamily := some creationFamily
    creationInputs := positions }
  return some (← retainLimitConstruction {
    value := retained.receiver
    category := some {
      role := .object, expression := selected.expression, bundle := selected.bundle,
      limit := some source } })

/-- A registered limit or colimit named by its shape and applied to the maps of its diagram
(`pullback(f, g)`, `cokernel(m)`): the apex of the declared cone or cocone at those maps, in the
category of the maps. Reuse: LimitEntry and the native LimitCone/ColimitCocone family. A row
whose declaration does not accept the maps is not a candidate; several accepting rows are a
semantic ambiguity. -/
opaque sourceNamedLimit (shape : String) (maps : Array NativeSourceJudgement) :
    TermElabM (Option NativeSourceJudgement) := do
  let state ← semanticState
  let rows := state.limits.filter (·.shape == shape)
  if rows.isEmpty then return none
  let some selected := maps[0]?.bind (·.category)
    | throwError "the universal construction {shape} requires maps of a selected category"
  unless maps.all (·.category.any (·.role == .morphism)) do
    throwError "the universal construction {shape} is applied to the maps of its diagram"
  let references := Array.replicate maps.size (← getRef)
  let present (row : LimitEntry) : TermElabM (Option Expr) := do
    discard <| checkedDeclaration row.declaration
    let declaration ← mkConstWithFreshMVarLevels row.declaration
    let explicitCount ← withoutModifyingState do
      let (_, binders, result) ← forallMetaTelescopeReducing (← inferType declaration)
      let constructor := if row.colimit then ``CategoryTheory.Limits.ColimitCocone
        else ``CategoryTheory.Limits.LimitCone
      unless (← whnfR result).isAppOf constructor do
        throwError "the registered universal presentation has a different native result family"
      return (binders.filter (·.isExplicit)).size
    unless maps.size == explicitCount do return none
    let applied ← elabSourceApplicationApplicable declaration references none fun index _ => do
      let some map := maps[index]?
        | throwError "the universal presentation lost an original map"
      return .ok map.value
    let .ok (value, _) := applied | return none
    let value ← instantiateMVars value
    if value.hasMVar || value.hasLevelMVar then
      throwError "the presentation of {shape} has undetermined parameters"
    return some value
  let mut candidates := #[]
  for row in rows do
    -- Applicability is the declaration's own typing at the actual maps.
    let accepts ← withoutModifyingState do
      return (← present row).isSome
    if accepts then candidates := candidates.push row
  if candidates.isEmpty then
    if let some created ← sourceCreatedLimit? state shape selected maps then return some created
  let #[row] := candidates
    | if candidates.isEmpty then
        throwUnsupportedSource m!"no registered {shape} accepts these maps"
      else throwSemanticAmbiguity s!"several registered presentations of {shape} accept these maps"
  let some presentation ← present row
    | throwError "the selected universal presentation no longer accepts its original maps"
  let construction ← mkFreshUserName `selectedLimit
  let (interface, ownerFamily) ← preparedSourceLimit row presentation construction
  let cone ← mkAppM (if row.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
    else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
  let apex ← mkAppM (if row.colimit then ``CategoryTheory.Limits.Cocone.pt
    else ``CategoryTheory.Limits.Cone.pt) #[cone]
  let value ← sourceReferenceAt ``LimitEntry row.id.raw row.declaration presentation apex
  let cone ← retainSourceApplication row.declaration presentation cone
  return some (← retainLimitConstruction ⟨value,
    some ⟨.object, selected.expression, selected.bundle, none,
      some ⟨row.id.raw, row.declaration, cone, row.colimit,
        selected.expression, selected.bundle, presentation, interface.diagram, interface,
        construction, some ownerFamily, none, none, #[]⟩⟩⟩)

/-- Read finite native constructor syntax at the original index type. Type synonyms are
transparent to this schema check; constructor fields must themselves have finite, independent
native constructor schemas. No runtime data, proof inhabitant or diagram port is consulted. -/
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

/-- The object of a diagram's index type that the ordinal `ordinal` names: the number itself in
`ℕ`, `⟨ordinal, _⟩` in `Fin n` when it is below `n`, else the `ordinal`-th constructor of a closed
enumeration. A native Discrete index wraps that same underlying selection by Discrete.mk.
Any other index, or an ordinal outside it, is invalid.
Reference: the original reader's `constructionIndex` (CasCatalogue/Language.lean). -/
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

/-- `K.leg(j)`: the defining leg of the registered limit or colimit `K` at the object of its shape
that the ordinal `j` names (constitution C7: a universal construction supplies its defining maps).
The row and the cone or cocone are the selection that the formation of `K` retained in its
judgement (constitution C23); a receiver with no such selection is not a limit. The leg is the
cone's `π` or the cocone's `ι` at that object, marked with the limit's row and the ordinal, so
that it is sent as the limit's named leg and not unfolded (C22). Reference: the original reader's
`constructionLeg` (CasCatalogue/Language.lean). -/
def sourceLimitLeg? (receiver : NativeSourceJudgement) (ordinal : Nat) :
    TermElabM (Option NativeSourceJudgement) := do
  let some category := receiver.category | return none
  let some selection := category.limit | return none
  let cone := selection.cone
  let some presentation ← sourceApplication? selection.declaration cone
    | throwError "the selected construction lost its original registered application"
  let colimit := selection.colimit
  let leg ← mkAppM (if colimit then ``CategoryTheory.Limits.Cocone.ι
    else ``CategoryTheory.Limits.Cone.π) #[cone]
  let component ← mkAppM ``CategoryTheory.NatTrans.app #[leg]
  let .forallE _ indexType _ _ ← whnf (← inferType component)
    | throwError "the defining leg has no shape index"
  let index ← constructionIndex indexType ordinal
  let hom := mkApp component index
  check hom
  -- The component belongs to this cone, while its apex is the actual selected source
  -- occurrence. Preserve that occurrence in the native hom type before a functor action
  -- reads its implicit endpoints. The other endpoint remains the original diagram object.
  let homType ← inferType hom
  let homType ← if homType.isAppOfArity ``Quiver.Hom 4 then pure homType else whnfR homType
  unless homType.isAppOfArity ``Quiver.Hom 4 do
    throwError "the defining leg lost its complete native morphism type"
  let endpoints := homType.getAppArgs.set! (if colimit then 3 else 2) receiver.value
  let hom ← mkExpectedTypeHint hom (mkAppN homType.getAppFn endpoints)
  check hom
  let hom ← retainLimitLeg category receiver.value index hom
  let .mdata data body ←
      sourceReferenceAt ``LimitEntry selection.row selection.declaration presentation hom
    | throwError "internal: a source reference is not an annotation"
  -- The diagram endpoint is a projection of this actual selected leg, just as the
  -- endpoint of a named map is a projection of that map. In particular, a functor
  -- action must not have to execute the diagram's object selector to reconstruct it.
  -- The selected apex remains its original binding in the Arrow constructor. The
  -- selection identity also makes the endpoint and the map share the same leg occurrence.
  let hom ← selectMorphism (.mdata (data.setNat `CasCompiler.source.leg ordinal) body)
  return some ⟨hom, some ⟨.morphism, selection.category, selection.bundle, none, none⟩⟩

end CasCompiler
