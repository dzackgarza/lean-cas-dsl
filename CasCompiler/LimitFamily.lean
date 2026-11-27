module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.Elaborate
public import CasCompiler.Layout
public import CasCompiler.Surface
public import CasCompiler.LimitSelection
public import LeanCategories.Catalogue.Registry.Semantic

public section

namespace CasCompiler

open Lean Meta CasCatalogue


def LimitFamily.operation (family : LimitFamily) : String := family.entry.id.raw

def LimitFamily.coneProjection (family : LimitFamily) : Name :=
  if family.entry.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
  else ``CategoryTheory.Limits.LimitCone.cone

def LimitFamily.apexProjection (family : LimitFamily) : Name :=
  if family.entry.colimit then ``CategoryTheory.Limits.Cocone.pt
  else ``CategoryTheory.Limits.Cone.pt

def LimitFamily.legProjection (family : LimitFamily) : Name :=
  if family.entry.colimit then ``CategoryTheory.Limits.Cocone.ι
  else ``CategoryTheory.Limits.Cone.π




opaque LimitFamily.forId (id : LimitId) : MetaM LimitFamily := withLCtx {} #[] do
  let state ← semanticState
  let #[entry] := state.limits.filter (·.id == id)
    | throwError "the selected limit lost its unique public registration"
  let #[category] := state.categories.filter (·.id == entry.category)
    | throwError "the selected limit lost its registered category"
  discard <| checkedDeclaration category.declaration
  if let some constructor := entry.dataConstructor then
    discard <| checkedDeclaration constructor
  if let some standardization := entry.standardization then
    discard <| checkedDeclaration standardization
  let declaration ← checkedDeclaration entry.declaration
  let presentationFamily := mkConst declaration.name (declaration.levelParams.map Level.param)
  forallTelescopeReducing declaration.type fun parameters result => do
    let result ← whnfR result
    let expected := if entry.colimit then ``CategoryTheory.Limits.ColimitCocone
      else ``CategoryTheory.Limits.LimitCone
    unless result.isAppOf expected do
      throwError "the selected limit has another native universal-presentation family"
    let some diagram := result.getAppArgs.back?
      | throwError "the selected limit lost its complete native diagram"
    let presentation := mkAppN presentationFamily parameters
    let cone ← mkAppM (if entry.colimit then ``CategoryTheory.Limits.ColimitCocone.cocone
      else ``CategoryTheory.Limits.LimitCone.cone) #[presentation]
    let family ← mkLambdaFVars parameters cone (usedOnly := false) (usedLetOnly := false)
    let diagramFamily ← mkLambdaFVars parameters diagram
      (usedOnly := false) (usedLetOnly := false)
    check family
    check diagramFamily
    if family.hasMVar || family.hasLevelMVar || diagramFamily.hasMVar ||
        diagramFamily.hasLevelMVar then
      throwError "the selected limit has an unresolved native family parameter"
    return ⟨entry, category, declaration.levelParams, parameters.size, presentationFamily,
      diagramFamily, family, ← inferType family⟩



opaque LimitFamily.presentationAt (family : LimitFamily) (universes : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm) : MetaM Expr := do
  unless universes.length == family.universeParams.length &&
      arguments.size == family.parameterCount do
    throwError "the limit request changed its complete native parameter telescope"
  let source ← withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    empty.close (family.presentationFamily.instantiateLevelParams family.universeParams universes)
  context.apply source arguments




opaque LimitFamily.requireInterface (family : LimitFamily)
    (selection : NativeSourceLimitSelection) : MetaM Unit := do
  unless selection.row == family.entry.id.raw && selection.declaration == family.entry.declaration &&
      selection.colimit == family.entry.colimit do
    throwError "the limit request changed its original selected presentation"
  let presentation := selection.interface.presentation
  unless presentation.consumeMData.getAppFn.isConstOf family.entry.declaration &&
      presentation.consumeMData.getAppNumArgs == family.parameterCount do
    throwError "the limit interface lost its complete original declaration application"
  let result ← whnfR (← inferType presentation)
  let expected := if family.entry.colimit then ``CategoryTheory.Limits.ColimitCocone
    else ``CategoryTheory.Limits.LimitCone
  unless result.isAppOf expected do
    throwError "the limit interface changed its original universal-presentation type"
  let some diagram := result.getAppArgs.back?
    | throwError "the limit interface lost its native diagram"
  unless ← isDefEq diagram selection.interface.diagram do
    throwError "the retained limit interface has another complete native diagram"
  match family.entry.dataConstructor, selection.interface.dataConstructor with
  | none, none => pure ()
  | some declaration, some constructor => do
    lambdaTelescope constructor fun _ body => do
      unless body.getAppFn.isConstOf declaration do
        throwError "the retained limit interface changed its original data constructor"
    check constructor
  | _, _ => throwError "the retained limit interface changed its accepted data-constructor presence"




opaque LimitFamily.diagramPorts (diagram : Expr) : MetaM (String × Array Expr) := do
  let diagram := diagram.consumeMData.headBeta
  let .const declaration _ := diagram.getAppFn
    | throwError "the selected native diagram has no original declaration constructor"
  let information ← getFunInfoNArgs diagram.getAppFn diagram.getAppNumArgs
  let mut fields := #[]
  for field in diagram.getAppArgs, index in [:diagram.getAppNumArgs] do
    if (information.paramInfo[index]?.map (·.isExplicit)).getD false then
      unless ← isProof field do fields := fields.push field
  return (declaration.getString!, fields)



opaque LimitFamily.prepareOwner (family : LimitFamily) (identities : CasRuntime.IdentitySupply)
    (levels : List Level) (construction : Name) : MetaM (SelectedLimitOwner Expr) := do
  unless levels.length == family.universeParams.length && !construction.isAnonymous do
    throwError "the cone owner requires its complete universes and original construction identity"
  let declaration :=
    family.presentationFamily.instantiateLevelParams family.universeParams levels
  forallTelescopeReducing (← inferType declaration) fun formals _ => do
    unless formals.size == family.parameterCount do
      throwError "the whole cone lost its original complete formal telescope"
    let formalBindings ← formals.mapM fun _ => do
      let allocated ← identities.fresh .sourceBinding
      return (⟨allocated.worker, allocated.serial⟩ : BindingId)
    let formalPresentation := mkAppN declaration formals
    let interface ← prepareLimitInterface family.entry formalPresentation
    let diagram := interface.diagram
    let (_, bundle) ← functorCategoryBundles diagram
    let cone ← mkAppM family.coneProjection #[formalPresentation]
    let apex ← mkAppM family.apexProjection #[cone]
    let source : NativeSourceLimitSelection := {
      row := family.entry.id.raw
      declaration := family.entry.declaration
      cone
      colimit := family.entry.colimit
      category := family.category.expression
      bundle
      presentation := formalPresentation
      diagram
      interface
      construction }
    let selected ← NativeLimitSelection.ofSource source apex
    let selected ← selected.mapM fun value =>
      mkLambdaFVars formals value (usedOnly := false) (usedLetOnly := false)
    return ⟨selected, formalBindings⟩


opaque LimitFamily.ownerFamily (family : LimitFamily) (owner : SelectedLimitOwner Expr) :
    MetaM Expr := do
  unless owner.formalBindings.size == family.parameterCount do
    throwError "the whole cone lost its original owner formal table"
  check owner.selection.receiver
  return owner.selection.receiver



opaque LimitFamily.ownerAt (family : LimitFamily) (owner : SelectedLimitOwner Expr)
    (parameters : Array Expr) : MetaM NativeLimitSelection := do
  unless parameters.size == family.parameterCount do
    throwError "the cone owner view requires every original native parameter position"
  let selected ← owner.specialize parameters
  family.requireInterface selected.source
  unless !selected.source.construction.isAnonymous &&
      selected.source.construction == owner.selection.source.construction do
    throwError "the cone owner view changed its original construction identity"
  return selected


opaque LimitFamily.selectedAtOwner (family : LimitFamily) (owner : SelectedLimitOwner Expr)
    (levels : List Level) (parameters : Array Expr) : MetaM (SourceSelection Expr) := do
  unless family.entry.dataConstructor.isSome do
    throwStratum .noImplementation
      m!"the selected limit {family.operation} has no accepted computational data constructor"
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    throwError "the whole cone request changed its complete native parameter telescope"
  let presentation := mkAppN
    (family.presentationFamily.instantiateLevelParams family.universeParams levels) parameters
  check presentation
  if presentation.hasMVar || presentation.hasLevelMVar then
    throwError "the whole cone request has unresolved native parameters"
  let selected ← family.ownerAt owner parameters
  unless selected.source.presentation.equal presentation do
    throwError "the whole cone request changed its original selected presentation"
  return {
    value := selected.source.cone
    observation := some (.limit family.entry)
    originalApplication := some presentation
    application := some {
      family := .limit family, universes := levels, parameters,
      owner := some selected.receiver, ownerSelection := some owner }
    limitFamily := some family
    limit := some selected }


opaque LimitFamily.selected (family : LimitFamily) (identities : CasRuntime.IdentitySupply)
    (levels : List Level) (parameters : Array Expr) : MetaM (SourceSelection Expr) := do
  let construction ← mkFreshUserName `rawLimitConstruction
  let owner ← family.prepareOwner identities levels construction
  family.selectedAtOwner owner levels parameters


opaque LimitFamily.formalAt (family : LimitFamily) (context : OpenContext) (original : NativeLimitSelection)
    (owner : SelectedLimitOwner Expr)
    (parameters : Array Expr) : MetaM (Option NativeLimitSelection) := do
  unless original.source.presentation.consumeMData.getAppFn.isConstOf
      original.source.declaration do return none
  family.requireInterface original.source
  let selected ← family.ownerAt owner parameters
  let samePresentation ← context.withOriginalSources
    #[selected.source.presentation, original.source.presentation] fun presentations =>
      isDefEq presentations[0]! presentations[1]!
  unless selected.source.construction == original.source.construction && samePresentation do
    throwError "the formal construction changed its original selected presentation"
  return some { selected with
    source := { selected.source with
      ownerFamily := original.source.ownerFamily
      creation := original.source.creation
      creationFamily := original.source.creationFamily
      creationInputs := original.source.creationInputs } }


opaque LimitFamily.wholeFrom (family : LimitFamily) (original : NativeLimitSelection)
    (owner : SelectedLimitOwner Expr) :
    MetaM (Option (SourceSelection Expr)) := do
  family.requireInterface original.source
  unless original.source.presentation.consumeMData.getAppFn.isConstOf
      original.source.declaration do
    throwStratum .noImplementation
      "the selected creation of a limit requires its accepted computational lift"
  let presentation := original.source.interface.presentation.consumeMData
  let .const declaration levels := presentation.getAppFn
    | throwError "the formal construction lost its original full native presentation"
  unless declaration == family.entry.declaration do
    throwError "the formal construction changed its original registered presentation"
  return some (← family.selectedAtOwner owner levels presentation.getAppArgs)

end CasCompiler
