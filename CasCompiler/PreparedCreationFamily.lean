module

public import CasCompiler.CreationFamily
public import CasCompiler.LimitFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue





structure CreationInputPlan where
  private mk ::
  evidence : ApplicationLayout
  diagram : ApplicationLayout
  standardization : ApplicationLayout
  target : ApplicationLayout
  diagramTag : String
  diagramPorts : Array ArgumentLayout




structure PreparedCreationFamily where
  private mk ::
  family : CreationFamily
  target : LimitFamily
  context : ContextTelescope
  owner : ClosedTerm
  selectionData : NativeLimitSelection ClosedTerm
  selections : SourceSelectionScope ClosedTerm
  targetOwner : SelectedLimitOwner ClosedTerm
  interface : LimitCreationInterface ClosedTerm
  universes : List Level
  targetUniverses : List Level
  construction : Name
  inputs : CreationInputPlan
  arguments : Array ClosedTerm
  sourceOwner : SelectedLimitOwner ClosedTerm
  sourceArguments : Array ClosedTerm
  sourcePositions : Array Nat

def PreparedCreationFamily.operation (prepared : PreparedCreationFamily) : String :=
  prepared.family.entry.id.raw

def PreparedCreationFamily.input (prepared : PreparedCreationFamily) : String :=
  prepared.operation ++ "#input"

def PreparedCreationFamily.requestFamily (prepared : PreparedCreationFamily) : ClosedTerm :=
  prepared.interface.requestFamily



def PreparedCreationFamily.captureSources (prepared : PreparedCreationFamily) : Array ClosedTerm :=
  (prepared.inputs.evidence.arguments ++ prepared.inputs.standardization.arguments ++
    prepared.inputs.target.arguments).filterMap fun argument =>
      if argument.wireIndex.isSome then some argument.source.source else none



private def creationInputApplication (context : OpenContext)
    (selections : SourceSelectionScope ClosedTerm) (application : Expr) :
    MetaM (List Level × ApplicationLayout) := do
  let .const declaration levels := application.consumeMData.getAppFn
    | throwError "the creation source input lost its original declaration application"
  let information ← checkedDeclaration declaration
  unless levels.length == information.levelParams.length do
    throwError "the creation source input changed its original universe arguments"
  let head := mkConst declaration levels
  let original ← context.close head
  let source ← SourceLayout.ofTerm original (selections := selections)
  let arguments ← application.getAppArgs.mapM context.close
  let (_, prepared) ← ApplicationLayout.ofSource source context arguments
  return (levels, prepared)



opaque PreparedCreationFamily.ofSelection (context : OpenContext) (owner : Expr)
    (selected : NativeLimitSelection) (family : CreationFamily) (target : LimitFamily)
    (selections : SourceSelectionScope Expr) : MetaM (Option PreparedCreationFamily) := do
  let some creation := selected.source.creation | return none
  unless creation.lift == family.entry.id && selected.source.row == target.entry.id.raw do
    throwError "the selected creation changed its complete original accepted families"
  unless creation.declaration == family.entry.evidence && creation.edge == family.entry.edge &&
      !selected.source.colimit && !selected.source.construction.isAnonymous do
    throwError "the selected creation changed its original lift or construction"
  target.requireInterface selected.source
  unless creation.diagram.equal selected.source.diagram do
    throwError "the selected creation changed its exact source diagram"
  let .const declaration universes := creation.evidence.consumeMData.getAppFn
    | throwError "the selected creation lost its exact original evidence application"
  unless declaration == family.entry.evidence &&
      creation.evidence.getAppNumArgs == family.parameterCount &&
      universes.length == family.universeParams.length do
    throwError "the selected creation changed its complete original evidence telescope"
  let some standardization := selected.source.interface.standardization
    | throwError "the selected creation lost its accepted original comparison"
  let some comparisonDeclaration := target.entry.standardization
    | throwError "the selected creation has no independently accepted diagram comparison"
  unless standardization.consumeMData.getAppFn.isConstOf comparisonDeclaration &&
      creation.standardization.equal standardization do
    throwError "the selected creation changed its declared original comparison"
  let expected ← family.interfaceAt creation.evidence creation.functor creation.diagram
    selected.source.interface
  unless (creation.terms.zip expected.terms).all
      (fun (actual, original) => actual.equal original) do
    throwError "the selected creation changed one of its original native interface fields"
  let presentation ← NativeLimitCreationInterface.presentation creation
  unless presentation.equal selected.source.presentation do
    throwError "the selected creation changed its original source presentation"
  let closedSelections ← selections.close context
  let (_, evidence) ← creationInputApplication context closedSelections creation.evidence
  let (_, diagram) ← creationInputApplication context closedSelections creation.diagram
  let (_, standardization) ← creationInputApplication context closedSelections creation.standardization
  let (targetUniverses, targetApplication) ←
    creationInputApplication context closedSelections selected.source.interface.presentation
  let (diagramTag, ports) ← LimitFamily.diagramPorts creation.diagram
  let diagramPorts := diagram.arguments.filter fun argument =>
    argument.binderInfo.isExplicit && argument.wireIndex.isSome
  unless diagramPorts.size == ports.size do
    throwError "the creation diagram changed its original explicit computational positions"
  let inputs : CreationInputPlan := ⟨evidence, diagram, standardization, targetApplication,
    diagramTag, diagramPorts⟩
  let some sourceOwner := selected.source.creationFamily
    | throwError "the selected creation lost its original source-input owner family"
  let sourceOwner ← SelectedLimitOwner.ofBinding context selections sourceOwner
  let some targetOwner := selected.source.ownerFamily
    | throwError "the selected creation lost its complete target owner template"
  let targetOwner ← SelectedLimitOwner.ofBinding context selections targetOwner
  let sourcePositions := selected.source.creationInputs
  let mut sourceArguments : Array ClosedTerm := #[]
  let mut previous : Option Nat := none
  for index in sourcePositions do
    if let some earlier := previous then
      unless earlier < index do
        throwError "the creation source owner changed original argument order"
    let some argument := diagram.arguments[index]?
      | throwError "the creation source owner names an absent original argument"
    unless argument.sourceIndex == index do
      throwError "the creation source owner changed an original native argument position"
    sourceArguments := sourceArguments.push argument.source.source
    previous := some index
  forallTelescope (← inferType sourceOwner.selection.receiver) fun parameters _ => do
    unless parameters.size == sourcePositions.size do
      throwError "the creation source owner lost its full native/proof input telescope"
    let formal ← sourceOwner.specialize parameters
    unless formal.source.construction == selected.source.construction &&
        formal.source.row == selected.source.row &&
        formal.source.diagram.consumeMData.getAppFn.equal creation.diagram.consumeMData.getAppFn do
      throwError "the creation source owner changed its original constructor or selection"
    for parameter in parameters, index in sourcePositions do
      let some original := formal.source.diagram.getAppArgs[index]?
        | throwError "the creation source owner lost a formal original argument"
      unless original.equal parameter do
        throwError "the creation source owner changed its declared positional input relation"
  return some {
    family, target, context := context.telescope, owner := ← context.close owner
    selectionData := ← selected.mapM context.close, selections := closedSelections
    targetOwner := ← targetOwner.mapM context.close
    interface := ← creation.mapM context.close, universes, targetUniverses
    construction := selected.source.construction, inputs
    arguments := #[← context.close creation.targetCone, ← context.close creation.targetUniversal]
    sourceOwner := ← sourceOwner.mapM context.close, sourceArguments, sourcePositions }




opaque PreparedCreationFamily.rebindSource [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    (prepared : PreparedCreationFamily) (identities : CasRuntime.IdentitySupply)
    (context : OpenContext) (selections : SourceSelectionScope Expr) (arguments : Array Expr)
    (action : OpenContext → SourceSelectionScope Expr → PreparedCreationFamily → m α) : m α := do
  let (selected, selections) ← liftM (m := MetaM) do
    unless arguments.size == prepared.sourceArguments.size do
      throwError "the creation source binding changed its complete original argument count"
    let family ← prepared.sourceOwner.mapM (·.inContext context)
    let selected ← family.specialize arguments
    let original ← prepared.selectionData.mapM (·.inContext context)
    unless selected.source.construction == prepared.construction &&
        selected.source.row == original.source.row do
      throwError "the creation source binding changed its original selected presentation"
    context.withOriginalSources #[selected.source.presentation, original.source.presentation] fun source => do
      unless ← isDefEq source[0]! source[1]! do
        throwError "the creation source binding changed its complete native presentation"
    let source := { selected.source with
      creationFamily := original.source.creationFamily
      ownerFamily := original.source.ownerFamily
      creationInputs := prepared.sourcePositions }
    let selected ← NativeLimitSelection.ofSource source selected.receiver
    let selections ← SourceSelectionScope.merge selections (← prepared.selections.inContext context)
    pure (selected, selections)
  let source : SourceSelection Expr := {
    value := selected.receiver, reference := some (.limit prepared.target.entry)
    originalApplication := some selected.source.interface.presentation, limit := some selected
    creationOwner := some (prepared.family, prepared.target)
    category := some {
      role := .object
      expression := selected.source.category
      bundle := selected.source.bundle
      limit := some selected.source } }
  SourceSelectionScope.withBinding identities selections context source
    fun context selections owner => do
      let rebound ← liftM (m := MetaM) do
        let some rebound ← PreparedCreationFamily.ofSelection context owner selected
            prepared.family prepared.target selections
          | throwError "the rebound source lost its complete selected creation"
        pure rebound
      action context selections rebound




opaque PreparedCreationFamily.withArguments (prepared : PreparedCreationFamily)
    (context : OpenContext) (cone universal : Expr) : MetaM PreparedCreationFamily := do
  let original ← prepared.interface.targetCone.inContext context
  let expectedCone ← inferType original
  unless ← isDefEq (← inferType cone) expectedCone do
    throwError "the fixed creation argument changed its original target cone interface"
  let expectedUniversal ← mkAppM ``CategoryTheory.Limits.IsLimit #[cone]
  unless ← isDefEq (← inferType universal) expectedUniversal do
    throwError "the fixed creation argument changed its actual target universal interface"
  let request ← prepared.requestFamily.inContext context
  let result := mkAppN request #[cone, universal]
  check result
  if result.hasMVar || result.hasLevelMVar then
    throwError "the fixed creation arguments have unresolved native parameters"
  return { prepared with arguments := #[← context.close cone, ← context.close universal] }



opaque PreparedCreationFamily.familyIn (prepared : PreparedCreationFamily)
    (context : OpenContext) : MetaM Expr :=
  prepared.requestFamily.inContext context


opaque PreparedCreationFamily.selection (prepared : PreparedCreationFamily)
    (context : OpenContext) : MetaM NativeLimitSelection := do
  let selected ← prepared.selectionData.mapM (·.inContext context)
  unless selected.source.construction == prepared.construction &&
      selected.source.row == prepared.target.entry.id.raw do
    throwError "the prepared creation changed its original construction or target"
  return selected


opaque PreparedCreationFamily.selectedArguments (prepared : PreparedCreationFamily)
    (context : OpenContext) (owner cone universal : Expr) : MetaM (SourceSelection Expr) := do
  let selected ← prepared.selection context
  context.withOriginalSources #[owner, ← prepared.owner.inContext context] fun values => do
    unless ← isDefEq values[0]! values[1]! do
      throwError "the fixed creation changed its original selected owner"
  let checked ← prepared.withArguments context cone universal
  let result := mkAppN (← checked.familyIn context) #[cone, universal]
  check result
  if result.hasMVar || result.hasLevelMVar then
    throwError "the fixed creation has unresolved native inputs"
  return {
    value := result
    application := some {
      family := .creation prepared.family prepared.target
      universes := prepared.universes
      parameters := #[]
      arguments := #[cone, universal]
      owner := some owner }
    limit := some selected, creationOwner := some (prepared.family, prepared.target) }


opaque PreparedCreationFamily.selected (prepared : PreparedCreationFamily)
    (context : OpenContext) : MetaM (SourceSelection Expr) := do
  let owner ← prepared.owner.inContext context
  let #[cone, universal] ← prepared.arguments.mapM (·.inContext context)
    | throwError "the fixed creation request lost an original data input"
  prepared.selectedArguments context owner cone universal

end CasCompiler
