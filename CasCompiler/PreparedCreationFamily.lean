module

public import CasCompiler.CreationFamily
public import CasCompiler.LimitFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- Original declaration argument positions for the selected creation's source descriptor.
Every native/proof slot is retained by ApplicationLayout; only the actual diagram's explicit
nonproof arguments are diagram ports. These schemas do not demand evaluation of evidence or
of the accepted standardization. -/
structure CreationInputPlan where
  private mk ::
  evidence : ApplicationLayout
  diagram : ApplicationLayout
  standardization : ApplicationLayout
  target : ApplicationLayout
  diagramTag : String
  diagramPorts : Array ArgumentLayout

/-- The fixed creation request in its original complete source scope. Its two data arguments
are the actual target Cone and IsLimit record. The source-selected transport and creation stay
inside requestFamily; no intermediate computed c′ or t′ is represented as a runtime value. -/
structure PreparedCreationFamily where
  private mk ::
  family : CreationFamily
  target : LimitFamily
  context : ContextTelescope
  owner : ClosedTerm
  interface : LimitCreationInterface ClosedTerm
  universes : List Level
  targetUniverses : List Level
  construction : Name
  inputs : CreationInputPlan
  arguments : Array ClosedTerm
  sourceOwner : ClosedTerm
  sourceArguments : Array ClosedTerm
  sourcePositions : Array Nat

def PreparedCreationFamily.operation (prepared : PreparedCreationFamily) : String :=
  prepared.family.entry.id.raw

def PreparedCreationFamily.input (prepared : PreparedCreationFamily) : String :=
  prepared.operation ++ "#input"

def PreparedCreationFamily.requestFamily (prepared : PreparedCreationFamily) : ClosedTerm :=
  prepared.interface.requestFamily

/-- All original computational capture slots, including implicit data parameters. Proof slots
remain in the three complete application layouts. Repeated occurrences are never deduplicated. -/
def PreparedCreationFamily.captureSources (prepared : PreparedCreationFamily) : Array ClosedTerm :=
  (prepared.inputs.evidence.arguments ++ prepared.inputs.standardization.arguments ++
    prepared.inputs.target.arguments).filterMap fun argument =>
      if argument.wireIndex.isSome then some argument.source.source else none

/-- Prepare the complete original native constant application. Nullary record families use
the ordinary retained-whole-family path; no synthetic publication marker is introduced. -/
private def creationInputApplication (context : OpenContext) (application : Expr) :
    MetaM (List Level × ApplicationLayout) := do
  let .const declaration levels := application.consumeMData.getAppFn
    | throwError "the creation source input lost its original declaration application"
  let information ← checkedDeclaration declaration
  unless levels.length == information.levelParams.length do
    throwError "the creation source input changed its original universe arguments"
  let head := mkConst declaration levels
  let original ← context.close head
  let source ← SourceLayout.ofTerm original
  let arguments ← application.getAppArgs.mapM context.close
  let (_, prepared) ← ApplicationLayout.ofSource source context arguments
  return (levels, prepared)

/-- Close an already retained selected construction. Every selected mathematical field is
checked at its original source position; native result data never chooses this selection. -/
opaque PreparedCreationFamily.ofSelection (context : OpenContext) (owner : Expr) :
    MetaM (Option PreparedCreationFamily) := do
  let some selected ← NativeLimitSelection.ofExpr? owner | return none
  let some creation := selected.source.creation | return none
  let family ← CreationFamily.forId creation.lift
  unless creation.declaration == family.entry.evidence && creation.edge == family.entry.edge &&
      !selected.source.colimit && !selected.source.construction.isAnonymous do
    throwError "the selected creation changed its original lift or construction"
  let target ← LimitFamily.forId ⟨selected.source.row⟩
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
  let presentation ← creation.presentation
  unless presentation.equal selected.source.presentation do
    throwError "the selected creation changed its original source presentation"
  let (_, evidence) ← creationInputApplication context creation.evidence
  let (_, diagram) ← creationInputApplication context creation.diagram
  let (_, standardization) ← creationInputApplication context creation.standardization
  let (targetUniverses, targetApplication) ←
    creationInputApplication context selected.source.interface.presentation
  let (diagramTag, ports) ← LimitFamily.diagramPorts creation.diagram
  let diagramPorts := diagram.arguments.filter fun argument =>
    argument.binderInfo.isExplicit && argument.wireIndex.isSome
  unless diagramPorts.size == ports.size do
    throwError "the creation diagram changed its original explicit computational positions"
  let inputs : CreationInputPlan := ⟨evidence, diagram, standardization, targetApplication,
    diagramTag, diagramPorts⟩
  let some sourceOwner := selected.source.creationFamily
    | throwError "the selected creation lost its original source-input owner family"
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
  lambdaTelescope sourceOwner fun parameters original => do
    unless parameters.size == sourcePositions.size do
      throwError "the creation source owner lost its full native/proof input telescope"
    let some formal ← NativeLimitSelection.ofExpr? original
      | throwError "the creation source owner lost its original formal construction"
    unless formal.source.construction == selected.source.construction &&
        formal.source.row == selected.source.row &&
        formal.source.diagram.consumeMData.getAppFn.equal creation.diagram.consumeMData.getAppFn do
      throwError "the creation source owner changed its original constructor or selection"
    for parameter in parameters, index in sourcePositions do
      let some original := formal.source.diagram.getAppArgs[index]?
        | throwError "the creation source owner lost a formal original argument"
      unless original.equal parameter do
        throwError "the creation source owner changed its declared positional input relation"
  return some ⟨family, target, context.telescope, ← context.close owner,
    ← creation.mapM context.close, universes, targetUniverses, selected.source.construction, inputs,
    #[← context.close creation.targetCone, ← context.close creation.targetUniversal],
    ← context.close sourceOwner, sourceArguments, sourcePositions⟩

/-- Rebind the original source inputs once before descriptor production. The complete retained
source owner determines both D and the mapped target's arguments from these same positions.
Neither a declaration lookup nor native expression equality discovers an input occurrence. -/
opaque PreparedCreationFamily.rebindSource (prepared : PreparedCreationFamily)
    (context : OpenContext) (arguments : Array Expr) : MetaM PreparedCreationFamily := do
  unless arguments.size == prepared.sourceArguments.size do
    throwError "the creation source binding changed its complete original argument count"
  let family ← prepared.sourceOwner.inContext context
  let owner := family.betaRev arguments.reverse (preserveMData := true)
  check owner
  let some original ← NativeLimitSelection.ofExpr? (← prepared.owner.inContext context)
    | throwError "the creation source binding lost its original selected owner"
  let some selected ← NativeLimitSelection.ofExpr? owner
    | throwError "the creation source binding lost its original formal owner application"
  unless selected.source.construction == prepared.construction &&
      selected.source.row == original.source.row &&
      (← isDefEq selected.source.presentation original.source.presentation) do
    throwError "the creation source binding changed its original selected presentation"
  let source := { selected.source with
    creationFamily := some family, creationInputs := prepared.sourcePositions }
  let owner ← retainLimitConstruction {
    value := selected.receiver
    category := some {
      role := .object, expression := source.category, bundle := source.bundle,
      limit := some source } }
  let some rebound ← PreparedCreationFamily.ofSelection context owner.value
    | throwError "the rebound source lost its complete selected creation"
  return rebound

/-- Retain the actual original data inputs supplied at this source boundary. This checks only
their complete dependent native interfaces. Runtime admission separately checks their exact
selected occurrences against the original source input map; native conversion is not identity. -/
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

/-- Reopen the already captured contextual request. ClosedTerm transports the original complete
BindingId telescope; callers must not use the empty-context global-family preparation path. -/
opaque PreparedCreationFamily.familyIn (prepared : PreparedCreationFamily)
    (context : OpenContext) : MetaM Expr :=
  prepared.requestFamily.inContext context

/-- Reopen the exact retained original owner, without rediscovering an apex or target by type. -/
opaque PreparedCreationFamily.selection (prepared : PreparedCreationFamily)
    (context : OpenContext) : MetaM NativeLimitSelection := do
  let some selected ← NativeLimitSelection.ofExpr? (← prepared.owner.inContext context)
    | throwError "the prepared creation lost its original typed selection"
  unless selected.source.construction == prepared.construction &&
      selected.source.row == prepared.target.entry.id.raw do
    throwError "the prepared creation changed its original construction or target"
  return selected

/-- Mark the fixed request with its original owner and explicit native data inputs.
Temporary source let-binders remain expressions until the caller closes the complete plan. -/
opaque PreparedCreationFamily.markArguments (prepared : PreparedCreationFamily)
    (context : OpenContext) (owner cone universal : Expr) : MetaM Expr := do
  let some selected ← NativeLimitSelection.ofExpr? owner
    | throwError "the fixed creation marker lost its original typed owner"
  unless selected.source.construction == prepared.construction &&
      selected.source.row == prepared.target.entry.id.raw &&
      (← isDefEq owner (← prepared.owner.inContext context)) do
    throwError "the fixed creation marker changed its original selected owner"
  let result := mkAppN (← prepared.familyIn context) #[cone, universal]
  check result
  if result.hasMVar || result.hasLevelMVar then
    throwError "the fixed creation marker has unresolved native inputs"
  let body ← mkAppM ``Function.const #[← inferType owner, result, owner]
  let body ← mkAppM ``Function.const #[← inferType universal, body, universal]
  let body ← mkAppM ``Function.const #[← inferType cone, body, cone]
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``CreationFamily
    |>.setString `CasCompiler.source.id prepared.family.entry.id.raw
    |>.setName `CasCompiler.source.declaration prepared.family.entry.evidence
    |>.setBool `CasCompiler.source.creation.fixed true
    |>.setName `CasCompiler.source.creation.construction prepared.construction
    |>.setString `CasCompiler.source.creation.target prepared.target.entry.id.raw) body

/-- Mark the complete fixed native request, retaining its original typed construction owner.
The marker names only the accepted lift; the full target comparison stays in that owner. -/
opaque PreparedCreationFamily.mark (prepared : PreparedCreationFamily)
    (context : OpenContext) : MetaM Expr := do
  let owner ← prepared.owner.inContext context
  let #[cone, universal] ← prepared.arguments.mapM (·.inContext context)
    | throwError "the fixed creation request lost an original data input"
  prepared.markArguments context owner cone universal

/-- Decode only the marker emitted for the same original selected construction. All native
fields are rechecked before exposing the contextual family and its original c/t arguments. -/
opaque PreparedCreationFamily.fromMark (context : OpenContext) (data : MData) (body : Expr) :
    MetaM PreparedCreationFamily := do
  unless data.getName `CasCompiler.source.kind == ``CreationFamily &&
      data.getBool `CasCompiler.source.creation.fixed &&
      body.isAppOfArity ``Function.const 4 do
    throwError "the source is not its original fixed creation request"
  let cone := body.getAppArgs[3]!
  let body := body.getAppArgs[2]!
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the fixed creation request lost its actual universal input"
  let universal := body.getAppArgs[3]!
  let body := body.getAppArgs[2]!
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the fixed creation request lost its original typed owner"
  let owner := body.getAppArgs[3]!
  let result := body.getAppArgs[2]!
  let some prepared ← PreparedCreationFamily.ofSelection context owner
    | throwError "the fixed creation request lost its original typed owner"
  unless data.getString `CasCompiler.source.id == prepared.family.entry.id.raw &&
      data.getName `CasCompiler.source.declaration == prepared.family.entry.evidence &&
      data.getName `CasCompiler.source.creation.construction == prepared.construction &&
      data.getString `CasCompiler.source.creation.target == prepared.target.entry.id.raw do
    throwError "the fixed creation marker changed its original selected owner"
  let prepared ← prepared.withArguments context cone universal
  let expected := mkAppN (← prepared.familyIn context) #[cone, universal]
  unless result.equal expected do
    throwError "the fixed creation marker changed its complete native result"
  return prepared

end CasCompiler
