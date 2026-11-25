module

public import CasCompiler.Elaborate
public import CasCompiler.Layout
public import CasCompiler.Surface
public import CasCompiler.LimitSelection
public import LeanCategories.Catalogue.Registry.Semantic

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The complete computational cone family of one independently selected universal
presentation. Its formal universal mediator is not a computational output of the cone port. -/
structure LimitFamily where
  private mk ::
  entry : LimitEntry
  category : NamedCategoryEntry
  universeParams : List Name
  parameterCount : Nat
  presentationFamily : Expr
  diagramFamily : Expr
  family : Expr
  familyType : Expr

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

/-- Resolve the supplied public identity before specializing its complete rigid native
telescope. Native projection selects the cone interface, without evaluating the presentation.
The independently accepted data constructor remains the sole authority for reply ports. -/
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
    let cone ← sourceReferenceAt ``LimitEntry entry.id.raw entry.declaration presentation cone
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

/-- The original presentation application at a complete caller-supplied argument table.
Only ordinary native application and rigid universe substitution are performed. -/
opaque LimitFamily.presentationAt (family : LimitFamily) (universes : List Level)
    (context : OpenContext) (arguments : Array ClosedTerm) : MetaM Expr := do
  unless universes.length == family.universeParams.length &&
      arguments.size == family.parameterCount do
    throwError "the limit request changed its complete native parameter telescope"
  let source ← withLCtx {} #[] do
    let empty ← ContextTelescope.capture #[]
    empty.close (family.presentationFamily.instantiateLevelParams family.universeParams universes)
  context.apply source arguments

/-- Validate the retained producer's interface without replacing it by a newly prepared one.
Creation selections may retain a distinct source presentation, while this exact accepted
interface still names the original target presentation and its diagram. -/
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


/-- Read the original native diagram head and every explicit nonproof field in declaration
order. The public tag is only that already selected head's name; it never selects a diagram. -/
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

/-- Prepare the original whole owner/interface once, before its actual parameter substitution.
The caller supplies the existing construction identity. Every implicit, explicit and proof
position remains in the native telescope, including any rigid constructor universes. -/
opaque LimitFamily.prepareOwner (family : LimitFamily) (levels : List Level)
    (construction : Name) : MetaM Expr := do
  unless levels.length == family.universeParams.length && !construction.isAnonymous do
    throwError "the cone owner requires its complete universes and original construction identity"
  let declaration :=
    family.presentationFamily.instantiateLevelParams family.universeParams levels
  forallTelescopeReducing (← inferType declaration) fun formals _ => do
    unless formals.size == family.parameterCount do
      throwError "the whole cone lost its original complete formal telescope"
    let formalPresentation := mkAppN declaration formals
    let interface ← prepareLimitInterface family.entry formalPresentation
    let diagram := interface.diagram
    let (_, bundle) ← functorCategoryBundles diagram
    let cone ← mkAppM family.coneProjection #[formalPresentation]
    let apex ← mkAppM family.apexProjection #[cone]
    let cone ← retainSourceApplication family.entry.declaration formalPresentation cone
    let apex ← sourceReferenceAt ``LimitEntry family.entry.id.raw
      family.entry.declaration formalPresentation apex
    let selection : NativeSourceLimitSelection := {
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
    let owner ← retainLimitConstruction {
      value := apex
      category := some {
        role := .object
        expression := family.category.expression
        bundle
        limit := some selection } }
    mkLambdaFVars formals owner.value (usedOnly := false) (usedLetOnly := false)

/-- Form a whole target-cone request from an already prepared original owner family.
This retains that exact construction and interface; no producer is invoked a second time. -/
opaque LimitFamily.markSelected (family : LimitFamily) (ownerFamily : Expr)
    (levels : List Level) (parameters : Array Expr) : MetaM Expr := do
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
  check ownerFamily
  let originalOwner := ownerFamily.betaRev parameters.reverse (preserveMData := true)
  check originalOwner
  let some selection ← NativeLimitSelection.ofExpr? originalOwner
    | throwError "the whole cone lost its original formal owner application"
  family.requireInterface selection.source
  unless !selection.source.construction.isAnonymous &&
      selection.source.presentation.equal presentation do
    throwError "the whole cone changed its original owner-family application"
  let ownerBody ← mkAppM ``Function.const
    #[← inferType ownerFamily, originalOwner, ownerFamily]
  let owner := Expr.mdata (KVMap.empty
    |>.setName `CasCompiler.source.limit.ownerFamily family.entry.declaration
    |>.setString `CasCompiler.source.limit.ownerId family.entry.id.raw) ownerBody
  let body ← mkAppM ``Function.const
    #[← inferType owner, selection.source.cone, owner]
  let body ← retainSourceApplication family.entry.declaration presentation body
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``LimitFamily
    |>.setString `CasCompiler.source.id family.entry.id.raw
    |>.setName `CasCompiler.source.declaration family.entry.declaration
    |>.setBool `CasCompiler.source.limit.whole true) body

/-- Form a new complete raw cone request at its own source formation occurrence. -/
opaque LimitFamily.mark (family : LimitFamily) (levels : List Level)
    (parameters : Array Expr) : MetaM Expr := do
  let construction ← mkFreshUserName `rawLimitConstruction
  let ownerFamily ← family.prepareOwner levels construction
  family.markSelected ownerFamily levels parameters

/-- Read only the original typed owner/family pair emitted above. The family is retained as
a field, never recovered by abstracting equal actual parameters from the selected interface. -/
private def limitOwner (family : LimitFamily) (owner : Expr) :
    MetaM (Expr × NativeLimitSelection) := do
  let .mdata data body := owner
    | throwError "the whole cone lost its original owner-family envelope"
  unless data.getName `CasCompiler.source.limit.ownerFamily == family.entry.declaration &&
      data.getString `CasCompiler.source.limit.ownerId == family.entry.id.raw &&
      body.isAppOfArity ``Function.const 4 do
    throwError "the whole cone changed its original owner-family envelope"
  let ownerFamily := body.getAppArgs[3]!
  let originalOwner := body.getAppArgs[2]!
  let some selected ← NativeLimitSelection.ofExpr? originalOwner
    | throwError "the whole cone lost its original construction selection"
  family.requireInterface selected.source
  let original := selected.source.presentation.consumeMData
  unless original.getAppNumArgs == family.parameterCount do
    throwError "the original owner lost a native declaration parameter"
  let applied := ownerFamily.betaRev original.getAppArgs.reverse (preserveMData := true)
  check applied
  unless applied.equal originalOwner do
    throwError "the original owner changed its retained formal family"
  return (ownerFamily, selected)

/-- Read the exact original formal owner family from its sealed raw-cone envelope.
Consumers use the original full telescope; equal actual parameters never reconstruct it. -/
opaque LimitFamily.ownerFamily (family : LimitFamily) (owner : Expr) : MetaM Expr := do
  return (← limitOwner family owner).1

/-- Reopen the original owner at the already admitted declaration positions. This only
substitutes the retained formal family; its construction identity and constructor universes
remain unchanged. The caller supplies marked actuals from the original application table. -/
opaque LimitFamily.ownerAt (family : LimitFamily) (owner : Expr)
    (parameters : Array Expr) : MetaM NativeLimitSelection := do
  unless parameters.size == family.parameterCount do
    throwError "the cone owner view requires every original native parameter position"
  let (ownerFamily, original) ← limitOwner family owner
  let applied := ownerFamily.betaRev parameters.reverse (preserveMData := true)
  check applied
  if applied.hasMVar || applied.hasLevelMVar then
    throwError "the cone owner view has an unresolved original parameter"
  let some selected ← NativeLimitSelection.ofExpr? applied
    | throwError "the cone owner view lost its retained original construction"
  family.requireInterface selected.source
  unless selected.source.construction == original.source.construction &&
      (← isDefEq selected.source.presentation original.source.presentation) do
    throwError "the cone owner view changed its original selected presentation"
  return selected

/-- Form the original whole-cone boundary from an already retained typed owner.
This is the same selected request as markSelected, without preparing another owner family. -/
opaque LimitFamily.markAtOwner (family : LimitFamily) (owner : Expr)
    (levels : List Level) (parameters : Array Expr) : MetaM Expr := do
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
  let body ← mkAppM ``Function.const #[← inferType owner, selected.source.cone, owner]
  let body ← retainSourceApplication family.entry.declaration presentation body
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``LimitFamily
    |>.setString `CasCompiler.source.id family.entry.id.raw
    |>.setName `CasCompiler.source.declaration family.entry.declaration
    |>.setBool `CasCompiler.source.limit.whole true) body

/-- A whole-cone marker resolves only its explicit accepted limit owner. -/
opaque LimitFamily.fromMark (data : MData) : MetaM LimitFamily := do
  unless data.getName `CasCompiler.source.kind == ``LimitFamily &&
      data.getBool `CasCompiler.source.limit.whole do
    throwError "the source value is not its original whole-cone request"
  let family ← LimitFamily.forId ⟨data.getString `CasCompiler.source.id⟩
  unless family.entry.declaration == data.getName `CasCompiler.source.declaration do
    throwError "the whole-cone request changed its original declaration"
  return family

/-- Recover the exact native application and retained original interface. Rechecking the
accepted shape does not regenerate a selection, presentation or result occurrence. -/
opaque LimitFamily.application (family : LimitFamily) (body : Expr) :
    MetaM (List Level × Array Expr × Expr × NativeLimitSelection) := do
  let .mdata applicationData applicationBody := body
    | throwError "the whole cone lost its original typed application envelope"
  unless applicationData.getName `CasCompiler.source.application == family.entry.declaration &&
      applicationBody.isAppOfArity ``Function.const 4 do
    throwError "the whole cone changed its original native application"
  let presentation := applicationBody.getAppArgs[3]!
  let .const declaration levels := presentation.consumeMData.getAppFn
    | throwError "the whole cone lost its original declared presentation"
  unless declaration == family.entry.declaration &&
      presentation.getAppNumArgs == family.parameterCount do
    throwError "the whole cone changed its complete presentation parameters"
  let selectedBody := applicationBody.getAppArgs[2]!
  unless selectedBody.isAppOfArity ``Function.const 4 do
    throwError "the whole cone lost its original typed construction owner"
  let owner := selectedBody.getAppArgs[3]!
  let cone := selectedBody.getAppArgs[2]!
  let (_, selected) ← limitOwner family owner
  unless selected.source.presentation.equal presentation &&
      selected.source.cone.equal cone do
    throwError "the whole cone changed its retained presentation or native cone"
  return (levels, presentation.getAppArgs, owner, selected)

/-- Rebind an original direct formal construction through its retained full owner family.
Creation lifts keep their distinct source owner and are handled by their accepted lift path. -/
opaque LimitFamily.formalAt (originalEnvelope : Expr) (parameters : Array Expr) :
    MetaM (Option Expr) := do
  let some original ← NativeLimitSelection.ofExpr? originalEnvelope | return none
  unless original.source.presentation.consumeMData.getAppFn.isConstOf
      original.source.declaration do return none
  let family ← LimitFamily.forId ⟨original.source.row⟩
  family.requireInterface original.source
  let some ownerFamily := original.source.ownerFamily
    | throwError "the formal construction lost its original complete owner family"
  unless parameters.size == family.parameterCount do
    throwError "the formal construction changed its original parameter positions"
  let applied := ownerFamily.betaRev parameters.reverse (preserveMData := true)
  check applied
  let some selected ← NativeLimitSelection.ofExpr? applied
    | throwError "the formal construction lost its original owner application"
  family.requireInterface selected.source
  unless selected.source.construction == original.source.construction &&
      (← isDefEq selected.source.presentation original.source.presentation) do
    throwError "the formal construction changed its original selected presentation"
  let selected := { selected.source with ownerFamily := some ownerFamily }
  let category : NativeSourceCategory := {
    role := .object, expression := selected.category, bundle := selected.bundle,
    limit := some selected }
  let some receiver ← NativeLimitSelection.ofExpr? applied
    | throwError "the formal construction lost its original receiver"
  return some (← retainLimitConstruction
    { value := receiver.receiver, category := some category }).value

/-- Demand the whole cone of an explicitly retained original formal construction.
The full marked declaration spine, interface family and construction identity are reused.
A created source cone never acquires the target category's raw cone role. -/
opaque LimitFamily.wholeFrom (originalEnvelope : Expr) : MetaM (Option Expr) := do
  let some selected ← NativeLimitSelection.ofExpr? originalEnvelope | return none
  let family ← LimitFamily.forId ⟨selected.source.row⟩
  family.requireInterface selected.source
  unless selected.source.presentation.consumeMData.getAppFn.isConstOf
      selected.source.declaration do
    throwStratum .noImplementation
      "the selected creation of a limit requires its accepted computational lift"
  let some ownerFamily := selected.source.ownerFamily
    | throwError "the formal construction lost its retained original interface family"
  let presentation := selected.source.interface.presentation.consumeMData
  let .const declaration levels := presentation.getAppFn
    | throwError "the formal construction lost its original full native presentation"
  unless declaration == family.entry.declaration do
    throwError "the formal construction changed its original registered presentation"
  return some (← family.markSelected ownerFamily levels presentation.getAppArgs)

end CasCompiler
