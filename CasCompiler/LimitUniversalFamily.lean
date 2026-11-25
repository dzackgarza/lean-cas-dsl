module

public import CasCompiler.LimitFamily

public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- The original native universal-property record of one accepted limit presentation.
The raw cone port remains a separate family; no cone parameter is added to the
mathematical declaration. Actual completed cones are retained by runtime captures. -/
structure LimitUniversalFamily where
  private mk ::
  presentation : LimitFamily
  projection : Name
  family : Expr
  familyType : Expr

def LimitUniversalFamily.operation (family : LimitUniversalFamily) : String :=
  family.presentation.operation ++ "#" ++ family.projection.getString!

def LimitUniversalFamily.input (family : LimitUniversalFamily) : String :=
  family.operation ++ "#input"

def LimitUniversalFamily.universeParams (family : LimitUniversalFamily) : List Name :=
  family.presentation.universeParams

def LimitUniversalFamily.parameterCount (family : LimitUniversalFamily) : Nat :=
  family.presentation.parameterCount

/-- The native selection from the complete original LimitCone/ColimitCocone. -/
def LimitUniversalFamily.path (family : LimitUniversalFamily) : Array Name :=
  #[family.projection]

/-- Project the already accepted universal data under every original declaration
parameter and rigid universe. IsLimit/IsColimit are data records, not proof fields. -/
opaque LimitUniversalFamily.forId (id : LimitId) : MetaM LimitUniversalFamily :=
    withLCtx {} #[] do
  let presentation ← LimitFamily.forId id
  let projection := if presentation.entry.colimit then
    ``CategoryTheory.Limits.ColimitCocone.isColimit
    else ``CategoryTheory.Limits.LimitCone.isLimit
  forallTelescopeReducing (← inferType presentation.presentationFamily) fun parameters _ => do
    unless parameters.size == presentation.parameterCount do
      throwError "the universal family changed its complete original parameter telescope"
    let selected := mkAppN presentation.presentationFamily parameters
    let universal ← mkAppM projection #[selected]
    if ← isProof universal then
      throwError "the original universal interface was replaced by a proof"
    let universal ← sourceReferenceAt ``LimitUniversalFamily id.raw
      presentation.entry.declaration selected universal
    let family ← mkLambdaFVars parameters universal
      (usedOnly := false) (usedLetOnly := false)
    check family
    if family.hasMVar || family.hasLevelMVar then
      throwError "the universal family has an unresolved original native parameter"
    return ⟨presentation, projection, family, ← inferType family⟩

/-- Retain an already selected owner at its complete actual parameter table.
The owner is the existing LimitFamily typed envelope. It carries the original
construction and formal interface, not a search key for a completed runtime cone. -/
opaque LimitUniversalFamily.markAtOwner (family : LimitUniversalFamily) (owner : Expr)
    (levels : List Level) (parameters : Array Expr)
    (cone : Option Expr := none) : MetaM Expr := do
  unless levels.length == family.universeParams.length &&
      parameters.size == family.parameterCount do
    throwError "the universal request changed its complete native parameter telescope"
  let presentation := mkAppN
    (family.presentation.presentationFamily.instantiateLevelParams
      family.universeParams levels) parameters
  check presentation
  if presentation.hasMVar || presentation.hasLevelMVar then
    throwError "the universal request has unresolved original native parameters"
  let selected ← family.presentation.ownerAt owner parameters
  unless selected.source.interface.presentation.equal presentation do
    throwError "the universal request changed its original target presentation"
  let universal ← mkAppM family.projection #[selected.source.interface.presentation]
  let nativeCone ← mkAppM family.presentation.coneProjection #[selected.source.interface.presentation]
  let cone ← match cone with
    | some cone => pure cone
    | none => family.presentation.markAtOwner owner levels parameters
  check cone
  unless ← isDefEq (← inferType cone) (← inferType nativeCone) do
    throwError "the retained universal input changed its original native cone interface"
  if cone.hasMVar || cone.hasLevelMVar then
    throwError "the retained universal cone has unresolved native parameters"
  let retained ← mkAppM ``Function.const #[← inferType cone, universal, cone]
  let body ← mkAppM ``Function.const #[← inferType owner, retained, owner]
  let body ← retainSourceApplication family.presentation.entry.declaration presentation body
  return .mdata (KVMap.empty
    |>.setName `CasCompiler.source.kind ``LimitUniversalFamily
    |>.setString `CasCompiler.source.id family.presentation.entry.id.raw
    |>.setName `CasCompiler.source.declaration family.presentation.entry.declaration
    |>.setName `CasCompiler.source.limit.universal family.projection) body

/-- Reuse the original owner family formed by the source producer. This performs
only positional substitution and adds no new construction or interface selection. -/
opaque LimitUniversalFamily.markSelected (family : LimitUniversalFamily) (ownerFamily : Expr)
    (levels : List Level) (parameters : Array Expr)
    (cone : Option Expr := none) : MetaM Expr := do
  unless parameters.size == family.parameterCount do
    throwError "the universal owner requires every original declaration parameter"
  check ownerFamily
  let originalOwner := ownerFamily.betaRev parameters.reverse (preserveMData := true)
  check originalOwner
  let body ← mkAppM ``Function.const
    #[← inferType ownerFamily, originalOwner, ownerFamily]
  let owner := Expr.mdata (KVMap.empty
    |>.setName `CasCompiler.source.limit.ownerFamily family.presentation.entry.declaration
    |>.setString `CasCompiler.source.limit.ownerId family.presentation.entry.id.raw) body
  family.markAtOwner owner levels parameters cone

/-- Resolve only the original accepted owner explicitly named by a universal marker. -/
opaque LimitUniversalFamily.fromMark (data : MData) : MetaM LimitUniversalFamily := do
  unless data.getName `CasCompiler.source.kind == ``LimitUniversalFamily do
    throwError "the source value is not its selected universal family"
  let family ← LimitUniversalFamily.forId ⟨data.getString `CasCompiler.source.id⟩
  unless data.getName `CasCompiler.source.declaration == family.presentation.entry.declaration &&
      data.getName `CasCompiler.source.limit.universal == family.projection do
    throwError "the universal source changed its original declaration or native projection"
  return family

/-- Read the exact selected application and owner supplied by markSelected/markAtOwner.
The original full parameter table remains positional, including implicit and proof inputs. -/
opaque LimitUniversalFamily.application (family : LimitUniversalFamily) (body : Expr) :
    MetaM (List Level × Array Expr × Expr × NativeLimitSelection × Expr) := do
  let .mdata data retained := body
    | throwError "the universal request lost its original typed application envelope"
  unless data.getName `CasCompiler.source.application == family.presentation.entry.declaration &&
      retained.isAppOfArity ``Function.const 4 do
    throwError "the universal request changed its original native application"
  let presentation := retained.getAppArgs[3]!
  let .const declaration levels := presentation.consumeMData.getAppFn
    | throwError "the universal request lost its original declaration application"
  unless declaration == family.presentation.entry.declaration &&
      levels.length == family.universeParams.length &&
      presentation.getAppNumArgs == family.parameterCount do
    throwError "the universal request changed its original complete declaration telescope"
  let selectedBody := retained.getAppArgs[2]!
  unless selectedBody.isAppOfArity ``Function.const 4 do
    throwError "the universal request lost its original typed owner"
  let owner := selectedBody.getAppArgs[3]!
  let retainedCone := selectedBody.getAppArgs[2]!
  unless retainedCone.isAppOfArity ``Function.const 4 do
    throwError "the universal request lost its exact retained cone input"
  let cone := retainedCone.getAppArgs[3]!
  let universal := retainedCone.getAppArgs[2]!
  let selected ← family.presentation.ownerAt owner presentation.getAppArgs
  unless selected.source.interface.presentation.equal presentation do
    throwError "the universal request changed its original selected presentation"
  let expected ← mkAppM family.projection #[selected.source.interface.presentation]
  unless universal.equal expected do
    throwError "the universal request changed its retained native universal data"
  let nativeCone ← mkAppM family.presentation.coneProjection #[selected.source.interface.presentation]
  check cone
  unless ← isDefEq (← inferType cone) (← inferType nativeCone) do
    throwError "the universal request changed its exact retained cone interface"
  return (levels, presentation.getAppArgs, owner, selected, cone)

end CasCompiler
