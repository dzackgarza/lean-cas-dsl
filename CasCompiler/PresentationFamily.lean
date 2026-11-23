module

public import CasCompiler.SourceCarrier
public import CasCompiler.Layout
public import CasCompiler.SourceReference

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue

/-- A registered isomorphism family and the native carrier-function paths of its two maps.
The paths are checked on an abstract isomorphism at the full rigid declaration telescope;
no actual endpoint, point or runtime payload chooses the path. -/
structure PresentationFamily where
  private mk ::
  entry : PresentationComparisonEntry
  source : ObjectEntry
  target : ObjectEntry
  category : NamedCategoryEntry
  family : Expr
  familyType : Expr
  universeParams : List Name
  forwardPath : Array Name
  inversePath : Array Name

private def originalPoint (argument : InputArgumentRef) (iso : BindingId) : MetaM Bool := do
  match argument with
  | .slot index => return index == 0
  | .expression source =>
    match ← source.inputProjectionThrough #[] #[] #[iso] with
    | some (.projection route) =>
      match route.target with
      | .argument index => return index == 0 && route.path.isEmpty
      | .context _ => return false
    | _ => return false

/-- Read exactly the existing selected carrier action, then trace its unchanged point argument
to the original abstract Iso. Reuse: sourceFunction and ApplicationLayout.inputProjectionThrough.
This does not identify a callable by a field suffix or by equality of actual input values. -/
private def carrierPath (context : OpenContext) (isoId : BindingId) (iso : Expr)
    (category : NativeSourceCategory) (inverse : Bool) : MetaM (Array Name) := do
  let selected ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[iso] else pure iso
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[selected]
  let function ← sourceFunction ⟨hom, some category⟩
  let layout ← SourceLayout.ofTerm (← context.close function)
  let (_, application) ← ApplicationLayout.ofSource layout context #[]
  let some (.callable route steps) ←
      application.inputProjectionThrough #[(#[], 1)] #[] #[isoId]
    | throwUnsupportedSource "the presentation carrier has no native input-function path"
  let .context original := route.target
    | throwError "the presentation carrier function changed its original isomorphism"
  unless original == isoId && !route.path.isEmpty do
    throwError "the presentation carrier function lost its exact isomorphism field"
  let #[step] := steps
    | throwUnsupportedSource "the presentation carrier requires an additional source action"
  let #[argument] := step.arguments
    | throwUnsupportedSource "the presentation carrier changed its complete point application"
  unless step.selection.isEmpty && (← originalPoint argument isoId) do
    throwUnsupportedSource "the presentation carrier does not apply its unchanged original point"
  return route.path

/-- Retain the already registered native Iso family under the release declaration checks.
The registered endpoint declarations and category are checked before deriving its two carrier
paths. Only supplied structural carrier actions participate. -/
opaque PresentationFamily.forEntry (row : PresentationComparisonEntry) :
    MetaM PresentationFamily := withLCtx {} #[] do
  let state ← semanticState
  validatePresentation { state with presentations := state.presentations.filter (·.id != row.id) } row
  let some source := state.objects.find? (·.id == row.source)
    | throwError "the presentation source is not registered"
  let some target := state.objects.find? (·.id == row.target)
    | throwError "the presentation target is not registered"
  let some category := state.categories.find? (·.id == source.category)
    | throwError "the presentation category is not registered"
  discard <| checkedDeclaration source.declaration
  discard <| checkedDeclaration target.declaration
  discard <| checkedDeclaration category.declaration
  let info ← checkedDeclaration row.declaration
  let family := mkConst row.declaration (info.levelParams.map Level.param)
  let (forwardPath, inversePath) ← forallTelescopeReducing info.type fun parameters result => do
    let result ← whnfR result
    unless result.isAppOfArity ``CategoryTheory.Iso 4 do
      throwError "the registered presentation has no complete native isomorphism result"
    let bundle ← mkAppOptM ``CategoryTheory.Cat.of
      #[some result.getAppArgs[0]!, some result.getAppArgs[1]!]
    withLocalDeclD `presentation result fun iso => do
      let bindings := (parameters.push iso).mapIdx fun index expression =>
        { id := { session := "presentation-path", serial := index },
          role := BindingRole.parameter, expression : LocalBinding }
      let context ← ContextTelescope.capture bindings
      let isoId := bindings.back!.id
      let selected : NativeSourceCategory := ⟨.morphism, category.expression, bundle, none, none⟩
      return (← carrierPath context isoId iso selected false,
        ← carrierPath context isoId iso selected true)
  unless forwardPath != inversePath do
    throwError "the presentation carrier paths lost their distinct Iso directions"
  return ⟨row, source, target, category, family, info.type, info.levelParams,
    forwardPath, inversePath⟩

def PresentationFamily.instantiate (family : PresentationFamily) : MetaM (Expr × List Level) := do
  let levels ← family.universeParams.mapM fun _ => mkFreshLevelMVar
  return (family.family.instantiateLevelParams family.universeParams levels, levels)

/-- The original, un-oriented native endpoints at these complete declaration parameters.
The supplied registry already requires these named families; the native terms retain every
parameter, and source references identify their exact rows without choosing runtime values. -/
def PresentationFamily.endpoints (family : PresentationFamily) (applied : Expr) :
    MetaM (Expr × Expr) := do
  unless applied.getAppFn.constName? == some family.entry.declaration do
    throwError "the selected presentation changed its declared native family"
  let result ← whnfR (← inferType applied)
  unless result.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the selected presentation requires its complete declaration parameters"
  let source := result.getAppArgs[2]!.headBeta
  let target := result.getAppArgs[3]!.headBeta
  unless source.isAppOf family.source.declaration && target.isAppOf family.target.declaration do
    throwError "the selected presentation lost its declared native endpoint families"
  return (sourceReference ``ObjectEntry family.source.id.raw family.source.declaration source,
    sourceReference ``ObjectEntry family.target.id.raw family.target.declaration target)

/-- Keep explicitly supplied original endpoints beside the original Iso, using the same typed
Function.const provenance layout as source types and retained source isomorphisms. Equality
checks validate these supplied terms; they never search for or choose a runtime occurrence. -/
def PresentationFamily.withEndpoints (family : PresentationFamily) (applied source target : Expr) :
    MetaM Expr := do
  let (expectedSource, expectedTarget) ← family.endpoints applied
  checkRegisteredDomains source expectedSource
  checkRegisteredDomains target expectedTarget
  unless ← isDefEq source expectedSource <&&> isDefEq target expectedTarget do
    throwError "the presentation request changed its complete declared endpoints"
  let body ← mkAppM ``Function.const #[← inferType target, applied, target]
  let body ← mkAppM ``Function.const #[← inferType source, body, source]
  return .mdata (KVMap.empty |>.setName `CasCompiler.source.kind ``PresentationFamily
    |>.setString `CasCompiler.source.id family.entry.id.raw
    |>.setName `CasCompiler.source.declaration family.entry.declaration
    |>.setString `CasCompiler.source.endpoints "supplied") body

/-- Mark the original named family. Lowering derives its endpoints from the same admitted
native argument positions, so repeated closed parameter syntax cannot create new inputs. -/
def PresentationFamily.mark (family : PresentationFamily) (applied : Expr) : MetaM Expr := do
  discard <| family.endpoints applied
  return .mdata (KVMap.empty |>.setName `CasCompiler.source.kind ``PresentationFamily
    |>.setString `CasCompiler.source.id family.entry.id.raw
    |>.setName `CasCompiler.source.declaration family.entry.declaration) applied

/-- Validate and recover only the endpoint layout emitted by mark or withEndpoints. -/
def PresentationFamily.unmark (family : PresentationFamily) (data : MData) (body : Expr) :
    MetaM (Expr × Option (Expr × Expr)) := do
  if data.getString `CasCompiler.source.endpoints != "supplied" then
    discard <| family.endpoints body
    return (body, none)
  unless body.isAppOfArity ``Function.const 4 do
    throwError "the presentation source lost its complete endpoint provenance"
  let source := body.getAppArgs[3]!
  let inner := body.getAppArgs[2]!
  unless inner.isAppOfArity ``Function.const 4 do
    throwError "the presentation source lost its second endpoint"
  let target := inner.getAppArgs[3]!
  let applied := inner.getAppArgs[2]!
  discard <| family.withEndpoints applied source target
  return (applied, some (source, target))

/-- The one declared direction selected by an exact native carrier-function path. -/
def PresentationFamily.direction? (family : PresentationFamily) (path : Array Name) : Option Bool :=
  if path == family.forwardPath then some false
  else if path == family.inversePath then some true
  else none

/-- The ordinary native carrier function of this actual selected Iso, retaining its complete
category dictionary. The caller supplies the original Iso value, including any native marks. -/
def PresentationFamily.function (family : PresentationFamily) (iso : Expr) (inverse : Bool) :
    MetaM Expr := do
  let result ← whnfR (← inferType iso)
  unless result.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the presentation action requires its actual native Iso"
  let bundle ← mkAppOptM ``CategoryTheory.Cat.of
    #[some result.getAppArgs[0]!, some result.getAppArgs[1]!]
  let selected ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[iso] else pure iso
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[selected]
  sourceFunction ⟨hom, some ⟨.morphism, family.category.expression, bundle, none, none⟩⟩

end CasCompiler
