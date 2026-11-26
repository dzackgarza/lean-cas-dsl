module

public import CasCompiler.SelectionData
import all CasCompiler.SelectionData

public import CasCompiler.SourceCarrier
public import CasCompiler.Layout
public import CasCompiler.SourceReference

@[expose] public section

namespace CasCompiler

open Lean Meta CasCatalogue


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
    MetaM (SourceSelection Expr × SourceSelection Expr) := do
  unless applied.getAppFn.constName? == some family.entry.declaration do
    throwError "the selected presentation changed its declared native family"
  let result ← whnfR (← inferType applied)
  unless result.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the selected presentation requires its complete declaration parameters"
  let source := result.getAppArgs[2]!.headBeta
  let target := result.getAppArgs[3]!.headBeta
  unless source.isAppOf family.source.declaration && target.isAppOf family.target.declaration do
    throwError "the selected presentation lost its declared native endpoint families"
  return (sourceReference (.named (.registered (.inl family.source) family.category)) source,
    sourceReference (.named (.registered (.inl family.target) family.category)) target)

/-- Retain the original named Iso family and complete selected presentation row. -/
def PresentationFamily.selected (family : PresentationFamily) (applied : Expr) :
    MetaM (SourceSelection Expr) := do
  discard <| family.endpoints applied
  let .const _ levels := applied.getAppFn
    | throwError "the selected presentation lost its original native declaration"
  unless levels.length == family.universeParams.length do
    throwError "the selected presentation changed its complete universe telescope"
  return {
    value := applied, reference := some (.presentation family.entry)
    originalApplication := some applied
    application := some {
      family := .presentation family, universes := levels
      parameters := applied.getAppArgs } }

/-- Check the supplied native endpoints and retain their exact original occurrences.
The original-source view is used only for this mathematical compatibility check. -/
def PresentationFamily.withEndpoints (family : PresentationFamily) (applied source target : Expr)
    (context : Option OpenContext := none) : MetaM (SourceSelection Expr) := do
  let selected ← family.selected applied
  let verify := fun (terms : Array Expr) => do
    let (expectedSource, expectedTarget) ← family.endpoints terms[0]!
    checkRegisteredDomains terms[1]! expectedSource.value
    checkRegisteredDomains terms[2]! expectedTarget.value
    unless ← isDefEq terms[1]! expectedSource.value <&&>
        isDefEq terms[2]! expectedTarget.value do
      throwError "the presentation request changed its complete declared endpoints"
  match context with
  | some context => context.withOriginalSources #[applied, source, target] verify
  | none => verify #[applied, source, target]
  return { selected with presentationEndpoints := some (source, target) }

/-- The one declared direction selected by an exact native carrier-function path. -/
def PresentationFamily.direction? (family : PresentationFamily) (path : Array Name) : Option Bool :=
  if path == family.forwardPath then some false
  else if path == family.inversePath then some true
  else none

/-- The ordinary native carrier function of this actual selected Iso, retaining its complete
category dictionary. The caller supplies the exact original Iso occurrence. -/
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
