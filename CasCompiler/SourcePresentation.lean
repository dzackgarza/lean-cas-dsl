module

public import CasCompiler.Surface
public import CasCompiler.PresentationFamily
public import CasCompiler.SourceProof

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- Retain the actual selected Iso beside its forward map in the typed source record.
The complete supplied Iso, including its native category dictionary, remains unchanged. -/
def retainSourceIso (iso : Expr) (source : SourceSelection Expr)
    (context : Option OpenContext := none) : MetaM (SourceSelection Expr) := do
  let verify := fun (values : Array Expr) => do
    let iso := values[0]!
    let value := values[1]!
    let type ← whnfR (← inferType iso)
    unless type.isAppOfArity ``CategoryTheory.Iso 4 do
      throwError "source invertibility requires its actual native isomorphism"
    let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
    unless ← isDefEq (← inferType value) (← inferType hom) <&&> isDefEq value hom do
      throwError "the source isomorphism has a different original map"
  match context with
  | none => verify #[iso, source.value]
  | some context => context.withOriginalSources #[iso, source.value] verify
  return { source with isoOrigin := some iso }

/-- Read the Iso supplied by the exact source binder. When the displayed forward arrow
is an opaque alias, keep that actual arrow and transport the original two checked laws. -/
def sourceIsoOrigin? (value : Expr) : SourceReadM (Option Expr) := do
  let some selected ← SourceReadM.selection? value | return none
  let some iso := selected.isoOrigin | return none
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
  if ← isDefEq hom value then return some iso
  let arguments := #[value, ← mkAppM ``CategoryTheory.Iso.inv #[iso],
    ← mkAppM ``CategoryTheory.Iso.hom_inv_id #[iso],
    ← mkAppM ``CategoryTheory.Iso.inv_hom_id #[iso]]
  let rebuilt ← elabSourceApplicationApplicableScoped
    (← mkConstWithFreshMVarLevels ``CategoryTheory.Iso.mk)
    (Array.replicate arguments.size Syntax.missing) none fun index expected => do
      let original := arguments[index]!
      if index < 2 then
        if ← isDefEq (← inferType original) expected then return .ok original
        let selected := (← SourceReadM.selection? original).getD { value := original }
        return .ok (← SourceReadM.select { selected with value := original } (some expected))
      return .ok (← SourceReadM.prove expected
        (fun _ sources => pure sources[0]!) #[original])
  match rebuilt with
  | .ok (iso, _) => return some iso
  | .error message => liftM (m := TermElabM) <| throwError message

/-- A genuine core morphism already contains its inverse data at its original endpoints. -/
def sourceMorphismIso? (value : Expr) : SourceReadM (Option Expr) := do
  if let some iso ← sourceIsoOrigin? value then return some iso
  let type ← whnfR (← inferType value)
  unless type.isAppOfArity ``CategoryTheory.CoreHom 4 do return none
  let iso ← mkAppM ``CategoryTheory.CoreHom.iso #[value]
  return some (← mkAppOptM ``CategoryTheory.Core.isoMk
    #[some type.getAppArgs[0]!, some type.getAppArgs[1]!,
      some type.getAppArgs[2]!, some type.getAppArgs[3]!, some iso])

/-- Use the actual inverse-bearing source data in a core action, preserving its dictionary.
Reuse: Mathlib Core.mk/CoreHom.mk; no IsIso instance or inverse is inferred. -/
def sourceIsoCoreHom (iso bundle : Expr) : MetaM Expr := do
  let type ← whnfR (← inferType iso)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the core action requires its actual source isomorphism"
  let carrier ← mkAppM ``CategoryTheory.Bundled.α #[bundle]
  let structureValue ← mkAppM ``CategoryTheory.Bundled.str #[bundle]
  unless ← isDefEq type.getAppArgs[0]! carrier <&&>
      isDefEq type.getAppArgs[1]! structureValue do
    throwError "the source isomorphism has a different complete selected category"
  let x ← mkAppM ``CategoryTheory.Core.mk #[type.getAppArgs[2]!]
  let y ← mkAppM ``CategoryTheory.Core.mk #[type.getAppArgs[3]!]
  mkAppOptM ``CategoryTheory.CoreHom.mk
    #[some carrier, some structureValue, some x, some y, some iso]

/-- Apply the selected whole comparison at the supplied native arguments and bind its
actual Iso before deriving a directed map. Complete endpoint and category rows stay typed. -/
opaque sourcePresentation (name : String) (inverse : Bool)
    (application : Expr → SourceReadM Expr) : SourceReadM NativeSourceJudgement := do
  let state ← semanticState
  let #[entry] := state.presentations.filter (·.name == name)
    | liftM (m := TermElabM) <|
      throwError "the selected source presentation requires one registered comparison"
  let family ← PresentationFamily.forEntry entry
  let iso ← application (← mkConstWithFreshMVarLevels entry.declaration)
  let iso ← liftM (m := MetaM) <| instantiateMVars iso
  if iso.hasMVar || iso.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the selected presentation has undetermined native parameters"
  let type ← whnfR (← inferType iso)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    liftM (m := TermElabM) <|
      throwError "the selected presentation is not its declared native isomorphism"
  let actual ← mkAppOptM ``CategoryTheory.Cat.of
    #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
  let category := family.category
  let categoryFamily ← mkConstWithFreshMVarLevels category.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType categoryFamily)
  unless ← expandSourceStructures parameters do
    liftM (m := TermElabM) <|
      throwError "the presentation category has inconsistent native parameters"
  let bundle := mkAppN categoryFamily parameters
  unless ← isDefEq bundle actual do
    liftM (m := TermElabM) <|
      throwError "the presentation has a different complete registered category"
  let bundle ← liftM (m := MetaM) <| instantiateMVars bundle
  discard <| SourceReadM.select (sourceReference (.category category) bundle)
  let (source, target) ← family.endpoints iso
  let source ← SourceReadM.select (← retainSourceApplication source source.value)
  let target ← SourceReadM.select (← retainSourceApplication target target.value)
  let selected ← family.withEndpoints iso source target (some (← get).context)
  let iso ← SourceReadM.select selected
  let iso ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[iso] else pure iso
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
  let category : NativeSourceCategory := ⟨.morphism, category.expression, bundle, none, none⟩
  let selected ← retainSourceIso iso {
    (sourceDerivedReference (.presentation entry) hom) with category := some category }
  let value ← selectMorphism selected
    (fun selected expected => SourceReadM.select selected expected) (some bundle)
  return ⟨value, some category⟩

end CasCompiler
