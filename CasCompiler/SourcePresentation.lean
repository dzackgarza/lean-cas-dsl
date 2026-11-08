module

public import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- Keep the actual selected isomorphism as typed native data beside its ordinary map.
Reuse: Function.const's identity law and native MData, as in source type provenance.
The full isomorphism is transported by native abstraction and substitution. -/
def retainSourceIso (iso value : Expr) : MetaM Expr := do
  let type ← whnfR (← inferType iso)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "source invertibility requires its actual native isomorphism"
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
  unless ← isDefEq (← inferType value) (← inferType hom) <&&> isDefEq value hom do
    throwError "the source isomorphism has a different original map"
  let body ← mkAppM ``Function.const #[← inferType iso, value, iso]
  return .mdata (KVMap.empty.setName `CasCompiler.source.isoOrigin ``CategoryTheory.Iso) body

/-- Read only the typed isomorphism retained by source formation, through native aliases.
Reuse: native let substitution and the checked Function.const provenance layout. -/
partial def sourceIsoOrigin? (value : Expr) : MetaM (Option Expr) := do
  match ← instantiateMVars value with
  | .mdata data body =>
    if data.getName `CasCompiler.source.isoOrigin != ``CategoryTheory.Iso then
      return ← sourceIsoOrigin? body
    unless body.isAppOfArity ``Function.const 4 do
      throwError "the source map lost its typed isomorphism data"
    let iso := body.getAppArgs[3]!
    discard <| retainSourceIso iso body.getAppArgs[2]!
    return some iso
  | .fvar id =>
    match (← id.getDecl).value? with
    | some value => sourceIsoOrigin? value
    | none => pure none
  | .letE _ _ value body _ => sourceIsoOrigin? (body.instantiate1 value)
  | _ => pure none

/-- A genuine core morphism already contains its inverse data.
Reuse: Mathlib CoreHom.iso and Core.isoMk, with their complete original endpoints. -/
def sourceMorphismIso? (value : Expr) : MetaM (Option Expr) := do
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

/-- Apply the selected presentation family at its actual dependent arguments.
Reuse: PresentationComparisonEntry/validatePresentation, native application, Iso.hom/symm.
The registered category and actual isomorphism retain their complete dictionaries. -/
opaque sourcePresentation (name : String) (inverse : Bool)
    (application : Expr → TermElabM Expr) : TermElabM NativeSourceJudgement := do
  let state ← semanticState
  let #[entry] := state.presentations.filter (·.name == name)
    | throwError "the selected source presentation requires one registered comparison"
  discard <| checkedDeclaration entry.declaration
  let #[source] := state.objects.filter (·.id == entry.source)
    | throwError "the selected presentation requires its registered source object"
  let #[target] := state.objects.filter (·.id == entry.target)
    | throwError "the selected presentation requires its registered target object"
  unless source.category == target.category do
    throwError "the presentation endpoints have different selected categories"
  discard <| checkedDeclaration source.declaration
  discard <| checkedDeclaration target.declaration
  let #[category] := state.categories.filter (·.id == source.category)
    | throwError "the selected presentation requires one complete category"
  discard <| checkedDeclaration category.declaration
  let iso ← application (← mkConstWithFreshMVarLevels entry.declaration)
  let iso ← instantiateMVars iso
  if iso.hasMVar || iso.hasLevelMVar then
    throwError "the selected presentation has undetermined native parameters"
  let type ← whnfR (← inferType iso)
  unless type.isAppOfArity ``CategoryTheory.Iso 4 do
    throwError "the selected presentation is not its declared native isomorphism"
  let actual ← mkAppOptM ``CategoryTheory.Cat.of
    #[some type.getAppArgs[0]!, some type.getAppArgs[1]!]
  let family ← mkConstWithFreshMVarLevels category.declaration
  let (parameters, _, _) ← forallMetaTelescopeReducing (← inferType family)
  unless ← expandSourceStructures parameters do
    throwError "the presentation category has inconsistent native parameters"
  let bundle := mkAppN family parameters
  unless ← isDefEq bundle actual do
    throwError "the presentation has a different complete registered category"
  let bundle ← instantiateMVars bundle
  let iso ← if inverse then mkAppM ``CategoryTheory.Iso.symm #[iso] else pure iso
  let hom ← mkAppM ``CategoryTheory.Iso.hom #[iso]
  let value ← retainSourceIso iso hom
  return ⟨sourceReference ``PresentationComparisonEntry entry.id.raw entry.declaration value,
    some ⟨.morphism, category.expression, bundle, none⟩⟩

end CasCompiler
