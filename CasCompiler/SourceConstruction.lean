module

public import CasCompiler.SourceCarrier
public import CasCompiler.SourcePresentation

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

/-- Apply a directly selected construction at its complete native source boundary.
Reuse: ConstructionEntry/validateConstruction, native dependent telescopes, the registered
Core constructor, and Mathlib Functor.obj/map. No inherited route chooses a construction.
Category arguments come from the full selected bundle; other explicit parameters are read
once at their declared types. A core action on a map requires the actual core morphism. -/
opaque sourceConstruction (entry : ConstructionEntry) (receiver : NativeSourceJudgement)
    (parameters : Array (Expr → TermElabM Expr)) : TermElabM NativeSourceJudgement := do
  let some selected := receiver.category
    | throwError "a category-sensitive construction requires its selected source category"
  discard <| checkedDeclaration entry.declaration
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, binders, result) ← forallMetaTelescopeReducing (← inferType declaration)
  let result ← whnfR result
  unless result.isAppOfArity ``CategoryTheory.Functor 4 do
    throwError "the source construction requires its complete native functor family"
  let core := (← whnfR result.getAppArgs[0]!).isAppOf ``CategoryTheory.Core
  let iso ← if selected.role == .morphism then sourceIsoOrigin? receiver.value else pure none
  let alreadyCore := (← whnfR (← mkAppM ``CategoryTheory.Bundled.α
    #[selected.bundle])).isAppOf ``CategoryTheory.Core
  let wrapCore := core && (selected.role == .object || (!alreadyCore && iso.isSome))
  let state ← semanticState
  let bundle ← if wrapCore then do
      let #[constructor] := state.constructors.filter
        (·.semantics == `CasCatalogue.Constructors.core)
        | throwError "the construction requires its registered core constructor"
      discard <| checkedDeclaration constructor.semantics
      applyConstructorInterface constructor.semantics #[selected.bundle] #[selected.bundle]
    else pure selected.bundle
  unless ← expandSourceStructures arguments do
    throwError "the construction has inconsistent native category parameters"
  let function := mkAppN declaration arguments
  let (domain, _) ← functorCategoryBundles function
  unless ← isDefEq domain bundle do
    throwError "the construction has a different complete selected source category"
  let mut index := 0
  let mut actual := arguments
  for argument in arguments, binder in binders, position in [:arguments.size] do
    unless binder.isExplicit do continue
    let type ← instantiateMVars (← inferType argument)
    if type.isConstOf ``LeanCategories.ObjCat || type.isConstOf ``CategoryTheory.Cat then
      continue
    let some parameter := parameters[index]?
      | throwError "the source construction requires its actual declaration parameter"
    let value ← parameter type
    unless ← isDefEq (← inferType value) type <&&> isDefEq argument value do
      throwError "the construction parameter differs from its complete source boundary"
    actual := actual.set! position value
    index := index + 1
  unless index == parameters.size do
    throwError "the source construction has arguments beyond its declared parameters"
  -- The template checks the full boundary; the retained application uses the actual
  -- supplied arguments, as Lean's dependent application does after hole elaboration.
  let function ← instantiateMVars (mkAppN declaration actual)
  if function.hasMVar || function.hasLevelMVar then
    throwError "the source construction has undetermined native declaration parameters"
  let (_, target) ← functorCategoryBundles function
  let value ← match selected.role with
    | .object => do
      let input ← if core then mkAppM ``CategoryTheory.Core.mk #[receiver.value]
        else pure receiver.value
      functorObject function input target
    | .morphism => do
      let input ← if wrapCore then do
          let some iso := iso | throwError "the core action lost its selected inverse data"
          sourceIsoCoreHom iso selected.bundle
        else pure receiver.value
      let action ← mkAppM ``CategoryTheory.Functor.map #[function]
      let value ← elabAppArgs action #[] #[Arg.expr input] none false false
      if let some iso ← sourceMorphismIso? input then
        retainSourceIso (← mkAppM ``CategoryTheory.Functor.mapIso #[function, iso]) value
      else pure value
  return ⟨sourceReference ``ConstructionEntry entry.id.raw entry.declaration value,
    some ⟨selected.role, entry.target, target, none⟩⟩

end CasCompiler
