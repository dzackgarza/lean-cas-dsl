module

public import CasCompiler.Surface
public import CasCompiler.SourcePresentation

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue






opaque sourceConstruction (entry : ConstructionEntry) (receiver : NativeSourceJudgement)
    (parameters : Array (Expr → SourceReadM Expr)) : SourceReadM NativeSourceJudgement := do
  let some selected := receiver.category
    | liftM (m := TermElabM) <| throwError "a category-sensitive construction requires its selected source category"
  discard <| checkedDeclaration entry.declaration
  let previous ← liftM (m := MetaM) getMCtx
  let declaration ← mkConstWithFreshMVarLevels entry.declaration
  let (arguments, binders, result) ← forallMetaTelescopeReducing (← inferType declaration)
  let owned := (← liftM (m := MetaM) getMCtx).decls.foldl (fun result identity _ =>
    if previous.decls.contains identity then result else result.push identity) #[]
  let result ← whnfR result
  unless result.isAppOfArity ``CategoryTheory.Functor 4 do
    liftM (m := TermElabM) <| throwError "the source construction requires its complete native functor family"
  let core := (← whnfR result.getAppArgs[0]!).isAppOf ``CategoryTheory.Core
  let iso ← if selected.role == .morphism then sourceIsoOrigin? receiver.value else pure none
  let alreadyCore := (← whnfR (← mkAppM ``CategoryTheory.Bundled.α
    #[selected.bundle])).isAppOf ``CategoryTheory.Core
  let wrapCore := core && (selected.role == .object || (!alreadyCore && iso.isSome))
  let state ← semanticState
  let bundle ← if wrapCore then do
      let #[constructor] := state.constructors.filter
        (·.semantics == `CasCatalogue.Constructors.core)
        | liftM (m := TermElabM) <| throwError "the construction requires its registered core constructor"
      discard <| checkedDeclaration constructor.semantics
      applyConstructorInterface constructor.semantics #[selected.bundle] #[selected.bundle]
    else pure selected.bundle
  extendSourceApplicationScope owned
  unless ← expandSourceStructures arguments do
    liftM (m := TermElabM) <| throwError "the construction has inconsistent native category parameters"
  let function := mkAppN declaration arguments
  let (domain, _) ← functorCategoryBundles function
  unless ← isDefEq domain bundle do
    liftM (m := TermElabM) <| throwError "the construction has a different complete selected source category"
  let mut index := 0
  let mut actual := arguments
  for argument in arguments, binder in binders, position in [:arguments.size] do
    unless binder.isExplicit do continue
    let type ← liftM (m := MetaM) <| instantiateMVars (← inferType argument)
    if type.isConstOf ``LeanCategories.ObjCat || type.isConstOf ``CategoryTheory.Cat then
      continue
    let some parameter := parameters[index]?
      | liftM (m := TermElabM) <| throwError "the source construction requires its actual declaration parameter"
    let value ← parameter type
    extendSourceApplicationScope owned
    unless ← isDefEq (← inferType value) type <&&> isDefEq argument value do
      liftM (m := TermElabM) <| throwError "the construction parameter differs from its complete source boundary"
    actual := actual.set! position value
    index := index + 1
  unless index == parameters.size do
    liftM (m := TermElabM) <| throwError "the source construction has arguments beyond its declared parameters"


  let function ← liftM (m := MetaM) <| instantiateMVars (mkAppN declaration actual)
  if function.hasMVar || function.hasLevelMVar then
    liftM (m := TermElabM) <| throwError "the source construction has undetermined native declaration parameters"
  let function ← SourceReadM.select (← sourceReferenceAt (.named (.construction entry)) function function)
  let (_, target) ← functorCategoryBundles function
  let value : SourceSelection Expr ← match selected.role with
    | .object => do
      let input ← if core then mkAppM ``CategoryTheory.Core.mk #[receiver.value]
        else pure receiver.value
      pure { value := ← functorObject function input target }
    | .morphism => do
      let input ← if wrapCore then do
          let some iso := iso | liftM (m := TermElabM) <| throwError "the core action lost its selected inverse data"
          sourceIsoCoreHom iso selected.bundle
        else pure receiver.value
      let action ← mkAppM ``CategoryTheory.Functor.map #[function]
      let value ← elabAppArgs action #[] #[Arg.expr input] none false false
      if let some iso ← sourceMorphismIso? input then
        retainSourceIso (← mkAppM ``CategoryTheory.Functor.mapIso #[function, iso])
          { value } (some (← get).context)
      else pure { value }
  let category : NativeSourceCategory := ⟨selected.role, entry.target, target, none, none⟩
  let selected := { value with
    observation := some (.named (.construction entry))
    category := some category }
  return ⟨← SourceReadM.select selected, some category⟩

end CasCompiler
