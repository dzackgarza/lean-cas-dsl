module

public import CasCompiler.Surface
public import LeanCategories.Catalogue.Registry.Semantic

public section

namespace CasCompiler

open Lean Meta Elab Term CasCatalogue

private partial def withRigidArguments {α : Type} (arguments : Array Expr)
    (infos : Array BinderInfo) (start stop : Nat)
    (action : Array Expr → MetaM α) : MetaM α := do
  let rec visit (index : Nat) (rigid : Array Expr) : MetaM α := do
    if index >= stop then return ← action rigid
    let argument ← instantiateMVars arguments[index]!
    if !argument.isMVar then return ← visit (index + 1) rigid
    let declaration ← argument.mvarId!.getDecl
    withLocalDecl declaration.userName infos[index]! (← instantiateMVars declaration.type)
        fun parameter => do
      argument.mvarId!.assign parameter
      visit (index + 1) (rigid.push parameter)
  visit start #[]

/-- A complete declaration family and the position of its original source object. -/
structure NativeOwnedFamily where
  value : Expr
  objectIndex : Nat

/-- Route a whole declaration at a rigid source object, retaining independent parameters.
Reuse: nativeOperationFamily's source telescope and withRigidArguments; the actual operation
or numeral signature determines its object position. -/
def nativeOwnedFamily (state : SemanticState) (source : CategoryExpr)
    (categoryFamily : Expr) (route : Route) (declaration : Name)
    (objectPosition : Array BinderInfo → Option Nat) : MetaM NativeOwnedFamily := do
  unless source.syntacticEq route.source do
    throwError "the declaration family has a different complete symbolic source"
  discard <| checkedDeclaration declaration
  forallTelescopeReducing (← inferType categoryFamily) fun parameters _ => do
    let category := mkAppN categoryFamily parameters
    let selected ← nativeRouteFunctor state route category
    let functor := selected.functor
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category]
    withLocalDeclD `sourceObject carrier fun object => do
      let prefunctor ← mkAppM ``CategoryTheory.Functor.toPrefunctor #[functor]
      let image ← mkAppM ``Prefunctor.obj #[prefunctor, object]
      let constant ← mkConstWithFreshMVarLevels declaration
      let (arguments, infos, result) ← forallMetaTelescopeReducing (← inferType constant)
      let some position := objectPosition infos
        | throwError "the whole declaration family has no object parameter"
      unless (← whnfR result).isAppOf ``Quiver.Hom do
        throwError "the declaration family does not retain its whole morphism result"
      unless ← isDefEq (← inferType arguments[position]!) (← inferType image) <&&>
          isDefEq arguments[position]! image do
        throwError "the declaration family has a different complete routed object"
      withRigidArguments arguments infos 0 position fun prefixParameters => do
        withRigidArguments arguments infos (position + 1) arguments.size
            fun suffixParameters => do
          let body ← instantiateMVars (mkAppN constant arguments)
          let value ← mkLambdaFVars
            (parameters ++ prefixParameters ++ #[object] ++ suffixParameters) body
          return ⟨value, parameters.size + prefixParameters.size⟩

/-- Form the whole native operation before selecting its source object or operands.
Reuse: validateOperation's object/numeral boundary and nativeOwnedFamily. -/
def nativeOperationFamily (state : SemanticState) (source : CategoryExpr)
    (categoryFamily : Expr) (route : Route) (binding : OperationEntry) : MetaM Expr := do
  let family ← nativeOwnedFamily state source categoryFamily route binding.declaration fun infos =>
    if infos.size > binding.numerals then some (infos.size - 1 - binding.numerals) else none
  return family.value

end CasCompiler
