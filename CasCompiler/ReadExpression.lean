module

public import CasCompiler.Surface
public import Lean.Elab.App

public section

namespace CasCompiler

open Lean Meta Elab Term

private def sourceAtomName? (source : Syntax) : Option String :=
  if source.isOfKind ``CasCatalogue.Language.casAtom ||
      source.isOfKind ``CasCatalogue.Language.casDomainAtom then
    -- Lean's alternative-token parser retains a token-kind node around its actual atom.
    some source[0][0].getAtomVal
  else none

-- Native application determines argument types before the original source is read once.
-- A final application uses the actual expressions, preserving lexical binding occurrences
-- even when expected-type unification has already assigned a provisional argument.
-- Reuse: Lean.Elab.App.elabAppArgs and Lean.Meta.mkFreshExprMVar at Lean 4.33.0.
partial def readExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none) : TermElabM NativeSourceJudgement :=
  withRef source do
  let application := fun (function : Expr) (arguments : Array (TSyntax `cas_term))
      (expected : Option Expr) => do
    let holes ← arguments.mapM fun _ => mkFreshExprMVar none
    discard <| elabAppArgs function #[] (holes.map Arg.expr) expected false false
    let mut actual := #[]
    for argument in arguments, hole in holes do
      let type ← instantiateMVars (← inferType hole)
      let value ← readExpression categoryOf argument (some type)
      unless ← isDefEq hole value.value do
        throwErrorAt argument "the source argument does not match its dependent native type"
      actual := actual.push (Arg.expr value.value)
    elabAppArgs function #[] actual expected false false
  let object := fun (name : String) (category : Option String)
      (arguments : Array (TSyntax `cas_term)) => do
    let (entry, categoryEntry) ← selectObject name category expected
    let (bundle, value) ← objectExpressions entry categoryEntry fun function expected =>
      application function arguments expected
    return (⟨value, some ⟨.object, categoryEntry.expression, bundle⟩⟩ : NativeSourceJudgement)
  let registered := fun (name : Ident) (arguments : Array (TSyntax `cas_term)) => do
    if let some declaration := (← getLCtx).findFromUserName? name.getId then
      let selected ← categoryOf declaration.fvarId
      let value ← application (mkFVar declaration.fvarId) arguments expected
      return ⟨value, if arguments.isEmpty then selected else none⟩
    object (name.getId.toString (escape := false)) qualification arguments
  let readFunctorAction := fun (role : SourceCategoryRole) (receiver : TSyntax `cas_term)
      (id : Ident) (arguments : Array (TSyntax `cas_term)) => do
    let entry ← selectView (id.getId.toString (escape := false))
    let receiver ← readExpression categoryOf receiver none
    if let some category := receiver.category then
      unless category.role == role do
        throwError "the source functor action has a different object or morphism role"
    let selected ← viewExpressions entry
        (receiver.category.map fun category => (category.expression, category.bundle)) fun constant =>
      application constant arguments none
    let image ← match role with
      | .object => functorObject selected.functor receiver.value selected.targetBundle
      | .morphism => do
        let function ← mkAppM ``CategoryTheory.Functor.map #[selected.functor]
        -- AppBuilder protects pre-existing metavariables. Native source application must
        -- solve the selected declaration's levels at the actual arrow in this context.
        elabAppArgs function #[] #[Arg.expr receiver.value] none false false
    let (kind, id) := match selected.reference with
      | .inl id => (``CasCatalogue.EdgeRef.functor, id.raw)
      | .inr id => (``CasCatalogue.EdgeRef.classifierForget, id.raw)
    -- Keep the exact selected reference beside its actual native action for source inspection.
    -- Lean MData preserves these names through closure; native checking uses the retained body.
    let data := KVMap.empty |>.setName `CasCompiler.view.kind kind
      |>.setString `CasCompiler.view.id id
      |>.setName `CasCompiler.view.declaration selected.declaration
    return (⟨.mdata data image, some ⟨role, selected.target, selected.targetBundle⟩⟩ :
      NativeSourceJudgement)
  let judgement ← if let some name := sourceAtomName? source then object name qualification #[]
    else match source with
    | `(cas_term| view $receiver:cas_term along $functor:ident) =>
      readFunctorAction .object receiver functor #[]
    | `(cas_term| view $receiver:cas_term along $functor:ident($arguments:cas_term,*)) =>
      readFunctorAction .object receiver functor arguments.getElems
    | `(cas_term| map $receiver:cas_term along $functor:ident($arguments:cas_term,*)) =>
      readFunctorAction .morphism receiver functor arguments.getElems
    | `(cas_term| $left:cas_term ∘ $right:cas_term) => do
      let left ← readExpression categoryOf left none
      let right ← readExpression categoryOf right none
      let some category := left.category <|> right.category
        | throwError "source composition requires its selected category"
      for selected in #[left.category, right.category] do
        if let some selected := selected then
          unless selected.role == .morphism do
            throwError "source composition requires morphisms"
          unless selected.expression.syntacticEq category.expression &&
              (← isDefEq selected.bundle category.bundle) do
            throwError "source composition has different complete selected categories"
      let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
      let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
      let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
        #[some carrier, some categoryInstance]
      let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
        #[some carrier, some categoryStructure]
      -- CategoryStruct.comp takes the earlier arrow first; source writes the later one first.
      let value ← elabAppArgs composition #[] #[Arg.expr right.value, Arg.expr left.value]
        expected false false
      pure ⟨value, some category⟩
    | `(cas_term| ($inner:cas_term)) =>
      readExpression categoryOf inner expected qualification
    | `(cas_term| $number:num) =>
      unless expected.isSome do
        throwError "a source numeral requires its independently declared parameter type"
      pure ⟨← elabTermEnsuringType (← `(term| $number:num)) expected, none⟩
    | `(cas_term| $name:ident) =>
      if let some declaration := (← getLCtx).findFromUserName? name.getId then
        pure ⟨mkFVar declaration.fvarId, ← categoryOf declaration.fvarId⟩
      else registered name #[]
    | `(cas_term| $name:ident($arguments:cas_term,*)) =>
      registered name arguments.getElems
    | `(cas_term| $body:cas_term in $category:ident) =>
      readExpression categoryOf body expected (some (category.getId.toString (escape := false)))
    | `(cas_term| ($function:cas_term)($arguments:cas_term,*)) => do
      let function ← readExpression categoryOf function none
      pure ⟨← application function.value arguments.getElems expected, none⟩
    | `(cas_term| $function:cas_term($arguments:cas_term,*)) => do
      let function ← readExpression categoryOf function none
      pure ⟨← application function.value arguments.getElems expected, none⟩
    | _ => throwError "source translation is not implemented for this expression form"
  if let some name := qualification then
    let required ← selectCategory (← CasCatalogue.semanticState) name
    let some selected := judgement.category
      | throwError "the retained source value has no selected category"
    unless selected.expression.syntacticEq required.expression do
      throwError "the retained source value has a different selected category"
  if let some expected := expected then
    unless ← isDefEq (← inferType judgement.value) expected do
      throwError "the source expression does not have its independently declared parameter type"
  return judgement

end CasCompiler

