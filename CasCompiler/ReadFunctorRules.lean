module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourceConstruction
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def readFunctorAction (context : ReadContext) :
    SourceCategoryRole → TSyntax `cas_term → Ident → Array (TSyntax `cas_term) → TermElabM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let application := application context
  fun (role : SourceCategoryRole) (receiver : TSyntax `cas_term)
      (id : Ident) (arguments : Array (TSyntax `cas_term)) => do
    let entry ← selectView (id.getId.toString (escape := false))
    let receiver ← readExpression categoryOf receiver none
    if let some category := receiver.category then
      unless category.role == role do
        throwError "the source functor action has a different object or morphism role"
    match entry with
    | .construction entry =>
      sourceConstruction entry receiver (arguments.map fun parameter type => do
          return (← readExpression categoryOf parameter (some type)).value)
    | .registered entry => do
      let selected ← viewExpressions entry
        (receiver.category.map fun category => (category.expression, category.bundle)) fun constant =>
        application ⟨constant, none⟩ arguments none
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
      let edge := match selected.reference with
        | .inl id => CasCatalogue.EdgeRef.functor id
        | .inr id => CasCatalogue.EdgeRef.classifierForget id
      let carrier : Option NativeSourceCarrierSelection ←
          match receiver.category.bind (·.carrier) with
        | none => pure none
        | some carrier =>
          if role != .object || carrier.refs[0]? != some edge then pure none
          else do
            let some action := carrier.actions[0]?
              | throwError "the selected carrier prefix has no complete native edge application"
            let action ← instantiateMVars action
            let actual ← instantiateMVars selected.functor
            let agrees ← if action == actual then pure true else do
              if action.hasMVar || action.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
                CasCatalogue.throwUnsupportedSource
                  "carrier-prefix comparison requires its complete native view parameters"
              withoutModifyingState <| isDefEq action actual
            pure <| if agrees then
              some { carrier with refs := carrier.refs.drop 1, actions := carrier.actions.drop 1 }
            else none
      -- Keep the selected reference beside its actual action for source inspection.
      return (⟨sourceReference kind id selected.declaration image,
        some ⟨role, selected.target, selected.targetBundle, carrier⟩⟩ : NativeSourceJudgement)

end SourceReader

namespace ReadFunctorRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let readFunctorAction := readFunctorAction context
  match source with
  | `(cas_term| $left:cas_term → $right:cas_term) => do
    let left ← sourceCarrier (← readExpression categoryOf left none)
    let right ← sourceCarrier (← readExpression categoryOf right none)
    let value ← mkAppM ``TypeCat.Hom #[left.value, right.value]
    sourceSetJudgement .object value
  | `(cas_term| view $receiver:cas_term along $functor:ident) =>
    readFunctorAction .object receiver functor #[]
  | `(cas_term| view $receiver:cas_term along $functor:ident($arguments:cas_term,*)) =>
    readFunctorAction .object receiver functor arguments.getElems
  | `(cas_term| map $receiver:cas_term along $functor:ident($arguments:cas_term,*)) =>
    readFunctorAction .morphism receiver functor arguments.getElems
  | `(cas_term| $left:cas_term ∘ $right:cas_term) => do
    let left ← readExpression categoryOf left none
    let right ← readExpression categoryOf right none
    let (left, right) ← sourceCommonCategory left right
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
  | _ => throwReadRuleMismatch

end ReadFunctorRules

end CasCompiler
