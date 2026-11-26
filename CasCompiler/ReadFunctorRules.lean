module

public import CasCompiler.ReadContext
public import CasCompiler.ReadApplication
public import CasCompiler.SourceConstruction
public import CasCompiler.CategoricalPointFamily
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def readFunctorAction (context : ReadContext) :
    SourceCategoryRole → TSyntax `cas_term → Ident → Array (TSyntax `cas_term) → SourceReadM NativeSourceJudgement :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let application := application context
  fun (role : SourceCategoryRole) (receiver : TSyntax `cas_term)
      (id : Ident) (arguments : Array (TSyntax `cas_term)) => do
    let entry ← selectView (id.getId.toString (escape := false))
    let receiver ← readExpression categoryOf receiver none
    if let some category := receiver.category then
      unless category.role == role do
        liftM (m := TermElabM) <| throwError (MessageData.tagged
          `CasCompiler.SourceReader.actionRole
          m!"the source functor action has a different object or morphism role")
    match entry with
    | .construction entry =>
      sourceConstruction entry receiver (arguments.map fun parameter type => do
          return (← readExpression categoryOf parameter (some type)).value)
    | .registered entry => do
      let selected ← viewExpressions entry
        (receiver.category.map fun category => (category.expression, category.bundle)) fun constant =>
        application ⟨constant, none⟩ arguments none
      let receiverValue ← match role with
        | .object => do
          let (domain, _) ← CasCatalogue.functorCategoryBundles selected.functor
          let inputType ← mkAppM ``CategoryTheory.Bundled.α #[domain]
          if ← isDefEq (← inferType receiver.value) inputType then pure receiver.value
          else do


            let original := (← SourceReadM.selection? receiver.value).getD {
              value := receiver.value, category := receiver.category }
            SourceReadM.select { original with value := receiver.value } (some inputType)
        | .morphism =>
          match receiver.category with
          | none => pure receiver.value
          | some category => do
            let (domain, _) ← CasCatalogue.functorCategoryBundles selected.functor
            if ← isDefEq category.bundle domain then pure receiver.value
            else do
              let original := (← SourceReadM.selection? receiver.value).getD {
                value := receiver.value, category := receiver.category }
              selectMorphism { original with value := receiver.value }
                (fun selection expected => SourceReadM.select selection expected)
                (category := some category.bundle) (declaredCategory := some domain)
      let image ← match role with
        | .object => functorObject selected.functor receiverValue selected.targetBundle
        | .morphism => do
          let function ← mkAppM ``CategoryTheory.Functor.map #[selected.functor]


          let image ← elabAppArgs function #[] #[Arg.expr receiverValue] none false false



          let stated ← liftM (m := MetaM) <| instantiateMVars (← inferType receiverValue)
          let type ← if stated.isAppOfArity ``Quiver.Hom 4 then pure stated else whnfR stated
          unless image.getAppFn.isConstOf ``CategoryTheory.Functor.map do
            liftM (m := TermElabM) <| throwError "the selected functor map lost its native arrow interface"
          let arguments := image.getAppArgs
          unless arguments.size >= 3 do
            liftM (m := TermElabM) <| throwError "the selected functor map lost its endpoint slots"




          let arguments := if type.isAppOfArity ``Quiver.Hom 4 then
              (arguments.set! (arguments.size - 3) type.getAppArgs[2]!).set!
                (arguments.size - 2) type.getAppArgs[3]!
            else if type.isAppOfArity ``TypeCat.Hom 2 then
              (arguments.set! (arguments.size - 3) type.getAppArgs[0]!).set!
                (arguments.size - 2) type.getAppArgs[1]!
            else arguments
          let retained := mkAppN image.getAppFn (arguments.set! (arguments.size - 1) receiverValue)
          let retained ← liftM (m := MetaM) <| instantiateMVars retained
          check retained
          unless ← isDefEq retained image do
            liftM (m := TermElabM) <| throwError "the selected functor map changed its native action"
          pure retained
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
              | liftM (m := TermElabM) <| throwError "the selected carrier prefix has no complete native edge application"
            let action ← liftM (m := MetaM) <| instantiateMVars action
            let actual ← liftM (m := MetaM) <| instantiateMVars selected.functor
            let agrees ← if action == actual then pure true else do
              if action.hasMVar || action.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
                liftM (m := TermElabM) <| CasCatalogue.throwUnsupportedSource
                  "carrier-prefix comparison requires its complete native view parameters"


              let scope ← get
              withoutModifyingState <|
                scope.context.withOriginalSources #[action, actual] fun original =>
                  isDefEq original[0]! original[1]!
            pure <| if agrees then
              some { carrier with refs := carrier.refs.drop 1, actions := carrier.actions.drop 1 }
            else none
      let .const declaration levels := selected.application.getAppFn
        | liftM (m := TermElabM) <| throwError "the selected action lost its original declaration"
      unless declaration == selected.declaration do
        liftM (m := TermElabM) <| throwError "the selected action changed its original declaration"
      let parameters := selected.application.getAppArgs
      let result ← match role with
        | .object => do
          let family ← SourceActionFamily.forEdge edge
          family.selected levels parameters receiverValue
        | .morphism => do
          let family ← (← CategoricalPointFamily.forOwner (.action edge)).asReference
          let inferred ← liftM (m := MetaM) <| instantiateMVars (← inferType receiverValue)
          let endpoints ← if inferred.isAppOfArity ``Quiver.Hom 4 then
              pure (inferred.getAppArgs[2]!, inferred.getAppArgs[3]!)
            else do
              let some endpoints ← mapEnds receiverValue
                | liftM (m := TermElabM) <| throwError "the source map action lost its original endpoints"
              pure endpoints
          let parameters := parameters ++ #[endpoints.1, endpoints.2, receiverValue]
          let (arrow, bundle) ← family.arrowAt levels parameters
          let (domain, _) ← categoricalPointEndpoints arrow
          let identity ← categoricalPointIdentity bundle domain
          family.selected levels parameters domain { value := identity }
      let scope ← get
      let agrees ← scope.context.withOriginalSources #[result.value, image] fun original =>
        isDefEq original[0]! original[1]!
      unless agrees do
        liftM (m := TermElabM) <| throwError "the selected action changed its whole native result"
      let category : NativeSourceCategory :=
        ⟨role, selected.target, selected.targetBundle, carrier, none⟩
      let value ← SourceReadM.select { result with value := image, category := some category }
      return ⟨value, some category⟩

end SourceReader

namespace ReadFunctorRules

open SourceReader

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
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
      | liftM (m := TermElabM) <| throwError "source composition requires its selected category"
    for selected in #[left.category, right.category] do
      if let some selected := selected then
        unless selected.role == .morphism do
          liftM (m := TermElabM) <| throwError "source composition requires morphisms"
        unless selected.expression.syntacticEq category.expression &&
            (← isDefEq selected.bundle category.bundle) do
          liftM (m := TermElabM) <| throwError "source composition has different complete selected categories"
    let carrier ← mkAppM ``CategoryTheory.Bundled.α #[category.bundle]
    let categoryInstance ← mkAppM ``CategoryTheory.Bundled.str #[category.bundle]
    let categoryStructure ← mkAppOptM ``CategoryTheory.Category.toCategoryStruct
      #[some carrier, some categoryInstance]
    let composition ← mkAppOptM ``CategoryTheory.CategoryStruct.comp
      #[some carrier, some categoryStructure]

    let value ← elabAppArgs composition #[] #[Arg.expr right.value, Arg.expr left.value]
      expected false false
    pure ⟨value, some category⟩
  | _ => throwReadRuleMismatch

end ReadFunctorRules

end CasCompiler
