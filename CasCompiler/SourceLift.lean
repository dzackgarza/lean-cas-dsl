module

public import LeanCategories.Catalogue.Lift
public import CasCompiler.LiftFamily
public import CasCompiler.SelectedField
public import CasCompiler.Elaborate
import CasCompiler.SourceCarrier
public import CasCompiler.SourceProof

public section

namespace CasCompiler

open CategoryTheory

universe u₁ u₂ v₁ v₂




structure SourceLiftApplication {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (U : C ⥤ D) where
  selected : CasCatalogue.MonoLift U
  object : C
  domain : D
  inclusion : domain ⟶ U.obj object
  monicity : Mono inclusion

open Lean Meta Elab Term CasCatalogue



private partial def liftEdgeBoundary (state : SemanticState) (ref : EdgeRef) :
    MetaM (CategoryExpr × CategoryExpr) := do
  match ref with
  | .constructMap id inner =>
    let (source, target) ← liftEdgeBoundary state inner
    return (.construct id #[.category source], .construct id #[.category target])
  | .functor id =>
    let some entry := state.functor? id
      | throwError "the selected lift functor is not registered"
    return (entry.source, entry.target)
  | .classifierForget id =>
    let some entry := state.classifier? id
      | throwError "the selected lift classifier is not registered"
    return (.classifierTotal id, entry.host)

private def liftBoundary (state : SemanticState) (row : LiftEntry) :
    MetaM (CategoryExpr × CategoryExpr) := do
  let .subobjects := row.kind
    | throwUnsupportedSource "selected limit lifting requires its declared diagram"
  let (source, target) ← liftEdgeBoundary state row.edge


  let .construct _ #[.category source] := source
    | throwError "the selected lift has no declared arrow source category"
  let .construct _ #[.category target] := target
    | throwError "the selected lift has no declared arrow target category"
  return (source, target)



private def applyLiftInputs (function : Expr) (arguments : Array Expr)
    (allArguments : Bool := true) : SourceReadM Expr := do
  let result ← elabSourceApplicationApplicableScoped function
    (Array.replicate arguments.size Syntax.missing) none (fun index expected => do
      let argument := arguments[index]!
      if ← isDefEq (← inferType argument) expected then return .ok argument
      let selected := (← SourceReadM.selection? argument).getD { value := argument }
      return .ok (← SourceReadM.select { selected with value := argument } (some expected)))
    allArguments
  match result with
  | .ok (value, _) => return value
  | .error message => liftM (m := TermElabM) <| throwError message



def sourceSelectedLift (row : LiftEntry) (receiver input : NativeSourceJudgement)
    (selected monicity : Expr) : SourceReadM NativeSourceJudgement := do
  let state ← semanticState
  let original ← match ← SourceReadM.selection? selected with
    | none => pure selected
    | some retained =>
      let same := SourceSelection.exactlyMatches Expr.equal
        { value := selected, reference := retained.reference }
        (sourceReference (.lift row) selected)
      unless same do
        liftM (m := TermElabM) <|
          throwError "the selected lift changed its independent source declaration"
      let some original := retained.originalApplication
        | liftM (m := TermElabM) <| throwError "the selected lift lost its original evidence"
      pure original
  unless original.consumeMData.getAppFn.constName? == some row.evidence do
    liftM (m := TermElabM) <|
      throwError "the selected lift changed its independent source declaration"
  let selected ← SourceReadM.select
    { (sourceReference (.lift row) selected) with originalApplication := some original }
  let (source, target) ← liftBoundary state row
  let some category := receiver.category
    | liftM (m := TermElabM) <| throwError "a selected lift requires its complete source category"
  unless category.role == .object && category.expression.syntacticEq source do
    liftM (m := TermElabM) <| throwError "the selected lift has a different complete source category"
  let type ← whnfR (← inferType selected)
  unless type.isAppOfArity ``MonoLift 5 do
    liftM (m := TermElabM) <| throwError "the selected lift declaration has a different native interface"
  let functor := type.getAppArgs[4]!
  let (domain, codomain) ← functorCategoryBundles functor
  unless ← isDefEq domain category.bundle do
    liftM (m := TermElabM) <| throwError "the selected lift has different native category parameters"
  let proofType ← whnfR (← inferType monicity)
  unless proofType.isAppOfArity ``CategoryTheory.Mono 5 do
    liftM (m := TermElabM) <| throwError "the selected lift requires its explicit monicity evidence"
  let inclusion := proofType.getAppArgs.back!
  let arrow : NativeSourceJudgement :=
    ⟨inclusion, some ⟨.morphism, target, codomain, none, none⟩⟩
  let actual ← if input.category.any (fun selected =>
      selected.role == .morphism && selected.expression.syntacticEq target) then
    pure arrow
  else sourceCarrier arrow
  let same ← (← get).context.withOriginalSources #[actual.value, input.value] fun values => do
    isDefEq (← inferType values[0]!) (← inferType values[1]!) <&&>
      isDefEq values[0]! values[1]!
  unless same do
    liftM (m := TermElabM) <|
      throwError "the supplied monicity evidence has a different original inclusion"
  let inputSelection := (← SourceReadM.selection? input.value).getD { value := input.value }
  let inputValue ← SourceReadM.select { inputSelection with value := input.value }
    (some (← inferType actual.value))
  let agreement ← SourceReadM.prove (← mkEq actual.value inputValue) fun proposition _ => do
    let proposition ← whnfR proposition
    unless proposition.isAppOfArity ``Eq 3 do
      throwError "the selected lift lost its original inclusion equation"
    mkExpectedTypeHint (← mkEqRefl proposition.getAppArgs[1]!) proposition
  let domainObject := proofType.getAppArgs[2]!
  let value ← applyLiftInputs (← mkConstWithFreshMVarLevels ``SourceLiftApplication.mk)
    #[selected, receiver.value, domainObject, inclusion, monicity] false
  let value ← liftM (m := MetaM) <| withLetDecl (← mkFreshUserName `liftInputAgreement)
      (← inferType agreement) agreement fun binding =>
    mkLetFVars #[binding] value (usedLetOnly := false) (generalizeNondepLet := false)
  let selection ← mkFreshUserName `selectedLift
  let computation ← selectRecordActions selection
    (← LiftFamily.atEvidence row .computation original)
    (fun selected expected => SourceReadM.select selected expected)
  let retained := { (sourceReference (.lift row) value) with
    originalApplication := some original
    recordSelection := some selection
    recordOwner := some computation }
  return ⟨← SourceReadM.select retained, none⟩

private def liftSelection (source : SourceSelection Expr) : MetaM Name := do
  let some selection := source.recordSelection
    | throwError "the selected lift lost its source identity"
  unless !selection.isAnonymous do throwError "the selected lift lost its source identity"
  return selection

private def liftReference (value : Expr) :
    SourceReadM (Option (LiftEntry × SourceSelection Expr)) := do
  let some selected ← SourceReadM.selection? value | return none
  let some (.lift row) := selected.reference | return none
  return some (row, selected)



private def liftInputs (value : Expr) : MetaM (Expr × Expr × Expr × Expr × Expr) := do
  return (← mkProjection value `selected, ← mkProjection value `object,
    ← mkProjection value `domain, ← mkProjection value `inclusion,
    ← mkProjection value `monicity)


def sourceLiftMember? (receiver : NativeSourceJudgement) (name : String) :
    SourceReadM (Option NativeSourceJudgement) := do
  let type ← whnfR (← inferType receiver.value)
  unless type.isAppOf ``SourceLiftApplication do return none
  let some (row, retained) ← liftReference receiver.value
    | liftM (m := TermElabM) <| throwError "the native lift application has no selected source reference"
  let some computation := retained.recordOwner
    | liftM (m := TermElabM) <| throwError "the selected lift lost its original computation owner"
  let (source, target) ← liftBoundary (← semanticState) row
  let (sourceBundle, targetBundle) ← functorCategoryBundles type.getAppArgs.back!
  let (_, object, domainObject, inclusion, monicity) ← liftInputs receiver.value
  let selection ← liftSelection retained
  let declaration ← match name with
    | "obj" => pure ``MonoLiftComputation.obj
    | "hom" => pure ``MonoLiftComputation.hom
    | "forward" => pure ``MonoLiftComputation.forward
    | "backward" => pure ``MonoLiftComputation.backward
    | _ => liftM (m := TermElabM) <| throwError "the selected lift has no declared member {name}"
  let function ← mkAppM declaration #[computation]
  let value ← applyLiftInputs function #[object, domainObject, inclusion, monicity]
  let category := if name == "forward" || name == "backward" then target else source
  let bundle := if name == "forward" || name == "backward" then targetBundle else sourceBundle
  let role := if name == "obj" then SourceCategoryRole.object else .morphism
  let category : NativeSourceCategory := ⟨role, category, bundle, none, none⟩
  let selected ← selectedFieldAt selection declaration computation value
  return some ⟨← SourceReadM.select { selected with category := some category }, some category⟩



def sourceLiftFactor (receiver : NativeSourceJudgement) (base source proof : Expr) :
    SourceReadM NativeSourceJudgement := do
  let type ← whnfR (← inferType receiver.value)
  unless type.isAppOf ``SourceLiftApplication do
    liftM (m := TermElabM) <| throwError "a source factor requires a selected lift application"
  let some (row, retained) ← liftReference receiver.value
    | liftM (m := TermElabM) <| throwError "the native lift application has no selected source reference"
  let some computation := retained.recordOwner
    | liftM (m := TermElabM) <| throwError "the selected lift lost its original computation owner"
  let some original := retained.originalApplication
    | liftM (m := TermElabM) <| throwError "the selected lift lost its original evidence"
  let (category, _) ← liftBoundary (← semanticState) row
  let (bundle, _) ← functorCategoryBundles type.getAppArgs.back!
  let (_, object, domainObject, inclusion, monicity) ← liftInputs receiver.value
  let factor ← LiftFamily.atEvidence row .factor original
  let some application := factor.application
    | liftM (m := TermElabM) <| throwError "the selected lift lost its accepted factor family"
  let factor := { factor with application := some { application with owner := some computation } }
  let selection ← liftSelection retained
  let factor ← selectRecordActions selection factor
    (fun selected expected => SourceReadM.select selected expected)
  let function ← mkAppM ``MonoLiftFactorComputation.factor #[factor]
  let sourceType ← inferType source
  let sourceType ← if sourceType.isAppOfArity ``Quiver.Hom 4 then pure sourceType else whnfR sourceType
  unless sourceType.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the factor's source arrow is not a morphism"
  let apex := sourceType.getAppArgs[2]!
  let value ← applyLiftInputs function
    #[object, domainObject, inclusion, monicity, apex, base, source, proof]
  let target ← applyLiftInputs (← mkAppM ``MonoLiftComputation.obj #[computation])
    #[object, domainObject, inclusion, monicity]
  let resultType ← inferType value
  let resultType ← if resultType.isAppOfArity ``Quiver.Hom 4 then pure resultType else whnfR resultType
  unless resultType.isAppOfArity ``Quiver.Hom 4 do
    liftM (m := TermElabM) <| throwError "the selected factor has no declared morphism endpoints"
  let resultType := mkAppN resultType.getAppFn (resultType.getAppArgs.set! 3 target)
  let selected ← selectedFieldAt selection ``MonoLiftFactorComputation.factor factor value
  let category : NativeSourceCategory := ⟨.morphism, category, bundle, none, none⟩
  return ⟨← SourceReadM.select { selected with category := some category } (some resultType),
    some category⟩

end CasCompiler
