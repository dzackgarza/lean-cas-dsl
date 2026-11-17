module

public import CasCompiler.ReadContext
public import CasCompiler.ReadSubset
public import CasCompiler.ReadAdmission
public import CasCompiler.SourceNumeral

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadSubsetRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let admitted := admitted context
  let membership := membership context
  let boundIn := boundIn context
  match source with
  | `(cas_term| $element:cas_term ∈ $container:cas_term) => membership element container
  | `(cas_term| $element:cas_term ∉ $container:cas_term) => do
    return ⟨mkNot (← membership element container).value, none⟩
  | `(cas_term| {$elements:cas_term,*}) => do
    let expected ← match expected with
      | some expected => pure expected
      | none => do
        -- With no declared power object, the set in which the elements meet determines it
        -- (`span({u₁, u₂})` for vectors of ℚ³).
        let types ← elements.getElems.mapM fun element => do
          inferType (← readExpression categoryOf element none).value
        let some base ← sourceCommonDomain types
          | throwError "a source set literal requires its declared power object"
        let power ← sourcePowerObjectAt base
        let some object := (← CasCatalogue.semanticState).objects.find? (·.id == power.row.object)
          | throwError "the registered power object has no object family"
        let family ← mkConstWithFreshMVarLevels object.declaration
        elabAppArgs family #[] #[Arg.expr base] none false false
    -- A literal in an admitted subobject of a power object (`𝒫_fin(X)`) is admitted there.
    if let some entry ← sourceAdmissionDomain? (← instantiateMVars expected) then
      return ⟨← admitted entry source expected, none⟩
    let some power ← sourcePowerObject? (← instantiateMVars expected)
      | throwError "a source set literal requires a subset of a registered power object"
    -- Elements are read in the registered form of the base set (`Poly(ℤ)` for `Polynomial ℤ`).
    let base ← sourceRegisteredForm power.base
    let elements ← elements.getElems.mapM fun element => do
      return (← readExpression categoryOf element (some base)).value
    return ⟨← sourceSubsetLiteral power elements expected, none⟩
  | `(cas_term| {$bound:ident ∈ $domain:cas_term | $body:cas_term}) => do
    -- Over a subset `A ⊆ X`: `{t ∈ X | t ∈ A and P}`, through `A`'s power object.
    let subset ← readExpression categoryOf domain none
    if let some power ← sourcePowerObject? (← instantiateMVars (← inferType subset.value)) then
      return ← withLocalDeclD bound.getId power.base fun parameter => do
        let predicate ← readExpression categoryOf body (some (mkSort .zero))
        let member ← sourceMembership power parameter subset.value
        let predicate ← mkLambdaFVars #[parameter] (mkAnd member predicate.value)
        return (⟨← sourceComprehension power predicate expected, none⟩ : NativeSourceJudgement)
    boundIn bound domain fun base parameter => do
      let predicate ← readExpression categoryOf body (some (mkSort .zero))
      let predicate ← mkLambdaFVars #[parameter] predicate.value
      let power ← sourcePowerObjectAt base
      return (⟨← sourceComprehension power predicate expected, none⟩ : NativeSourceJudgement)
  | `(cas_term| {$body:cas_term | $bound:ident ∈ $domain:cas_term}) =>
    boundIn bound domain fun base parameter => do
      let value ← readExpression categoryOf body none
      let target ← instantiateMVars (← inferType value.value)
      if target.containsFVar parameter.fvarId! then
        throwError "the source image has a codomain that depends on its bound variable"
      let function ← mkLambdaFVars #[parameter] value.value
      let power ← sourcePowerObjectAt target
      return (⟨← sourceImage power base function expected, none⟩ : NativeSourceJudgement)
  | _ => throwReadRuleMismatch

end ReadSubsetRules

end CasCompiler
