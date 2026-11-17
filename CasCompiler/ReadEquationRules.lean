module

public import CasCompiler.ReadContext
public import CasCompiler.SourceSubset
public import CasCompiler.SourceRing

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def equationOperands (context : ReadContext) :
    TSyntax `cas_term → TSyntax `cas_term → TermElabM (NativeSourceJudgement × NativeSourceJudgement) :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (left right : TSyntax `cas_term) => do
    let leftPrincipal ← sourcePrincipal left
    let rightPrincipal ← sourcePrincipal right
    let (left, right) ← if !leftPrincipal && rightPrincipal then do
      -- An annotated operand `x in D` gives the other operand D's carrier with its selected
      -- source object, not only the native type of x (`2 + 3 = 0 in ℤ/5`).
      let domain ← match right with
        | `(cas_term| $_:cas_term in $domain:cas_term) => do
          if domain.raw.isIdent then pure none
          else pure (some (← sourceCarrier (← readExpression categoryOf domain none)).value)
        | _ => pure none
      let right ← readExpression categoryOf right none
      let leftType ← match domain with
        | some domain => pure domain
        | none => inferType right.value
      let left ← readExpression categoryOf left (some leftType) none right.category
      pure (left, right)
    else do
      let left ← readExpression categoryOf left none
      -- A global element `1 ⟶ X` compared with a numeral is compared at its point, where the
      -- numeral reads in X by the numeral rules (`dimension(ℚ) = 0`).
      let pointType ← whnfR (← inferType left.value)
      let mut left := left
      if sourceNumeric right.raw && pointType.isAppOfArity ``Quiver.Hom 4 then
        let source := pointType.getAppArgs[2]!
        if (← whnfR (← inferType source)).isSort then
          if (← synthInstance? (← mkAppM ``Unique #[source])).isSome then
            left := ⟨← sourcePointValue left.value none, none⟩
      let type ← inferType left.value
      -- A set compared with a subset of itself is the whole subset, the image of its identity
      -- (`X = ℕ` for `X` in `𝒫(ℕ)`).
      let wholeSubset := fun (type : Expr) => do
        unless right.raw.isOfKind ``CasCatalogue.Language.casAtom do return none
        let some power ← sourcePowerObject? (← instantiateMVars type) | return none
        let object ← readExpression categoryOf right none
        unless object.category.any (·.role == .object) do return none
        unless ← isDefEq object.value power.base do return none
        let identity ← withLocalDeclD `x power.base fun x => mkLambdaFVars #[x] x
        return some (⟨← sourceImage power power.base identity (some type), none⟩ :
          NativeSourceJudgement)
      let whole ← wholeSubset type
      let right ← match whole with
        | some whole => pure whole
        | none =>
          readExpression categoryOf right (if rightPrincipal then none else some type) none
            (if rightPrincipal then none else left.category)
      pure (left, right)
    let (left, right) ← sourceCommonCategory left right
    checkRegisteredDomains (← inferType left.value) (← inferType right.value)
    return (left, right)

end SourceReader

namespace ReadEquationRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let source := context.source
  let equationOperands := equationOperands context
  match source with
  | `(cas_term| $left:cas_term = $right:cas_term) => do
    -- Within a term, `=` is the equality predicate of the operands' common domain.
    let (left, right) ← equationOperands left right
    return ⟨← mkEq left.value right.value, none⟩
  | _ => throwReadRuleMismatch

end ReadEquationRules

end CasCompiler
