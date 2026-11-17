module

public import CasCompiler.ReadContext
public import CasCompiler.ReadAdmission
public import CasCompiler.SourceNumeral

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadNumeralRules

open SourceReader

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let expectedCategory := context.expectedCategory
  let admitted := admitted context
  match source with
  | `(cas_term| $number:num in $domain:cas_term using ($evidence:cas_term,*)) => do
    let domain ← readExpression categoryOf domain none
    let some category := domain.category
      | throwError "source numeral evidence requires a selected domain object"
    unless category.role == .object do
      throwError "source numeral evidence requires a domain object"
    discard <| getLevel domain.value
    if let some expected := expected then
      checkRegisteredDomains domain.value expected
    let proofs ← evidence.getElems.mapM fun evidence => do
      let `(cas_term| proof($body:term)) := evidence
        | throwError "source numeral evidence requires the explicit proof wrapper"
      pure body
    pure ⟨← sourceNumeral categoryOf number.getNat domain.value proofs, none⟩
  | `(cas_term| ℵ₀) => do
    let some expected := expected
      | throwError "a named object literal requires its selected category"
    let some category := expectedCategory
      | throwError "a named object literal requires its selected category"
    let some value ← sourceObjectNamedLiteral `«ℵ₀» category expected
      | throwError "the selected category has no registered named literal form"
    return value
  | `(cas_term| $number:num) => do
    let some expected := expected
      | throwError "a source numeral requires its independently declared parameter type"
    if let some entry ← sourceAdmissionDomain? (← instantiateMVars expected) then
      return ⟨← admitted entry source expected, none⟩
    if let some category := expectedCategory then
      if let some value ← sourceObjectNumeral number.getNat category expected then return value
    let direct ← withoutModifyingState do
      try pure (some (← sourceNumeral categoryOf number.getNat expected)) catch _ => pure none
    if direct.isNone then
      -- A set with no numeral of its own reads it through a registered inclusion.
      if let some value ← sourceIncludedNumeral expected fun type => do
          return (← readExpression categoryOf source (some type)).value then
        return ⟨value, none⟩
    pure ⟨← sourceNumeral categoryOf number.getNat expected, none⟩
  | _ => throwReadRuleMismatch

end ReadNumeralRules

end CasCompiler
