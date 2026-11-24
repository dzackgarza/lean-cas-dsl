module

public import CasCompiler.ReadContext
public import CasCompiler.ReadAdmission
public import CasCompiler.ReadDispatch
public import CasCompiler.SourceNumeral
public import CasCompiler.SourceGenerator

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace ReadNumeralRules

open SourceReader

/-- Numeric syntax has explicit absence only when its original point producer and every
registered inclusion have no reading. Admissions and object literals keep their existing
priority, and failed proof, domain or family checks never become absence. -/
private partial def numeralReading? (context : ReadContext) (number : Nat) :
    TermElabM (Option NativeSourceJudgement) := do
  let some expected := context.expected
    | throwError "a source numeral requires its independently declared parameter type"
  if let some entry ← sourceAdmissionDomain? (← instantiateMVars expected) then
    return some ⟨← admitted context entry context.source expected, none⟩
  if let some category := context.expectedCategory then
    if let some value ← sourceObjectNumeral number category expected then return some value
  let direct ← withoutModifyingState do
    return (← sourceNumeral? context.categoryOf number expected).isSome
  if direct then
    return some ⟨← sourceNumeral context.categoryOf number expected, none⟩
  -- Inclusion sources use exactly the ordinary unqualified numeric rule order, followed
  -- by the assembled reader's same complete input checks on that successful judgement.
  let included ← sourceIncludedNumeral expected fun type => do
    let inner := { context with
      expected := some type
      qualification := none
      expectedCategory := none }
    let some judgement ← numeralReading? inner number | return none
    match ← checkReadJudgementApplicable inner judgement with
    | .ok judgement => return some judgement.value
    | .error message => throwError message
  return included.map fun value => ⟨value, none⟩

def rule (context : ReadContext) : TermElabM NativeSourceJudgement := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  let source := context.source
  let expected := context.expected
  let expectedCategory := context.expectedCategory
  match source with
  | `(cas_term| generator($object:cas_term)) => do
    let object ← readExpression categoryOf object none
    return ⟨← sourceObjectGenerator object, none⟩
  | `(cas_term| $number:num in $domain:cas_term using ($evidence:cas_term,*)) => do
    let domain ← readExpression categoryOf domain none
    let some category := domain.category
      | throwReadRuleMismatch
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
    if let some value ← numeralReading? context number.getNat then return value
    let some expected := expected
      | throwError "a source numeral requires its independently declared parameter type"
    pure ⟨← sourceNumeral categoryOf number.getNat expected, none⟩
  | _ => throwReadRuleMismatch

end ReadNumeralRules

end CasCompiler
