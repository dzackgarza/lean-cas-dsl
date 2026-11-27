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

private partial def numeralReading? (context : ReadContext) (number : Nat) :
    SourceReadM (Option NativeSourceJudgement) := do
  let phase : String → SourceReadM Unit := fun event => do
    try
      let heartbeats ← liftM (m := BaseIO) IO.getNumHeartbeats
      liftM (m := CoreM) <| CasTools.Diagnostics.emit event (Json.mkObj [
        ("heartbeats", toJson heartbeats), ("number", toJson number),
        ("startByte", toJson (context.source.raw.getPos?.map (·.byteIdx))),
        ("stopByte", toJson (context.source.raw.getTailPos?.map (·.byteIdx)))])
    catch _ => pure ()
  phase "source.numeral.started"
  let some expected := context.expected
    | liftM (m := TermElabM) <| throwError "a source numeral requires its independently declared parameter type"
  if let some entry ← sourceAdmissionDomain? (← liftM (m := MetaM) <| instantiateMVars expected) then
    let value ← admitted context entry context.source expected
    phase "source.numeral.finished"
    return some ⟨value, none⟩
  if let some category := context.expectedCategory then
    if let some value ← sourceObjectNumeral number category expected then
      phase "source.numeral.finished"
      return some value
  let absent : MessageData := m!"there is no direct source numeral reading"
  let direct ← SourceReadM.chooseApplicable #[do
      let some value ← sourceNumeral? context.categoryOf number expected
        | return .error absent
      return .ok value]
    absent m!"the direct source numeral producer has several readings" (restoreInfo := true)
  if let .ok value := direct then
    phase "source.numeral.direct.present"
    phase "source.numeral.finished"
    return some ⟨value, none⟩
  phase "source.numeral.direct.absent"
  let included ← sourceIncludedNumeral expected fun type => do
    let inner := { context with
      expected := some type
      qualification := none
      expectedCategory := none }
    let some judgement ← numeralReading? inner number | return none
    match ← checkReadJudgementApplicable inner judgement with
    | .ok judgement => return some judgement.value
    | .error message => liftM (m := TermElabM) <| throwError message
  phase "source.numeral.finished"
  return included.map fun value => ⟨value, none⟩

def rule (context : ReadContext) : SourceReadM NativeSourceJudgement := do
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
      liftM (m := TermElabM) <| throwError "source numeral evidence requires a domain object"
    discard <| getLevel domain.value
    if let some expected := expected then
      checkRegisteredSourceDomains domain.value expected
    let proofs ← evidence.getElems.mapM fun evidence => do
      let `(cas_term| proof($body:term)) := evidence
        | liftM (m := TermElabM) <| throwError "source numeral evidence requires the explicit proof wrapper"
      pure body
    pure ⟨← sourceNumeral categoryOf number.getNat domain.value proofs, none⟩
  | `(cas_term| ℵ₀) => do
    let some expected := expected
      | liftM (m := TermElabM) <| throwError "a named object literal requires its selected category"
    let some category := expectedCategory
      | liftM (m := TermElabM) <| throwError "a named object literal requires its selected category"
    let some value ← sourceObjectNamedLiteral `«ℵ₀» category expected
      | liftM (m := TermElabM) <| throwError "the selected category has no registered named literal form"
    return value
  | `(cas_term| $number:num) => do
    if let some value ← numeralReading? context number.getNat then return value
    let some expected := expected
      | liftM (m := TermElabM) <| throwError "a source numeral requires its independently declared parameter type"
    pure ⟨← sourceNumeral categoryOf number.getNat expected, none⟩
  | _ => throwReadRuleMismatch

end ReadNumeralRules

end CasCompiler
