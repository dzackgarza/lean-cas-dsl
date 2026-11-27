module

public import CasCompiler.ReadContext
public import CasCompiler.SourceAdmission
public import CasCompiler.SourceConstrainedPoint

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

private def admissionData (context : ReadContext) (body : TSyntax `cas_term)
    (base : Expr) : SourceReadM Expr := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf



  return (← readExpression categoryOf body (some base)).value

private def admissionDataApplicable (context : ReadContext) (body : TSyntax `cas_term)
    (base : Expr) : SourceReadM (Except MessageData Expr) := do
  return (← context.readExpressionApplicable context.categoryOf body (some base)).map (·.value)

def admitted (context : ReadContext) (entry : CasCatalogue.ObjectEntry)
    (body : TSyntax `cas_term) (domain : Expr) : SourceReadM Expr :=
  sourceAdmission entry domain (admissionData context body)

def constrained (context : ReadContext) (body : TSyntax `cas_term)
    (domain : Expr) (evidence : Array (TSyntax `cas_term)) :
    SourceReadM NativeSourceJudgement := do
  let proofs ← evidence.mapM fun evidence => do
    let `(cas_term| proof($proof:term)) := evidence
      | liftM (m := TermElabM) <| throwError (MessageData.tagged `CasCompiler.SourceReader.explicitProof
          "a constrained point requires explicit native proof terms")
    pure proof
  sourceConstrainedPointApplicable domain proofs (admissionDataApplicable context body)
    (context.readExpression context.categoryOf body none)

end SourceReader

end CasCompiler
