module

public import CasCompiler.ReadContext
public import CasCompiler.SourceAdmission
public import CasCompiler.SourceConstrainedPoint

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

private def admissionData (context : ReadContext) (body : TSyntax `cas_term)
    (base : Expr) : TermElabM Expr := do
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  -- The admitted declaration supplies the data's type before its syntax is read.
  -- Selected morphisms use ReadDispatch's checked carrier-function conversion at this same
  -- boundary; literals and lambdas receive their declared domain on their only reading.
  return (← readExpression categoryOf body (some base)).value

def admitted (context : ReadContext) (entry : CasCatalogue.ObjectEntry)
    (body : TSyntax `cas_term) (domain : Expr) : TermElabM Expr :=
  sourceAdmission entry domain (admissionData context body)

def constrained (context : ReadContext) (body : TSyntax `cas_term)
    (domain : Expr) (evidence : Array (TSyntax `cas_term)) :
    TermElabM NativeSourceJudgement := do
  let proofs ← evidence.mapM fun evidence => do
    let `(cas_term| proof($proof:term)) := evidence
      | throwError (MessageData.tagged `CasCompiler.SourceReader.explicitProof
          "a constrained point requires explicit native proof terms")
    pure proof
  sourceConstrainedPoint domain proofs (admissionData context body)
    (context.readExpression context.categoryOf body none)

end SourceReader

end CasCompiler
