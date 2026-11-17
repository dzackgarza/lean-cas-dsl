module

public import CasCompiler.ReadContext
public import CasCompiler.SourceAdmission

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader

def admitted (context : ReadContext) :
    CasCatalogue.ObjectEntry → TSyntax `cas_term → Expr → TermElabM Expr :=
  let readExpression := @ReadContext.readExpression context
  let categoryOf := context.categoryOf
  fun (entry : CasCatalogue.ObjectEntry) (body : TSyntax `cas_term)
      (domain : Expr) => do
    sourceAdmission entry domain fun base => do
      if (← whnfR base).isForall then
        let value ← readExpression categoryOf body none
        let type ← whnfR (← inferType value.value)
        if type.isAppOfArity ``Quiver.Hom 4 || type.isAppOf ``TypeCat.Hom then
          return ← sourceSetFunction value.value
      return (← readExpression categoryOf body (some base)).value

end SourceReader

end CasCompiler
