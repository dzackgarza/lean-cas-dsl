module

public import CasCompiler.Elaborate
public import CasCompiler.Syntax

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader
end SourceReader



structure ReadContext where
  categoryOf : FVarId → TermElabM (Option NativeSourceCategory)
  source : TSyntax `cas_term
  expected : Option Expr
  qualification : Option String
  expectedCategory : Option NativeSourceCategory
  project : NativeSourceJudgement → String → Array (TSyntax `cas_term) →
    SourceReadM (Option NativeSourceJudgement)
  read : (FVarId → TermElabM (Option NativeSourceCategory)) → TSyntax `cas_term →
    Option Expr → Option String → Option NativeSourceCategory →
      SourceReadM (Except MessageData NativeSourceJudgement)



def ReadContext.readExpressionApplicable (context : ReadContext)
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) :
    SourceReadM (Except MessageData NativeSourceJudgement) :=
  context.read categoryOf source expected qualification expectedCategory

def ReadContext.readExpression (context : ReadContext)
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) : SourceReadM NativeSourceJudgement :=
  SourceReadM.withRef source do
    match ← context.readExpressionApplicable categoryOf source expected qualification expectedCategory with
    | .ok value => pure value
    | .error message => liftM (m := TermElabM) <| throwError message



abbrev ReadRule := ReadContext → SourceReadM NativeSourceJudgement



abbrev ReadApplicableRule :=
  ReadContext → SourceReadM (Except MessageData NativeSourceJudgement)

def ReadRule.applicable (rule : ReadRule) : ReadApplicableRule := fun context => do
  return .ok (← rule context)



abbrev ReadCompletion :=
  NativeSourceJudgement → SourceReadM (Except MessageData NativeSourceJudgement)



abbrev ReadCompletingRule :=
  ReadContext → ReadCompletion → SourceReadM (Except MessageData NativeSourceJudgement)

def ReadApplicableRule.completing (rule : ReadApplicableRule) : ReadCompletingRule :=
  fun context complete => do
    match ← rule context with
    | .ok value => complete value
    | .error message => pure (.error message)

def ReadRule.completing (rule : ReadRule) : ReadCompletingRule :=
  ReadApplicableRule.completing (ReadRule.applicable rule)

initialize readRuleMismatch : InternalExceptionId ← registerInternalExceptionId `cas.readRuleMismatch


def throwReadRuleMismatch : SourceReadM α := throw (Exception.internal readRuleMismatch)

def sourceAtomName? (source : Syntax) : Option String :=
  if source.isOfKind ``CasCatalogue.Language.casAtom ||
      source.isOfKind ``CasCatalogue.Language.casDomainAtom then

    some source[0][0].getAtomVal
  else none


partial def sourceNumeric (source : Syntax) : Bool :=
  !source.isIdent && !(source.isAtom &&
    (source.getAtomVal == "√" || source.getAtomVal == "|")) && source.getArgs.all sourceNumeric




partial def sourcePrincipal (source : TSyntax `cas_term) : TermElabM Bool := do
  match source with
  | `(cas_term| ($inner:cas_term)) => sourcePrincipal inner
  | `(cas_term| $name:ident) =>
    return ((← getLCtx).findFromUserName? name.getId).isSome
  | `(cas_term| $_:cas_term in $_:cas_term)
  | `(cas_term| $_:cas_term → $_:cas_term)
  | `(cas_term| $_:cas_term × $_:cas_term)
  | `(cas_term| $_:cas_term ⊔ $_:cas_term)
  | `(cas_term| $_:cas_term ∘ $_:cas_term)
  | `(cas_term| |$_:cas_term|)
  | `(cas_term| view $_:cas_term along $_:ident)
  | `(cas_term| view $_:cas_term along $_:ident($_:cas_term,*))
  | `(cas_term| map $_:cas_term along $_:ident($_:cas_term,*)) => return true
  | `(cas_term| $name:ident($_:cas_term,*)) =>
    return name.getId == `id && ((← getLCtx).findFromUserName? name.getId).isNone
  | _ => return false

end CasCompiler
