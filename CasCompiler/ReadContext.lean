module

public import CasCompiler.Elaborate
public import CasCompiler.Syntax

public section

namespace CasCompiler

open Lean Meta Elab Term

namespace SourceReader
end SourceReader

/-- The typed context of one source-reading rule. Recursive calls return through the assembled
reader; rules retain the actual Lean expressions and selected categories. -/
structure ReadContext where
  categoryOf : FVarId → TermElabM (Option NativeSourceCategory)
  source : TSyntax `cas_term
  expected : Option Expr
  qualification : Option String
  expectedCategory : Option NativeSourceCategory
  project : NativeSourceJudgement → String → Array (TSyntax `cas_term) →
    TermElabM (Option NativeSourceJudgement)
  read : (FVarId → TermElabM (Option NativeSourceCategory)) → TSyntax `cas_term →
    Option Expr → Option String → Option NativeSourceCategory →
      TermElabM (Except MessageData NativeSourceJudgement)

/-- The result of this operand's own native expected-type check. Recursive source readings
remain ordinary readings: their exceptions cannot reject a containing candidate. -/
def ReadContext.readExpressionApplicable (context : ReadContext)
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) :
    TermElabM (Except MessageData NativeSourceJudgement) :=
  context.read categoryOf source expected qualification expectedCategory

def ReadContext.readExpression (context : ReadContext)
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) : TermElabM NativeSourceJudgement :=
  withRef source do
    match ← context.readExpressionApplicable categoryOf source expected qualification expectedCategory with
    | .ok value => pure value
    | .error message => throwError message

/-- A syntax rule rejects only unmatched syntax with its private dispatch exception.
Errors from a matched construction propagate through the assembled reader. -/
abbrev ReadRule := ReadContext → TermElabM NativeSourceJudgement

/-- A matched rule may reject only its own explicit native expected-type comparison.
Unmatched syntax and semantic exceptions keep the ordinary rule contract. -/
abbrev ReadApplicableRule :=
  ReadContext → TermElabM (Except MessageData NativeSourceJudgement)

def ReadRule.applicable (rule : ReadRule) : ReadApplicableRule := fun context => do
  return .ok (← rule context)

initialize readRuleMismatch : InternalExceptionId ← registerInternalExceptionId `cas.readRuleMismatch

/-- Used only at a rule's unmatched syntax branch, never for a failed interpretation. -/
def throwReadRuleMismatch : TermElabM α := throw (Exception.internal readRuleMismatch)

def sourceAtomName? (source : Syntax) : Option String :=
  if source.isOfKind ``CasCatalogue.Language.casAtom ||
      source.isOfKind ``CasCatalogue.Language.casDomainAtom then
    -- Lean's alternative-token parser retains a token-kind node around its actual atom.
    some source[0][0].getAtomVal
  else none

-- Reuse Language.numeric's source rule: numeral-only syntax has no chosen set yet.
partial def sourceNumeric (source : Syntax) : Bool :=
  !source.isIdent && !(source.isAtom &&
    (source.getAtomVal == "√" || source.getAtomVal == "|")) && source.getArgs.all sourceNumeric

-- These forms determine their category and type from their own source inputs.
-- Other forms retain expected-type flow, including unqualified registered objects,
-- literals, tuples, lambdas and applications with implicit parameters.
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
