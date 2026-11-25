module

public import CasCompiler.Elaborate

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
    Option Expr → Option String → Option NativeSourceCategory → TermElabM NativeSourceJudgement

def ReadContext.readExpression (context : ReadContext)
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) : TermElabM NativeSourceJudgement :=
  context.read categoryOf source expected qualification expectedCategory

/-- A syntax rule rejects only unmatched syntax with its private dispatch exception.
Errors from a matched construction propagate through the assembled reader. -/
abbrev ReadRule := ReadContext → TermElabM NativeSourceJudgement

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
  | `(cas_term| $_:cas_term ∈ $_:cas_term)
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
