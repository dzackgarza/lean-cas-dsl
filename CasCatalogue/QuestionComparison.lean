/- Copyright (c) 2026 Dzack Garza. Released under Apache 2.0 license. -/
module

public import CasCatalogue.Language
public import CasCatalogue.QuestionIdentity

@[expose] public section

open Lean Meta Elab Term

namespace CasCatalogue.QuestionIdentity

/-- Infer a question's types independently of any serialized identity or cached
type list. A supplied list is checked against those actual types; it cannot change
the meaning of the retained operands. An empty list is the reader's unprepared form. -/
def questionTypes (terms recorded : Array Expr) : TermElabM (Array Expr) := do
  let terms ← terms.mapM instantiateMVars
  let types ← terms.mapM fun term => do
    if term.hasMVar || term.hasLevelMVar || term.hasFVar || term.hasLooseBVars then
      throwError "question comparison requires complete closed operands"
    unless ← isTypeCorrect term do
      throwError "question comparison received an ill-typed operand"
    instantiateMVars (← inferType term)
  unless recorded.isEmpty do
    unless recorded.size == types.size do
      throwError "the question's recorded type list has the wrong length"
    for (recordedType, actualType) in recorded.zip types do
      unless ← equivalent recordedType actualType do
        throwError "the question's recorded type differs from its actual operand type"
  return types

/-- Compare complete ordered typed operands without serializing them. -/
def equivalentOperands (left right leftTypes rightTypes : Array Expr) : TermElabM Bool := do
  let actualLeftTypes ← questionTypes left leftTypes
  let actualRightTypes ← questionTypes right rightTypes
  unless left.size == right.size do return false
  for (first, second) in actualLeftTypes.zip actualRightTypes do
    unless ← equivalent first second do return false
  for (first, second) in left.zip right do
    unless ← equivalent first second do return false
  return true

/-- Direct independent comparison of the mathematical question tree. Relation
names, ordered structural routes, selected declaration identities and logical
constructors remain significant. Only the explicitly stated typed-term identity
quotient applies to operands and their actual types. No outcome, backend, revision
label, serialized DAG, or regenerated candidate identity participates. -/
partial def equivalentQuestion (left right : Language.Question) : TermElabM Bool := do
  match left, right with
  | .proposition first, .proposition second =>
      equivalentOperands #[first] #[second] #[] #[]
  | .judgement relation terms route declarations types,
      .judgement other otherTerms otherRoute otherDeclarations otherTypes =>
      unless relation == other && route == otherRoute && declarations == otherDeclarations do
        return false
      equivalentOperands terms otherTerms types otherTypes
  | .conjunction first second, .conjunction otherFirst otherSecond =>
      equivalentQuestion first otherFirst <&&> equivalentQuestion second otherSecond
  | .negation question, .negation other => equivalentQuestion question other
  | _, _ => return false

end CasCatalogue.QuestionIdentity
