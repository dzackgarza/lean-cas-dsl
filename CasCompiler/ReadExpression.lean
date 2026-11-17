module

public import CasCompiler.ReadAtomNotation
public import CasCompiler.ReadMemberNotation
public import CasCompiler.ReadSubsetNotation
public import CasCompiler.ReadRingNotation
public import CasCompiler.ReadBinderNotation
public import CasCompiler.ReadProductNotation
public import CasCompiler.ReadLiftRules
public import CasCompiler.ReadLimitRules
public import CasCompiler.ReadOperationRules
public import CasCompiler.ReadSubsetRules
public import CasCompiler.ReadPowerRules
public import CasCompiler.ReadGraphRules
public import CasCompiler.ReadEquationRules
public import CasCompiler.ReadMemberRules
public import CasCompiler.ReadLambdaRules
public import CasCompiler.ReadNumeralRules
public import CasCompiler.ReadFunctorRules
public import CasCompiler.ReadTupleRules
public import CasCompiler.ReadNameRules
public import CasCompiler.ReadAnnotationRules
public import CasCompiler.ReadApplicationRules
public import CasCompiler.ReadProjection
public import CasCompiler.ReadDispatch
public import CasCompiler.SourceRing
import CasCompiler.SourceCarrier

public section

namespace CasCompiler

open Lean Meta Elab Term

private def sourceRules : Array ReadRule := #[
  ReadAtomNotation.rule,
  ReadMemberNotation.rule,
  ReadSubsetNotation.rule,
  ReadRingNotation.rule,
  ReadBinderNotation.rule,
  ReadProductNotation.rule,
  ReadLiftRules.rule,
  ReadLimitRules.rule,
  ReadOperationRules.rule,
  ReadSubsetRules.rule,
  ReadPowerRules.rule,
  ReadGraphRules.rule,
  ReadEquationRules.rule,
  ReadMemberRules.rule,
  ReadLambdaRules.rule,
  ReadNumeralRules.rule,
  ReadFunctorRules.rule,
  ReadTupleRules.rule,
  ReadNameRules.rule,
  ReadAnnotationRules.rule,
  ReadApplicationRules.rule
]

partial def readExpression
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (source : TSyntax `cas_term) (expected : Option Expr)
    (qualification : Option String := none)
    (expectedCategory : Option NativeSourceCategory := none) : TermElabM NativeSourceJudgement :=
  readWithRules sourceRules ⟨categoryOf, source, expected, qualification, expectedCategory,
    readProjection, fun categoryOf source expected qualification expectedCategory =>
      readExpression categoryOf source expected qualification expectedCategory⟩

/-- Read a whole source term. Each variable of a ring `R[v]` that the term writes and uses free is
bound to that ring's registered generator for this term only.
Source: the public language contract, "`R[x]`: the polynomials over `R`, whose generator `x`
names". A variable named by two different written rings is ambiguous. -/
partial def withRingVariables
    (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (recorded : Array (Name × Expr × Option Nat))
    (source : TSyntax `cas_term) (read : TermElabM NativeSourceJudgement) :
    TermElabM NativeSourceJudgement := do
  let mut written : Array (Name × Syntax × Option Nat) := #[]
  for (name, ring, index) in sourceRingVariables source.raw do
    unless sourceUses name source.raw && !sourceBinds name source.raw do continue
    if let some (_, other, _) := written.find? (·.1 == name) then
      unless other.reprint == ring.reprint do
        CasCatalogue.throwSemanticAmbiguity m!"{name} is the variable of several rings"
      continue
    written := written.push (name, ring, index)
  -- The rings of the definitions the term uses supply the variables it does not write.
  let mut inherited : Array (Name × Expr × Option Nat) := #[]
  for (name, carrier, index) in recorded do
    unless sourceUses name source.raw && !sourceBinds name source.raw do continue
    if written.any (·.1 == name) then continue
    if let some (_, other, _) := inherited.find? (·.1 == name) then
      unless other == carrier do
        CasCatalogue.throwSemanticAmbiguity m!"{name} is the variable of several rings"
      continue
    inherited := inherited.push (name, carrier, index)
  let mut bindings : Array (Name × Sum Syntax Expr × Option Nat) := #[]
  for (name, ring, index) in written do bindings := bindings.push (name, .inl ring, index)
  for (name, carrier, index) in inherited do bindings := bindings.push (name, .inr carrier, index)
  bind bindings.toList
where
  bind : List (Name × Sum Syntax Expr × Option Nat) → TermElabM NativeSourceJudgement
    | [] => read
    | (name, ring, index) :: rest => do
      if ((← getLCtx).findFromUserName? name).isSome then return ← bind rest
      let carrier ← match ring with
        | .inl ring => pure (← sourceCarrier (← readExpression categoryOf ⟨ring⟩ none)).value
        | .inr carrier => pure carrier
      let some generator ← sourceGeneratorAt? carrier index
        | throwError "the ring of {name} has no registered generator"
      withLetDecl name carrier generator fun bound => do
        let judgement ← bind rest
        return { judgement with value := ← mkLetFVars #[bound] judgement.value }

/-- Read a whole source term with its written rings' variables (`withRingVariables`). -/
def readSourceTerm (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (recorded : Array (Name × Expr × Option Nat))
    (source : TSyntax `cas_term) (expected : Option Expr) : TermElabM NativeSourceJudgement :=
  withRingVariables categoryOf recorded source (readExpression categoryOf source expected)

/-- `a = b` in a question: native equality of the operands at their common domain, as in
SourceEquality and the public claimEqual contract. Formation supplies no proof. -/
def sourceEquation (categoryOf : FVarId → TermElabM (Option NativeSourceCategory))
    (left right : TSyntax `cas_term) : TermElabM Expr := do
  let equation ← `(cas_term| $left:cas_term = $right:cas_term)
  return (← readExpression categoryOf equation (some (mkSort .zero))).value

end CasCompiler

